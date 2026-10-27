module

public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Subgroup
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem exists_minimal_subgroup [Finite M] (P : Subgroup M → Prop) {H₀ : Subgroup M}
    (h₀ : P H₀) : ∃ H : Subgroup M, H ≤ H₀ ∧ P H ∧ ∀ H' : Subgroup M, H' ≤ H → P H' → H' = H := by
  classical
  have hex : ∃ n : ℕ, ∃ H : Subgroup M, H ≤ H₀ ∧ P H ∧ Nat.card H = n := ⟨_, H₀, le_rfl, h₀, rfl⟩
  obtain ⟨H, hHH₀, hPH, hcard⟩ := Nat.find_spec hex
  refine ⟨H, hHH₀, hPH, fun H' hle hP' => ?_⟩
  have hmin := Nat.find_min' hex ⟨H', hle.trans hHH₀, hP', rfl⟩
  exact eq_of_le_of_card_ge hle (hcard ▸ hmin)

theorem closure_comm {S : Set M} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  have h1 : closure S ≤ centralizer S :=
    (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb => hS b hb a ha
  intro a ha b hb
  exact (mem_centralizer_iff.mp (closure_le_centralizer_centralizer S ha) b (h1 hb)).symm

theorem abelian_exponent_of_minimal [Finite M] {S : Subgroup M} {H : Subgroup M}
    (hodd : Odd (Nat.card H)) (hne : H ≠ ⊥) (hconj : ∀ g ∈ S, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hmin : ∀ H' : Subgroup M, H' ≤ H → H' ≠ ⊥ → (∀ g ∈ S, ∀ h ∈ H', g * h * g⁻¹ ∈ H') →
      H' = H) :
    (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧ ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ ∀ h ∈ H, h ^ l = 1 := by
  classical
  have hCH : ⁅H, H⁆ ≤ H := commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hCconj : ∀ g ∈ S, ∀ c ∈ ⁅H, H⁆, g * c * g⁻¹ ∈ ⁅H, H⁆ := by
    intro g hg c hc
    have hle : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [commutator_le]
      intro a ha b hb
      rw [mem_comap]
      change g * ⁅a, b⁆ * g⁻¹ ∈ _
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact commutator_mem_commutator (hconj g hg a ha) (hconj g hg b hb)
    exact hle hc
  have hCne : ⁅H, H⁆ ≠ H := by
    intro heq
    have hsolv : Group.IsSolvable H := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hne
    have htop : commutator H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [map_subtype_commutator, heq, ← MonoidHom.range_eq_map, range_subtype]
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne htop
  have hCbot : ⁅H, H⁆ = ⊥ := by
    by_contra hC
    exact hCne (hmin _ hCH hC hCconj)
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅H, H⁆ := commutator_mem_commutator ha hb
    rw [hCbot, mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  refine ⟨hcomm, ?_⟩
  have hcard1 : Nat.card H ≠ 1 := fun h => hne ((card_eq_one).mp h)
  obtain ⟨l, hl, hldvd⟩ := Nat.exists_prime_and_dvd hcard1
  have hl2 : l ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hldvd)
  refine ⟨l, hl, hl2, ?_⟩
  let Ω : Subgroup M :=
    { carrier := {h | h ∈ H ∧ h ^ l = 1}
      one_mem' := ⟨H.one_mem, one_pow l⟩
      mul_mem' := by
        rintro a b ⟨ha, hal⟩ ⟨hb, hbl⟩
        refine ⟨H.mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hcomm a ha b hb).mul_pow, hal, hbl, one_mul]
      inv_mem' := by
        rintro a ⟨ha, hal⟩
        exact ⟨H.inv_mem ha, by rw [inv_pow, hal, inv_one]⟩ }
  have hΩH : Ω ≤ H := fun h hh => hh.1
  have hΩne : Ω ≠ ⊥ := by
    have : Fact l.Prime := ⟨hl⟩
    let _ : Fintype H := Fintype.ofFinite H
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card (G := H) l
      (by rwa [← Nat.card_eq_fintype_card])
    intro hbot
    have hh' : orderOf (h : M) = l := by rw [Subgroup.orderOf_coe, hh]
    have hmem : (h : M) ∈ Ω := ⟨h.2, by rw [← hh', pow_orderOf_eq_one]⟩
    rw [hbot, mem_bot] at hmem
    rw [hmem, orderOf_one] at hh'
    exact hl.one_lt.ne hh'
  have hΩconj : ∀ g ∈ S, ∀ h ∈ Ω, g * h * g⁻¹ ∈ Ω := by
    rintro g hg h ⟨hh, hhl⟩
    exact ⟨hconj g hg h hh, by rw [conj_pow, hhl, mul_one, mul_inv_cancel]⟩
  have hΩeq := hmin Ω hΩH hΩne hΩconj
  intro h hh
  rw [← hΩeq] at hh
  exact hh.2

theorem conj_eq_inv_of_comm {H : Subgroup M} (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {s w : M} (hs2 : s * s = 1) (hsH : ∀ h ∈ H, s * h * s⁻¹ ∈ H) (hsw : s * w = w * s)
    (hfree : ∀ h ∈ H, h * s = s * h → h * w = w * h → h = 1)
    {h : M} (hh : h ∈ H) (hhw : h * w = w * h) : s * h * s⁻¹ = h⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨h', hh'⟩ : ∃ h', h' = s * h * s⁻¹ := ⟨_, rfl⟩
  rw [← hh']
  have hh'H : h' ∈ H := by rw [hh']; exact hsH h hh
  have e1 : h' * s = s * h := by rw [hh']; group
  have e2 : s * h' = h * s := by
    rw [hh']
    calc s * (s * h * s⁻¹) = (s * s) * h * s⁻¹ := by group
      _ = h * s := by rw [hs2, hsinv]; group
  have e3 : h' * w = w * h' := by
    have hsw' : s⁻¹ * w = w * s⁻¹ := by rw [hsinv]; exact hsw
    rw [hh']
    calc s * h * s⁻¹ * w = s * h * (s⁻¹ * w) := by group
      _ = s * h * (w * s⁻¹) := by rw [hsw']
      _ = s * (h * w) * s⁻¹ := by group
      _ = s * (w * h) * s⁻¹ := by rw [hhw]
      _ = (s * w) * h * s⁻¹ := by group
      _ = (w * s) * h * s⁻¹ := by rw [hsw]
      _ = w * (s * h * s⁻¹) := by group
  have hk : h * h' = 1 := by
    apply hfree _ (H.mul_mem hh hh'H)
    · calc h * h' * s = h * (s * h) := by rw [mul_assoc, e1]
        _ = (h * s) * h := by group
        _ = (s * h') * h := by rw [e2]
        _ = s * (h' * h) := by group
        _ = s * (h * h') := by rw [hHcomm h' hh'H h hh]
    · calc h * h' * w = h * (h' * w) := by group
        _ = h * (w * h') := by rw [e3]
        _ = (h * w) * h' := by group
        _ = (w * h) * h' := by rw [hhw]
        _ = w * (h * h') := by group
  exact eq_inv_of_mul_eq_one_right hk

theorem exists_ne_one_comm {H : Subgroup M} (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hne : H ≠ ⊥) {t v y : M} (ht2 : t * t = 1) (hv2 : v * v = 1)
    (htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H) (hvH : ∀ h ∈ H, v * h * v⁻¹ ∈ H)
    (hyH : ∀ h ∈ H, y * h * y⁻¹ ∈ H) (hyt : y⁻¹ * t * y = v) (hyv : y⁻¹ * v * y = t * v) :
    ∃ x ∈ H, x ≠ 1 ∧ x * t = t * x := by
  by_contra hcon
  have hCt : ∀ x ∈ H, x * t = t * x → x = 1 := fun x hx hxt =>
    by_contra fun h1 => hcon ⟨x, hx, h1, hxt⟩
  have hyv' : y * v * y⁻¹ = t := by rw [← hyt]; group
  have hytv' : y * (t * v) * y⁻¹ = v := by rw [← hyv]; group
  have hconj_eq : ∀ a b : M, y * b * y⁻¹ = a → ∀ x ∈ H, x * b = b * x →
      (y * x * y⁻¹) * a = a * (y * x * y⁻¹) := by
    intro a b hab x _ hxb
    rw [← hab]
    calc y * x * y⁻¹ * (y * b * y⁻¹) = y * (x * b) * y⁻¹ := by group
      _ = y * (b * x) * y⁻¹ := by rw [hxb]
      _ = y * b * y⁻¹ * (y * x * y⁻¹) := by group
  have hback : ∀ x : M, y * x * y⁻¹ = 1 → x = 1 := fun x h1 => by
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hCv : ∀ x ∈ H, x * v = v * x → x = 1 := fun x hx hxv =>
    hback x (hCt _ (hyH x hx) (hconj_eq t v hyv' x hx hxv))
  have hCtv : ∀ x ∈ H, x * (t * v) = (t * v) * x → x = 1 := fun x hx hxtv =>
    hback x (hCv _ (hyH x hx) (hconj_eq v (t * v) hytv' x hx hxtv))
  have hinv : ∀ s : M, s * s = 1 → (∀ h ∈ H, s * h * s⁻¹ ∈ H) →
      (∀ x ∈ H, x * s = s * x → x = 1) → ∀ h ∈ H, s * h * s⁻¹ = h⁻¹ := by
    intro s hs2 hsH hCs h hh
    exact conj_eq_inv_of_comm hHcomm (w := 1) hs2 hsH (by simp)
      (fun x hx hxs _ => hCs x hx hxs) hh (by simp)
  have htinvH := hinv t ht2 htH hCt
  have hvinvH := hinv v hv2 hvH hCv
  apply hne
  rw [eq_bot_iff]
  intro h hh
  rw [mem_bot]
  apply hCtv h hh
  have e : (t * v) * h * (t * v)⁻¹ = h := by
    calc (t * v) * h * (t * v)⁻¹ = t * (v * h * v⁻¹) * t⁻¹ := by group
      _ = t * h⁻¹ * t⁻¹ := by rw [hvinvH h hh]
      _ = (t * h * t⁻¹)⁻¹ := by group
      _ = h := by rw [htinvH h hh, inv_inv]
  calc h * (t * v) = ((t * v) * h * (t * v)⁻¹) * (t * v) := by rw [e]
    _ = (t * v) * h := by group

theorem indep_of_inv {C : Type*} [CommGroup C] {x₁ x₂ x₃ : C} {l : ℕ} (hl : l.Prime)
    (hl2 : l ≠ 2) (ho₁ : orderOf x₁ = l) (ho₂ : orderOf x₂ = l) (ho₃ : orderOf x₃ = l)
    (σ τ : C →* C) (hσ₁ : σ x₁ = x₁) (hσ₂ : σ x₂ = x₂⁻¹) (hσ₃ : σ x₃ = x₃⁻¹)
    (hτ₁ : τ x₁ = x₁⁻¹) (hτ₂ : τ x₂ = x₂) (hτ₃ : τ x₃ = x₃⁻¹) :
    ∀ α β γ : ℕ, x₁ ^ α * x₂ ^ β * x₃ ^ γ = 1 → l ∣ α ∧ l ∣ β ∧ l ∣ γ := by
  intro α β γ h
  have hσ := congrArg σ h
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hσ₁, hσ₂, hσ₃, map_one, inv_pow,
    inv_pow] at hσ
  have hτ := congrArg τ h
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hτ₁, hτ₂, hτ₃, map_one, inv_pow,
    inv_pow] at hτ
  have hcop : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have key₁ : x₁ ^ α * x₂ ^ β * x₃ ^ γ * (x₁ ^ α * (x₂ ^ β)⁻¹ * (x₃ ^ γ)⁻¹) =
      x₁ ^ (2 * α) := by
    rw [mul_mul_mul_comm (x₁ ^ α * x₂ ^ β), mul_mul_mul_comm (x₁ ^ α) (x₂ ^ β), mul_inv_cancel,
      mul_inv_cancel, mul_one, mul_one, ← pow_add, two_mul]
  have key₂ : x₁ ^ α * x₂ ^ β * x₃ ^ γ * ((x₁ ^ α)⁻¹ * x₂ ^ β * (x₃ ^ γ)⁻¹) =
      x₂ ^ (2 * β) := by
    rw [mul_mul_mul_comm (x₁ ^ α * x₂ ^ β), mul_mul_mul_comm (x₁ ^ α) (x₂ ^ β), mul_inv_cancel,
      mul_inv_cancel, one_mul, mul_one, ← pow_add, two_mul]
  have h1 : x₁ ^ (2 * α) = 1 := by rw [← key₁, h, hσ, one_mul]
  have h2 : x₂ ^ (2 * β) = 1 := by rw [← key₂, h, hτ, one_mul]
  have dα : l ∣ α := hcop.dvd_of_dvd_mul_left (ho₁ ▸ orderOf_dvd_of_pow_eq_one h1)
  have dβ : l ∣ β := hcop.dvd_of_dvd_mul_left (ho₂ ▸ orderOf_dvd_of_pow_eq_one h2)
  have hα1 : x₁ ^ α = 1 := orderOf_dvd_iff_pow_eq_one.mp (ho₁ ▸ dα)
  have hβ1 : x₂ ^ β = 1 := orderOf_dvd_iff_pow_eq_one.mp (ho₂ ▸ dβ)
  rw [hα1, hβ1, one_mul, one_mul] at h
  exact ⟨dα, dβ, ho₃ ▸ orderOf_dvd_of_pow_eq_one h⟩

end SixNineCount

end CFSG.SeitzReduction.RankOne
