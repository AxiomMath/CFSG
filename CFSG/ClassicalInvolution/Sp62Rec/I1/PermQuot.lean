module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ClassicalInvolution.Q3.AE.Wreath
import CFSG.ClassicalInvolution.Q3.AE.Models
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem commutator_le_of_sup {Γ : Type*} [Group Γ] (N Zs : Subgroup Γ) [N.Normal]
    (hZ : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x) (hsup : Zs ⊔ N = ⊤) : commutator Γ ≤ N := by
  have hdec : ∀ a : Γ, ∃ z ∈ Zs, ∃ n ∈ N, a = z * n := by
    intro a
    have : a ∈ ((Zs ⊔ N : Subgroup Γ) : Set Γ) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal] at this
    obtain ⟨z, hz, n, hn, rfl⟩ := this
    exact ⟨z, hz, n, hn, rfl⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := hdec a
  obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := hdec b
  rw [← QuotientGroup.eq_one_iff (N := N)]
  have h1 : (z₁ * n₁ : Γ) = z₁ * n₁ := rfl
  simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    (QuotientGroup.eq_one_iff n₁).mpr hn₁, (QuotientGroup.eq_one_iff n₂).mpr hn₂, mul_one,
    inv_one]
  have := hZ z₁ hz₁ z₂ hz₂
  have h2 : ((z₁ : Γ) : Γ ⧸ N) * (z₂ : Γ ⧸ N) = (z₂ : Γ ⧸ N) * (z₁ : Γ ⧸ N) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  calc ((z₁ : Γ ⧸ N) * (z₂ : Γ ⧸ N) * (z₁ : Γ ⧸ N)⁻¹ * (z₂ : Γ ⧸ N)⁻¹)
      = ((z₂ : Γ ⧸ N) * (z₁ : Γ ⧸ N) * (z₁ : Γ ⧸ N)⁻¹ * (z₂ : Γ ⧸ N)⁻¹) := by rw [h2]
    _ = 1 := by group

theorem map_perm_eq_alternating {Γ : Type*} [Group Γ] (N Zs : Subgroup Γ) [N.Normal]
    (hZ : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x) (hsup : Zs ⊔ N = ⊤)
    (ρ : Γ →* Perm (Fin 6)) (hρ : Function.Surjective ρ)
    (hN : ∀ x ∈ N, Perm.sign (ρ x) = 1) :
    N.map ρ = alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Perm.mem_alternatingGroup.mpr (hN x hx)
  · rw [← alternatingGroup.commutator_perm_eq (α := Fin 6) (by simp)]
    have h1 : (commutator Γ).map ρ = commutator (Perm (Fin 6)) := by
      rw [commutator, commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρ]
    rw [← h1]
    exact Subgroup.map_mono (commutator_le_of_sup N Zs hZ hsup)

theorem exists_odd_mem_of_perm_quotient {Γ : Type*} [Group Γ] (N Zs : Subgroup Γ) [N.Normal]
    (hZ : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x) (hsup : Zs ⊔ N = ⊤)
    (ρ : Γ →* Perm (Fin 6)) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ N)
    (hN : ∀ x ∈ N, Perm.sign (ρ x) = 1) :
    ∃ τ ∈ Zs, τ ∉ N ∧ Perm.sign (ρ τ) = -1 ∧ ∀ g : Γ, g ∈ N ∨ g * τ⁻¹ ∈ N := by
  have hmap := map_perm_eq_alternating N Zs hZ hsup ρ hρ hN
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Γ, Perm.sign (ρ g₀) = -1 := by
    obtain ⟨s, hs⟩ := Perm.sign_surjective (Fin 6) (-1 : ℤˣ)
    obtain ⟨g, rfl⟩ := hρ s
    exact ⟨g, hs⟩
  have hdec : ∃ z ∈ Zs, ∃ n ∈ N, g₀ = z * n := by
    have : g₀ ∈ ((Zs ⊔ N : Subgroup Γ) : Set Γ) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal] at this
    obtain ⟨z, hz, n, hn, h⟩ := this
    exact ⟨z, hz, n, hn, h.symm⟩
  obtain ⟨z, hz, n, hn, rfl⟩ := hdec
  have hzs : Perm.sign (ρ z) = -1 := by
    have := hg₀
    rw [map_mul, map_mul, hN n hn, mul_one] at this
    exact this
  have hτN : z ∉ N := fun h => by rw [hN z h] at hzs; exact absurd hzs (by decide)
  refine ⟨z, hz, hτN, hzs, fun g => ?_⟩
  by_cases hg : Perm.sign (ρ g) = 1
  · left
    have : ρ g ∈ N.map ρ := by rw [hmap]; exact Perm.mem_alternatingGroup.mpr hg
    obtain ⟨x, hx, hxg⟩ := this
    have : x⁻¹ * g ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
    have h2 := hker this
    simpa using N.mul_mem hx h2
  · right
    have hg' : Perm.sign (ρ g) = -1 := by
      rcases Int.units_eq_one_or (Perm.sign (ρ g)) with h | h
      · exact absurd h hg
      · exact h
    have : Perm.sign (ρ (g * z⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hg', hzs]; decide
    have hmem : ρ (g * z⁻¹) ∈ N.map ρ := by rw [hmap]; exact Perm.mem_alternatingGroup.mpr this
    obtain ⟨x, hx, hxg⟩ := hmem
    have : x⁻¹ * (g * z⁻¹) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
    have h2 := hker this
    simpa using N.mul_mem hx h2

theorem center_perm_fin_six_eq_bot : Subgroup.center (Perm (Fin 6)) = ⊥ := by
  have hex : ∀ a : Fin 6, ∃ b b' : Fin 6, b ≠ a ∧ b' ≠ a ∧ b ≠ b' := by decide
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_center_iff] at hc
  rw [Subgroup.mem_bot]
  refine Perm.ext fun a => ?_
  have key : ∀ b : Fin 6, b ≠ a → c a = a ∨ c a = b := by
    intro b hb
    have h := congrArg (fun g : Perm (Fin 6) => g a) (hc (swap a b))
    simp only [Perm.mul_apply, swap_apply_left] at h
    by_cases h1 : c a = a
    · exact Or.inl h1
    · by_cases h2 : c a = b
      · exact Or.inr h2
      · rw [swap_apply_of_ne_of_ne h1 h2] at h
        exact absurd (c.injective h).symm hb
  obtain ⟨b, b', hb, hb', hbb'⟩ := hex a
  rcases key b hb with h | h
  · simpa using h
  · rcases key b' hb' with h' | h'
    · simpa using h'
    · exact absurd (h.symm.trans h') hbb'

theorem mem_of_central_of_perm_quotient {Γ : Type*} [Group Γ] (N : Subgroup Γ)
    (ρ : Γ →* Perm (Fin 6)) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ N) {c : Γ}
    (hc : ∀ g : Γ, g * c = c * g) : c ∈ N := by
  have : ρ c ∈ Subgroup.center (Perm (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨g, rfl⟩ := hρ s
    rw [← map_mul, ← map_mul, hc g]
  rw [center_perm_fin_six_eq_bot, Subgroup.mem_bot] at this
  exact hker (MonoidHom.mem_ker.mpr this)

theorem eq_one_of_commute_alternating (c : Perm (Fin 6))
    (hc : ∀ a ∈ alternatingGroup (Fin 6), c * a = a * c) : c = 1 := by
  by_cases hs : Perm.sign c = 1
  · have hcA : c ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr hs
    have : (⟨c, hcA⟩ : alternatingGroup (Fin 6)) ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (hc a a.2).symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have hs' : Perm.sign c = -1 := by
      rcases Int.units_eq_one_or (Perm.sign c) with h | h
      · exact absurd h hs
      · exact h
    have hcen : c ∈ Subgroup.center (Perm (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hg : Perm.sign g = 1
      · exact (hc g (Perm.mem_alternatingGroup.mpr hg)).symm
      · have hg' : Perm.sign g = -1 := by
          rcases Int.units_eq_one_or (Perm.sign g) with h | h
          · exact absurd h hg
          · exact h
        have hgc : g * c ∈ alternatingGroup (Fin 6) := by
          rw [Perm.mem_alternatingGroup, map_mul, hg', hs']; decide
        have := hc (g * c) hgc
        have h2 : c * g * c = g * c * c := by
          calc c * g * c = c * (g * c) := by group
            _ = (g * c) * c := this
        exact (mul_right_cancel h2).symm
    rw [center_perm_fin_six_eq_bot, Subgroup.mem_bot] at hcen
    rw [hcen] at hs'
    simp at hs'

theorem hom_eq_one_of_perfect_quotient {N Q A : Type*} [Group N] [Group Q] [CommGroup A]
    (q : N →* Q) (hq : Function.Surjective q) (hQ : Group.IsPerfect Q) (s : N →* A)
    (hs : q.ker ≤ s.ker) : s = 1 := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let s' : Q →* A := (QuotientGroup.lift q.ker s hs).comp e.symm.toMonoidHom
  have hs' : ∀ y, s' y = 1 := by
    have hcomm : commutator Q ≤ s'.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      simp [commutatorElement_def, MonoidHom.mem_ker, map_mul, mul_comm]
    have htop : commutator Q = ⊤ := hQ.commutator_eq_top
    intro y
    exact MonoidHom.mem_ker.mp (hcomm (htop ▸ Subgroup.mem_top y))
  ext x
  have h1 : e.symm (q x) = (x : N ⧸ q.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have : s' (q x) = s x := by
    show (QuotientGroup.lift q.ker s hs) (e.symm (q x)) = s x
    rw [h1, QuotientGroup.lift_mk]
  rw [← this, hs']
  rfl

theorem normal_le_alternating_eq {T : Subgroup (Perm (Fin 6))} (hT : T ≤ alternatingGroup (Fin 6))
    (hn : ∀ a ∈ alternatingGroup (Fin 6), ∀ x ∈ T, a * x * a⁻¹ ∈ T) :
    T = ⊥ ∨ T = alternatingGroup (Fin 6) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hnorm : (T.subgroupOf (alternatingGroup (Fin 6))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn g g.2 x hx
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf (alternatingGroup (Fin 6)))
    with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxA := hT hx
    have : (⟨x, hxA⟩ : alternatingGroup (Fin 6)) ∈ T.subgroupOf (alternatingGroup (Fin 6)) := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    refine le_antisymm hT fun x hx => ?_
    have : (⟨x, hx⟩ : alternatingGroup (Fin 6)) ∈ T.subgroupOf (alternatingGroup (Fin 6)) := by
      rw [h]; trivial
    exact this

theorem wr_sq_eq_one_of_perm_eq_one {a : Wr 6} (h : a.perm = 1) : a * a = 1 := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, h]
    exact zmod_two_add_self _
  · rw [mul_perm, h, mul_one]; rfl

theorem exists_three_cycle_alt : ∃ g ∈ alternatingGroup (Fin 6), g * g ≠ 1 := by
  refine ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide), by decide⟩

theorem rho_eq_one_of_perm_eq_one {N Γ : Type*} [Group N] [Group Γ] (ι : N →* Γ)
    (ρ : Γ →* Perm (Fin 6)) (hρN : ι.range.map ρ = alternatingGroup (Fin 6))
    (f : N →* Wr 6) (hker : ∀ x : N, f x = 1 → Odd (orderOf x)) :
    ∀ x : N, (f x).perm = 1 → ρ (ι x) = 1 := by
  set θ : N →* Perm (Fin 6) := ρ.comp ι with hθ
  have hθr : θ.range = alternatingGroup (Fin 6) := by
    rw [← hρN, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
  have hθA : ∀ x : N, θ x ∈ alternatingGroup (Fin 6) := fun x => hθr ▸ ⟨x, rfl⟩
  have hθs : ∀ a ∈ alternatingGroup (Fin 6), ∃ n : N, θ n = a := fun a ha => by
    rw [← hθr] at ha; exact ha
  have hnorm : ∀ K : Subgroup N, K.Normal → ∀ a ∈ alternatingGroup (Fin 6), ∀ x ∈ K.map θ,
      a * x * a⁻¹ ∈ K.map θ := by
    intro K hK a ha x hx
    obtain ⟨n, rfl⟩ := hθs a ha
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨n * k * n⁻¹, hK.conj_mem k hk n, by simp [map_mul]⟩
  have hkf : f.ker.map θ = ⊥ := by
    have hle : f.ker.map θ ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨x, _, rfl⟩; exact hθA x
    rcases normal_le_alternating_eq hle (hnorm _ inferInstance) with h | h
    · exact h
    · exfalso
      have hg : swap 0 1 * swap 2 3 ∈ f.ker.map θ := by
        rw [h]; exact Perm.mem_alternatingGroup.mpr (by decide)
      obtain ⟨x, hx, hxg⟩ := hg
      obtain ⟨k, hk⟩ := hker x hx
      have h1 : (swap 0 1 * swap 2 3 : Perm (Fin 6)) ^ orderOf x = 1 := by
        rw [← hxg, ← map_pow, pow_orderOf_eq_one, map_one]
      have h2 : (swap 0 1 * swap 2 3 : Perm (Fin 6)) ^ 2 = 1 := by decide
      have h3 : (swap 0 1 * swap 2 3 : Perm (Fin 6)) ^ orderOf x = swap 0 1 * swap 2 3 := by
        rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
      rw [h3] at h1
      exact absurd h1 (by decide)
  have hker' : ∀ x : N, f x = 1 → θ x = 1 := fun x hx => by
    have : θ x ∈ f.ker.map θ := ⟨x, hx, rfl⟩
    rw [hkf, Subgroup.mem_bot] at this; exact this
  intro x hx
  let M : Subgroup N := ((permHom 6).comp f).ker
  have hM : M.Normal := MonoidHom.normal_ker _
  have hMA : M.map θ ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨y, _, rfl⟩; exact hθA y
  have hsq : ∀ y ∈ M.map θ, y * y = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    have hperm : (f m).perm = 1 := hm
    have h1 : f (m * m) = 1 := by rw [map_mul]; exact wr_sq_eq_one_of_perm_eq_one hperm
    rw [← map_mul]
    exact hker' _ h1
  rcases normal_le_alternating_eq hMA (hnorm _ hM) with h | h
  · have : θ x ∈ M.map θ := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨g, hg, hg2⟩ := exists_three_cycle_alt
    have : g ∈ M.map θ := by rw [h]; exact hg
    exact hg2 (hsq g this)

theorem sign_perm_eq_neg_one {N Γ : Type*} [Group N] [Group Γ] (ι : N →* Γ)
    (ρ : Γ →* Perm (Fin 6)) (hρN : ι.range.map ρ = alternatingGroup (Fin 6))
    (f : N →* Wr 6) (hfalt : ∀ s ∈ alternatingGroup (Fin 6), ∃ x : N, (f x).perm = s)
    (hker : ∀ x : N, (f x).perm = 1 → ρ (ι x) = 1)
    (τ : Γ) (hτ : Perm.sign (ρ τ) = -1) (w : Wr 6)
    (hτN : ∀ x : N, ∃ y : N, ι y = τ * ι x * τ⁻¹)
    (hw : ∀ (x y : N), ι y = τ * ι x * τ⁻¹ → f y = w * f x * w⁻¹) :
    Perm.sign w.perm = -1 := by
  set θ : N →* Perm (Fin 6) := ρ.comp ι with hθ
  have hθr : θ.range = alternatingGroup (Fin 6) := by
    rw [← hρN, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
  have hθA : ∀ x : N, θ x ∈ alternatingGroup (Fin 6) := fun x => hθr ▸ ⟨x, rfl⟩
  have hθs : ∀ a ∈ alternatingGroup (Fin 6), ∃ n : N, θ n = a := fun a ha => by
    rw [← hθr] at ha; exact ha
  by_contra hne
  have hσ : Perm.sign w.perm = 1 := by
    rcases Int.units_eq_one_or (Perm.sign w.perm) with h | h
    · exact h
    · exact absurd h hne
  have hσA : w.perm ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr hσ
  obtain ⟨x₀, hx₀⟩ := hfalt w.perm⁻¹ (inv_mem hσA)
  have hcomm : ∀ a ∈ alternatingGroup (Fin 6), (ρ (τ * ι x₀)) * a = a * (ρ (τ * ι x₀)) := by
    intro a ha
    obtain ⟨y, rfl⟩ := hθs a ha
    obtain ⟨y', hy'⟩ := hτN (x₀ * y * x₀⁻¹)
    have hy'' : ι y' = (τ * ι x₀) * ι y * (τ * ι x₀)⁻¹ := by
      rw [hy']; simp [map_mul]; group
    have hf1 : f y' = w * f (x₀ * y * x₀⁻¹) * w⁻¹ := hw _ _ hy'
    have hperm : (f y').perm = (f y).perm := by
      have : (f y').perm = w.perm * ((f x₀).perm * (f y).perm * (f x₀).perm⁻¹) * w.perm⁻¹ := by
        rw [hf1]; simp [map_mul, mul_perm, inv_perm]
      rw [this, hx₀]; group
    have h1 : (f (y'⁻¹ * y)).perm = 1 := by
      rw [map_mul, map_inv, mul_perm, inv_perm, hperm]; simp
    have h2 := hker _ h1
    rw [map_mul, map_inv] at h2
    have h3 : ρ (ι y') = ρ (ι y) := by
      have := h2
      simpa [mul_eq_one_iff_eq_inv] using this
    show _ * θ y = θ y * _
    have : ρ (ι y') = ρ (τ * ι x₀) * θ y * (ρ (τ * ι x₀))⁻¹ := by
      rw [hy'', map_mul, map_mul, map_inv]; rfl
    rw [h3] at this
    have h4 : θ y * ρ (τ * ι x₀) = ρ (τ * ι x₀) * θ y := by
      calc θ y * ρ (τ * ι x₀) = (ρ (τ * ι x₀) * θ y * (ρ (τ * ι x₀))⁻¹) * ρ (τ * ι x₀) := by
            rw [← this]; rfl
        _ = ρ (τ * ι x₀) * θ y := by group
    exact h4.symm
  have hone := eq_one_of_commute_alternating _ hcomm
  have hsgn : Perm.sign (ρ (τ * ι x₀)) = -1 := by
    have := hθA x₀
    have h' : Perm.sign (ρ (ι x₀)) = 1 := Perm.mem_alternatingGroup.mp this
    simp only [map_mul, hτ, h']; simp
  rw [hone] at hsgn
  simp at hsgn

end CFSG.ClassicalInvolution.Sp62Rec.I1
