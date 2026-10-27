module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Data

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] (N : Subgroup G)

theorem s7tg_map_perfect (M : Subgroup ↥N) (h : ⁅M, M⁆ = M) :
    ⁅M.map N.subtype, M.map N.subtype⁆ = M.map N.subtype := by
  rw [← Subgroup.map_commutator, h]

theorem s7tg_map_cover {H : Type*} [Group H] (M : Subgroup ↥N) (f : ↥M →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥M) :
    ∃ f' : ↥(M.map N.subtype) →* H, Function.Surjective f' ∧
      f'.ker ≤ Subgroup.center ↥(M.map N.subtype) := by
  let e : ↥M ≃* ↥(M.map N.subtype) := Subgroup.equivMapOfInjective M N.subtype N.subtype_injective
  refine ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective, ?_⟩
  intro x hx
  have hx' : e.symm x ∈ f.ker := hx
  have hc := hker hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hc (e.symm y)

theorem s7tg_map_conj (M : Subgroup ↥N) (t : ↥N) (ht2 : t * t = 1)
    (hM : ∀ g ∈ M, t * g * t⁻¹ ∈ M) :
    conjSub (t : G) (M.map N.subtype) = M.map N.subtype := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  apply le_antisymm
  · rintro x ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨t * m * t⁻¹, hM m hm, ?_⟩
    simp
  · rintro x ⟨m, hm, rfl⟩
    refine ⟨N.subtype (t * m * t⁻¹), ⟨_, hM m hm, rfl⟩, ?_⟩
    have h1 : (t * (t * m * t⁻¹) * t⁻¹ : ↥N) = m := by
      rw [ht]
      calc t * (t * m * t) * t = (t * t) * m * (t * t) := by simp only [mul_assoc]
        _ = m := by rw [ht2]; simp
    simp only [MulAut.conj_apply, MonoidHom.coe_coe, Subgroup.coe_subtype, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have := congrArg (fun x : ↥N => (x : G)) h1
    simpa using this

theorem s7tg_map_comm (M : Subgroup ↥N) (t : ↥N)
    (h : ∀ a ∈ M, ∀ b ∈ M, Commute a (t * b * t⁻¹)) :
    ∀ a ∈ M.map N.subtype, ∀ b ∈ M.map N.subtype,
      Commute a ((t : G) * b * (t : G)⁻¹) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have := h a ha b hb
  have h2 := congrArg (fun x : ↥N => (x : G)) this.eq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  exact h2

theorem s7tg_map_le_centralizer (M S : Subgroup ↥N)
    (h : M ≤ Subgroup.centralizer (S : Set ↥N)) :
    M.map N.subtype ≤ Subgroup.centralizer ((S.map N.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  have := Subgroup.mem_centralizer_iff.1 (h hm) s hs
  have h2 := congrArg (fun x : ↥N => (x : G)) this
  simpa using h2

theorem s7tg_map_mono {M M' : Subgroup ↥N} (h : M ≤ M') :
    M.map N.subtype ≤ M'.map N.subtype :=
  Subgroup.map_mono h

theorem s7tg_conj_mem_map (M : Subgroup ↥N) [M.Normal] {x : G} (hx : x ∈ N) {e : G}
    (he : e ∈ M.map N.subtype) : x * e * x⁻¹ ∈ M.map N.subtype := by
  obtain ⟨m, hm, rfl⟩ := he
  refine ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, Subgroup.Normal.conj_mem inferInstance m hm _, ?_⟩
  simp

end Generic

section GLevel

theorem s7tg_oddCore_bot {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) {t : G}
    (ht : orderOf t = 2) : CFSG.oddCore G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
  · exact h
  · exfalso
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heq : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
      unfold CFSG.oddCore CFSG.pPrimeCore
      congr 1
      ext K
      exact and_congr_right fun _ => Nat.coprime_two_left.symm
    have hodd : Odd (Nat.card (CFSG.oddCore G)) := by
      rw [heq]
      exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hodd
    have hdvd : orderOf t ∣ Nat.card G := orderOf_dvd_natCard t
    rw [ht] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end GLevel

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.s7_cent_F₀_le_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Subgroup.centralizer (a.F₀ : Set G) ≤ a.s7_N₁ := by
  intro x hx
  have hc := Subgroup.mem_centralizer_iff.1 hx
  rw [a.s7_mem_N₁]
  have hcomm : ∀ y ∈ Subgroup.centralizer (a.F₀ : Set G), ∀ f ∈ a.F₀, y * f * y⁻¹ = f := by
    intro y hy f hf
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hy f hf).symm
  refine ⟨fun f => ⟨fun hf => by rw [hcomm x hx f hf]; exact hf, fun hf => ?_⟩, ?_⟩
  · have h2 := hcomm x⁻¹ (inv_mem hx) _ hf
    have h3 : x⁻¹ * (x * f * x⁻¹) * x⁻¹⁻¹ = f := by group
    rw [h3] at h2
    rw [h2]
    exact hf
  · exact (hc _ (a.s7_ub_mem_F₀ hb)).symm

theorem PA5.s7_simple (hb : PAB G L t E W z) : IsSimpleGroup G :=
  hb.setting.1.simple

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
