module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Rank
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEnd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Gen

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEnd.Endgame

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAb_cent_of_cover {X : Subgroup G}
    (hZ : Odd (Nat.card (center X))) (e : X ⧸ center X ≃* SU52) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    ∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ (∀ y ∈ E, y * y = 1) ∧
      8 ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) with hα
  have hα2 : α * α = 1 := quotientCenterConj_mul_self hxX hx2
  set θ : MulAut SU52 := (MulAut.congr e) α with hθ
  have hθ2 : θ * θ = 1 := by
    rw [hθ, ← map_mul, hα2, map_one]
  obtain ⟨E, hEsq, hEcomm, hE8, hEfix⟩ := exists_elemAb_fixed θ hθ2
  have hEp : IsPGroup 2 E := fun y => ⟨1, by
    have := hEsq y y.2
    rw [pow_one, sq]
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hEp
  set E₀ : Subgroup (X ⧸ center X) := E.map e.symm.toMonoidHom with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ m := by
    rw [← hm]
    exact Subgroup.card_map_of_injective e.symm.injective
  have hfix : ∀ b ∈ E₀, α b = b := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : e (α (e.symm y)) = y := hEfix y hy
    simp only [MulEquiv.coe_toMonoidHom]
    have h2 : e (α (e.symm y)) = e (e.symm y) := by rw [h1, e.apply_symm_apply]
    exact e.injective h2
  have hsq : ∀ b ∈ E₀, b * b = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hEsq y hy, map_one]
  have hm3 : 3 ≤ m := by
    have h8 : 2 ^ 3 ≤ 2 ^ m := by rw [← hm]; exact hE8
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h8
  obtain ⟨E', hE'X, hE'c, hE'sq, hE'card⟩ :=
    exists_exp_two_le_centralizer_of_fixed hZ hxX hx2 E₀ hfix hsq hE₀card
  refine ⟨E', hE'X, hE'c, hE'sq, ?_⟩
  rw [hE'card]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm3
  simpa using this


theorem map_equiv_quotient_equiv {X : Subgroup G} (φ : G ≃* G) (e : X ⧸ center X ≃* SU52) :
    Nonempty ((X.map φ.toMonoidHom) ⧸ center (X.map φ.toMonoidHom) ≃* SU52) := by
  set e1 : X ≃* X.map φ.toMonoidHom := X.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc : (center X).map (e1 : X →* X.map φ.toMonoidHom) =
      center (X.map φ.toMonoidHom) := Subgroup.map_center_eq e1
  exact ⟨(QuotientGroup.congr _ _ e1 hc).symm.trans e⟩

theorem odd_center_map_equiv {X : Subgroup G} (φ : G ≃* G) (hZ : Odd (Nat.card (center X))) :
    Odd (Nat.card (center (X.map φ.toMonoidHom))) := by
  set e1 : X ≃* X.map φ.toMonoidHom := X.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc : (center X).map (e1 : X →* X.map φ.toMonoidHom) =
      center (X.map φ.toMonoidHom) := Subgroup.map_center_eq e1
  rw [← hc, Subgroup.card_map_of_injective e1.injective]
  exact hZ

theorem eq_one_of_central_of_sq {X : Subgroup G} (hZ : Odd (Nat.card (center X))) {y : G}
    (hy : y ∈ X) (hyc : ∀ a ∈ X, a * y = y * a) (hsq : y * y = 1) : y = 1 := by
  have hmem : (⟨y, hy⟩ : X) ∈ center X :=
    Subgroup.mem_center_iff.2 fun a => Subtype.ext (hyc a a.2)
  set z : center X := ⟨⟨y, hy⟩, hmem⟩ with hz
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [sq]; exact Subtype.ext (Subtype.ext hsq))
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat hZ (orderOf_dvd_natCard z)
  have h1 : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hz1 : z = 1 := orderOf_eq_one_iff.1 h1
  have h4 : (z : X) = 1 := by rw [hz1]; rfl
  exact congrArg Subtype.val h4

theorem comm_of_sq_eq_one {E : Subgroup G} (hsq : ∀ y ∈ E, y * y = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have h1 := hsq (x * y) (E.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hx', hy'] at hxy
  exact hxy.symm

variable {d : Data G} {A : Subgroup G}

theorem Data.Hyp.false_of_normalizes_both (h : d.Hyp) (hU : d.UnitaryProductData A) (g : G)
    (htA : d.t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (htB : d.t ∈ normalizer (((A.map (MulAut.conj d.t).toMonoidHom).map
      (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) : False := by
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'
  set B : Subgroup G := A.map (MulAut.conj d.t).toMonoidHom with hB
  set B' : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hB'
  obtain ⟨e⟩ := h.quotient_equiv hU
  have eA : ↥A ⧸ center ↥A ≃* SU52 := e.trans d.η
  obtain ⟨eA'⟩ := map_equiv_quotient_equiv (MulAut.conj g) eA
  obtain ⟨eB⟩ := map_equiv_quotient_equiv (MulAut.conj d.t) eA
  obtain ⟨eB'⟩ := map_equiv_quotient_equiv (MulAut.conj g) eB
  have hZA := h.odd_center hU
  have hZA' := odd_center_map_equiv (MulAut.conj g) hZA
  have hZB := odd_center_map_equiv (MulAut.conj d.t) hZA
  have hZB' := odd_center_map_equiv (MulAut.conj g) hZB
  obtain ⟨E₁, hE₁A, hE₁t, hE₁sq, hE₁8⟩ := exists_elemAb_cent_of_cover hZA' eA' htA h.t_mul_t
  obtain ⟨E₂, hE₂B, hE₂t, hE₂sq, hE₂8⟩ := exists_elemAb_cent_of_cover hZB' eB' htB h.t_mul_t
  have hAB : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    have hcomm : ⁅A', B'⁆ = ⊥ := by
      rw [hA', hB', ← Subgroup.map_commutator, hU.comm, Subgroup.map_bot]
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hE₁₂ : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb => hAB a (hE₁A ha) b (hE₂B hb)
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_central_of_sq hZA' (hE₁A hy1) (fun a ha => hAB a ha y (hE₂B hy2))
      (hE₁sq y hy1)
  have hEsq : ∀ y ∈ E₁ ⊔ E₂, y * y = 1 := fun y hy =>
    sq_eq_one_of_mem_sup hE₁₂ hE₁sq hE₂sq hy
  have hcard := card_sup_of_commute_of_inf_eq_bot hE₁₂ hinf
  have hEH : E₁ ⊔ E₂ ≤ d.H := sup_le hE₁t hE₂t
  have hbound := h.card_le_of_elemAb hEH
    (fun x hx y hy => comm_of_sq_eq_one hEsq hx hy) hEsq
  have h64 : 8 * 8 ≤ Nat.card ↥E₁ * Nat.card ↥E₂ := Nat.mul_le_mul hE₁8 hE₂8
  rw [hcard] at hbound
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
