module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.CocodeFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.OrderM24

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  Certificates.RouteP.M24Defect
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

noncomputable abbrev E0q : Subgroup ↥Zq := E0.subgroupOf Zq

section Normal


theorem conj_mem_E0_of_gen {g : Q3} (hg : g = aElt ∨ g = bElt ∨ ∃ j, g = epsElt j) {x : Q3}
    (hx : x ∈ E0) : g * x * g⁻¹ ∈ E0 := by
  obtain ⟨m, -, rfl⟩ := exists_epsMask_of_mem_E0 hx
  rcases hg with rfl | rfl | ⟨j, rfl⟩
  · rw [aElt_mul_epsMask_mul_inv]
    exact epsMask_mem_E0 _
  · rw [bElt_mul_epsMask_mul_inv]
    exact epsMask_mem_E0 _
  · rw [E0_comm (epsElt_mem_E0 j) (epsMask_mem_E0 m), mul_assoc, mul_inv_cancel, mul_one]
    exact epsMask_mem_E0 m

theorem inv_conj_mem_E0 {g : Q3} (hg : ∀ x ∈ E0, g * x * g⁻¹ ∈ E0) {x : Q3} (hx : x ∈ E0) :
    g⁻¹ * x * g⁻¹⁻¹ ∈ E0 := by
  haveI : Finite E0 := finite_and_card_E0_le.1
  let f : E0 → E0 := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
  have hinj : Function.Injective f := by
    intro y z h
    have h' : g * (y : Q3) * g⁻¹ = g * z * g⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj ⟨x, hx⟩
  have hy' : g * (y : Q3) * g⁻¹ = x := congrArg Subtype.val hy
  have h2 : g⁻¹ * x * g⁻¹⁻¹ = y := by
    rw [← hy']
    group
  rw [h2]
  exact y.2

theorem conj_mem_E0 {g : Q3} (hg : g ∈ Zq) : ∀ x ∈ E0, g * x * g⁻¹ ∈ E0 := by
  refine Subgroup.closure_induction (p := fun g _ => ∀ x ∈ E0, g * x * g⁻¹ ∈ E0) ?_ ?_ ?_ ?_ hg
  · rintro g ((rfl | rfl) | ⟨j, rfl⟩) x hx
    · exact conj_mem_E0_of_gen (Or.inl rfl) hx
    · exact conj_mem_E0_of_gen (Or.inr (Or.inl rfl)) hx
    · exact conj_mem_E0_of_gen (Or.inr (Or.inr ⟨j, rfl⟩)) hx
  · intro x hx
    simpa using hx
  · intro g h _ _ hg hh x hx
    have := hg _ (hh x hx)
    simpa [mul_assoc] using this
  · intro g _ hg x hx
    exact inv_conj_mem_E0 hg hx

theorem E0q_normal : E0q.Normal where
  conj_mem x hx g := conj_mem_E0 g.2 x hx

theorem card_E0q : Nat.card E0q = 2 ^ 11 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe E0_le_Zq).toEquiv).trans card_E0

end Normal

section Order


theorem card_Zq_le : Nat.card Zq ≤ 2 ^ 11 * Nat.card (NativeSporadic.Carrier .M24) := by
  haveI : E0q.Normal := E0q_normal
  let a' : Zq := ⟨aElt, aElt_mem_Zq⟩
  let b' : Zq := ⟨bElt, bElt_mem_Zq⟩
  have hrel : ∀ r ∈ relWords, wordProd (img2 (QuotientGroup.mk a' : Zq ⧸ E0q)
      (QuotientGroup.mk b')) r = 1 := by
    intro r hr
    have h1 : wordProd (img2 (QuotientGroup.mk a' : Zq ⧸ E0q) (QuotientGroup.mk b')) r =
        QuotientGroup.mk' E0q (wordProd (img2 a' b') r) := by
      rw [map_wordProd]
      congr 1
      funext i
      unfold img2
      split_ifs <;> rfl
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have himg : (fun i => ((img2 a' b' i : Zq) : Q3)) = img2 aElt bElt := by
      funext i
      unfold img2
      split_ifs <;> rfl
    show ((wordProd (img2 a' b') r : Zq) : Q3) ∈ E0
    rw [coe_wordProd, himg]
    exact wordProd_relWords_mem_E0 hr
  obtain ⟨H, haH, hbH, -, hcard⟩ := exists_subgroup_card_le _ _ hrel
  have key : ∀ g (hg : g ∈ Zq), (QuotientGroup.mk (⟨g, hg⟩ : Zq) : Zq ⧸ E0q) ∈ H := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g hg => (QuotientGroup.mk (⟨g, hg⟩ : Zq) : Zq ⧸ E0q) ∈ H) ?_ ?_ ?_ ?_ hg
    · rintro x ((rfl | rfl) | ⟨j, rfl⟩)
      · exact haH
      · exact hbH
      · have h1 : (QuotientGroup.mk (⟨epsElt j, epsElt_mem_Zq j⟩ : Zq) : Zq ⧸ E0q) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (epsElt_mem_E0 j)
        show (QuotientGroup.mk (⟨epsElt j, epsElt_mem_Zq j⟩ : Zq) : Zq ⧸ E0q) ∈ H
        rw [h1]
        exact H.one_mem
    · exact (QuotientGroup.mk_one (N := E0q)).symm ▸ H.one_mem
    · intro x y _ _ hxH hyH
      exact H.mul_mem hxH hyH
    · intro x _ hxH
      exact H.inv_mem hxH
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact key g.1 g.2
  rw [htop, Subgroup.card_top] at hcard
  have h24 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := card_M24
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup E0q, card_E0q, h24]
  calc Nat.card (Zq ⧸ E0q) * 2 ^ 11 ≤ 244823040 * 2 ^ 11 := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ 11 * 244823040 := mul_comm _ _

theorem card_Zq : Nat.card Zq = 2 ^ 11 * Nat.card (NativeSporadic.Carrier .M24) :=
  le_antisymm card_Zq_le card_Zq_ge

theorem planeHom_ker_eq : planeHom.ker = E0q := by
  haveI : Finite Q3 := Finite.of_injective rho rho_injective
  have hle : E0q ≤ planeHom.ker := fun g hg => planeHom_eq_one_of_mem_E0 hg
  have h24 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := card_M24
  have hrange : Nat.card (NativeSporadic.Carrier .M24) ≤ Nat.card planeHom.range := by
    refine card_M24_le_card_closure_PA_PB.trans (Subgroup.card_le_of_le ?_)
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, planeHom_aElt⟩
    · exact ⟨_, planeHom_bElt⟩
  have hmul := Subgroup.card_ker_mul_card_range planeHom
  have h1 : Nat.card planeHom.ker * Nat.card planeHom.range ≤
      2 ^ 11 * Nat.card planeHom.range := by
    rw [hmul, card_Zq]
    exact Nat.mul_le_mul_left _ hrange
  have hker : Nat.card planeHom.ker ≤ Nat.card E0q := by
    rw [card_E0q]
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  exact (Subgroup.eq_of_le_of_card_ge hle hker).symm

end Order

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
