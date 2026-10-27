module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Data
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.E6 (chain13 chain56 e6Index chainRoot e6RootVec isRoot_iff_exists_e6RootVec
  a2Equiv₁ a2Equiv₂ coe_a2Rep₁ coe_a2Rep₂ a2Equiv₁_apply a2Equiv₂_apply)

open CFSG.RankThree.PartOne.TCX.E
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Main

variable {K : Type} [Field K]

@[expose] def e6A2Rho (K : Type) [Field K] : (i : Fin 3) → SL(3, K) →* ModGL Tag.E6 K
  | 0 => e6rhoA2₁ K
  | 1 => e6rhoA2₂ K
  | 2 => a2Std₁.rhoV K ((coxeterSystem Tag.E6).wordProd e6A2Word)

theorem e6A2Rho_injective (i : Fin 3) : Function.Injective (e6A2Rho K i) := by
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · exact e6rhoA2₁_injective
  · exact e6rhoA2₂_injective
  · exact (MulAut.conj _).injective.comp (a2Std₁.inj K)

theorem e6A2Rho_transvection (i : Fin 3) {a b : Fin 3} (hab : a ≠ b) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
      e6A2Rho K i (Matrix.SpecialLinearGroup.transvection hab t) =
        pinnedX Tag.E6 K (e6A2Root i a b) (ε * t) := by
  have h0 : ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
      e6rhoA2₁ K (Matrix.SpecialLinearGroup.transvection hab t) =
        pinnedX Tag.E6 K (chainRoot chain13 a b) (ε * t) := by
    obtain ⟨s, hs, hρ⟩ := CFSG.RankThree.Classical2.a2Mat₁_pinnedX_chainRoot13 (Ω := K) hab
    have hss : (s : K) * s = 1 := CFSG.RankThree.Classical2.sign_mul_self hs
    refine ⟨s, by rcases hs with rfl | rfl <;> simp, fun t => ?_⟩
    have h : (a2Equiv₁ K).symm (Matrix.SpecialLinearGroup.transvection hab t) =
        ⟨pinnedX Tag.E6 K (chainRoot chain13 a b) ((s : K) * t),
          CFSG.RankThree.Classical2.pinnedX_chainRoot13_mem hab _⟩ := by
      rw [MulEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, ← mul_assoc, hss, one_mul]
      rfl
    simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [h]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · obtain ⟨ε, hε, h⟩ := h0
    exact ⟨ε, hε, fun t => by rw [← chainRoot13_eq]; exact h t⟩
  · obtain ⟨s, hss, hρ⟩ := CFSG.RankThree.Classical2.a2Mat₂_pinnedX_chainRoot56 (Ω := K) hab
    refine ⟨s, mul_self_eq_one_iff.1 hss, fun t => ?_⟩
    have h : (a2Equiv₂ K).symm (Matrix.SpecialLinearGroup.transvection hab t) =
        ⟨pinnedX Tag.E6 K (chainRoot chain56 a b) (s * t),
          CFSG.RankThree.Classical2.pinnedX_chainRoot56_mem hab _⟩ := by
      rw [MulEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [a2Equiv₂_apply, coe_a2Rep₂, hρ, ← mul_assoc, hss, one_mul]
      rfl
    rw [← chainRoot56_eq]
    simp only [e6A2Rho, e6rhoA2₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    rw [h]
  · obtain ⟨ε₀, h₀, hρ₀⟩ := h0
    have hα : IsRoot Tag.E6 (chainRoot chain13 a b) := ((a2Std₁.roots _).2 ⟨a, b, hab, rfl⟩).1
    obtain ⟨ε, hεε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K
      ((coxeterSystem Tag.E6).wordProd e6A2Word) hα
    refine ⟨ε * ε₀, ?_, fun t => ?_⟩
    · rcases mul_self_eq_one_iff.1 hεε with h | h <;> rcases h₀ with h' | h' <;>
        simp [h, h']
    · rw [← wordProd_chainRoot13_eq]
      have : e6A2Rho K 2 (Matrix.SpecialLinearGroup.transvection hab t) =
          canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd e6A2Word) *
            e6rhoA2₁ K (Matrix.SpecialLinearGroup.transvection hab t) *
            (canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd e6A2Word))⁻¹ :=
        rfl
      rw [this, hρ₀, hX, mul_assoc]

theorem isRoot_e6A2Root (i : Fin 3) {a b : Fin 3} (hab : a ≠ b) : IsRoot Tag.E6 (e6A2Root i a b) :=
  isRoot_iff_exists_e6RootVec.2 (e6A2_root_check.1 i a b hab)

theorem e6A2Rho_mem (i : Fin 3) (A : SL(3, K)) : e6A2Rho K i A ∈ adjointGroup Tag.E6 K := by
  have h : ∀ A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K),
      e6A2Rho K i A ∈ adjointGroup Tag.E6 K := by
    intro A hA
    induction hA using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, t, rfl⟩ := hx
      obtain ⟨ε, -, h⟩ := e6A2Rho_transvection (K := K) i hab
      rw [h]
      exact pinnedX_mem_adjointGroup _ _
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  exact h A (by rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial)

theorem commute_pinnedX_E6 {r s : Fin Tag.E6.rank → ℤ} (hr : IsRoot Tag.E6 r) (hs : IsRoot Tag.E6 s)
    (hne : r ≠ s) (hne' : r + s ≠ 0) (hnr : ¬ IsRoot Tag.E6 (r + s)) (c d : K) :
    Commute (pinnedX Tag.E6 K r c) (pinnedX Tag.E6 K s d) := by
  obtain ⟨-, h2⟩ := simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hr hs hne
    (fun h => hne' (by rw [h]; abel))
  exact h2 hnr K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem e6A2Rho_commute {i j : Fin 3} (hij : i ≠ j) (A B : SL(3, K)) :
    Commute (e6A2Rho K i A) (e6A2Rho K j B) := by
  have hgen : ∀ x ∈ CFSG.LinearGroups.elementarySet 3 K, ∀ y ∈ CFSG.LinearGroups.elementarySet 3 K,
      Commute (e6A2Rho K i x) (e6A2Rho K j y) := by
    rintro _ ⟨a, b, hab, t, rfl⟩ _ ⟨a', b', hab', t', rfl⟩
    obtain ⟨ε, -, h⟩ := e6A2Rho_transvection (K := K) i hab
    obtain ⟨ε', -, h'⟩ := e6A2Rho_transvection (K := K) j hab'
    rw [h, h']
    obtain ⟨hne, hne', hnr⟩ := e6A2_root_check.2 i j hij a b a' b' hab hab'
    exact commute_pinnedX_E6 (isRoot_e6A2Root i hab) (isRoot_e6A2Root j hab') hne hne'
      (fun hr => hnr (isRoot_iff_exists_e6RootVec.1 hr)) _ _
  have hA : ∀ A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K),
      ∀ y ∈ CFSG.LinearGroups.elementarySet 3 K, Commute (e6A2Rho K i A) (e6A2Rho K j y) := by
    intro A hA y hy
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx y hy
    | one => rw [map_one]; exact Commute.one_left _
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul_left hz
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  have hB : ∀ B ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K),
      ∀ A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K),
      Commute (e6A2Rho K i A) (e6A2Rho K j B) := by
    intro B hBc A hAc
    induction hBc using Subgroup.closure_induction with
    | mem y hy => exact hA A hAc y hy
    | one => rw [map_one]; exact Commute.one_right _
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul_right hz
    | inv x _ hx => rw [map_inv]; exact hx.inv_right
  have htop : ∀ X : SL(3, K), X ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) := fun X => by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial
  exact hB B (htop B) A (htop A)

theorem mem_rootsA2_E6 {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![-1, 0] ∨ γ = ![0, -1] ∨ γ = ![-1, -1] := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq] at hγ
  have inj := CFSG.LieType.Universal.SpecialLinear.toStd_injective 2
  obtain ⟨i, j, hij, h⟩ := hγ
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Or.inl (inj (h.trans (by decide)))
  · exact Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide))))))
  · exact absurd rfl hij
  · exact Or.inr (Or.inl (inj (h.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inj (h.trans (by decide)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))))
  · exact absurd rfl hij

theorem sl_x_frame (K : Type) [Field K] (i : Fin 3) {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    ∃ (a b : Fin 3) (hab : a ≠ b),
      (∀ c : K, CFSG.LieType.Steinberg.SL.x 2 K γ c =
        Matrix.SpecialLinearGroup.transvection hab c) ∧ e6A2Frame i γ = e6A2Root i a b := by
  rcases mem_rootsA2_E6 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨1, 2, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨0, 2, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
  · exact ⟨1, 0, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨2, 1, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
  · exact ⟨2, 0, by decide, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
