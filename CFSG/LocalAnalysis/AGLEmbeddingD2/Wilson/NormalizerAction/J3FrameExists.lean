module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3ClassFrame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.ALeAux

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
  CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.RankThree.Asc83Table

section Main


set_option linter.unusedSectionVars false

theorem exists_frame_cover {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3) :
    ∃ F : Subgroup X, center X ≤ F ∧ Nat.card F = 81 ∧ CFSG.IsElementaryAbelian 3 F ∧
      CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))) := by
  obtain ⟨B₀, -, hB₀j, hB₀e, hB₀c, -⟩ := j3P_e27_split
  obtain ⟨Bq, hBq, hBq27⟩ : ∃ Bq : Subgroup (X ⧸ center X), CFSG.IsElementaryAbelian 3 Bq ∧
      Nat.card Bq = 27 := by
    set ψ : (X ⧸ center X) ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
    set A' : Subgroup ↥j3P := B₀.subgroupOf j3P with hA'
    have hA'e : IsElementaryAbelian 3 A' := by
      have hB₀' := isElementaryAbelian_iff.1 hB₀e
      rw [isElementaryAbelian_iff]
      refine ⟨fun a ha b hb => Subtype.ext (hB₀'.1 a.1 ha b.1 hb), fun a ha => ?_⟩
      exact Subtype.ext (hB₀'.2 a.1 ha)
    have hA'27 : Nat.card A' = 27 := by
      rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀j).toEquiv, hB₀c]
    refine ⟨A'.map ψ.symm.toMonoidHom, IsElementaryAbelian.map_hom ψ.symm.toMonoidHom hA'e, ?_⟩
    rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective, hA'27]
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set F : Subgroup X := Bq.comap π with hF
  have hZF : center X ≤ F := fun z hz => by
    show π z ∈ Bq
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [h1]; exact Subgroup.one_mem _
  have hFmap : F.map π = Bq := Subgroup.map_comap_eq_self_of_surjective hsurj Bq
  have hF81 : Nat.card F = 3 ^ 4 := by
    have := card_map_mul_ker π F (hker.le.trans hZF)
    rw [hFmap, hker, hZ3, hBq27] at this
    omega
  have hBq' := isElementaryAbelian_iff.1 hBq
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ * y⁻¹ ∈ center X := by
    intro x hx y hy
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := hBq'.1 (π x) hx (π y) hy
    rw [h1]; group
  have hcube : ∀ x ∈ F, x ^ 3 ∈ center X := by
    intro x hx
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hBq'.2 (π x) hx
  have hTri : Sec4.IsTripleCover X NativeSporadic.J3 := ⟨hZ3, ⟨e⟩⟩
  have hFea := ks217J3CoverPreimage_holds X hX hTri F hZF hF81 hcomm hcube
  refine ⟨F, hZF, by rw [hF81]; norm_num, isElemAbelian_iff_isElementaryAbelian.1 hFea, ?_⟩
  rw [hFmap]; exact hBq


set_option maxRecDepth 20000 in
theorem exists_local_frame_cover {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3) :
    ∃ (a y : X) (W : Subgroup X), a ∉ center X ∧ a ^ 3 = 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧
      a * y = y * a ∧ y ∉ zpowers a ⊔ center X ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧
      (∀ w ∈ W, a * w = w * a) ∧ y ∈ normalizer (W : Set X) := by
  obtain ⟨F, hZF, hF81, hFea, hFbar⟩ := exists_frame_cover hX hZ3 e
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, -, -, h3A, -⟩ := exists_F1_of_class hZ3 e hFbar hZF hF81
  have hex : ∃ a ∈ F, a ∉ F₁ := by
    by_contra hno
    push Not at hno
    have : Nat.card F ≤ Nat.card F₁ := by
      have hle : F ≤ F₁ := hno
      exact Subgroup.card_le_of_le hle
    omega
  obtain ⟨a, haF, haF₁⟩ := hex
  have ha : a ∉ center X := fun h => haF₁ (hZF₁ h)
  have h5 := h3A a haF haF₁
  have ha3' : a ^ 3 = 1 := (isElementaryAbelian_iff.1 hFea).2 a haF
  have ha3 : a ^ 3 ∈ center X := by rw [ha3']; exact one_mem _
  obtain ⟨I, hIC, hIperf, ⟨φ⟩, -, -, -, hDI, -, -⟩ :=
    centralizer_structure_J3Cover hX hZ3 e ha ha3 h5
  obtain ⟨y, hyI, hy3, hy1, W, hWI, hW0, hW2, hyN⟩ := exists_three_normalizing_two_subgroup I φ
  refine ⟨a, y, W, ha, ha3', hy3, hy1, ?_, ?_, hW0, hW2, ?_, hyN⟩
  · have := mem_centralizer_singleton_iff.1 (hIC hyI)
    exact this.symm
  · intro hyD
    have : y ∈ (zpowers a ⊔ center X) ⊓ I := ⟨hyD, hyI⟩
    rw [hDI.eq_bot] at this
    exact hy1 (Subgroup.mem_bot.1 this)
  · intro w hw
    have := mem_centralizer_singleton_iff.1 (hIC (hWI hw))
    exact this.symm

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
