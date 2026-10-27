module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HNRecog.TwoHSData
open scoped commutatorElement

variable {H H' : Type} [Group H] [Group H']

theorem TwoHSFacts.of_mulEquiv (e : H ≃* H') {a z b z₁ : H} (h : TwoHSFacts H a z b z₁) :
    TwoHSFacts H' (e a) (e z) (e b) (e z₁) := by
  have hmem : ∀ x : H, x ∈ commutator H → e x ∈ commutator H' := by
    intro x hx
    rw [← map_commutator_mulEquiv e]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact
    { center_eq := by
        rw [← Subgroup.map_center_eq e, h.center_eq, MonoidHom.map_zpowers]
        rfl
      orderOf_a := (orderOf_injective e.toMonoidHom e.injective a).trans h.orderOf_a
      orderOf_z := (orderOf_injective e.toMonoidHom e.injective z).trans h.orderOf_z
      orderOf_b := (orderOf_injective e.toMonoidHom e.injective b).trans h.orderOf_b
      orderOf_z₁ := (orderOf_injective e.toMonoidHom e.injective z₁).trans h.orderOf_z₁
      not_isConj := by
        intro i j hij hc
        rw [vec_apply_map e a z b z₁ i, vec_apply_map e a z b z₁ j] at hc
        exact h.not_isConj i j hij (isConj_of_map_mulEquiv e hc)
      involution_cover := by
        intro x' hx'
        have hx : orderOf (e.symm x') = 2 := by rw [orderOf_symm e x']; exact hx'
        obtain ⟨i, hi⟩ := h.involution_cover (e.symm x') hx
        refine ⟨i, ?_⟩
        rw [vec_apply_map e a z b z₁ i]
        simpa using isConj_map_mulEquiv e hi
      cent_z := IsShapeTwoTwoSixS5.of_mulEquiv (centralizerMulEquiv e z) h.cent_z
      cent_az := by
        rw [← map_mul]
        exact IsShapeTwoTwoSixS5.of_mulEquiv (centralizerMulEquiv e (a * z)) h.cent_az
      cent_b := IsShapeTwoTwoTimesA8.of_mulEquiv (centralizerMulEquiv e b) h.cent_b
      cent_z₁ :=
        IsShapeTwoTwoTimesTwoFourA5.of_mulEquiv (centralizerMulEquiv e z₁) h.cent_z₁
      mem_commutator := by
        refine ⟨hmem a h.mem_commutator.1, hmem z h.mem_commutator.2.1, ?_⟩
        rw [← map_mul]
        exact hmem (a * z) h.mem_commutator.2.2
      not_mem_commutator := by
        refine ⟨?_, ?_⟩
        · intro hb
          rw [← map_commutator_mulEquiv e] at hb
          obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hb
          exact h.not_mem_commutator.1 (e.injective hyb ▸ hy)
        · intro hb
          rw [← map_commutator_mulEquiv e] at hb
          obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hb
          exact h.not_mem_commutator.2 (e.injective hyb ▸ hy)
      K_shape := by
        rw [← map_K_eq e z]
        exact IsShapeK.of_mulEquiv
          (mapSubgroupMulEquiv e (commutator H ⊓ centralizer ({z} : Set H))) h.K_shape
      center_K := center_K_of_mulEquiv e a z h.center_K
      exists_sq_eq := by
        obtain ⟨g, hg⟩ := h.exists_sq_eq
        exact ⟨e g, by rw [← map_pow, hg]⟩
      isConj_of_sq_eq := by
        intro g' g'' hg' hg''
        have hg : (e.symm g') ^ 2 = a := by
          apply e.injective
          rw [map_pow, e.apply_symm_apply, hg']
        have hgg : (e.symm g'') ^ 2 = a := by
          apply e.injective
          rw [map_pow, e.apply_symm_apply, hg'']
        simpa using isConj_map_mulEquiv e
          (h.isConj_of_sq_eq (e.symm g') (e.symm g'') hg hgg)
      not_isSectionOf_A8 := by
        intro g' hg' hsec
        have hg : (e.symm g') ^ 2 = a := by
          apply e.injective
          rw [map_pow, e.apply_symm_apply, hg']
        exact h.not_isSectionOf_A8 (e.symm g') hg
          (isSectionOf_of_mulEquiv (centralizerMulEquiv' e g').symm hsec)
      card_eq := by rw [← Nat.card_congr e.toEquiv, h.card_eq]
      table_three := by
        intro x' hx'
        have hx : orderOf (e.symm x') = 3 := by rw [orderOf_symm e x']; exact hx'
        exact IsShapeCentralizerThree.of_mulEquiv (centralizerMulEquiv' e x')
          (h.table_three (e.symm x') hx)
      table_five := by
        intro x' hx'
        have hx : orderOf (e.symm x') = 5 := by rw [orderOf_symm e x']; exact hx'
        rcases h.table_five (e.symm x') hx with hA | hB | hC
        · exact Or.inl (IsShapeCentralizerFiveA.of_mulEquiv (centralizerMulEquiv' e x') hA)
        · exact Or.inr
            (Or.inl (IsShapeCentralizerFiveB.of_mulEquiv (centralizerMulEquiv' e x') hB))
        · exact Or.inr
            (Or.inr (IsShapeCentralizerFiveC.of_mulEquiv (centralizerMulEquiv' e x') hC))
      table_seven := by
        intro x' hx'
        have hx : orderOf (e.symm x') = 7 := by rw [orderOf_symm e x']; exact hx'
        exact IsShapeCentralizerSeven.of_mulEquiv (centralizerMulEquiv' e x')
          (h.table_seven (e.symm x') hx)
      table_eleven := by
        intro x' hx'
        have hx : orderOf (e.symm x') = 11 := by rw [orderOf_symm e x']; exact hx'
        exact IsShapeCentralizerEleven.of_mulEquiv (centralizerMulEquiv' e x')
          (h.table_eleven (e.symm x') hx)
      sl25_le_centralizer := by
        intro ρ' hρ' hC'
        have hρ : orderOf (e.symm ρ') = 5 := by rw [orderOf_symm e ρ']; exact hρ'
        have hC : IsShapeCentralizerFiveC ↥(centralizer ({e.symm ρ'} : Set H)) :=
          IsShapeCentralizerFiveC.of_mulEquiv (centralizerMulEquiv' e ρ').symm hC'
        obtain ⟨S, hS⟩ := h.sl25_le_centralizer (e.symm ρ') hρ hC
        refine ⟨S.map (centralizerMulEquiv' e ρ').toMonoidHom, ?_⟩
        obtain ⟨iso⟩ := hS
        exact ⟨(mapSubgroupMulEquiv (centralizerMulEquiv' e ρ') S).symm.trans iso⟩
      sylow_two_five := by
        intro ρ' hρ' hB' T'
        let C : Subgroup H := centralizer ({e.symm ρ'} : Set H)
        let C' : Subgroup H' := centralizer ({ρ'} : Set H')
        let φ : ↥C ≃* ↥C' := centralizerMulEquiv' e ρ'
        have hρ : orderOf (e.symm ρ') = 5 := by rw [orderOf_symm e ρ']; exact hρ'
        have hB : IsShapeCentralizerFiveB ↥C :=
          IsShapeCentralizerFiveB.of_mulEquiv φ.symm hB'
        let T : Sylow 2 ↥C := T'.comapOfInjective φ.toMonoidHom φ.injective (by simp)
        have hT : (T : Subgroup ↥C) = (T' : Subgroup ↥C').comap φ.toMonoidHom := rfl
        obtain ⟨u, hu, hTU⟩ := h.sylow_two_five (e.symm ρ') hρ hB T
        refine ⟨e u, isConj_map_mulEquiv e hu, ?_⟩
        have hsub : ∀ x : ↥C, e (C.subtype x) = C'.subtype (φ x) :=
          fun x => (centralizerMulEquiv'_coe e ρ' x).symm
        have hTmap : (T : Subgroup ↥C).map φ.toMonoidHom = (T' : Subgroup ↥C') := by
          rw [hT]
          exact Subgroup.map_comap_eq_self_of_surjective φ.surjective _
        have hmm := map_map_subtype_mulEquiv e φ C.subtype C'.subtype hsub (T : Subgroup ↥C)
        rw [← hTmap, ← hmm, hTU, MonoidHom.map_closure, Set.image_pair]
        rfl
      m11_unique_class := by
        constructor
        · obtain ⟨M, hM⟩ := h.m11_unique_class.1
          refine ⟨M.map e.toMonoidHom, ?_⟩
          obtain ⟨iso⟩ := hM
          exact ⟨(mapSubgroupMulEquiv e M).symm.trans iso⟩
        · intro M' N' hM' hN'
          let M : Subgroup H := M'.comap e.toMonoidHom
          let N : Subgroup H := N'.comap e.toMonoidHom
          have hMeq : M.map e.toMonoidHom = M' := by
            change (M'.comap e.toMonoidHom).map e.toMonoidHom = M'
            exact Subgroup.map_comap_eq_self_of_surjective e.surjective M'
          have hNeq : N.map e.toMonoidHom = N' := by
            change (N'.comap e.toMonoidHom).map e.toMonoidHom = N'
            exact Subgroup.map_comap_eq_self_of_surjective e.surjective N'
          have hM : IsSporadic ↥M .M11 := by
            obtain ⟨iso⟩ := hM'
            exact ⟨((mapSubgroupMulEquiv e M).trans (MulEquiv.subgroupCongr hMeq)).trans iso⟩
          have hN : IsSporadic ↥N .M11 := by
            obtain ⟨iso⟩ := hN'
            exact ⟨((mapSubgroupMulEquiv e N).trans (MulEquiv.subgroupCongr hNeq)).trans iso⟩
          obtain ⟨g, hg⟩ := h.m11_unique_class.2 M N hM hN
          refine ⟨e g, ?_⟩
          rw [hNeq.symm, hg, ← hMeq, Subgroup.map_map, Subgroup.map_map, conj_comp_mulEquiv e g]
      m11_centralizer_five := by
        intro M' hM' ρ' hρ'M' hρ'
        let M : Subgroup H := M'.comap e.toMonoidHom
        have hMeq : M.map e.toMonoidHom = M' := by
          change (M'.comap e.toMonoidHom).map e.toMonoidHom = M'
          exact Subgroup.map_comap_eq_self_of_surjective e.surjective M'
        have hM : IsSporadic ↥M .M11 := by
          obtain ⟨iso⟩ := hM'
          exact ⟨((mapSubgroupMulEquiv e M).trans (MulEquiv.subgroupCongr hMeq)).trans iso⟩
        have hρM : e.symm ρ' ∈ M := by
          change e.symm ρ' ∈ M'.comap e.toMonoidHom
          rw [Subgroup.mem_comap]
          simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hρ'M'
        have hρ : orderOf (e.symm ρ') = 5 := by rw [orderOf_symm e ρ']; exact hρ'
        exact IsShapeCentralizerFiveB.of_mulEquiv (centralizerMulEquiv' e ρ')
          (h.m11_centralizer_five M hM (e.symm ρ') hρM hρ)
      centralizer_five_of_A8 := by
        intro c' hc' hA8' ρ' hρ' hcomm'
        have hc : orderOf (e.symm c') = 2 := by rw [orderOf_symm e c']; exact hc'
        have hA8 : IsShapeTwoTwoTimesA8 ↥(centralizer ({e.symm c'} : Set H)) :=
          IsShapeTwoTwoTimesA8.of_mulEquiv (centralizerMulEquiv' e c').symm hA8'
        have hρ : orderOf (e.symm ρ') = 5 := by rw [orderOf_symm e ρ']; exact hρ'
        have hcomm : e.symm ρ' * e.symm c' = e.symm c' * e.symm ρ' :=
          e.injective (by simpa only [map_mul, e.apply_symm_apply] using hcomm')
        exact IsShapeCentralizerFiveC.of_mulEquiv (centralizerMulEquiv' e ρ')
          (h.centralizer_five_of_A8 (e.symm c') hc hA8 (e.symm ρ') hρ hcomm) }

theorem exists_twoHSFacts_of_mulEquiv {P : Type} [Group P]
    (hP : ∃ a z b z₁ : P, TwoHSFacts P a z b z₁) {H : Type} [Group H] (e : H ≃* P) :
    ∃ a z b z₁ : H, TwoHSFacts H a z b z₁ := by
  obtain ⟨a, z, b, z₁, h⟩ := hP
  exact ⟨e.symm a, e.symm z, e.symm b, e.symm z₁, TwoHSFacts.of_mulEquiv e.symm h⟩

end CFSG.EvenSporadicStandard.HNRecog
