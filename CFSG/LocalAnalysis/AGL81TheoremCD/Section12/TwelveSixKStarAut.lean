module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

private theorem commutator_eq_top_of_isExtNotation_altSix {X : Type} [Group X] [Finite X]
    (h : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 3) X) :
    _root_.commutator X = ⊤ := by
  obtain ⟨N, hNnormal, hN3, hAN, hno⟩ := h
  haveI : N.Normal := hNnormal
  obtain ⟨e⟩ := hAN
  have hA6 : _root_.commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hquot : _root_.commutator (X ⧸ N) = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
      ← _root_.commutator_def, hA6]
  have hsup : _root_.commutator X ⊔ N = ⊤ := by
    have hmap : (_root_.commutator X).map (QuotientGroup.mk' N) = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N), ← _root_.commutator_def, hquot]
    have hc := Subgroup.comap_map_eq (f := QuotientGroup.mk' N) (H := _root_.commutator X)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hc
    exact hc.symm
  by_contra hne
  have hnot : ¬ N ≤ _root_.commutator X := by
    intro hle
    exact hne ((sup_eq_left.mpr hle).symm.trans hsup)
  have hNprime : (Nat.card N).Prime := by rw [hN3]; norm_num
  have hinf : _root_.commutator X ⊓ N = ⊥ :=
    CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card
      (_root_.commutator X) N hNprime hnot
  exact hno ⟨_root_.commutator X, inferInstance, by rw [inf_comm]; exact hinf,
    by rw [sup_comm]; exact hsup⟩

private theorem center_eq_of_perfect_of_normal_card_three {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN3 : Nat.card N = 3)
    (e : (X ⧸ N) ≃* alternatingGroup (Fin 6)) (hperf : _root_.commutator X = ⊤) :
    Subgroup.center X = N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNcyc : IsCyclic N := isCyclic_of_prime_card hN3
  haveI hcommAut : IsMulCommutative (MulAut N) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (IsCyclic.mulAutMulEquiv N).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  letI : CommGroup (MulAut N) := IsMulCommutative.instCommGroup
  have hNcenter : N ≤ Subgroup.center X := by
    have hker : _root_.commutator X ≤ (MulAut.conjNormal : X →* MulAut N).ker :=
      Abelianization.commutator_subset_ker _
    have hkerTop : (MulAut.conjNormal : X →* MulAut N).ker = ⊤ := by
      rw [eq_top_iff, ← hperf]
      exact hker
    have hφ : (MulAut.conjNormal : X →* MulAut N) = 1 :=
      MonoidHom.ker_eq_top_iff.mp hkerTop
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : (MulAut.conjNormal (H := N) x : MulAut N) = 1 := by
      have h := congrArg (fun f : X →* MulAut N => f x) hφ
      simpa using h
    have hval : x * n * x⁻¹ = n := by
      have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : X)) hx
      simpa [MulAut.conjNormal_apply] using h
    calc x * n = (x * n * x⁻¹) * x := by group
      _ = n * x := by rw [hval]
  have hcenterQuot : Subgroup.center (X ⧸ N) = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by simp)] at h
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (X ⧸ N))
      (f := e.toMonoidHom) e.injective).mp h
  refine le_antisymm ?_ hNcenter
  have hmap : (Subgroup.center X).map (QuotientGroup.mk' N) ≤
      Subgroup.center (X ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
  have hmapbot : (Subgroup.center X).map (QuotientGroup.mk' N) = ⊥ :=
    le_antisymm (hmap.trans (le_of_eq hcenterQuot)) bot_le
  have hle : Subgroup.center X ≤ (QuotientGroup.mk' N).ker :=
    (Subgroup.map_eq_bot_iff (H := Subgroup.center X) (f := QuotientGroup.mk' N)).mp hmapbot
  rwa [QuotientGroup.ker_mk'] at hle

private theorem perfect_quot_center_altSix {X : Type} [Group X] [Finite X]
    (h : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 3) X) :
    _root_.commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) := by
  have hperf := commutator_eq_top_of_isExtNotation_altSix h
  obtain ⟨N, hNnormal, hN3, hAN, -⟩ := h
  haveI : N.Normal := hNnormal
  obtain ⟨e⟩ := hAN
  have hcenter := center_eq_of_perfect_of_normal_card_three hN3 e hperf
  refine ⟨hperf, ?_, ?_⟩
  · rw [hcenter, hN3]
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans e⟩

theorem pRank_three_mulAut_le_two_of_kStarType {X : Type} [Group X] [Finite X]
    (h : IsPSLType 2 (GaloisField 2 3) X ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
        (fun B _ => Nat.card B = 3) X ∨ IsSLType 3 (GaloisField 2 2) X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  rcases h with hL2 | hExt | hSL
  · exact i112f_pRank_mulAut_L2 ⟨3, by decide, by norm_num, hL2⟩
  · obtain ⟨hperf, -, ⟨he⟩⟩ := perfect_quot_center_altSix hExt
    exact i112f_pRank_mulAut_hatAlt (Or.inl rfl) hperf he
  · obtain ⟨e⟩ := hSL
    have hIs : IsSLThreeFour X := by
      refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
      · simpa using GaloisField.card 2 2 (by norm_num)
      · exact ⟨e.trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 2 2))⟩
    have hperf : _root_.commutator X = ⊤ := by
      have hSLperf :
          _root_.commutator (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = ⊤ :=
        CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le
          (n := 3) (by norm_num)
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
        ← _root_.commutator_def, hSLperf]
    exact pRank_mulAut_le_two_of_isSLThreeFour hIs hperf

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
