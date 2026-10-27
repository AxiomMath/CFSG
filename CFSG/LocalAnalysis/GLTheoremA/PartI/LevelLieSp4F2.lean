module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4F1
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4E

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)
open scoped commutatorElement

theorem kdLieRowSp4EightField_holds : KDLieRowSp4EightField := by
  intro q hv hq α hα3 hαin I hI
  obtain ⟨e⟩ := bridge_B2 q hv hq
  haveI : Finite ↥(StatedSp 2 F8) := inferInstance
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group :=
    Finite.of_equiv _ e.symm.toEquiv
  let eT : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group ≃* TF :=
    e.trans eQ.symm
  have hβ3 : (MulAut.congr eT α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hβin : MulAut.congr eT α ∉ innTF := by
    intro h
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 h
    apply hαin
    refine MonoidHom.mem_range.2 ⟨eT.symm y, (MulAut.congr eT).injective ?_⟩
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hy
  have hfix : fixSubgroup (MulAut.congr eT α) = (fixSubgroup α).map eT.toMonoidHom := by
    ext y
    rw [mem_fixSubgroup, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨eT.symm y, ?_, by simp⟩
      rw [mem_fixSubgroup]
      have h1 : eT (α (eT.symm y)) = y := hy
      have h2 := congrArg eT.symm h1
      simpa using h2
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fixSubgroup] at hx
      show eT (α (eT.symm (eT x))) = eT x
      rw [MulEquiv.symm_apply_apply, hx]
  have hIβ : GLAPComponent 3 (fixSubgroup (MulAut.congr eT α)) (I.map eT.toMonoidHom) := by
    rw [hfix]
    exact glaPComponent_map_mulEquiv Nat.prime_three eT hI
  have hlev := fieldT_level (MulAut.congr eT α) hβ3 hβin hIβ
  obtain ⟨eP⟩ := pSimple_map_equiv' 3 eT I
  rw [← kLevel_congr 3 eP]
  exact hlev

@[expose] def KDLieRowSp4EightFPFLayer : Prop :=
  ∀ A : ↥(StatedSp 2 (GaloisField 2 3)), A ^ 3 = 1 → Pm (mat A) = 0 →
    ∃ N : Subgroup ↥(StatedSp 2 (GaloisField 2 3)),
      N ≤ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3))) ∧
      (∀ g ∈ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3))),
        ∀ h ∈ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3))), ⁅g, h⁆ ∈ N) ∧
      Nonempty (↥N ≃* ↥(StatedSL 2 (GaloisField 2 3)))

theorem kdLieRowSp4EightFreeBlock_of_FPF (hL : KDLieRowSp4EightFPFLayer) :
    KDLieRowSp4EightFreeBlock := by
  intro A hA3 hP I hI
  obtain ⟨N, hNC, hcomm, ⟨eN⟩⟩ := hL A hA3 hP
  haveI : Finite ↥(StatedSp 2 (GaloisField 2 3)) := inferInstance
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  haveI : IsSimpleGroup ↥(StatedSL 2 (GaloisField 2 3)) :=
    isSimpleGroup_SL2 (K := GaloisField 2 3) card_F8
  haveI : IsSimpleGroup ↥N := eN.isSimpleGroup
  have hIN : I ≤ N := by
    calc I = ⁅I, I⁆ := (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hI).symm
      _ ≤ ⁅Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3))),
            Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3)))⁆ :=
          Subgroup.commutator_mono hI.1 hI.1
      _ ≤ N := Subgroup.commutator_le.2 (fun g hg h hh => hcomm g hg h hh)
  have hsub : CFSG.Open.IsSubnormal (I ⊓ N) N := hI.2.1.inf_of_le hNC
  rw [inf_eq_left.2 hIN] at hsub
  have hIeq : I = N :=
    (CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance).resolve_left
      (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI)
  rw [hIeq]
  have hnc : ¬ IsMulCommutative ↥N := not_comm_of_mulEquiv eN (not_comm_SL2 (K := GaloisField 2 3))
  have h3 : 3 ∣ Nat.card ↥N := by
    rw [Nat.card_congr eN.toEquiv, nat_card_SL2 (K := GaloisField 2 3) card_F8]
    norm_num
  obtain ⟨eP⟩ := pSimple_equiv_of_simple' N hnc h3
  rw [kLevel_congr 3 eP, kLevel_congr 3 eN]
  exact kLevel_le_two_of_k2' (catalog_SL2 (K := GaloisField 2 3) card_F8)

theorem kdLieRowSp4Eight_of_FPFLayer (hL : KDLieRowSp4EightFPFLayer) : KDLieRowSp4Eight :=
  kdLieRowSp4Eight_of_residuals kdLieRowSp4EightField_holds (kdLieRowSp4EightFreeBlock_of_FPF hL)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F
