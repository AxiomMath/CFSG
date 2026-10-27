module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain
public import CFSG.ClassicalInvolution.Q3.TA3FrameSp4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4U1
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4U2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatFactsSp4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Blueprint CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TA3
open CFSG.CGT.PushingUpLit.SolKNA.R4


theorem twin_false_psp4_odd {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (e : ↥(genFittingFStar Y) ≃* StatedProj (StatedSp 2 K)) : False := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have htN : t ∈ genFittingFStar Y :=
    twin_mem_of_noQ8Outer h hC fun φ => Q5Sp4.not_injective_outer h2 e φ
  have hu2 : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h.core.datum.order]
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu2
  set e' : ↥(genFittingFStar Y) ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj g⁻¹) with he'
  have he't : e' ⟨t, htN⟩ = g⁻¹ * e ⟨t, htN⟩ * g := by simp [he']
  rcases hg with h1 | h1
  · exact twin_false_of_model h e' htN (he't.trans h1) (E1 K) (E2 K)
      (Frame.isComponentOf_E1 h2 h4) (Frame.isComponentOf_E2 h2 h4)
      (by rw [← Q5Sp4.X0_eq_sup h2]; exact Q5Sp4.noQ8Fix_X0 hodd h4)
  · have hLC : Lsub K ≤ Subgroup.centralizer ({u2 K} : Set _) := Lsub_le_centralizer
    have hCN := TA3.Sp4.centralizer_u2_le_normalizer_Lsub h2 h4
    have hn : ((Lsub K).subgroupOf (Subgroup.centralizer ({u2 K} : Set _))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hLC]
      intro l c hl hc
      exact (Subgroup.mem_normalizer_iff.mp (hCN hc) l).mp hl
    have hcomp := Frame.isComponentOf_of_normal hLC hn
      (Frame.isQuasisimple_of_simple (isSimpleGroup_Lsub h4) (TA3.Sp4.isPerfect_Lsub h4))
    exact twin_false_of_model h e' htN (he't.trans h1) (Lsub K) (Lsub K) hcomp hcomp
      (by rw [sup_idem]; exact Q5Sp4.noQ8Fix_Lsub hodd h4)

theorem twinLeafR_psp4Ne3 {r n : ℕ} : TwinLeafR r n SmallPSp4Ne3 := by
  intro Y _ _ R S t hP _ hF
  obtain ⟨p, f, hp, hp2, hf, hq3, hL⟩ := hF
  rcases hL with ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ p := by
            rcases hp.eq_two_or_odd' with h | h
            · exact absurd h hp2
            · have := hp.two_le
              obtain ⟨k, hk⟩ := h
              omega
        _ ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h5 : 5 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      rw [hK] at hk
      omega
    exact twin_false_psp4_odd hP hodd h5 e
  all_goals exact absurd ht (by decide)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
