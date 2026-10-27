module

public import CFSG.LargeExtraspecial.S14C13B2Act
public import CFSG.LargeExtraspecial.S14C13B2Abs
public import CFSG.LargeExtraspecial.S14C13B2CaseI
public import CFSG.LargeExtraspecial.S14C13B2Atil
public import CFSG.LargeExtraspecial.S14C13B2Fbar
public import CFSG.LargeExtraspecial.S14C13B2WS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

theorem claim14_13B2_of (hCE : CentralExtInput.{0}) (h83 : S8_3Stmt) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
      Stage S g t → Config.omegaPlus8b.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
        IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
        FCt S t ≠ Nbar S g t → False := by
  intro G _ _ _ S g t hSt hocc hext h6 h7 h8 hF
  have H := hSt.hyp4
  have haQ := H.conj_mem
  have ht := hSt.mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
  have hNo : NoA2 S g := noA2_of_stage hSt
  have hocc1 := hocc.1
  obtain ⟨⟨H', C, ht', ht1, hVQ, hΩ, hdim⟩, -⟩ := hocc1
  have hDstd := S8.Std.nonempty hCE hNo hΩ
  obtain ⟨Dstd⟩ := hDstd
  have : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  let D : B2Data S g hSt.mem := B2Data.ofStd Dstd hdim
  have W := weakSetting_of hSt hext h7
  have hsimp : IsSimpleGroup (omegaGroup D.Q D.hQ) := D.hX ▸ isSimpleGroup_RmodN_of_occurs hocc
  have hψ := exists_psi hCE hSt hocc hext h7 hF D
  obtain ⟨α, hα, hψR, hrk, hr8, hψc⟩ := hψ
  have hcN := D.nq_isCompl hCE hSt hocc
  have hfix := S8.fixOf_nqRep_radFix_eq hNo Dstd
  have hfixL : fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV hSt.mem) : Set _) ≤
      nqSub S g t (S.Lbar g) := by
    rw [radFix_bot] at hfix
    exact hfix.le
  have hB : W.B2Hyp (nqPre S g t (LinearMap.range (cLin (g := g) hα - 1))) (S.Lbar g) :=
    { t_mem_A := zpowers_le_nqPre htN _ (mem_zpowers t)
      A_le := nqPre_le _
      A_comm := fun a ha b hb => comm_of_mem_nqPre_range W hα hrk ha hb
      A_norm := fun h hX hht a ha =>
        conj_mem_nqPre_range hψc ⟨hX, mem_centralizer_singleton_iff.mpr hht⟩ ha
      t_mem_L := ht
      L_le := S.Lbar_le_Mbar g
      L_comm := fun a ha b hb => Lbar_comm S haQ ha hb
      L_fus := fun k hk hkL => by
        have hn := S5.exists_mem_normalizer_conj H hSt.cons hk
          (fun l hl => Lbar_comm S haQ ht hl) (fun l hl => Lbar_comm S haQ hkL hl)
        obtain ⟨n, hnM, hnN, hn⟩ := hn
        exact ⟨n, hnM, hnN, hn.symm⟩
      N_norm_L := fun n hn => by
        have hnM := Rbar_le_Mbar (Nbar_le_Rbar hn)
        have := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hnM
          (by simpa using hn.2 _ (cl_a_mem_Vt ht))
        simpa using this
      exists_AL := exists_mem_A_inf_Lbar D H hcN hψR hr8 hfixL
      tv := fun y hy c hc h =>
        comm_mem_zpowers_of_rank_le_one D H hcN hψR hr8 (Lbar_le_Rbar ht hy) hc h
      faith := fun y hy h => mem_Nbar_of_comm_A D H hcN hψR hr8 (Lbar_le_Rbar ht hy) h }
  have hτ := exists_conj_mem_Lbar_not_mem_Nbar h83 hSt hocc
  obtain ⟨k, hk, hτL, hτN⟩ := hτ
  have he := exists_conj_mem_Nbar_inf hCE hSt hocc D W hk hτL hτN
  obtain ⟨e, heD, heL, heN, heNτ, het⟩ := he
  rw [S10.Nbar_conj haQ k t] at heNτ
  exact hB.false (kτ := S.ρ k) ⟨k, rfl⟩ hτL hτN heD heL heN heNτ het

end CFSG.LargeExtraspecial.S14
