module

public import CFSG.LargeExtraspecial.S14C13B2Gen
public import CFSG.LargeExtraspecial.S14C13B2Data
public import CFSG.LargeExtraspecial.S14C13Schur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Lin

variable {t : S.O} [NQHyp S g t]

theorem cLin_eq_of_eq {x y : S.O} (hx : x ∈ Ct S t) (hy : y ∈ Ct S t) (h : x = y) :
    cLin (g := g) hx = cLin (g := g) hy := by
  subst h
  rfl

theorem cLin_mul_inv {c : S.O} (hc : c ∈ Ct S t) :
    cLin (g := g) hc * cLin (g := g) (inv_mem hc) = 1 :=
  (cLin_mul hc (inv_mem hc)).symm.trans
    ((cLin_eq_of_eq _ (one_mem _) (mul_inv_cancel c)).trans cLin_one)

theorem cLin_inv_mul {c : S.O} (hc : c ∈ Ct S t) :
    cLin (g := g) (inv_mem hc) * cLin (g := g) hc = 1 :=
  (cLin_mul (inv_mem hc) hc).symm.trans
    ((cLin_eq_of_eq _ (one_mem _) (inv_mul_cancel c)).trans cLin_one)

theorem cLin_conj {α c : S.O} (hα : α ∈ Ct S t) (hc : c ∈ Ct S t) :
    cLin (g := g) (mul_mem (mul_mem hc hα) (inv_mem hc)) =
      cLin (g := g) hc * cLin (g := g) hα * cLin (g := g) (inv_mem hc) :=
  (cLin_mul (mul_mem hc hα) (inv_mem hc)).trans
    (congrArg (· * cLin (g := g) (inv_mem hc)) (cLin_mul hc hα))

theorem cLin_comm {α β : S.O} (hα : α ∈ Ct S t) (hβ : β ∈ Ct S t)
    (hαβ : α * β * α⁻¹ * β⁻¹ ∈ Nbar S g t) :
    cLin (g := g) hα * cLin (g := g) hβ = cLin (g := g) hβ * cLin (g := g) hα := by
  have hn : α * β * α⁻¹ * β⁻¹ ∈ Ct S t :=
    mul_mem (mul_mem (mul_mem hα hβ) (inv_mem hα)) (inv_mem hβ)
  calc cLin (g := g) hα * cLin (g := g) hβ = cLin (g := g) (mul_mem hα hβ) :=
        (cLin_mul hα hβ).symm
    _ = cLin (g := g) (mul_mem hn (mul_mem hβ hα)) := cLin_eq_of_eq _ _ (by group)
    _ = cLin (g := g) hn * cLin (g := g) (mul_mem hβ hα) := cLin_mul hn (mul_mem hβ hα)
    _ = cLin (g := g) (mul_mem hβ hα) := by rw [cLin_eq_one_of_mem_Nbar hn hαβ, one_mul]
    _ = cLin (g := g) hβ * cLin (g := g) hα := cLin_mul hβ hα

theorem cLin_ne_one (h7 : Concl14_7 S g t) {α : S.O} (hα : α ∈ Ct S t)
    (hαN : α ∉ Nbar S g t) (hne : ∃ n ∈ Nbar S g t, n ∉ zpowers t) :
    cLin (g := g) hα ≠ 1 := fun h =>
  hαN (mem_Nbar_of_cLin_eq_smul h7 hα hne (c := 1)
    ((h.trans Module.End.one_eq_id).trans (one_smul (ZMod 2) LinearMap.id).symm))

end Lin

theorem exists_psi [IsSimpleGroup G] (hCE : CentralExtInput.{0}) {t : S.O} [NQHyp S g t]
    (hSt : Stage S g t) (hocc : Config.omegaPlus8b.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (h7 : Concl14_7 S g t)
    (hF : FCt S t ≠ Nbar S g t) (D : B2Data S g hSt.mem) :
    ∃ (α : S.O) (hα : α ∈ Ct S t),
      (∀ e v, (cLin (g := g) hα - 1) (nqRep S g t D.hX e v) =
        nqRep S g t D.hX e ((cLin (g := g) hα - 1) v)) ∧
      LinearMap.range (cLin (g := g) hα - 1) = LinearMap.ker (cLin (g := g) hα - 1) ∧
      finrank (ZMod 2) (LinearMap.range (cLin (g := g) hα - 1)) = 8 ∧
      ∀ (c : S.O) (hc : c ∈ Ct S t),
        cLin (g := g) hc * (cLin (g := g) hα - 1) = (cLin (g := g) hα - 1) * cLin (g := g) hc := by
  have H := hSt.hyp4
  have haQ := H.conj_mem
  have ht := hSt.mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
  have hne := exists_mem_Nbar_not_mem_zpowers hext htN hSt.ne_one fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have hex := exists_mem_comm_mem_of_lt (Nbar_le_FCt haQ hext.1) hF.symm
    (fun f hf n hn => conj_mem_Nbar_of_mem_Ct haQ (FCt_le_Ct t hf) hn) (isPGroup_FCt h7)
  obtain ⟨α, hαF, hαN, hαc⟩ := hex
  have hα := FCt_le_Ct t hαF
  have hRep : ∀ β (hβ : β ∈ FCt S t), ∀ e v, cLin (g := g) (FCt_le_Ct t hβ)
      (nqRep S g t D.hX e v) = nqRep S g t D.hX e (cLin (g := g) (FCt_le_Ct t hβ) v) :=
    fun β hβ e v => cLin_comm_nqRep _ (comm_mem_Nbar_of_mem_FCt hCE hSt hocc hext h7 hβ)
      D.hX e v
  have hPow : ∀ β (hβ : β ∈ FCt S t), ∃ k, cLin (g := g) (FCt_le_Ct t hβ) ^ (2 ^ k) = 1 := by
    intro β hβ
    have hP := isPGroup_FCt h7 ⟨β, hβ⟩
    obtain ⟨k, hk⟩ := hP
    exact ⟨k, cLin_pow_eq_one _ (by simpa using congrArg Subtype.val hk)⟩
  have hdimM : finrank (ZMod 2) (NQ S g t) = 2 ^ 4 := B2Data.finrank_nq hSt hocc
  have hc := D.nq_isCompl hCE hSt hocc
  have hPα := hPow α hαF
  obtain ⟨k, hk⟩ := hPα
  have hdata := psi_data (nqRep S g t D.hX) (m := 4) (by norm_num) (by rw [D.hdim])
    hdimM (aV_ne_zero H ht) (D.Q_aV H) (D.Q_bV H) D.hab hc (hRep α hαF) hk
    (cLin_ne_one h7 hα hαN hne)
  obtain ⟨-, hrk, hr⟩ := hdata
  refine ⟨α, hα, sub_one_comm_of_comm _ (hRep α hαF), hrk, hr, fun c hcC => ?_⟩
  have hβF : c * α * c⁻¹ ∈ FCt S t := conj_mem_FCt_of_mem_Ct hcC hαF
  have hβN : c * α * c⁻¹ ∉ Nbar S g t := fun h => hαN (by
    have := conj_mem_Nbar_of_mem_Ct haQ (inv_mem hcC) h
    rwa [show c⁻¹ * (c * α * c⁻¹) * c⁻¹⁻¹ = α by group] at this)
  have hPβ := hPow _ hβF
  obtain ⟨k', hk'⟩ := hPβ
  have heq := psi_unique (nqRep S g t D.hX) (m := 4) (by norm_num) (by rw [D.hdim]) hdimM
    (aV_ne_zero H ht) (D.Q_aV H) (D.Q_bV H) D.hab hc (hRep α hαF) (hRep _ hβF) hk hk'
    (cLin_ne_one h7 hα hαN hne) (cLin_ne_one h7 _ hβN hne)
    (cLin_comm hα (FCt_le_Ct t hβF) (hαc _ hβF))
  exact psi_comm_of_conj (cLin_mul_inv hcC) (cLin_inv_mul hcC)
    (heq.trans (congrArg (· - 1) (cLin_conj hα hcC)))

end CFSG.LargeExtraspecial.S14
