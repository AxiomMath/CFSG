module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10St
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Real
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ABas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ACand
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ANum2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import Certificates.Certificate441791

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}

theorem fzr_a_base_le_wreath :
    (baseGrp x₁ x₂ : Subgroup G) ≤ wreathGrp x₁ x₂ lam := by
  unfold baseGrp wreathGrp
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  tauto

@[expose] noncomputable def fzrANum {Q R P : Subgroup G} {a b : G} {Mt Ms Ml : Mat}
    (S : FzR10ASet t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) Q R T₂ P a b)
    (hM : FzR10AMats t tau lam a b Mt Ms Ml) (htP : t ∉ P) :
    FzRNum t x₁ x₂ lam rho tau T₂ where
  par := parOfA Mt Ms Ml
  mu := fzrAMu a b t tau lam
  mu_mem := fzrAMu_mem S
  mu_zero := fzrAMu_zero
  mu_mul := fun _ _ hn hm => fzrAMu_mul S hM hn hm
  mu_inj := fun _ _ hn hm h => fzrAMu_inj S htP hn hm h
  mu_surj := fun _ hg => fzrAMu_surj S htP hg
  tI_eq := rfl
  sI_eq := rfl
  mu_tI := fzrAMu_tI
  mu_sI := fzrAMu_sI
  e_lt := fun _ _ hx hy => fzr_a_emA_lt Mt Ms Ml hx hy
  gens_lt := by
    intro g hg
    simp only [parOfA] at hg
    fin_cases hg <;> norm_num
  rho_lt := by
    intro x hx
    have h1 : rho0.ap (x % 64) < 64 := fzr_a_ap_lt rho0 (x % 64)
    simp only [parOfA]
    omega
  mu_rho := fun _ hx => fzrAMu_rho S hx
  mu_inW := fun _ h => fzrAMu_inW S hM h
  mu_inTL := fun _ hx h =>
    fzrAMu_inTL S hM hx h fzr_a_base_le_wreath (Subgroup.subset_closure (by simp))
  mu_inTZ := fun _ hz _ hx h => fzrAMu_inTZ S htP hz hx h
  t_mem := S.str.RT (S.str.QR (S.str.WQ S.str.t_mem))
  t_sq := S.str.t_sq
  tau_sq1 := S.pf.tau_sq1
  tau_t := S.str.tau_t

theorem fzr_noA :
    FzR10NoA := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hsyl htP h8
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  have hpf := fzl_pfacts hstr (P := fzP t x₁ x₂ rho) rfl htP
  obtain ⟨a, b, hB, hrho⟩ := fzr_a_basis hstr hpf h8
  let SA := FzR10ASet.mk hstr hpf h8 hB hrho
  have hnrm : ∀ c ∈ T₂, ∀ p ∈ fzP t x₁ x₂ rho, c * p * c⁻¹ ∈ fzP t x₁ x₂ rho :=
    fun c hc p hp => hpf.nrm_P c hc p hp
  obtain ⟨Mt, hMt, hct⟩ := fzr_a_act_exists hB (hnrm t (hstr.RT (hstr.QR (hstr.WQ hstr.t_mem))))
  obtain ⟨Ms, hMs, hcs⟩ := fzr_a_act_exists hB (hnrm tau (hstr.RT hstr.tau_R))
  obtain ⟨Ml, hMl, hcl⟩ := fzr_a_act_exists hB (hnrm lam hstr.lam_T)
  have hM : FzR10AMats t tau lam a b Mt Ms Ml := ⟨hMt, hMs, hMl, hct, hcs, hcl⟩
  exact Certificates.certificate441791 Mt Ms Ml hMt hMs hMl (fzr_a_candT SA hMt hct)
    (fzr_a_candS SA hMt hMs hct hcs) (fzr_a_candL SA hMt hMl hct hcl)
    (fzr_a_comm_SL SA hMs hMl hcs hcl)
    ⟨fzrTh (fzrANum SA hM htP), fzr_rules (fzrANum SA hM htP) hctx hK hT hsyl⟩

end CFSG.OddStandard.SmallF3.FritzII
