module

public import CFSG.CGT.T75M23.L2FModel7
public import CFSG.CGT.T75M23.P7Cert
public import CFSG.CGT.T75M23.N7Cert
public import CFSG.CGT.T75JM.L2GMain
public import Certificates.Certificate271032

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I
open CFSG.CGT.T75JM (evalWord7 TCtx OntoEmb)

theorem l2Statement7_of_certificate :
    L2Statement7 := by
  intro G _ _ _ T T₁ hyp
  have hchecks : L2Checks7 := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := Certificates.certificate271032
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  have hf := pFacts7_of_certificate
  have hctx : TCtx T T₁ := ⟨hyp.wc, hyp.inf_bot, hyp.conj, hyp.norm1, hyp.norm2⟩
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hyp.wc.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ T, a ^ 2 = 1 := hyp.wc.1.2
  obtain ⟨φ⟩ := hyp.quot
  obtain ⟨ψ₀, hψ₀⟩ :=
    exists_mulEquiv_normalizer7_of_certificate hcomm hsq hyp.card16 hyp.cent_eq φ
  let M := l2Model7 hchecks
  let E : OntoEmb N7 (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv ψ₀
  have hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGen7) ↔
        ψ₀ x ∈ Subgroup.map ψ₀.toMonoidHom (Subgroup.closure (Set.range tGen7)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hψ₀, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨E', g, k, hT', hgT, hg2, hrel⟩ := hctx.exists_config M E hE
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  ·
    have hgg : g * g = 1 := by
      have h : g * g = E'.Φ (n7 (d0W7 0)) := hg2
      rw [h]
      show E'.Φ (n7 []) = 1
      rw [n7_nil, map_one]
    have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    refine ⟨⟨E'.toEquiv, ?_, g, hgT, ?_⟩⟩
    · ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
      have h3 : E'.Φ (E'.toEquiv.symm y) = (y : G) := by
        rw [← OntoEmb.toEquiv_apply_coe, MulEquiv.apply_symm_apply]
      have := hT' (E'.toEquiv.symm y)
      rw [h3] at this
      exact this
    · intro r hr
      have hg6 := genTuple7_six E'.toEquiv g
      simp only [thetaRels7, List.mem_cons, List.mem_ofFn] at hr
      rcases hr with rfl | ⟨i, rfl⟩
      · rw [show ([(6, true), (6, true)] : M23Word) = [(6, true)] ++ [(6, true)] from rfl,
          evalWord7_append7, evalWord7_single7, hg6, hgg]
      · simp only [evalWord7_append7, evalWord7_single7, hg6, evalWord7_genTuple7_liftWord,
          n7_invWord, OntoEmb.toEquiv_apply_coe, map_inv]
        have h1 : g * E'.Φ (n7 (dGen7 i)) * g = E'.Φ (n7 (dTheta7 i)) := by
          have := hrel i
          rw [hg'] at this
          exact this
        rw [h1]
        exact mul_inv_cancel _
  ·
    exact (PCfg7.false_of_one (T₁ := T₁) ⟨E', hT', g, hg2, hrel⟩ hf hyp.cent_le).elim

end CFSG.CGT.T75M23
