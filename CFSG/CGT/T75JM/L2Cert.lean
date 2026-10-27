module

public import CFSG.CGT.T75JM.L2FModel
public import CFSG.CGT.T75JM.L2GMain
public import CFSG.CGT.T75JM.N6Cert
public import Certificates.Certificate271030
public import Certificates.Certificate271031

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I

variable {G : Type} [Group G]

theorem evalWord7_genTuple_liftWord {T : Subgroup G}
    (ψ : PG 6 rels6 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) (w : List (Fin 6 × Bool)) :
    evalWord7 (genTuple ψ g) (liftWord w) =
      ((ψ (n0 w) : ↥(Subgroup.normalizer (T : Set G))) : G) := by
  rw [evalWord7_liftWord]
  have h2 : (FreeGroup.lift (fun i : Fin 6 => genTuple ψ g (Fin.castSucc i)) :
      FreeGroup (Fin 6) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) |
          r ∈ rels6.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [genTuple, PresentedGroup.mk]
    rfl
  rw [h2]
  rfl

theorem evalWord7_append_cfg {H : Type*} [Group H] (e : Fin 7 → H) (a b : M22Word) :
    evalWord7 e (a ++ b) = evalWord7 e a * evalWord7 e b := by
  simp only [evalWord7, ← map_mul, FreeGroup.mul_mk]

theorem evalWord7_g {H : Type*} [Group H] (e : Fin 7 → H) :
    evalWord7 e [(6, true)] = e 6 := by
  simp [evalWord7, FreeGroup.lift_mk]

theorem l2Statement_of_certificate :
    L2Statement := by
  intro G _ _ _ T T₁ hyp
  have hchecks : L2Checks := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := Certificates.certificate271030
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Certificates.certificate271031
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6⟩
  have hctx : TCtx T T₁ := ⟨hyp.wc, hyp.inf_bot, hyp.conj, hyp.norm1, hyp.norm2⟩
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hyp.wc.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ T, a ^ 2 = 1 := hyp.wc.1.2
  obtain ⟨φ⟩ := hyp.quot
  obtain ⟨ψ₀, hψ₀⟩ := exists_mulEquiv_normalizer_of_certificate hcomm hsq hyp.card16 hyp.cent_eq φ
  let M := l2Model hchecks
  let E : OntoEmb N0 (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv ψ₀
  have hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGen) ↔
        ψ₀ x ∈ Subgroup.map ψ₀.toMonoidHom (Subgroup.closure (Set.range tGen)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hψ₀, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨E', g, hT', hgT, hgg, hrel⟩ := hctx.exists_config_one M rfl E hE
  refine ⟨⟨E'.toEquiv, ?_, g, hgT, ?_⟩⟩
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    have h3 : E'.Φ (E'.toEquiv.symm y) = (y : G) := by
      rw [← OntoEmb.toEquiv_apply_coe, MulEquiv.apply_symm_apply]
    have := hT' (E'.toEquiv.symm y)
    rw [h3] at this
    exact this
  · intro r hr
    have hg6 : genTuple E'.toEquiv g 6 = g := by simp [genTuple]
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    simp only [thetaRels, List.mem_cons, List.mem_ofFn] at hr
    rcases hr with rfl | ⟨i, rfl⟩
    · rw [show ([(6, true), (6, true)] : M22Word) = [(6, true)] ++ [(6, true)] from rfl,
        evalWord7_append_cfg, evalWord7_g, hg6, hgg]
    · simp only [evalWord7_append_cfg, evalWord7_g, hg6, evalWord7_genTuple_liftWord, n0_invWord,
        OntoEmb.toEquiv_apply_coe, map_inv]
      have h1 : g * E'.Φ (n0 (dGen i)) * g = E'.Φ (n0 (dTheta i)) := by
        have := hrel i
        rw [hginv] at this
        exact this
      rw [h1]
      exact mul_inv_cancel _

end CFSG.CGT.T75JM
