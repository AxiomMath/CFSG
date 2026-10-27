module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwDefs
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X} [K.Normal]

private theorem tw_center_commutator_eq_bot (h : SwapShape t Sg V) :
    Subgroup.center (⁅Sg, Sg⁆ : Subgroup X) = ⊥ := by
  haveI : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := h.isSimpleGroup_commutator_sg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (⁅Sg, Sg⁆ : Subgroup X)) with hbot | htop
  · exact hbot
  · exfalso
    haveI : IsMulCommutative (⁅Sg, Sg⁆ : Subgroup X) :=
      Subgroup.center_eq_top_iff.mp htop
    have hprime : (Nat.card (⁅Sg, Sg⁆ : Subgroup X)).Prime :=
      (Group.is_simple_iff_prime_card (α := (⁅Sg, Sg⁆ : Subgroup X))).mp inferInstance
    rw [h.card_commutator_sg] at hprime
    norm_num at hprime

private theorem tw_mem_center_commutator_of_mem_center (hA : ⁅Sg, Sg⁆ ≤ K)
    (z : (⁅Sg, Sg⁆ : Subgroup X))
    (hz : Subgroup.inclusion hA z ∈ Subgroup.center ↥K) :
    z ∈ Subgroup.center (⁅Sg, Sg⁆ : Subgroup X) := by
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hcomm := Subgroup.mem_center_iff.mp hz (Subgroup.inclusion hA w)
  simpa [Subgroup.coe_mul] using congrArg Subtype.val hcomm

private noncomputable def tw_psi (hA : ⁅Sg, Sg⁆ ≤ K) :
    (⁅Sg, Sg⁆ : Subgroup X) →* (K ⧸ Subgroup.center K) :=
  (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hA)

private theorem tw_psi_apply (hA : ⁅Sg, Sg⁆ ≤ K) (c : (⁅Sg, Sg⁆ : Subgroup X)) :
    tw_psi hA c = QuotientGroup.mk (Subgroup.inclusion hA c) := rfl

private theorem tw_psi_injective (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) :
    Function.Injective (tw_psi hA) := by
  rw [← MonoidHom.ker_eq_bot_iff (tw_psi hA)]
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hz : Subgroup.inclusion hA c ∈ Subgroup.center ↥K := by
      rw [← QuotientGroup.eq_one_iff, ← tw_psi_apply hA c]
      exact hc
    have hcenter : c ∈ Subgroup.center (⁅Sg, Sg⁆ : Subgroup X) :=
      tw_mem_center_commutator_of_mem_center hA c hz
    rw [tw_center_commutator_eq_bot h] at hcenter
    exact hcenter
  · exact bot_le

private noncomputable def tw_actionFun (K : Subgroup X) [K.Normal] (x : X) :
    MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center K) (Subgroup.center K)
    (MulAut.conjNormal x) (Subgroup.map_center_eq (MulAut.conjNormal x))

private theorem tw_actionFun_apply (K : Subgroup X) [K.Normal] (x : X) (k : K) :
    tw_actionFun K x (QuotientGroup.mk k) =
      QuotientGroup.mk (MulAut.conjNormal x k) :=
  rfl

private noncomputable def tw_action (K : Subgroup X) [K.Normal] :
    X →* MulAut (K ⧸ Subgroup.center K) where
  toFun := tw_actionFun K
  map_one' := by
    ext u
    refine QuotientGroup.induction_on u (fun k => ?_)
    rw [tw_actionFun_apply]
    simp
  map_mul' := by
    intro x y
    ext u
    refine QuotientGroup.induction_on u (fun k => ?_)
    rw [MulAut.mul_apply, tw_actionFun_apply, tw_actionFun_apply, tw_actionFun_apply,
      map_mul (MulAut.conjNormal) x y, MulAut.mul_apply]

private theorem tw_action_mk (K : Subgroup X) [K.Normal] (x : X) (k : K) :
    tw_action K x (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal x k) :=
  rfl

private theorem tw_conjNormal_inclusion_eq (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K)
    (c : (⁅Sg, Sg⁆ : Subgroup X)) :
    MulAut.conjNormal t (Subgroup.inclusion hA c) = Subgroup.inclusion hA c := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, Subgroup.coe_inclusion]
  have hc : t * (c : X) = (c : X) * t := by
    have hmem : (c : X) ∈ centralizer ({t} : Set X) := h.commutator_sg_le_centralizer c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    exact hmem.symm
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

private theorem tw_action_eq_conj (hA : ⁅Sg, Sg⁆ ≤ K) {a : X}
    (ha : a ∈ (⁅Sg, Sg⁆ : Subgroup X)) :
    tw_action K a = MulAut.conj (QuotientGroup.mk (⟨a, hA ha⟩ : K)) := by
  ext u
  refine QuotientGroup.induction_on u (fun k => ?_)
  rw [tw_action_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1

private theorem tw_action_t_psi (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K)
    (c : (⁅Sg, Sg⁆ : Subgroup X)) :
    tw_action K t (tw_psi hA c) = tw_psi hA c := by
  simp only [tw_psi_apply, tw_action_mk, tw_conjNormal_inclusion_eq h hA]

private theorem tw_mulEquiv_symm_trans_apply {G H I : Type*} [Group G] [Group H] [Group I]
    (e : G ≃* H) (f : G ≃* I) (x : I) :
    ((e.symm.trans f).symm x : H) = e (f.symm x) := by
  apply (e.symm.trans f).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]

theorem false_of_hs_of_conj (hF : TwHSFusion) {X : Type} [Group X] [Finite X] {t : X}
    {Sg V K : Subgroup X} [K.Normal] (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* NativeSporadic.HS))
    (eA : (⁅Sg, Sg⁆ : Subgroup X) ≃* alternatingGroup (Fin 8)) {y a : X}
    (ha : a ∈ (⁅Sg, Sg⁆ : Subgroup X)) (heA : eA ⟨a, ha⟩ = abType22)
    (hy : y * t * y⁻¹ = t * a) : False := by
  classical
  haveI : Finite (K ⧸ Subgroup.center K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective (Subgroup.center K))
  have ht2 : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [h.order_eq] at hpow
    simpa [pow_two] using hpow
  have hτ2 : tw_action K t * tw_action K t = 1 := by
    rw [← map_mul (tw_action K) t t, ht2, map_one (tw_action K)]
  let ψ : (⁅Sg, Sg⁆ : Subgroup X) →* (K ⧸ Subgroup.center K) := tw_psi hA
  have hψ : Function.Injective ψ := tw_psi_injective h hA
  let B : Subgroup (K ⧸ Subgroup.center K) := ψ.range
  let eB : B ≃* alternatingGroup (Fin 8) := (MonoidHom.ofInjective hψ).symm.trans eA
  have hb0 : ((eB.symm abType22 : B) : (K ⧸ Subgroup.center K)) = ψ ⟨a, ha⟩ := by
    have h1 : (eB.symm abType22 : B) =
        MonoidHom.ofInjective hψ (eA.symm abType22) :=
      tw_mulEquiv_symm_trans_apply (MonoidHom.ofInjective hψ) eA abType22
    rw [h1, MonoidHom.ofInjective_apply, ← heA, MulEquiv.symm_apply_apply]
  have hτB : ∀ b : B, tw_action K t (b : (K ⧸ Subgroup.center K)) = b := by
    intro b
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp b.2
    rw [← hc]
    exact tw_action_t_psi h hA c
  have hconj : tw_action K y * tw_action K t * (tw_action K y)⁻¹ =
      tw_action K t *
        MulAut.conj ((eB.symm abType22 : B) : (K ⧸ Subgroup.center K)) := by
    calc tw_action K y * tw_action K t * (tw_action K y)⁻¹
        = tw_action K (y * t * y⁻¹) := by
          rw [← map_mul (tw_action K) y t, ← map_inv (tw_action K) y,
            ← map_mul (tw_action K) (y * t) y⁻¹]
      _ = tw_action K (t * a) := by rw [hy]
      _ = tw_action K t * tw_action K a := by rw [map_mul (tw_action K) t a]
      _ = tw_action K t *
            MulAut.conj ((eB.symm abType22 : B) : (K ⧸ Subgroup.center K)) := by
          rw [tw_action_eq_conj hA ha, hb0]
          congr 1
  exact hF (K ⧸ Subgroup.center K) e (tw_action K t) hτ2 B eB hτB (tw_action K y) hconj

end CFSG.OddStandard.AltStdSec.SwapPartner
