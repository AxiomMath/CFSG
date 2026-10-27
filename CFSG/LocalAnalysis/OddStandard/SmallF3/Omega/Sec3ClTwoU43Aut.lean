module

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffSimOmegaAct_h2_irrel (hQ : Q.Nondegenerate)
    {h2a h2b : 2 ≤ Module.finrank (ZMod 3) V} :
    ffSimOmegaAct hQ h2a = ffSimOmegaAct hQ h2b := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.ext
  intro w
  exact Subtype.ext rfl

private theorem ffSimOmegaAct_injective' (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Injective (ffSimOmegaAct hQ h2) := by
  have h := ffSimOmegaAct_injective hQ h5
  rwa [← ffSimOmegaAct_h2_irrel (hQ := hQ) (h2a := h2)] at h

private theorem ffSimOmegaAct_surjective' (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Surjective (ffSimOmegaAct hQ h2) := by
  have h := (ffSimOmegaAct_bijective_six_minus hQ hdim hs).2
  rwa [← ffSimOmegaAct_h2_irrel (hQ := hQ) (h2a := h2)] at h

private theorem ker_omegaToProj_eq_center (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    (omegaToProj hQ).ker = Subgroup.center (omegaGroup hQ) := by
  have hpi : piOrth Q ∈ omegaGroup hQ := ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs
  let p : omegaGroup hQ := ⟨piOrth Q, hpi⟩
  have hp2 : p * p = 1 := Subtype.ext (by
    change piOrth Q * piOrth Q = 1
    exact piOrth_mul_self)
  have hp1 : p ≠ 1 := fun h =>
    piOrth_ne_one (by omega) (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h)
  have hpker : p ∈ (omegaToProj hQ).ker := by
    rw [MonoidHom.mem_ker]
    exact (omegaToProj_eq_one_iff hQ p).mpr (Or.inr rfl)
  have hle : (omegaToProj hQ).ker ≤ Subgroup.center (omegaGroup hQ) := fun m hm =>
    Subgroup.mem_center_iff.mpr (fun g =>
      omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g)
  have hzle : Subgroup.zpowers p ≤ (omegaToProj hQ).ker := Subgroup.zpowers_le.mpr hpker
  have hzcard : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hp2) hp1
  refine Subgroup.eq_of_le_of_card_ge (H := (omegaToProj hQ).ker)
    (K := Subgroup.center (omegaGroup hQ)) hle ?_
  rw [natCard_center_omegaGroup_six_minus hQ hdim hs, ← hzcard]
  exact Nat.card_le_card_of_injective
    (fun x : Subgroup.zpowers p =>
      (⟨(x : omegaGroup hQ), hzle x.2⟩ : (omegaToProj hQ).ker))
    (fun x y h => Subtype.ext
      (congrArg (fun z : (omegaToProj hQ).ker => (z : omegaGroup hQ)) h))

theorem cl_exists_simil_of_mulAut_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (α : MulAut (omegaGroup hQ)) (hα : α * α = 1) :
    ∃ γ : simGroup Q, ((∀ v, (γ : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) = v) ∨
        (∀ v, (γ : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) = -v)) ∧
      ∀ t : omegaGroup hQ, ((α t : omegaGroup hQ) : OGroup Q) = simAct Q γ (t : OGroup Q) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hker_eq : (omegaToProj hQ).ker = Subgroup.center (omegaGroup hQ) :=
    ker_omegaToProj_eq_center hQ hdim hs
  have hker : ∀ n ∈ (omegaToProj hQ).ker, α n ∈ (omegaToProj hQ).ker := by
    intro n hn
    rw [hker_eq] at hn ⊢
    rw [Subgroup.mem_center_iff] at hn ⊢
    intro g
    obtain ⟨h, rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, hn h]
  obtain ⟨abar, habar, -⟩ :=
    sec63PT_exists_induced_aut (omegaToProj_surjective hQ) hα hker
  obtain ⟨x, hx⟩ := ffSimOmegaAct_surjective' hQ hdim hs h2 abar
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have habar' : ∀ y : omegaGroup hQ,
      omegaToProj hQ (α y) = ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) (omegaToProj hQ y) := by
    intro y
    rw [habar y, hx]
  have htoProj : ∀ t : omegaGroup hQ,
      toProj Q ((α t : omegaGroup hQ) : OGroup Q) =
        toProj Q (simAct Q γ ((t : omegaGroup hQ) : OGroup Q)) := by
    intro t
    have h := congrArg (fun z : omegaProj hQ => (z : ProjOrth Q)) (habar' t)
    simpa only [coe_omegaToProj, coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj] using h
  let cγ : MulAut (omegaGroup hQ) :=
    { toFun := fun w => ⟨simAct Q γ (w : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 γ w.2⟩
      invFun := fun w => ⟨simAct Q γ⁻¹ (w : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 γ⁻¹ w.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        change simAct Q γ⁻¹ (simAct Q γ (w : OGroup Q)) = (w : OGroup Q)
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun w => by
        apply Subtype.ext
        change simAct Q γ (simAct Q γ⁻¹ (w : OGroup Q)) = (w : OGroup Q)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun a b => by
        apply Subtype.ext
        change simAct Q γ ((a : OGroup Q) * (b : OGroup Q)) =
          simAct Q γ (a : OGroup Q) * simAct Q γ (b : OGroup Q)
        exact map_mul (simAct Q γ) _ _ }
  have hc : ∀ a : omegaGroup hQ,
      omegaToProj hQ ((cγ * α⁻¹) a) = omegaToProj hQ a := by
    intro a
    apply Subtype.ext
    change toProj Q (((cγ * α⁻¹) a : omegaGroup hQ) : OGroup Q) = toProj Q (a : OGroup Q)
    have h1 := htoProj (α⁻¹ a)
    have h3 : α (α⁻¹ a) = a := by
      have hh := congrArg (fun f : MulAut (omegaGroup hQ) => f a) (mul_inv_cancel α)
      simpa [MulAut.mul_apply, MulAut.one_apply] using hh
    rw [h3] at h1
    rw [show (((cγ * α⁻¹) a : omegaGroup hQ) : OGroup Q) =
        simAct Q γ (((α⁻¹) a : omegaGroup hQ) : OGroup Q) from by
          rw [MulAut.mul_apply]; rfl]
    exact h1.symm
  have hperf : commutator (omegaGroup hQ) = ⊤ :=
    Group.isPerfect_def.mp (isQuasisimple_omegaGroup_six_minus hQ hdim hs).1
  have hσ : cγ * α⁻¹ = 1 :=
    sec63PT_eq_one_of_induced_eq_one (le_of_eq hker_eq) hperf hc
  have hαeq : cγ = α := by
    have hh := congrArg (fun f : MulAut (omegaGroup hQ) => f * α) hσ
    simpa [mul_assoc] using hh
  refine ⟨γ, ?_, ?_⟩
  ·
    have hcγ2 : cγ * cγ = 1 := by rw [hαeq]; exact hα
    have hfix : ∀ t : omegaGroup hQ, simAct Q (γ * γ) (t : OGroup Q) = (t : OGroup Q) := by
      intro t
      have hfix' : ((cγ (cγ t) : omegaGroup hQ) : OGroup Q) = (t : OGroup Q) := by
        have hh := congrArg (fun f : MulAut (omegaGroup hQ) => f t) hcγ2
        have hh' := congrArg (fun w : omegaGroup hQ => (w : OGroup Q)) hh
        simpa [MulAut.mul_apply, MulAut.one_apply] using hh'
      calc simAct Q (γ * γ) (t : OGroup Q)
          = ((simAct Q γ * simAct Q γ) (t : OGroup Q)) := by
            rw [show simAct Q (γ * γ) = simAct Q γ * simAct Q γ from map_mul (simAct Q) γ γ]
        _ = simAct Q γ (simAct Q γ (t : OGroup Q)) := by rw [MulAut.mul_apply]
        _ = ((cγ (cγ t) : omegaGroup hQ) : OGroup Q) := rfl
        _ = (t : OGroup Q) := hfix'
    have hff : ffSimOmegaAct hQ h2 (QuotientGroup.mk (γ * γ)) = 1 :=
      (ffSimOmegaAct_eq_one_iff hQ h2 (γ * γ)).mpr (fun t ht => Or.inl (hfix ⟨t, ht⟩))
    have hmk : QuotientGroup.mk (γ * γ) = (1 : ProjSim Q) :=
      ffSimOmegaAct_injective' hQ (by omega) h2 (by rw [hff, map_one])
    have hmem : γ * γ ∈ piSim Q :=
      (QuotientGroup.eq_one_iff (N := piSim Q) (γ * γ)).mp hmk
    rcases mem_piSim_iff.mp hmem with h1 | h1
    · left
      intro v
      calc (γ : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v)
          = ((γ : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V)) v := rfl
        _ = ((γ * γ : simGroup Q) : V ≃ₗ[ZMod 3] V) v := by rw [Subgroup.coe_mul]
        _ = ((1 : simGroup Q) : V ≃ₗ[ZMod 3] V) v := by rw [h1]
        _ = v := rfl
    · right
      intro v
      calc (γ : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v)
          = ((γ : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V)) v := rfl
        _ = ((γ * γ : simGroup Q) : V ≃ₗ[ZMod 3] V) v := by rw [Subgroup.coe_mul]
        _ = (orthToSim Q (piOrth Q) : V ≃ₗ[ZMod 3] V) v := by rw [h1]
        _ = (piOrth Q : V ≃ₗ[ZMod 3] V) v := rfl
        _ = -v := coe_piOrth_apply (Q := Q) v
  ·
    intro t
    rw [← hαeq]
    rfl

end CFSG.OddStandard.SmallF3.Omega
