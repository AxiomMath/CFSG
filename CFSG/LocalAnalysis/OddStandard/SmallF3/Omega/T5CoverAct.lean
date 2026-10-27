module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_eq_of_inv_mul_mem_center {P Q' : Type} [Group P] [Group Q']
    (hP : Group.IsPerfect P) (f g : P →* Q')
    (h : ∀ b, (f b)⁻¹ * g b ∈ Subgroup.center Q') : f = g := by
  haveI : Group.IsPerfect P := hP
  let k : P →* ↥(Subgroup.center Q') :=
  { toFun := fun b => ⟨(f b)⁻¹ * g b, h b⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun a b => Subtype.ext (by
      have hca : ((f a)⁻¹ * g a) ∈ Subgroup.center Q' := h a
      have hcomm : (f b)⁻¹ * ((f a)⁻¹ * g a) = ((f a)⁻¹ * g a) * (f b)⁻¹ :=
        Subgroup.mem_center_iff.mp hca (f b)⁻¹
      show (f (a * b))⁻¹ * g (a * b) = ((f a)⁻¹ * g a) * ((f b)⁻¹ * g b)
      calc (f (a * b))⁻¹ * g (a * b)
          = (f b)⁻¹ * ((f a)⁻¹ * g a) * g b := by
            rw [map_mul f, map_mul g, mul_inv_rev]; group
        _ = ((f a)⁻¹ * g a) * (f b)⁻¹ * g b := by rw [hcomm]
        _ = ((f a)⁻¹ * g a) * ((f b)⁻¹ * g b) := by group) }
  have hk1 : k = 1 := by
    refine MonoidHom.ext (fun b => ?_)
    have hle : commutator P ≤ k.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ c _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subtype.ext (Subgroup.mem_center_iff.mp (k a).2 (k c : Q')).symm)
    have hb : b ∈ commutator P := by
      rw [hP.commutator_eq_top]
      exact Subgroup.mem_top b
    exact MonoidHom.mem_ker.mp (hle hb)
  ext b
  have hb : k b = 1 := by rw [hk1]; rfl
  have hbval : (f b)⁻¹ * g b = 1 := by
    have h1 : ((k b : ↥(Subgroup.center Q')) : Q') = 1 := by rw [hb]; rfl
    change (f b)⁻¹ * g b = 1 at h1
    exact h1
  exact inv_mul_eq_one.mp hbval

@[expose] def CoverAct (L : Subgroup G) (φ : ↥L →* omegaGroup hQ) (s : G) (x : simGroup Q) : Prop :=
  s ∈ normalizer (L : Set G) ∧ ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
    ((φ l' : omegaGroup hQ) : OGroup Q) = simAct Q x ((φ l : omegaGroup hQ) : OGroup Q)

theorem t5_coverAct_of_inducesViaP (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (h : IsCoverMap L φ) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (he : ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φ l)) {s : G} {x : ProjSim Q}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e s x) {x' : simGroup Q}
    (hx' : (QuotientGroup.mk x' : ProjSim Q) = x) : CoverAct L φ s x' := by
  let ψ : ↥L →* ↥L :=
  { toFun := fun l => ⟨s * (l : G) * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx.1 (l : G)).mp l.2⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun a b => Subtype.ext (by
      change s * ((a : G) * (b : G)) * s⁻¹ =
        (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹)
      group) }
  have hψ : ∀ l : ↥L, ((ψ l : ↥L) : G) = s * (l : G) * s⁻¹ := fun l => rfl
  let A : ↥L →* OGroup Q :=
    ((simAct Q x').toMonoidHom).comp ((Subgroup.subtype (omegaGroup hQ)).comp φ)
  let B : ↥L →* OGroup Q :=
    ((Subgroup.subtype (omegaGroup hQ)).comp φ).comp ψ
  have hA : ∀ l : ↥L, A l = simAct Q x' ((φ l : omegaGroup hQ) : OGroup Q) := fun l => rfl
  have hB : ∀ l : ↥L, B l = ((φ (ψ l) : omegaGroup hQ) : OGroup Q) := fun l => rfl
  have hBA : ∀ l : ↥L, toProj Q (B l) = toProj Q (A l) := by
    intro l
    rw [hB, hA l]
    have h1 := hx.2 l (ψ l) (hψ l)
    simp only [he (ψ l), he l, coe_omegaToProj, ← hx', projSimAct_mk,
      projActAux_toProj] at h1
    exact h1
  have hcent : piGroup Q ≤ Subgroup.center (OGroup Q) :=
    Subgroup.zpowers_le.mpr piOrth_mem_center
  have hmem : ∀ l : ↥L, (A l)⁻¹ * B l ∈ Subgroup.center (OGroup Q) := by
    intro l
    apply hcent
    have h : toProj Q ((A l)⁻¹ * B l) = 1 := by
      rw [map_mul (toProj Q), map_inv (toProj Q), hBA l, inv_mul_cancel]
    have h' : (QuotientGroup.mk' (piGroup Q) ((A l)⁻¹ * B l) : ProjOrth Q) = 1 := h
    rw [QuotientGroup.mk'_apply] at h'
    exact (QuotientGroup.eq_one_iff _).mp h'
  have hAB : A = B := t5_eq_of_inv_mul_mem_center hL.1.1 A B hmem
  refine ⟨hx.1, fun l l' hl => ?_⟩
  have hψl : ψ l = l' := Subtype.ext ((hψ l).trans hl.symm)
  have hBval : B l = ((φ l' : omegaGroup hQ) : OGroup Q) := by rw [hB, hψl]
  have hEq : B l = A l := by rw [hAB]
  rw [hBval, hA l] at hEq
  exact hEq

theorem t5_exists_coverAct (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {s : G} (hs : s ∈ normalizer (L : Set G)) : ∃ x : simGroup Q, CoverAct L φ s x := by
  obtain ⟨e, he⟩ := t5_exists_model hL h
  obtain ⟨x, hx⟩ := ff_exists_induces hQ
    (Or.inr ⟨h.finrank_eq, Or.inr h.quadSign_eq⟩) e hs
  obtain ⟨x', hx'⟩ := QuotientGroup.mk_surjective x
  exact ⟨x', t5_coverAct_of_inducesViaP hL h he hx hx'⟩

theorem t5_cent_map_mem {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (hx : CoverAct L φ s x) {l : ↥L} (hl : s * (l : G) = (l : G) * s) :
    simAct Q x ((φ l : omegaGroup hQ) : OGroup Q) = ((φ l : omegaGroup hQ) : OGroup Q) := by
  let l' : ↥L := ⟨s * (l : G) * s⁻¹,
    (Subgroup.mem_normalizer_iff.mp hx.1 (l : G)).mp l.2⟩
  have hl' : (l' : G) = (l : G) := by
    show s * (l : G) * s⁻¹ = (l : G)
    rw [hl]
    group
  have h2 := hx.2 l l' rfl
  have h3 : l' = l := Subtype.ext hl'
  rw [h3] at h2
  exact h2.symm

theorem t5_cent_exists (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ) {s : G}
    {x : simGroup Q} (hx : CoverAct L φ s x) (hs2 : s * s = 1) {g : OGroup Q}
    (hg : g ∈ omegaGroup hQ ⊓ fixSub (simAct Q x)) :
    ∃ l : ↥L, s * (l : G) = (l : G) * s ∧ ((φ l : omegaGroup hQ) : OGroup Q) = g := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [h.finrank_eq]; norm_num
  let σ : MulAut ↥L := conjAut L hs2 hx.1
  let α : MulAut (omegaGroup hQ) :=
  { toFun := fun w => ⟨simAct Q x (w : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 x w.2⟩
    invFun := fun w => ⟨simAct Q x⁻¹ (w : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 x⁻¹ w.2⟩
    left_inv := fun w => by
      apply Subtype.ext
      change simAct Q x⁻¹ (simAct Q x (w : OGroup Q)) = (w : OGroup Q)
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    right_inv := fun w => by
      apply Subtype.ext
      change simAct Q x (simAct Q x⁻¹ (w : OGroup Q)) = (w : OGroup Q)
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    map_mul' := fun a b => by
      apply Subtype.ext
      change simAct Q x ((a : OGroup Q) * (b : OGroup Q)) =
        simAct Q x (a : OGroup Q) * simAct Q x (b : OGroup Q)
      exact map_mul (simAct Q x) (a : OGroup Q) (b : OGroup Q) }
  have hφσ : ∀ l : ↥L, φ (σ l) = α (φ l) := by
    intro l
    apply Subtype.ext
    change ((φ (σ l) : omegaGroup hQ) : OGroup Q) =
      simAct Q x ((φ l : omegaGroup hQ) : OGroup Q)
    exact hx.2 l (σ l) (coe_conjAut L hs2 hx.1 l)
  have hσ : σ * σ = 1 := conjAut_mul_self L hs2 hx.1
  have hc : α ⟨g, hg.1⟩ = ⟨g, hg.1⟩ := by
    apply Subtype.ext
    change simAct Q x g = g
    exact mem_fixSub_iff.mp hg.2
  let c : ↥(fixSub α) := ⟨⟨g, hg.1⟩, mem_fixSub_iff.mpr hc⟩
  obtain ⟨p, hp⟩ := (h.oddCentralCover hL).fixHom_surjective hσ hφσ c
  refine ⟨(p : ↥L), ?_, ?_⟩
  · have hpfix : σ (p : ↥L) = (p : ↥L) := mem_fixSub_iff.mp p.2
    have hpval : s * ((p : ↥L) : G) * s⁻¹ = ((p : ↥L) : G) := by
      have h := congrArg (fun q : ↥L => (q : G)) hpfix
      rw [coe_conjAut L hs2 hx.1] at h
      exact h
    exact mul_inv_eq_iff_eq_mul.mp hpval
  · have h1 : ((fixHom φ σ α hφσ p : ↥(fixSub α)) : omegaGroup hQ) = (c : omegaGroup hQ) :=
      congrArg (fun q : ↥(fixSub α) => (q : omegaGroup hQ)) hp
    rw [coe_fixHom] at h1
    exact congrArg (fun q : omegaGroup hQ => (q : OGroup Q)) h1

end CFSG.OddStandard.SmallF3.Omega
