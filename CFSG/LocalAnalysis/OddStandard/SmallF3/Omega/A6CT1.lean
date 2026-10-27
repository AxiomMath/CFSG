module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CKlein
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CRed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CXFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CElt
public import Certificates.Data.A6CMat6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem a6c_a0M6_toMat :
    A6CToMat 6 (Certificates.A6C.a0M6 ()) =
      Matrix.diagonal fun i : Fin 6 =>
        if i ∈ ({0, 1} : Finset (Fin 6)) then (-1 : ZMod 3) else 1 := by
  decide +kernel

theorem a6c_diag_sim :
    A6CSimMat (Matrix.diagonal fun i : Fin 6 =>
      if i ∈ ({0, 1} : Finset (Fin 6)) then (-1 : ZMod 3) else 1) :=
  Or.inl (by decide +kernel)

theorem a6c_a0M6_ne_one {Γ : Type} [Group Γ] (m : A6CModel 6 Γ) :
    A6CElt m (Certificates.A6C.a0M6 ()) ≠ 1 := by
  intro h
  rw [A6CElt, a6c_a0M6_toMat, ← m.ofMat_one] at h
  rcases (m.ofMat_eq _ _ a6c_diag_sim A6CSimMat.one).mp h with h1 | h1
  · have h2 := congrFun (congrFun h1 0) 0
    revert h2
    decide +kernel
  · have h2 := congrFun (congrFun h1 2) 2
    revert h2
    decide +kernel

@[expose] def A6C6Facts : Prop :=
  ∀ {Γ : Type} [Group Γ] (m : A6CModel 6 Γ), Nat.card Γ = 26127360 →
    A6CPairFacts Γ (fun a => IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a) 40 4

theorem a6c_autCentChain3_of_facts (hF : A6C6Facts) : Asc82AutCentChain3 := by
  intro G _ _ X Z Y hX _ hY hXL _ hY6 hXZ hZY R hR2 hR
  have hXY : X ≤ Y := hXZ.trans hZY
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus (L := Y) ⟨hY, hY6⟩
  have hsh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  obtain ⟨φ, ψ, hker, hmem, hcomm, hψ⟩ := a6c_theta_homs hQ hsh hY.1.commutator_eq_top e hXY
    (fun r hr => (hR hr).1) (fun r hr => (hR hr).2)
  obtain ⟨⟨eA⟩, hodd⟩ := a6c_X_facts hX hXL
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨m, hm⟩ := a6c_model_of_frame fr one_ne_zero
  have hcard : Nat.card (ProjSim Q) = 26127360 := ff_natCard_projSim_six_minus hQ hdim hsgn
  haveI : Finite (ProjSim Q) := Nat.finite_of_card_ne_zero (by omega)
  have hΓ : ¬ 25 ∣ Nat.card (ProjSim Q) := by rw [hcard]; norm_num
  have hJ : Even ({0, 1} : Finset (Fin 6)).card := by decide
  let u0 : ↥(omegaProj hQ) :=
    omegaToProj hQ ⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩
  have hu0img : projOrthToProjSim Q (u0 : ProjOrth Q) = A6CElt m (Certificates.A6C.a0M6 ()) := by
    show QuotientGroup.mk (orthToSim Q (fr.signChange {0, 1})) = _
    rw [← hm {0, 1}, A6CElt, a6c_a0M6_toMat]
  have hu0sq : u0 * u0 = 1 := by
    rw [← map_mul]
    have : (⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩ *
        ⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩ : omegaGroup hQ) = 1 :=
      Subtype.ext (fr.signChange_mul_self {0, 1})
    rw [this, map_one]
  have hu01 : u0 ≠ 1 := by
    intro h
    apply a6c_a0M6_ne_one m
    rw [← hu0img, h]
    exact map_one _
  have hA : ∀ a ∈ φ.range, a * a = 1 → a ≠ 1 → IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a := by
    rintro a ⟨x, rfl⟩ haa ha1
    obtain ⟨u, hu⟩ := hmem x
    rw [hu] at haa ha1 ⊢
    have hu2 : u * u = 1 := by
      refine Subtype.ext (projOrthToProjSim_injective (Q := Q) ?_)
      show projOrthToProjSim Q ((u : ProjOrth Q) * (u : ProjOrth Q)) = projOrthToProjSim Q 1
      rw [map_mul, map_one]
      exact haa
    have hu1 : u ≠ 1 := fun h => ha1 (by rw [h]; exact map_one _)
    obtain ⟨b, hb⟩ := ff6m_conj_involutions hQ hdim hsgn hu0sq hu2 hu01 hu1
    refine isConj_iff.mpr ⟨projOrthToProjSim Q (b : ProjOrth Q), ?_⟩
    have hb' := congrArg (fun w : ↥(omegaProj hQ) => projOrthToProjSim Q (w : ProjOrth Q)) hb
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu0img] at hb'
    exact hb'
  obtain ⟨hle, hexp⟩ := a6c_red (P := fun a => IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a)
    (kc := 40) (bound := 4) (fun a δ ha => ha.trans (isConj_iff.mpr ⟨δ, rfl⟩)) hΓ (by norm_num)
    (hF m hcard) φ ψ eA hodd hker hA hcomm
  exact a6c_relIndex_or_klein R (centralizer (Y : Set G)) ψ hR2 hψ hle hexp

end CFSG.OddStandard.SmallF3.Omega
