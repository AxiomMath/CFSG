module

public import CFSG.GH74.QTGen4.U42.ModelFrameC

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

section Model


abbrev sigma0 : Equiv.Perm (Fin 5) := Equiv.swap 0 4

@[expose] noncomputable def permOf4 (g : ↥P2) : Equiv.Perm (Fin 5) := sigma0 * permOf g * sigma0⁻¹

theorem permOf4_apply (g : ↥P2) : permOf4 g = sigma0 * permOf g * sigma0⁻¹ := rfl

@[expose] noncomputable def permHom4 : ↥P2 →* Equiv.Perm (Fin 5) :=
  (MulAut.conj sigma0).toMonoidHom.comp permHom

theorem permHom4_apply (g : ↥P2) : permHom4 g = permOf4 g := rfl

theorem pact_conj (σ p : Equiv.Perm (Fin 5)) (x : W5) :
    pact (σ * p * σ⁻¹) (pact σ x) = pact σ (pact p x) := by
  have hinv : pact σ⁻¹ (pact σ x) = x := by
    have h1 : pact σ⁻¹ * pact σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact (congrArg (fun f : MulAut W5 => f x) h1).trans rfl
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hinv]

theorem vsub_subgroupOf_normal : (Vsub.subgroupOf P2).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using P2_conj_V g.2 hn

theorem permOf4_eq_one_iff (g : ↥P2) : permOf4 g = 1 ↔ permOf g = 1 := by
  have key : ∀ x : Equiv.Perm (Fin 5), sigma0 * x * sigma0⁻¹ = 1 ↔ x = 1 := by
    intro x
    constructor
    · intro h
      have hx : x = sigma0⁻¹ * (sigma0 * x * sigma0⁻¹) * sigma0 := by group
      rw [hx, h]
      simp
    · intro h
      rw [h]
      simp
  exact key (permOf g)

@[expose] noncomputable def modelCoordData : CoordData ↥P2 where
  V := Vsub.subgroupOf P2
  hV := vsub_subgroupOf_normal
  ψ := (Subgroup.subgroupOfEquivOfLe Vsub_le_P2).trans (psiEq.trans (pact sigma0))
  ρ := permHom4
  ker_ρ := by
    ext g
    rw [MonoidHom.mem_ker, permHom4_apply, permOf4_eq_one_iff, permOf_eq_one_iff,
      Subgroup.mem_subgroupOf]
  conj_ψ := by
    intro m v
    have hv : (v : Y) ∈ Vsub := Subgroup.mem_subgroupOf.1 v.2
    have hc : (m : Y) * (v : Y) * (m : Y)⁻¹ ∈ Vsub := P2_conj_V m.2 hv
    let w : Vsub := ⟨(v : Y), hv⟩
    have e : (⟨(m : Y) * (v : Y) * (m : Y)⁻¹, hc⟩ : Vsub) =
        conjAct Vsub ⟨(m : Y), hN_le m.2⟩ w :=
      Subtype.ext ((conjAct_val ⟨(m : Y), hN_le m.2⟩ w).symm)
    have hpsi : psiEq (⟨(m : Y) * (v : Y) * (m : Y)⁻¹, hc⟩ : Vsub) =
        pact (permOf m) (psiEq w) :=
      calc psiEq (⟨(m : Y) * (v : Y) * (m : Y)⁻¹, hc⟩ : Vsub)
          = psiEq (conjAct Vsub ⟨(m : Y), hN_le m.2⟩ w) := congrArg psiEq e
        _ = psiM (conjAct Vsub ⟨(m : Y), hN_le m.2⟩ w) := psiEq_apply _
        _ = pact (permOf m) (psiM w) := psiM_conj m w
        _ = pact (permOf m) (psiEq w) := by rw [psiEq_apply]
    show pact sigma0 (psiEq (⟨(m : Y) * (v : Y) * (m : Y)⁻¹, hc⟩ : Vsub)) =
      pact (permHom4 m) (pact sigma0 (psiEq w))
    rw [hpsi, permHom4_apply, permOf4_apply]
    exact (pact_conj sigma0 (permOf m) (psiEq w)).symm

end Model

end CFSG.GH74.QTGen4.U42
