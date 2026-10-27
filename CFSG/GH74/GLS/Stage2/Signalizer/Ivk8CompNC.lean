module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools

namespace CompNC

theorem exists_sylow_of_isSylowOf_top {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    {P : Subgroup A} (h : IsSylowOf p P ⊤) : ∃ Q : Sylow p A, (Q : Subgroup A) = P := by
  rw [isSylowOf_iff] at h
  obtain ⟨-, hP, hdvd⟩ := h
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, IsPGroup.toSylow_coe hP hdvd⟩

end CompNC

theorem AFrame.exists_comp_nc {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) :
    ∃ J : Subgroup A, IsComponent J ∧ ¬ Vb ≤ centralizer (J : Set A) := by
  by_contra hcon
  push Not at hcon
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdisj : Disjoint Vb (pCore 2 A) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) Vb (pCore 2 A) hfr.v3 pCore_isPGroup
  have hE : layer A ≤ centralizer (Vb : Set A) := by
    refine sSup_le fun K hK => ?_
    exact Subgroup.le_centralizer_iff.mp (hcon K hK)
  have hle : pCore 2 A ≤ Sb := by
    obtain ⟨Q, hQ⟩ := CompNC.exists_sylow_of_isSylowOf_top hfr.sylow
    rw [← hQ]
    exact IsPGroup.le_sylow_of_normal pCore_isPGroup Q
  have hO : pCore 2 A ≤ centralizer (Vb : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : x * v⁻¹ * x⁻¹ ∈ Vb :=
      (mem_normalizer_iff.mp (hfr.v_norm (hle hx)) v⁻¹).mp (Vb.inv_mem hv)
    have h2' : v * x * v⁻¹ ∈ pCore 2 A := (pCore_normal (p := 2) (G := A)).conj_mem x hx v
    have hc : v * x * v⁻¹ * x⁻¹ ∈ Vb ⊓ pCore 2 A := by
      refine ⟨?_, ?_⟩
      · have := Vb.mul_mem hv h1
        simpa [mul_assoc] using this
      · exact (pCore 2 A).mul_mem h2' ((pCore 2 A).inv_mem hx)
    have hc1 : v * x * v⁻¹ * x⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj hc.1 hc.2
    calc v * x = (v * x * v⁻¹ * x⁻¹) * x * v := by group
      _ = x * v := by rw [hc1]; group
  have hFs : generalizedFitting A ≤ centralizer (Vb : Set A) := by
    rw [generalizedFitting, Fitting_eq_pcore A 2 hfr.core]
    exact sup_le hO hE
  have hVF : Vb ≤ centralizer (generalizedFitting A : Set A) :=
    Subgroup.le_centralizer_iff.mpr hFs
  have hVF' : Vb ≤ generalizedFitting A := hVF.trans (centralizer_generalizedFitting_le A)
  have hFn : (generalizedFitting A).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  let Z : Subgroup A := generalizedFitting A ⊓ centralizer (generalizedFitting A : Set A)
  have : Z.Normal := Subgroup.normal_inf_normal _ _
  have : IsMulCommutative Z :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp b.2.2) (a : A) a.2.1)⟩⟩
  have hZF : Z ≤ fittingSubgroup A :=
    CFSG.LocalCores.fitting_characteristic.2.2 Z inferInstance inferInstance
  have hVZ : Vb ≤ Z := le_inf hVF' hVF
  have hV2 : Vb ≤ pCore 2 A := by
    have := hVZ.trans hZF
    rwa [Fitting_eq_pcore A 2 hfr.core] at this
  exact hfr.v_ne (hdisj.eq_bot_of_le hV2)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
