module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepADefs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
  CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis (repA)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)

private def repAComp : Fin 3 → List (Fin Tag.E6.rank → ℤ) :=
  ![[![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
      ![0, 0, -1, 0, 0, 0], ![-1, 0, -1, 0, 0, 0]],
    [![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, -1, -1]],
    [![0, 1, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![1, 1, 2, 3, 2, 1], ![0, -1, 0, 0, 0, 0],
      ![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1]]]

private theorem repAComp_root : ∀ j, ∀ β ∈ repAComp j, β ∈ rootFinset Tag.E6 := by
  decide +kernel

private theorem repAComp_ker : ∀ β ∈ rootFinset Tag.E6,
    triPairing repA β = 0 ↔ ∃ j, β ∈ repAComp j := by
  decide +kernel

private theorem repAComp_ne_nil : ∀ j, repAComp j ≠ [] := by
  decide +kernel

private theorem repAComp_neg : ∀ j, ∀ β ∈ repAComp j, -β ∈ repAComp j := by
  decide +kernel

private theorem repAComp_orth : ∀ i j, i ≠ j → ∀ β ∈ repAComp i, ∀ γ ∈ repAComp j,
    β ≠ γ ∧ β ≠ -γ ∧ β + γ ∉ rootFinset Tag.E6 ∧ iform β γ = 0 := by
  decide +kernel

private theorem repAComp_clique : ∀ j, ∀ β ∈ repAComp j, ∀ γ ∈ repAComp j, iform β γ ≠ 0 := by
  decide +kernel

private theorem repAComp_reflect : ∀ i j, ∀ α ∈ repAComp i, ∀ γ ∈ repAComp j,
    γ - corootPair α γ • α ∈ repAComp j := by
  decide +kernel

private theorem repA_tuple_one : ∀ j, ∀ β ∈ repAComp j,
    e6Certificate.tupleVec [1, 5, 68, 64, 2, 0] β ∈ repAComp ((finRotate 3).symm j) := by
  decide +kernel

private theorem repA_tuple_two : ∀ j, ∀ β ∈ repAComp j,
    e6Certificate.tupleVec [5, 0, 4, 65, 68, 1] β ∈ repAComp (finRotate 3 j) := by
  decide +kernel

private theorem vec3_stab_repA : vec3 (τ := .E6) e6ThreeStab7.vec = repA := by
  decide +kernel

private theorem passing_stab_repA : e6ThreeStab7.passing e6Certificate =
    [[1, 5, 68, 64, 2, 0], [5, 0, 4, 65, 68, 1], List.range Tag.E6.rank] := by
  decide +kernel

set_option linter.unusedSectionVars false


private theorem isRoot_of_mem_repAComp {j : Fin 3} {β : Fin Tag.E6.rank → ℤ}
    (h : β ∈ repAComp j) : IsRoot Tag.E6 β :=
  mem_rootFinset.1 (repAComp_root j β h)

private theorem triPairing_repA_eq_zero_iff {β : Fin Tag.E6.rank → ℤ}
    (h : IsRoot Tag.E6 β) :
    triPairing repA β = 0 ↔ ∃ j, β ∈ repAComp j :=
  repAComp_ker β (mem_rootFinset.2 h)

private theorem kernelWeylGroup_repAComp {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar repA)) :
    ∀ j, ∀ β ∈ repAComp j, u • β ∈ repAComp j ∧ u⁻¹ • β ∈ repAComp j := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w₁, i, hα, rfl⟩ := hx
    rw [conj_simple_eq_rootReflection w₁ i, rootReflection_inv hα.1]
    obtain ⟨k, hk⟩ := (triPairing_repA_eq_zero_iff hα.1).1 (mem_kernelRoots_triChar.1 hα).2
    intro j β hβ
    rw [rootReflection_smul hα.1]
    exact ⟨repAComp_reflect k j _ hk β hβ, repAComp_reflect k j _ hk β hβ⟩
  | one =>
    intro j β hβ
    rw [inv_one, one_smul]
    exact ⟨hβ, hβ⟩
  | mul x y _ _ ihx ihy =>
    intro j β hβ
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact (ihx j _ (ihy j β hβ).1).1
    · rw [mul_inv_rev, mul_smul]
      exact (ihy j _ (ihx j β hβ).2).2
  | inv x _ ihx =>
    intro j β hβ
    rw [inv_inv]
    exact (ihx j β hβ).symm

private theorem repA_cyclic {w : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar repA)) (hsh : triPairing repA (e6Shift w) ≠ 0) :
    ∃ π : Equiv.Perm (Fin 3), π 0 ≠ 0 ∧ π (π 0) ≠ 0 ∧
      ∀ j, ∀ β ∈ repAComp j, w • β ∈ repAComp (π j) := by
  obtain ⟨u, hu, hωmem⟩ := exists_mul_mem_kernelPosStabilizer hw
  rw [← vec3_stab_repA] at hωmem
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check
    (e6ThreeScCheck_spec.2 e6ThreeStab7 (by simp [e6ThreeStabs])).1 hωmem
  rw [passing_stab_repA] at ht
  have hact : ∀ β, w • β = e6Certificate.tupleVec t (u⁻¹ • β) := fun β => by
    rw [RootCertificate.tupleVec_eq hrep, ← mul_smul, mul_inv_cancel_right]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨(finRotate 3).symm, by decide +kernel, by decide +kernel, fun j β hβ => ?_⟩
    rw [hact β]
    exact repA_tuple_one j _ (kernelWeylGroup_repAComp hu j β hβ).2
  · refine ⟨finRotate 3, by decide +kernel, by decide +kernel, fun j β hβ => ?_⟩
    rw [hact β]
    exact repA_tuple_two j _ (kernelWeylGroup_repAComp hu j β hβ).2
  · exfalso
    have h1 : w * u = 1 := RootCertificate.represents_unique hrep
      (RootCertificate.represents_one e6Certificate_check)
    rw [eq_inv_of_mul_eq_one_left h1] at hsh
    exact hsh (triPairing_e6Shift_of_mem_kernelWeylGroup (inv_mem hu))

theorem classA_components {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {w : WeylGroup Tag.E6} (h : HeisClassA a w) :
    ∃ (C : Fin 3 → Set (Fin Tag.E6.rank → ℤ)) (π : Equiv.Perm (Fin 3)),
      (∀ j, ∀ β ∈ C j, IsRoot Tag.E6 β) ∧
      (∀ j, ∀ β ∈ C j, -β ∈ C j) ∧
      (∀ β, β ∈ rootCharKernel a ↔ ∃ j, β ∈ C j) ∧
      (∀ i j, i ≠ j → ∀ β ∈ C i, ∀ γ ∈ C j, β ≠ γ ∧ β ≠ -γ ∧ ¬ IsRoot Tag.E6 (β + γ)) ∧
      (∀ j, ∀ β ∈ C j, ∀ γ ∈ C j, iform β γ ≠ 0) ∧
      (∀ j, (C j).Nonempty) ∧
      π 0 ≠ 0 ∧ π (π 0) ≠ 0 ∧
      (∀ j, ∀ β ∈ C j, w • β ∈ C (π j)) := by
  obtain ⟨b, t, hker, hpair, hwr, hsh⟩ := h
  obtain ⟨π, hπ0, hπ1, hπ⟩ := repA_cyclic hwr hsh
  have hb : ∀ β, triPairing b β = triPairing repA (t⁻¹ • β) := fun β => by
    rw [← hpair, smul_inv_smul]
  refine ⟨fun j => {β | t⁻¹ • β ∈ repAComp j}, π, ?_, ?_, ?_, ?_, ?_, ?_, hπ0, hπ1, ?_⟩
  · intro j β hβ
    have hβ' : t⁻¹ • β ∈ repAComp j := hβ
    exact (isRoot_smul_iff t⁻¹).1 (isRoot_of_mem_repAComp hβ')
  · intro j β hβ
    have hβ' : t⁻¹ • β ∈ repAComp j := hβ
    change t⁻¹ • -β ∈ repAComp j
    rw [smul_neg]
    exact repAComp_neg j _ hβ'
  · intro β
    rw [hker β, mem_kernelRoots_triChar, hb]
    constructor
    · rintro ⟨hr, h0⟩
      exact (triPairing_repA_eq_zero_iff (IsRoot.smul hr t⁻¹)).1 h0
    · rintro ⟨j, hj⟩
      have hj' : t⁻¹ • β ∈ repAComp j := hj
      have hr := isRoot_of_mem_repAComp hj'
      exact ⟨(isRoot_smul_iff t⁻¹).1 hr, (triPairing_repA_eq_zero_iff hr).2 ⟨j, hj'⟩⟩
  · intro i j hij β hβ γ hγ
    have hβ' : t⁻¹ • β ∈ repAComp i := hβ
    have hγ' : t⁻¹ • γ ∈ repAComp j := hγ
    obtain ⟨h1, h2, h3, -⟩ := repAComp_orth i j hij _ hβ' _ hγ'
    refine ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e, smul_neg]), fun hr => h3 ?_⟩
    rw [← smul_add]
    exact mem_rootFinset.2 (IsRoot.smul hr t⁻¹)
  · intro j β hβ γ hγ
    have hβ' : t⁻¹ • β ∈ repAComp j := hβ
    have hγ' : t⁻¹ • γ ∈ repAComp j := hγ
    rw [← iform_smul t⁻¹ β γ]
    exact repAComp_clique j _ hβ' _ hγ'
  · intro j
    obtain ⟨β, hβ⟩ := List.exists_mem_of_ne_nil _ (repAComp_ne_nil j)
    refine ⟨t • β, ?_⟩
    change t⁻¹ • t • β ∈ repAComp j
    rwa [inv_smul_smul]
  · intro j β hβ
    have hβ' : t⁻¹ • β ∈ repAComp j := hβ
    change t⁻¹ • w • β ∈ repAComp (π j)
    have e : t⁻¹ • w • β = (t⁻¹ * w * t) • t⁻¹ • β := by
      simp only [mul_smul, smul_inv_smul]
    rw [e]
    exact hπ j _ hβ'

end CFSG.LieType.SeitzGeneration.ExcWideThree
