module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab

public section

namespace CFSG.LieType.Chevalley.E6CubicPointwiseStabilizer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.Blueprint.Chevalley.RootCertificate
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

theorem passing_eq_identity_of_fix : ∀ r < e6ThreeStabs.length,
    ∀ t ∈ (e6ThreeStabs.getD r e6ThreeStab0).passing e6Certificate,
      (∀ k < e6Certificate.roots.length,
        triPairing (vec3 (τ := .E6) (e6ThreeReps.getD r [])) (e6Certificate.root k) = 0 →
          e6Certificate.tupleVec t (e6Certificate.root k) = e6Certificate.root k) →
      t = List.range Tag.E6.rank := by
  decide +kernel



theorem eq_one_of_mem_charStabilizer_of_fix_kernelRoots
    (b : Fin Tag.E6.rank → ZMod 3) {w : WeylGroup .E6}
    (hw : w ∈ charStabilizer (triChar b))
    (hfix : ∀ beta ∈ kernelRoots (triChar b), w • beta = beta) : w = 1 := by
  obtain ⟨horbit, hstab⟩ := e6ThreeScCheck_spec
  have hvec := e6ThreeStabs_vec
  obtain ⟨r, hr, v, hv⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  have hlen : r < e6ThreeStabs.length := by
    rw [← List.length_map StabCert3.vec, hvec]
    exact hr
  set S := e6ThreeStabs[r] with hS
  have hSv : S.vec = e6ThreeReps.getD r [] := by
    rw [List.getD_eq_getElem _ _ hr, hS]
    have h := congrArg (fun l => l[r]?) hvec
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hr,
      Option.map_some, Option.some.injEq] at h
    exact h
  obtain ⟨hSc, _⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at hv
  have hwr : v⁻¹ * w * v ∈ charStabilizer (triChar (vec3 (τ := .E6) S.vec)) :=
    (charStabilizer_iff_of_isCharConj hv).mp hw
  have hfixr : ∀ beta ∈ kernelRoots (triChar (vec3 (τ := .E6) S.vec)),
      (v⁻¹ * w * v) • beta = beta := by
    intro beta hb
    have hbr : v • beta ∈ kernelRoots (triChar b) := by
      refine ⟨IsRoot.smul hb.1 v, ?_⟩
      rw [hv (v • beta), inv_smul_smul]
      exact hb.2
    rw [mul_smul, mul_smul, hfix _ hbr, inv_smul_smul]
  have hpos : v⁻¹ * w * v ∈ kernelPosStabilizer (triChar (vec3 (τ := .E6) S.vec)) := by
    refine ⟨hwr, ?_⟩
    calc (fun beta => (v⁻¹ * w * v) • beta) ''
          posRoots (kernelRoots (triChar (vec3 (τ := .E6) S.vec))) =
          id '' posRoots (kernelRoots (triChar (vec3 (τ := .E6) S.vec))) :=
        Set.image_congr fun beta hb => hfixr beta hb.1
      _ = _ := Set.image_id _
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hSc hpos
  have htOne : t = List.range Tag.E6.rank := by
    apply passing_eq_identity_of_fix r hlen t
    · rw [List.getD_eq_getElem _ _ hlen]
      exact ht
    · intro k hk hker
      rw [tupleVec_eq hrep]
      apply hfixr
      refine ⟨e6Certificate.isRoot_root e6Certificate_check k hk, ?_⟩
      rw [triChar_apply, hSv, hker]
      rfl
  have hOne : v⁻¹ * w * v = 1 := by
    rw [htOne] at hrep
    exact represents_unique hrep (represents_one e6Certificate_check)
  calc w = v * (v⁻¹ * w * v) * v⁻¹ := by group
    _ = 1 := by rw [hOne]; group

theorem eq_one_of_mem_rootCharStabilizer_of_fix_kernelRoots
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) (ha : ∀ i, a i ^ 3 = 1)
    {w : WeylGroup .E6} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ beta ∈ kernelRoots (rootCharHom a), w • beta = beta) : w = 1 := by
  obtain ⟨chi', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun _ => Iff.rfl
  obtain ⟨b, rfl⟩ : ∃ b, chi' = triChar b := ⟨_, eq_triChar chi'⟩
  have hroots : kernelRoots (rootCharHom3 a) = kernelRoots (triChar b) :=
    kernelRoots_congr_ker hker
  apply eq_one_of_mem_charStabilizer_of_fix_kernelRoots b
  · rw [← charStabilizer_congr_ker hker, ← hS]
    exact hw
  · intro beta hb
    apply hfix beta
    change beta ∈ kernelRoots (rootCharHom3 a)
    rw [hroots]
    exact hb

end CFSG.LieType.Chevalley.E6CubicPointwiseStabilizer
