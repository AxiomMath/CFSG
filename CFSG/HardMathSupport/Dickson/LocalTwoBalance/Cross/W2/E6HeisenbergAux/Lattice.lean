module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Reps

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley.RootCertificate


private def rootComb (l : List (ℕ × ℤ)) : Fin Tag.E6.rank → ℤ :=
  (l.map fun p => p.2 • e6Certificate.root p.1).sum

section Psi

variable {G : Type*} [CommGroup G] (ψ : Multiplicative (Fin Tag.E6.rank → ℤ) →* G)

private theorem map_rootComb {b : Fin Tag.E6.rank → ZMod 3}
    (hker : ∀ β ∈ kernelRoots (triChar b), ψ (Multiplicative.ofAdd β) = 1) :
    ∀ l : List (ℕ × ℤ), (∀ p ∈ l, p.1 < e6Certificate.roots.length ∧
      triPairing b (e6Certificate.root p.1) = 0) → ψ (Multiplicative.ofAdd (rootComb l)) = 1
  | [], _ => by simp [rootComb]
  | p :: l, hl => by
    have hp := hl p List.mem_cons_self
    have hβ : e6Certificate.root p.1 ∈ kernelRoots (triChar b) :=
      mem_kernelRoots_triChar.2 ⟨isRoot_root e6Certificate_check _ hp.1, hp.2⟩
    have ih := map_rootComb hker l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [rootComb] at ih ⊢
    rw [List.map_cons, List.sum_cons, ofAdd_add, map_mul, ofAdd_zsmul, map_zpow, hker _ hβ,
      one_zpow, one_mul, ih]

private theorem map_eq_one_of_rootComb {b : Fin Tag.E6.rank → ZMod 3}
    (hker : ∀ β ∈ kernelRoots (triChar b), ψ (Multiplicative.ofAdd β) = 1)
    {ω : WeylGroup Tag.E6}
    (hω : ∀ v, ψ (Multiplicative.ofAdd (ω • v)) = ψ (Multiplicative.ofAdd v))
    {t : List ℕ} (hrep : e6Certificate.Represents t ω) {l : List (ℕ × ℤ)}
    (hl : ∀ p ∈ l, p.1 < e6Certificate.roots.length ∧ triPairing b (e6Certificate.root p.1) = 0)
    {c x : Fin Tag.E6.rank → ℤ} (hx : x = rootComb l + (e6Certificate.tupleVec t c - c)) :
    ψ (Multiplicative.ofAdd x) = 1 := by
  rw [hx, ofAdd_add, map_mul, map_rootComb ψ hker l hl, tupleVec_eq hrep, ofAdd_sub, map_div, hω,
    div_self', mul_one]

private theorem pow_three_eq_one_of_single
    (h : ∀ j : Fin Tag.E6.rank,
      ψ (Multiplicative.ofAdd ((3 : ℕ) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) = 1)
    (v : Fin Tag.E6.rank → ℤ) : ψ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  have key : (powMonoidHom 3).comp ψ = 1 := lattice_hom_ext fun j => by
    rw [MonoidHom.comp_apply, powMonoidHom_apply, MonoidHom.one_apply, ← map_pow, ← ofAdd_nsmul]
    exact h j
  have := DFunLike.congr_fun key (Multiplicative.ofAdd v)
  rwa [MonoidHom.comp_apply, powMonoidHom_apply, MonoidHom.one_apply] at this

private theorem kernelWeylGroup_le_charStabilizer {b : Fin Tag.E6.rank → ZMod 3}
    (hker : ∀ β ∈ kernelRoots (triChar b), ψ (Multiplicative.ofAdd β) = 1) :
    kernelWeylGroup (triChar b) ≤ charStabilizer ψ := by
  refine le_trans (Subgroup.closure_mono ?_) kernelWeylGroup_le
  rintro _ ⟨w, i, hα, rfl⟩
  exact ⟨w, i, ⟨hα.1, hker _ hα⟩, rfl⟩

end Psi

private def latA : Fin Tag.E6.rank → List (ℕ × ℤ) :=
  ![[(0, 3)], [(1, 3)], [(2, 3)], [(0, -1), (1, -1), (2, -2), (4, -2), (5, -1), (68, 1)],
    [(4, 3)], [(5, 3)]]

private theorem latA_spec : ∀ j : Fin Tag.E6.rank,
    (∀ p ∈ latA j, p.1 < e6Certificate.roots.length ∧
      triPairing repA (e6Certificate.root p.1) = 0) ∧
    (3 : ℕ) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = rootComb (latA j) := by
  decide +kernel

private theorem lattice_cube_repA {G : Type*} [CommGroup G]
    (ψ : Multiplicative (Fin Tag.E6.rank → ℤ) →* G)
    (hker : ∀ β ∈ kernelRoots (triChar repA), ψ (Multiplicative.ofAdd β) = 1)
    (v : Fin Tag.E6.rank → ℤ) : ψ (Multiplicative.ofAdd v) ^ 3 = 1 :=
  pow_three_eq_one_of_single ψ (fun j => by
    rw [(latA_spec j).2]
    exact map_rootComb ψ hker _ (latA_spec j).1) v

private theorem vec3_e6ThreeStab6 : vec3 (τ := .E6) e6ThreeStab6.vec = repD := by
  decide +kernel

private theorem passing_e6ThreeStab6 : e6ThreeStab6.passing e6Certificate =
    [[33, 35, 71, 28, 4, 3], List.range Tag.E6.rank, [68, 51, 47, 5, 4, 28]] := by
  decide +kernel

private def latD₁ : Fin Tag.E6.rank → List (ℕ × ℤ) × (Fin Tag.E6.rank → ℤ) :=
  ![([(4, 3), (28, 6)], ![1, 2, 3, 1, 0, 0]),
    ([], ![1, -1, 0, 1, 0, 0]),
    ([(4, -3), (28, -6)], ![-2, -1, -3, 1, 0, 0]),
    ([(3, 3)], ![0, 0, 0, 0, 0, 0]),
    ([(4, 3)], ![0, 0, 0, 0, 0, 0]),
    ([(5, 3)], ![0, 0, 0, 0, 0, 0])]

private def latD₂ : Fin Tag.E6.rank → List (ℕ × ℤ) × (Fin Tag.E6.rank → ℤ) :=
  ![([(3, 6), (4, 3)], ![0, 2, 1, 7, 0, 4]),
    ([], ![0, -1, 1, 1, 0, 1]),
    ([(3, -6), (4, -3)], ![0, -1, -2, -5, 0, -2]),
    ([(3, 3)], ![0, 0, 0, 0, 0, 0]),
    ([(4, 3)], ![0, 0, 0, 0, 0, 0]),
    ([(5, 3)], ![0, 0, 0, 0, 0, 0])]

private theorem latD₁_spec : ∀ j : Fin Tag.E6.rank,
    (∀ p ∈ (latD₁ j).1, p.1 < e6Certificate.roots.length ∧
      triPairing repD (e6Certificate.root p.1) = 0) ∧
    (3 : ℕ) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = rootComb (latD₁ j).1 +
      (e6Certificate.tupleVec [33, 35, 71, 28, 4, 3] (latD₁ j).2 - (latD₁ j).2) := by
  decide +kernel

private theorem latD₂_spec : ∀ j : Fin Tag.E6.rank,
    (∀ p ∈ (latD₂ j).1, p.1 < e6Certificate.roots.length ∧
      triPairing repD (e6Certificate.root p.1) = 0) ∧
    (3 : ℕ) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = rootComb (latD₂ j).1 +
      (e6Certificate.tupleVec [68, 51, 47, 5, 4, 28] (latD₂ j).2 - (latD₂ j).2) := by
  decide +kernel

private theorem lattice_cube_repD {G : Type*} [CommGroup G]
    (ψ : Multiplicative (Fin Tag.E6.rank → ℤ) →* G)
    {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar repD))
    (hsh : triPairing repD (e6Shift w) ≠ 0)
    (hker : ∀ β ∈ kernelRoots (triChar repD), ψ (Multiplicative.ofAdd β) = 1)
    (hψ : ∀ v, ψ (Multiplicative.ofAdd (w • v)) = ψ (Multiplicative.ofAdd v))
    (v : Fin Tag.E6.rank → ℤ) : ψ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  obtain ⟨u, hu, hωmem⟩ := exists_mul_mem_kernelPosStabilizer hw
  have hωψ : ∀ v, ψ (Multiplicative.ofAdd ((w * u) • v)) = ψ (Multiplicative.ofAdd v) :=
    fun v => by rw [mul_smul, hψ, kernelWeylGroup_le_charStabilizer ψ hker hu v]
  have hωsh : triPairing repD (e6Shift (w * u)) ≠ 0 := by
    rwa [triPairing_e6Shift_mul hw, triPairing_e6Shift_of_mem_kernelWeylGroup hu, zero_add]
  rw [← vec3_e6ThreeStab6] at hωmem
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check
    (e6ThreeScCheck_spec.2 e6ThreeStab6 (by simp [e6ThreeStabs])).1 hωmem
  rw [passing_e6ThreeStab6] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  refine pow_three_eq_one_of_single ψ (fun j => ?_) v
  rcases ht with rfl | rfl | rfl
  · exact map_eq_one_of_rootComb ψ hker hωψ hrep (latD₁_spec j).1 (latD₁_spec j).2
  · refine absurd ?_ hωsh
    rw [represents_unique hrep (represents_one e6Certificate_check), e6Shift_one, triPairing_zero]
  · exact map_eq_one_of_rootComb ψ hker hωψ hrep (latD₂_spec j).1 (latD₂_spec j).2

theorem lattice_cube_rep {G : Type*} [CommGroup G]
    (ψ : Multiplicative (Fin Tag.E6.rank → ℤ) →* G) {b : Fin Tag.E6.rank → ZMod 3}
    (hb : b = repD ∨ b = repA)
    {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0)
    (hker : ∀ β ∈ kernelRoots (triChar b), ψ (Multiplicative.ofAdd β) = 1)
    (hψ : ∀ v, ψ (Multiplicative.ofAdd (w • v)) = ψ (Multiplicative.ofAdd v))
    (v : Fin Tag.E6.rank → ℤ) : ψ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  rcases hb with rfl | rfl
  · exact lattice_cube_repD ψ hw hsh hker hψ v
  · exact lattice_cube_repA ψ hker v

theorem lattice_cube {G : Type*} [CommGroup G]
    (ψ : Multiplicative (Fin Tag.E6.rank → ℤ) →* G) (b : Fin Tag.E6.rank → ZMod 3)
    {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0)
    (hker : ∀ β ∈ kernelRoots (triChar b), ψ (Multiplicative.ofAdd β) = 1)
    (hψ : ∀ v, ψ (Multiplicative.ofAdd (w • v)) = ψ (Multiplicative.ofAdd v))
    (v : Fin Tag.E6.rank → ℤ) : ψ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  obtain ⟨t, b', hb', hpair, hw', hsh'⟩ := exists_rep b hw hsh
  have hker' : ∀ β ∈ kernelRoots (triChar b'), charComp ψ t (Multiplicative.ofAdd β) = 1 := by
    intro β hβ
    obtain ⟨hr, h0⟩ := mem_kernelRoots_triChar.1 hβ
    rw [charComp_apply]
    exact hker _ (mem_kernelRoots_triChar.2 ⟨IsRoot.smul hr t, (hpair β).trans h0⟩)
  have hψ' : ∀ v, charComp ψ t (Multiplicative.ofAdd ((t⁻¹ * w * t) • v)) =
      charComp ψ t (Multiplicative.ofAdd v) := fun v => by
    rw [charComp_apply, charComp_apply, mul_smul, mul_smul, smul_inv_smul, hψ]
  have h := lattice_cube_rep (charComp ψ t) hb' hw' hsh' hker' hψ' (t⁻¹ • v)
  rwa [charComp_apply, smul_inv_smul] at h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
