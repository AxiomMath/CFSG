module

public import CFSG.LieType.Chevalley.FoldedRootOrbits

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

abbrev E6Vec : Type :=
  Fin TwistTag.E6.tag.rank → ℤ

@[expose] def orbits : Set (Finset E6Vec) :=
  {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
    (O.card = 2 ∨ (O.card = 1 ∧ ∀ α ∈ O, Even (α ⟨1, by decide⟩)))}

@[expose] def orbitVec (O : Finset E6Vec) : E6Vec :=
  (2 / O.card) • ∑ α ∈ O, α

@[expose] def vecs : Set E6Vec :=
  orbitVec '' orbits

@[expose] def posVecs : Set E6Vec :=
  {v | v ∈ vecs ∧ 0 < height v}

@[expose] def simpleVec : Fin 4 → E6Vec :=
  ![![0, 2, 1, 2, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 0], ![0, 0, 0, 2, 0, 0]]

@[expose] def simpleRoot : Fin 4 → E6Vec :=
  ![![0, 1, 1, 1, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]

@[expose] def simpleOrbit (i : Fin 4) : Finset E6Vec :=
  TwistTag.E6.diagramOrbit (simpleRoot i)

@[expose] def rho (v : E6Vec) : E6Vec :=
  permLattice TwistTag.E6.perm v

@[expose] def keep (α : E6Vec) : Bool :=
  !decide (rho α = α) || decide (Even (α ⟨1, by decide⟩))

@[expose] def vecOf (α : E6Vec) : E6Vec :=
  if rho α = α then 2 • α else α + rho α

theorem perm_symm_symm (j : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm (TwistTag.E6.perm.symm j) = j := by
  revert j
  decide

theorem rho_rho (v : E6Vec) : rho (rho v) = v := by
  funext j
  simp only [rho, permLattice, Function.comp_apply]
  rw [perm_symm_symm]

theorem rho_apply_one (v : E6Vec) : rho v ⟨1, by decide⟩ = v ⟨1, by decide⟩ := by
  simp only [rho, permLattice, Function.comp_apply]
  rfl

theorem diagramOrbit_eq (α : E6Vec) :
    TwistTag.E6.diagramOrbit α = {α, rho α} := by
  have h2 : Finset.range TwistTag.E6.order = {0, 1} := by decide
  rw [TwistTag.diagramOrbit, h2, Finset.image_insert, Finset.image_singleton, pow_zero, pow_one]
  congr 1

theorem card_pair_rho (α : E6Vec) :
    ({α, rho α} : Finset E6Vec).card = if rho α = α then 1 else 2 := by
  split_ifs with h
  · rw [h, Finset.pair_eq_singleton, Finset.card_singleton]
  · exact Finset.card_pair (Ne.symm h)

theorem orbitVec_diagramOrbit (α : E6Vec) :
    orbitVec (TwistTag.E6.diagramOrbit α) = vecOf α := by
  rw [diagramOrbit_eq, orbitVec, card_pair_rho, vecOf]
  split_ifs with h
  · rw [h, Finset.pair_eq_singleton, Finset.sum_singleton]
  · rw [Finset.sum_pair (Ne.symm h)]
    exact one_smul ℕ _

theorem cond_pair_iff (α : E6Vec) :
    (({α, rho α} : Finset E6Vec).card = 2 ∨
      (({α, rho α} : Finset E6Vec).card = 1 ∧
        ∀ β ∈ ({α, rho α} : Finset E6Vec),
          Even (β ⟨1, by decide⟩))) ↔
      keep α = true := by
  rw [card_pair_rho, keep]
  by_cases h : rho α = α
  · simp [h]
  · simp [h]

theorem mem_orbits {O : Finset E6Vec} :
    O ∈ orbits ↔
      ∃ α, IsRoot TwistTag.E6.tag α ∧ keep α = true ∧ TwistTag.E6.diagramOrbit α = O := by
  constructor
  · rintro ⟨⟨α, hα, rfl⟩, hc⟩
    rw [diagramOrbit_eq] at hc
    exact ⟨α, hα, (cond_pair_iff α).1 hc, rfl⟩
  · rintro ⟨α, hα, hk, rfl⟩
    refine ⟨⟨α, hα, rfl⟩, ?_⟩
    rw [diagramOrbit_eq]
    exact (cond_pair_iff α).2 hk

theorem mem_vecs {v : E6Vec} :
    v ∈ vecs ↔ ∃ α, IsRoot TwistTag.E6.tag α ∧ keep α = true ∧ vecOf α = v := by
  constructor
  · rintro ⟨O, hO, rfl⟩
    obtain ⟨α, hα, hk, rfl⟩ := mem_orbits.1 hO
    exact ⟨α, hα, hk, (orbitVec_diagramOrbit α).symm⟩
  · rintro ⟨α, hα, hk, rfl⟩
    exact ⟨_, mem_orbits.2 ⟨α, hα, hk, rfl⟩, orbitVec_diagramOrbit α⟩

@[expose] def cert : RootCertificate TwistTag.E6.tag :=
  TwistTag.E6.tag.rootCertificate

theorem cert_check : cert.check = true :=
  Tag.rootCertificate_check _

theorem isRoot_iff_cert {v : E6Vec} :
    IsRoot TwistTag.E6.tag v ↔ ∃ k < cert.roots.length, cert.root k = v :=
  RootCertificate.isRoot_iff cert_check

@[expose] def vecList : List (E6Vec) :=
  [![-2, -4, -4, -6, -4, -2], ![-2, -2, -3, -4, -3, -2], ![-2, 0, -2, -2, -2, -2],
    ![-1, -2, -3, -4, -3, -1], ![-1, -2, -2, -4, -2, -1], ![-1, -2, -2, -2, -2, -1],
    ![-1, -2, -1, -2, -1, -1], ![-1, 0, -2, -2, -2, -1], ![-1, 0, -1, -2, -1, -1],
    ![-1, 0, -1, 0, -1, -1], ![-1, 0, 0, 0, 0, -1], ![0, -2, -1, -2, -1, 0],
    ![0, 0, -2, -2, -2, 0], ![0, 0, -1, -2, -1, 0], ![0, 0, -1, 0, -1, 0], ![0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 2, 0, 0], ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 2, 1, 0], ![0, 0, 2, 2, 2, 0],
    ![0, 2, 1, 2, 1, 0], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 1, 1], ![1, 0, 1, 2, 1, 1],
    ![1, 0, 2, 2, 2, 1], ![1, 2, 1, 2, 1, 1], ![1, 2, 2, 2, 2, 1], ![1, 2, 2, 4, 2, 1],
    ![1, 2, 3, 4, 3, 1], ![2, 0, 2, 2, 2, 2], ![2, 2, 3, 4, 3, 2], ![2, 4, 4, 6, 4, 2]]

@[expose] def posList : List (E6Vec) :=
  vecList.filter fun v => decide (0 < height v)

theorem vecOf_mem_vecList : ∀ k < cert.roots.length,
    keep (cert.root k) = true → vecOf (cert.root k) ∈ vecList := by
  decide +kernel

theorem exists_vecOf_eq : ∀ v ∈ vecList, ∃ k < cert.roots.length,
    keep (cert.root k) = true ∧ vecOf (cert.root k) = v := by
  decide +kernel

theorem vecs_eq : vecs = {v | v ∈ vecList} := by
  ext v
  rw [mem_vecs, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨α, hα, hk, rfl⟩
    obtain ⟨k, hk', rfl⟩ := isRoot_iff_cert.1 hα
    exact vecOf_mem_vecList k hk' hk
  · intro hv
    obtain ⟨k, hk, hkeep, rfl⟩ := exists_vecOf_eq v hv
    exact ⟨_, RootCertificate.isRoot_root cert_check k hk, hkeep, rfl⟩

theorem mem_vecs_iff {v : E6Vec} : v ∈ vecs ↔ v ∈ vecList := by
  rw [vecs_eq]
  rfl

theorem mem_posVecs_iff {v : E6Vec} : v ∈ posVecs ↔ v ∈ posList := by
  rw [posVecs, Set.mem_ofPred_eq, mem_vecs_iff, posList, List.mem_filter, decide_eq_true_eq]

theorem vecList_nodup : vecList.Nodup := by
  decide +kernel

theorem ncard_setOf_mem {l : List (E6Vec)} (hl : l.Nodup) :
    {v | v ∈ l}.ncard = l.length := by
  have e : {v | v ∈ l} = ↑l.toFinset := by
    ext v
    simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

theorem ncard_vecs : vecs.ncard = 32 := by
  rw [vecs_eq, ncard_setOf_mem vecList_nodup]
  rfl

theorem ncard_posVecs : posVecs.ncard = 16 := by
  have e : posVecs = {v | v ∈ posList} := by
    ext v
    exact mem_posVecs_iff
  rw [e, ncard_setOf_mem (l := posList) (vecList_nodup.filter _)]
  decide +kernel

@[expose] def injCheck : Bool :=
  (List.range 72).all fun k => (List.range 72).all fun k' =>
    !(keep (cert.root k) && keep (cert.root k') &&
      decide (vecOf (cert.root k) = vecOf (cert.root k'))) ||
    decide (cert.root k' = cert.root k) ||
    decide (cert.root k' = rho (cert.root k))

theorem injCheck_eq : injCheck = true := by
  decide +kernel

theorem eq_or_eq_rho_of_vecOf_eq {k k' : ℕ} (hk : k < 72) (hk' : k' < 72)
    (h1 : keep (cert.root k) = true)
    (h2 : keep (cert.root k') = true)
    (h3 : vecOf (cert.root k) =
      vecOf (cert.root k')) :
    cert.root k' = cert.root k ∨
      cert.root k' = rho (cert.root k) := by
  have hc := injCheck_eq
  rw [injCheck, List.all_eq_true] at hc
  have hc' := hc k (List.mem_range.2 hk)
  rw [List.all_eq_true] at hc'
  have hc'' := hc' k' (List.mem_range.2 hk')
  rw [h1, h2, decide_eq_true h3] at hc''
  simpa using hc''

theorem e6_roots_length : cert.roots.length = 72 := by
  decide +kernel

theorem diagramOrbit_rho (α : E6Vec) :
    TwistTag.E6.diagramOrbit (rho α) = TwistTag.E6.diagramOrbit α := by
  rw [diagramOrbit_eq, diagramOrbit_eq, rho_rho, Finset.pair_comm]

theorem injOn_orbitVec : Set.InjOn orbitVec orbits := by
  intro O hO O' hO' h
  obtain ⟨α, hα, hk, rfl⟩ := mem_orbits.1 hO
  obtain ⟨β, hβ, hk', rfl⟩ := mem_orbits.1 hO'
  rw [orbitVec_diagramOrbit, orbitVec_diagramOrbit] at h
  obtain ⟨k, hk1, hkα⟩ := isRoot_iff_cert.1 hα
  obtain ⟨k', hk1', hkβ⟩ := isRoot_iff_cert.1 hβ
  rw [e6_roots_length] at hk1 hk1'
  rw [← hkα, ← hkβ] at h
  rw [← hkα] at hk
  rw [← hkβ] at hk'
  rcases eq_or_eq_rho_of_vecOf_eq hk1 hk1' hk hk' h with h1 | h1
  · rw [← hkα, ← hkβ, h1]
  · rw [← hkα, ← hkβ, h1, diagramOrbit_rho]

@[expose] def coeffs (v : E6Vec) : Fin 4 → ℤ :=
  ![v ⟨1, by decide⟩ / 2, v ⟨0, by decide⟩, v ⟨2, by decide⟩ - v ⟨1, by decide⟩ / 2,
    v ⟨3, by decide⟩ / 2 - v ⟨1, by decide⟩ / 2]

theorem coeffs_check : ∀ v ∈ vecList, v = ∑ i, coeffs v i • simpleVec i ∧
    ((0 < height v ∧ ∀ i, 0 ≤ coeffs v i) ∨ (height v < 0 ∧ ∀ i, coeffs v i ≤ 0)) := by
  decide +kernel

theorem sum_simpleVec_apply (c : Fin 4 → ℤ) :
    (∑ i, c i • simpleVec i) ⟨0, by decide⟩ = c 1 ∧
      (∑ i, c i • simpleVec i) ⟨1, by decide⟩ = 2 * c 0 ∧
      (∑ i, c i • simpleVec i) ⟨2, by decide⟩ = c 0 + c 2 ∧
      (∑ i, c i • simpleVec i) ⟨3, by decide⟩ = 2 * c 0 + 2 * c 3 := by
  simp only [Finset.sum_apply, Fin.sum_univ_four]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c 0 * 0 + c 1 * 1 + c 2 * 0 + c 3 * 0 = c 1
    ring
  · show c 0 * 2 + c 1 * 0 + c 2 * 0 + c 3 * 0 = 2 * c 0
    ring
  · show c 0 * 1 + c 1 * 0 + c 2 * 1 + c 3 * 0 = c 0 + c 2
    ring
  · show c 0 * 2 + c 1 * 0 + c 2 * 0 + c 3 * 2 = 2 * c 0 + 2 * c 3
    ring

theorem simpleVec_sum_injective {c c' : Fin 4 → ℤ}
    (h : ∑ i, c i • simpleVec i = ∑ i, c' i • simpleVec i) : c = c' := by
  obtain ⟨a0, a1, a2, a3⟩ := sum_simpleVec_apply c
  obtain ⟨b0, b1, b2, b3⟩ := sum_simpleVec_apply c'
  have h0 := congrFun h ⟨0, by decide⟩
  have h1 := congrFun h ⟨1, by decide⟩
  have h2 := congrFun h ⟨2, by decide⟩
  have h3 := congrFun h ⟨3, by decide⟩
  rw [a0, b0] at h0
  rw [a1, b1] at h1
  rw [a2, b2] at h2
  rw [a3, b3] at h3
  funext i
  fin_cases i <;> simp <;> omega

theorem coeffs_spec {v : E6Vec} (hv : v ∈ vecs) :
    v = ∑ i, coeffs v i • simpleVec i ∧
      ((0 < height v ∧ ∀ i, 0 ≤ coeffs v i) ∨ (height v < 0 ∧ ∀ i, coeffs v i ≤ 0)) :=
  coeffs_check v (mem_vecs_iff.1 hv)

theorem iform_simpleVec : ∀ i j, iform (simpleVec i) (simpleVec j) =
    ![![4, -2, 0, 0], ![-2, 4, -2, 0], ![0, -2, 4, -4], ![0, 0, -4, 8]] i j := by
  decide +kernel

theorem cartan_simpleVec (i j : Fin 4) :
    (2 * iform (simpleVec i) (simpleVec j) : ℚ) / iform (simpleVec i) (simpleVec i) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -2; 0, 0, -1, 2] i j := by
  rw [iform_simpleVec, iform_simpleVec]
  fin_cases i <;> fin_cases j <;> norm_num

theorem isRoot_simpleRoot
    (i : Fin 4) : IsRoot TwistTag.E6.tag (simpleRoot i) := by
  have h : ∀ i, ∃ k < cert.roots.length, cert.root k = simpleRoot i := by
    decide +kernel
  exact isRoot_iff_cert.2 (h i)

theorem isRoot_rho_simpleRoot
    (i : Fin 4) : IsRoot TwistTag.E6.tag (rho (simpleRoot i)) := by
  have h : ∀ i, ∃ k < cert.roots.length, cert.root k = rho (simpleRoot i) := by
    decide +kernel
  exact isRoot_iff_cert.2 (h i)

theorem simpleOrbit_spec (i : Fin 4) :
    simpleOrbit i ∈ orbits ∧ orbitVec (simpleOrbit i) = simpleVec i := by
  have hkeep : ∀ i, keep (simpleRoot i) = true := by
    decide +kernel
  have hvec : ∀ i, vecOf (simpleRoot i) = simpleVec i := by
    decide +kernel
  refine ⟨mem_orbits.2 ⟨simpleRoot i, isRoot_simpleRoot i, hkeep i, rfl⟩, ?_⟩
  rw [simpleOrbit, orbitVec_diagramOrbit, hvec]

theorem height_ne_zero_check : ∀ v ∈ vecList, height v ≠ 0 := by
  decide +kernel

theorem neg_mem_check : ∀ v ∈ vecList, -v ∈ vecList := by
  decide +kernel

theorem height_ne_zero_of_mem_vecs
    {v : E6Vec} (hv : v ∈ vecs) : height v ≠ 0 :=
  height_ne_zero_check v (mem_vecs_iff.1 hv)

theorem neg_mem_vecs {v : E6Vec} (hv : v ∈ vecs) : -v ∈ vecs :=
  mem_vecs_iff.2 (neg_mem_check v (mem_vecs_iff.1 hv))

theorem neg_mem_posVecs_iff
    {v : E6Vec} (hv : v ∈ vecs) : -v ∈ posVecs ↔ height v < 0 := by
  rw [posVecs, Set.mem_ofPred_eq, height_neg]
  exact ⟨fun h => by linarith [h.2], fun h => ⟨neg_mem_vecs hv, by linarith⟩⟩

theorem mem_posVecs_or_neg
    {v : E6Vec} (hv : v ∈ vecs) : v ∈ posVecs ∨ -v ∈ posVecs := by
  rcases lt_or_gt_of_ne (height_ne_zero_of_mem_vecs hv) with h | h
  · exact Or.inr ((neg_mem_posVecs_iff hv).2 h)
  · exact Or.inl ⟨hv, h⟩

theorem not_neg_mem_posVecs
    {v : E6Vec} (hv : v ∈ posVecs) : -v ∉ posVecs := fun h => by
  have h1 := h.2
  rw [height_neg] at h1
  linarith [hv.2]

theorem simpleVec_mem_posVecs
    (i : Fin 4) : simpleVec i ∈ posVecs := by
  have h : ∀ i, simpleVec i ∈ posList := by
    decide +kernel
  exact mem_posVecs_iff.2 (h i)

end CFSG.LieType.Chevalley.E6SignedGraph
