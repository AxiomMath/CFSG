module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12ThreeCentralZ2
public import Certificates.Certificate9681

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Cover

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Certificates
  CFSG.AGLEmbedding.KFactProofs.M12Z2

section Stream

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem exists_rep_of_forall₂ {T : List Table} {Gs : List G}
    (h : List.Forall₂ (Rep n) T Gs) {t : G} (ht : t ∈ Gs) : ∃ tT ∈ T, Rep n tT t := by
  induction h with
  | nil => simp at ht
  | cons hab _ ih =>
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, hr⟩ := ih ht
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

theorem countProducts_eq_zero {f : Table → Bool} :
    ∀ {Tss : List (List Table)} {Gss : List (List G)},
      List.Forall₂ (List.Forall₂ (Rep n)) Tss Gss → ∀ {gT : Table} {g : G}, Rep n gT g →
        countProducts n f Tss gT = 0 →
        ∀ h ∈ (products Gss).map (g * ·), ∃ T, Rep n T h ∧ f T = false
  | [], [], .nil, gT, g, hg, hc, h, hh => by
    simp only [products, List.map_cons, List.map_nil, mul_one, List.mem_singleton] at hh
    subst hh
    refine ⟨gT, hg, ?_⟩
    by_contra hf
    rw [Bool.not_eq_false] at hf
    simp [countProducts, hf] at hc
  | T :: Ts, Gs :: Gss, .cons hT hTs, gT, g, hg, hc, h, hh => by
    rw [countProducts, foldl_add_eq_sum, zero_add, List.sum_eq_zero_iff] at hc
    rw [products_map_mul, List.mem_flatMap] at hh
    obtain ⟨t, ht, hh⟩ := hh
    obtain ⟨tT, htT, hRep⟩ := exists_rep_of_forall₂ hT ht
    exact countProducts_eq_zero hTs (Rep.compT hg hRep) (hc _ (List.mem_map_of_mem htT)) h hh

end Stream

theorem rep_perm_eq {T : Table} {g h : Equiv.Perm (Fin 12)} (hg : Rep 12 T g) (hh : Rep 12 T h) :
    g = h := by
  ext i
  have h1 := hg i i.2
  have h2 := hh i i.2
  rw [idx_of_lt _ i.2] at h1 h2
  simpa [Equiv.Perm.smul_def] using h1.symm.trans h2

theorem m12CoverCov_sound {T : Table} {g : Equiv.Perm (Fin 12)} (hT : Rep 12 T g)
    (h : m12CoverCov T = true) :
    ∃ k, ∃ n ∈ m12CoverNorm, ∃ r ∈ m12CoverReps, g ^ k = n * r.1 * n⁻¹ := by
  unfold m12CoverCov at h
  rw [List.any_eq_true] at h
  obtain ⟨k, -, hk⟩ := h
  unfold m12CoverOrbSet at hk
  rw [Std.HashSet.contains_ofList, List.contains, List.elem_eq_mem, decide_eq_true_eq,
    m12CoverOrb] at hk
  simp only [List.mem_flatMap, List.mem_map, m12CoverNormTabs, m12CoverRepTabs] at hk
  obtain ⟨_, ⟨n, hn, rfl⟩, _, ⟨r, hr, rfl⟩, hkT⟩ := hk
  refine ⟨k + 1, n, hn, r, hr, ?_⟩
  have h1 := Rep.compT (rep_toTable (by norm_num) n)
    (Rep.compT (rep_toTable (by norm_num) r.1) (rep_toTable (by norm_num) n⁻¹))
  have h2 := Rep.powT (by norm_num) hT (k + 1)
  rw [hkT] at h1
  rw [rep_perm_eq h2 h1, mul_assoc]

theorem m12Cover_closure {M : Subgroup (Equiv.Perm (Fin 12))} {u v g n r : Equiv.Perm (Fin 12)}
    {k : ℕ} (hg : g ∈ M) (hu : u ∈ M) (hv : v ∈ M)
    (hnu : n * u * n⁻¹ ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 12))))
    (hnv : n * v * n⁻¹ ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 12))))
    (hr : M ≤ Subgroup.closure ({u, v, r} : Set (Equiv.Perm (Fin 12))))
    (hgk : g ^ k = n * r * n⁻¹) :
    M ≤ Subgroup.closure ({u, v, g} : Set (Equiv.Perm (Fin 12))) := by
  set H := Subgroup.closure ({u, v, g} : Set (Equiv.Perm (Fin 12))) with hH
  have hHM : H ≤ M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | rfl | rfl)
    · exact hu
    · exact hv
    · exact hg
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hvH : v ∈ H := Subgroup.subset_closure (by simp)
  have hgH : g ∈ H := Subgroup.subset_closure (by simp)
  have hcl : Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 12))) ≤ H :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  set H' := H.map (MulAut.conj n⁻¹).toMonoidHom with hH'
  have hcard : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective
  have hu' : u ∈ H' := ⟨n * u * n⁻¹, hcl hnu, by simp [mul_assoc]⟩
  have hv' : v ∈ H' := ⟨n * v * n⁻¹, hcl hnv, by simp [mul_assoc]⟩
  have hr' : r ∈ H' := ⟨g ^ k, H.pow_mem hgH k, by
    rw [hgk]; simp [mul_assoc]⟩
  have hMH' : M ≤ H' := by
    refine hr.trans ((Subgroup.closure_le _).2 ?_)
    rintro x (rfl | rfl | rfl)
    · exact hu'
    · exact hv'
    · exact hr'
  have hle : Nat.card M ≤ Nat.card H := hcard ▸ Subgroup.card_le_of_le hMH'
  exact (Subgroup.eq_of_le_of_card_ge hHM hle).symm.le

@[expose] def m12CoverB0 : List (Equiv.Perm (Fin 12)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => m12CoverU ^ i * m12CoverV ^ j

@[expose] def m12CoverWordsOK : Bool :=
  m12CoverReps.all fun r =>
    decide (evalCodes [m12CoverU, m12CoverV, r.1] r.2.1 = m12gA) &&
      decide (evalCodes [m12CoverU, m12CoverV, r.1] r.2.2 = m12gB)

@[expose] def m12CoverNormOK : Bool :=
  m12CoverNorm.all fun n =>
    decide (n * m12CoverU * n⁻¹ ∈ m12CoverB0) && decide (n * m12CoverV * n⁻¹ ∈ m12CoverB0)

set_option maxRecDepth 100000 in
theorem m12CoverWordsOK_true : m12CoverWordsOK = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12CoverNormOK_true : m12CoverNormOK = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12CoverU_eq : m12CoverU = m12HeisC := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12CoverV_eq : m12CoverV = m12HeisB := by decide +kernel

theorem m12CoverU_mem : m12CoverU ∈ NativeSporadic.M12 := by
  rw [m12CoverU_eq, m12HeisC]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m12HeisA_mem m12HeisB_mem)
    (Subgroup.inv_mem _ m12HeisA_mem)) (Subgroup.inv_mem _ m12HeisB_mem)

theorem m12CoverV_mem : m12CoverV ∈ NativeSporadic.M12 := by
  rw [m12CoverV_eq]
  exact m12HeisB_mem

theorem m12CoverB0_mem_closure {x : Equiv.Perm (Fin 12)} (hx : x ∈ m12CoverB0) :
    x ∈ Subgroup.closure ({m12CoverU, m12CoverV} : Set (Equiv.Perm (Fin 12))) := by
  simp only [m12CoverB0, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨i, -, j, -, rfl⟩ := hx
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem evalCodes_mem_closure (S : List (Equiv.Perm (Fin 12))) :
    ∀ w : List ℤ, evalCodes S w ∈ Subgroup.closure {x | x ∈ S}
  | [] => Subgroup.one_mem _
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ Subgroup.closure {x | x ∈ S} := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[k]? with
      | none => exact Subgroup.one_mem _
      | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)
    rw [evalCodes]
    refine Subgroup.mul_mem _ ?_ (evalCodes_mem_closure S w)
    split_ifs
    · exact hget _
    · exact Subgroup.inv_mem _ (hget _)

theorem m12Cover_rep_le {r : Equiv.Perm (Fin 12) × List ℤ × List ℤ} (hr : r ∈ m12CoverReps) :
    NativeSporadic.M12 ≤ Subgroup.closure ({m12CoverU, m12CoverV, r.1} :
      Set (Equiv.Perm (Fin 12))) := by
  have h := List.all_eq_true.1 m12CoverWordsOK_true r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hS : {x | x ∈ [m12CoverU, m12CoverV, r.1]} =
      ({m12CoverU, m12CoverV, r.1} : Set (Equiv.Perm (Fin 12))) := by
    ext x; simp
  have hA := evalCodes_mem_closure [m12CoverU, m12CoverV, r.1] r.2.1
  have hB := evalCodes_mem_closure [m12CoverU, m12CoverV, r.1] r.2.2
  rw [h.1, hS] at hA
  rw [h.2, hS] at hB
  rw [m12_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro x (rfl | rfl)
  · exact hA
  · exact hB

theorem m12Cover_core
    {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hord : orderOf g = 5 ∨ orderOf g = 11) :
    NativeSporadic.M12 ≤
      Subgroup.closure ({m12CoverU, m12CoverV, g} : Set (Equiv.Perm (Fin 12))) := by
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have hz := Certificates.certificate9681
  have hall := countProducts_eq_zero (forall₂_levelTables (by norm_num) m12Certificate)
    (Rep.idT (by norm_num)) hz
  have hmem : g ∈ (products ((List.finRange m12Certificate.baseCount).map
      (levelTransversals m12Certificate))).map ((1 : Equiv.Perm (Fin 12)) * ·) := by
    simp only [one_mul, List.map_id']
    exact (mem_enumeration_iff m12Certificate hQ g).2
      (by rw [m12Certificate_originalSubgroup]; exact hg)
  obtain ⟨T, hT, hf⟩ := hall g hmem
  have hcov : m12CoverCov T = true := by
    unfold m12CoverBad at hf
    have hord' : ordTest 12 5 T = true ∨ ordTest 12 11 T = true := by
      rcases hord with h | h
      · exact Or.inl ((ordTest_iff perm_faithful hT (by norm_num)).2 h)
      · exact Or.inr ((ordTest_iff perm_faithful hT (by norm_num)).2 h)
    simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not,
      Bool.not_false] at hf
    rcases hf with hf | hf
    · rcases hord' with h | h <;> simp_all
    · exact hf
  obtain ⟨k, n, hn, r, hr, hgk⟩ := m12CoverCov_sound hT hcov
  have hnorm := List.all_eq_true.1 m12CoverNormOK_true n hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hnorm
  exact m12Cover_closure hg m12CoverU_mem m12CoverV_mem
    (m12CoverB0_mem_closure hnorm.1) (m12CoverB0_mem_closure hnorm.2) (m12Cover_rep_le hr) hgk

end CFSG.AGLEmbedding.KFactProofs.M12Cover
