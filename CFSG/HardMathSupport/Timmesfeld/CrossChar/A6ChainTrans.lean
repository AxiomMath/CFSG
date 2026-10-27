module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralChain

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable (τ : Tag)

@[expose] def vecA6 (l : List ℤ) : Fin τ.rank → ℤ := fun i => l.getD i 0

@[expose] def rootVecA6 (k : ℕ) : Fin τ.rank → ℤ := vecA6 τ (τ.artifactRoots.getD k [])

@[expose] def wordA6 (ws : List ℕ) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ws.foldr (fun g v => v - corootPair (rootVecA6 τ g) v • rootVecA6 τ g) v

@[expose] def CandA6 (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (t : Fin τ.rank → ℤ) : Prop :=
  ∀ j : Fin 6, j < k → iform t (s j) = if j.val + 1 = k.val then -1 else 0

@[expose] def TabEntryA6 (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (ia : ℕ) (e : ℕ × List ℕ) :
    Prop :=
  e.1 = ia ∧ (∀ i ∈ e.2, i < τ.rootCount ∧ ∀ j : Fin 6, j < k → iform (rootVecA6 τ i) (s j) = 0) ∧
    wordA6 τ e.2 (s k) = rootVecA6 τ ia

@[expose] def NoExtA6 (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (ia : ℕ) : Prop :=
  (k : ℕ) < 5 ∧ ∀ ib : Fin τ.rootCount, ¬ (iform (rootVecA6 τ ib) (rootVecA6 τ ia) = -1 ∧
    ∀ j : Fin 6, j < k → iform (rootVecA6 τ ib) (s j) = 0)

@[expose] def ChainTabA6 (s : Fin 6 → Fin τ.rank → ℤ) (tab : Fin 6 → List (ℕ × List ℕ)) :
    Prop :=
  ∀ k : Fin 6, ∀ ia : Fin τ.rootCount, CandA6 τ s k (rootVecA6 τ ia) →
    (∃ e ∈ tab k, TabEntryA6 τ s k ia e) ∨ NoExtA6 τ s k ia

instance (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (t : Fin τ.rank → ℤ) :
    Decidable (CandA6 τ s k t) := by
  unfold CandA6
  infer_instance

instance (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (ia : ℕ) (e : ℕ × List ℕ) :
    Decidable (TabEntryA6 τ s k ia e) := by
  unfold TabEntryA6
  infer_instance

instance (s : Fin 6 → Fin τ.rank → ℤ) (k : Fin 6) (ia : ℕ) : Decidable (NoExtA6 τ s k ia) := by
  unfold NoExtA6
  infer_instance

instance (s : Fin 6 → Fin τ.rank → ℤ) (tab : Fin 6 → List (ℕ × List ℕ)) :
    Decidable (ChainTabA6 τ s tab) := by
  unfold ChainTabA6
  infer_instance

variable {τ}

theorem vecA6_ofFn (t : Fin τ.rank → ℤ) : vecA6 τ (List.ofFn t) = t := by
  funext i
  simp [vecA6]

section


theorem exists_rootVecA6_of_isRoot {t : Fin τ.rank → ℤ} (ht : IsRoot τ t) :
    ∃ ia : Fin τ.rootCount, rootVecA6 τ ia = t := by
  have h1 := (isRoot_iff_mem_artifactRoots (τ := τ)).1 ht
  obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.1 h1
  have hlen : τ.artifactRoots.length = τ.rootCount := Tag.length_artifactRoots τ
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [rootVecA6, List.getD_eq_getElem _ _ hk, hkt, vecA6_ofFn]

theorem isRoot_rootVecA6 {k : ℕ} (hk : k < τ.rootCount) : IsRoot τ (rootVecA6 τ k) := by
  have hlen : τ.artifactRoots.length = τ.rootCount := Tag.length_artifactRoots τ
  have hmem : τ.artifactRoots.getD k [] ∈ τ.artifactRoots := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [isRoot_iff_mem_artifactRoots, rootVecA6]
  generalize τ.artifactRoots.getD k [] = l at hmem ⊢
  have hl := length_of_mem_artifactRoots hmem
  have : List.ofFn (vecA6 τ l) = l := by
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    simp [vecA6, List.getD_eq_getElem?_getD, h2]
  rw [this]
  exact hmem

variable (τ) in
@[expose] def prodA6 (ws : List ℕ) : WeylGroup τ :=
  (ws.map fun g => rootReflection (rootVecA6 τ g)).prod

theorem prodA6_smul {ws : List ℕ} (hws : ∀ g ∈ ws, g < τ.rootCount) (v : Fin τ.rank → ℤ) :
    prodA6 τ ws • v = wordA6 τ ws v := by
  induction ws with
  | nil => simp [prodA6, wordA6]
  | cons g ws ih =>
    have hg : g < τ.rootCount := hws g (by simp)
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    simp only [prodA6, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul (isRoot_rootVecA6 hg)]
    rfl

theorem prodA6_fix {x : Fin τ.rank → ℤ} {ws : List ℕ}
    (hws : ∀ g ∈ ws, g < τ.rootCount ∧ iform (rootVecA6 τ g) x = 0) : prodA6 τ ws • x = x := by
  induction ws with
  | nil => simp [prodA6]
  | cons g ws ih =>
    have hg := hws g (by simp)
    have ih' := ih (fun y hy => hws y (by simp [hy]))
    simp only [prodA6, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul_of_iform_eq_zero (isRoot_rootVecA6 hg.1) hg.2]

theorem levelStepA6 {s : Fin 6 → Fin τ.rank → ℤ} {tab : Fin 6 → List (ℕ × List ℕ)}
    (hok : ChainTabA6 τ s tab) (k : Fin 6) {t : Fin τ.rank → ℤ} (ht : IsRoot τ t)
    (hc : CandA6 τ s k t)
    (hext : (k : ℕ) < 5 → ∃ u : Fin τ.rank → ℤ, IsRoot τ u ∧ iform u t = -1 ∧
      ∀ j : Fin 6, j < k → iform u (s j) = 0) :
    ∃ u : WeylGroup τ, (∀ j : Fin 6, j < k → u • s j = s j) ∧ u • s k = t := by
  obtain ⟨ia, rfl⟩ := exists_rootVecA6_of_isRoot ht
  rcases hok k ia hc with ⟨e, -, he1, hwords, happ⟩ | ⟨hk5, hno⟩
  · refine ⟨prodA6 τ e.2, fun j hj => ?_, ?_⟩
    · exact prodA6_fix fun g hg => ⟨(hwords g hg).1, (hwords g hg).2 j hj⟩
    · rw [prodA6_smul fun g hg => (hwords g hg).1, happ]
  · obtain ⟨u, hu, hut, huj⟩ := hext hk5
    obtain ⟨ib, rfl⟩ := exists_rootVecA6_of_isRoot hu
    exact absurd ⟨hut, huj⟩ (hno ib)

theorem exists_weyl_a6chain {s : Fin 6 → Fin τ.rank → ℤ} {tab : Fin 6 → List (ℕ × List ℕ)}
    (hok : ChainTabA6 τ s tab) {β : Fin 6 → Fin τ.rank → ℤ} (hβ : IsAChain β) :
    ∃ v : WeylGroup τ, ∀ k : Fin 6, v • s k = β k := by
  have hgram : ∀ j k : Fin 6, j < k → iform (β k) (β j) = if j.val + 1 = k.val then -1 else 0 := by
    intro j k hjk
    split_ifs with h
    · rw [iform_comm]
      exact hβ.adj j k h.symm
    · rw [iform_comm]
      exact hβ.orth j k (by have : (j : ℕ) < k := hjk; omega)
  have key : ∀ n : ℕ, n ≤ 6 → ∃ v : WeylGroup τ, ∀ j : Fin 6, j.val < n → v • s j = β j := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, fun j hj => absurd hj (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨v, hv⟩ := ih (by omega)
      set k : Fin 6 := ⟨n, by omega⟩ with hk
      have hinv : ∀ (x : Fin τ.rank → ℤ) (j : Fin 6), j.val < n →
          iform (v⁻¹ • x) (s j) = iform x (β j) := fun x j hj => by
        rw [← hv j hj, ← iform_smul v (v⁻¹ • x), smul_inv_smul]
      have htroot : IsRoot τ (v⁻¹ • β k) := IsRoot.smul (hβ.isRoot k) v⁻¹
      have hcand : CandA6 τ s k (v⁻¹ • β k) := by
        intro j hj
        rw [hinv _ j hj]
        exact hgram j k hj
      have hext : (k : ℕ) < 5 → ∃ u : Fin τ.rank → ℤ, IsRoot τ u ∧ iform u (v⁻¹ • β k) = -1 ∧
          ∀ j : Fin 6, j < k → iform u (s j) = 0 := by
        intro hk5
        set k' : Fin 6 := ⟨n + 1, by simp [hk] at hk5; omega⟩ with hk'
        refine ⟨v⁻¹ • β k', IsRoot.smul (hβ.isRoot k') v⁻¹, ?_, fun j hj => ?_⟩
        · rw [iform_smul, iform_comm]
          exact hβ.adj k k' (by simp [hk, hk'])
        · have hjn : j.val < n := hj
          rw [hinv _ j hjn, iform_comm]
          exact hβ.orth j k' (by simp [hk']; omega)
      obtain ⟨u, hu1, hu2⟩ := levelStepA6 hok k htroot hcand hext
      refine ⟨v * u, fun j hj => ?_⟩
      by_cases hjn : j.val < n
      · rw [mul_smul, hu1 j hjn, hv j hjn]
      · have : j = k := Fin.ext (by simp [hk]; omega)
        subst this
        rw [mul_smul, hu2, smul_inv_smul]
  obtain ⟨v, hv⟩ := key 6 le_rfl
  exact ⟨v, fun k => hv k k.2⟩

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar
