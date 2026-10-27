module

public import CFSG.HardMathSupport.Timmesfeld.Torality.E8ChainTab
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e8idx (i : Fin 8) : Fin Tag.E8.rank := i

@[expose] def e8s : Fin 4 → Fin Tag.E8.rank → ℤ :=
  ![Pi.single (e8idx 0) 1, Pi.single (e8idx 2) 1, Pi.single (e8idx 3) 1, Pi.single (e8idx 4) 1]

@[expose] def e8vec (l : List ℤ) : Fin Tag.E8.rank → ℤ := fun i => l.getD i 0

@[expose] def e8rootVec (k : ℕ) : Fin Tag.E8.rank → ℤ := e8vec (Tag.E8.artifactRoots.getD k [])

@[expose] def e8Word (ws : List ℕ) (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  ws.foldr (fun g v => v - corootPair (e8rootVec g) v • e8rootVec g) v

@[expose] def e8ChainTab (k : Fin 4) : List (ℕ × List ℕ) :=
  match k with
  | 0 => e8ChainTab0
  | 1 => e8ChainTab1
  | 2 => e8ChainTab2
  | 3 => e8ChainTab3

@[expose] def e8Cand (k : Fin 4) (t : Fin Tag.E8.rank → ℤ) : Prop :=
  ∀ j : Fin 4, j < k → iform t (e8s j) = if j.val + 1 = k.val then -1 else 0

instance (k : Fin 4) (t : Fin Tag.E8.rank → ℤ) : Decidable (e8Cand k t) := by
  unfold e8Cand; infer_instance

theorem e8Chain_check : ∀ k : Fin 4, ∀ ia : Fin 240, e8Cand k (e8rootVec ia) →
    ∃ e ∈ e8ChainTab k, e.1 = ia ∧ (∀ i ∈ e.2, i < 240 ∧ ∀ j : Fin 4, j < k →
        iform (e8rootVec i) (e8s j) = 0) ∧ e8Word e.2 (e8s k) = e8rootVec ia := by
  decide +kernel


section


theorem e8vec_ofFn (t : Fin Tag.E8.rank → ℤ) : e8vec (List.ofFn t) = t := by
  funext i
  simp [e8vec]

theorem exists_e8rootVec_of_isRoot {t : Fin Tag.E8.rank → ℤ} (ht : IsRoot Tag.E8 t) :
    ∃ ia : Fin 240, e8rootVec ia = t := by
  have h1 := (isRoot_iff_mem_artifactRoots (τ := Tag.E8)).1 ht
  obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.1 h1
  have hlen : Tag.E8.artifactRoots.length = 240 := Tag.length_artifactRoots Tag.E8
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [e8rootVec, List.getD_eq_getElem _ _ hk, hkt, e8vec_ofFn]

theorem isRoot_e8rootVec {k : ℕ} (hk : k < 240) : IsRoot Tag.E8 (e8rootVec k) := by
  have hlen : Tag.E8.artifactRoots.length = 240 := Tag.length_artifactRoots Tag.E8
  have hmem : Tag.E8.artifactRoots.getD k [] ∈ Tag.E8.artifactRoots := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [isRoot_iff_mem_artifactRoots, e8rootVec]
  generalize Tag.E8.artifactRoots.getD k [] = l at hmem ⊢
  have hl := length_of_mem_artifactRoots hmem
  have : List.ofFn (e8vec l) = l := by
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    simp [e8vec, List.getD_eq_getElem?_getD, h2]
  rw [this]
  exact hmem

@[expose] def e8Prod (ws : List ℕ) : WeylGroup Tag.E8 :=
  (ws.map fun g => rootReflection (e8rootVec g)).prod

theorem e8Prod_smul {ws : List ℕ} (hws : ∀ g ∈ ws, g < 240) (v : Fin Tag.E8.rank → ℤ) :
    e8Prod ws • v = e8Word ws v := by
  induction ws with
  | nil => simp [e8Prod, e8Word]
  | cons g ws ih =>
    have hg : g < 240 := hws g (by simp)
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    simp only [e8Prod, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul (isRoot_e8rootVec hg)]
    rfl

theorem e8Prod_fix {x : Fin Tag.E8.rank → ℤ} {ws : List ℕ} (hws : ∀ g ∈ ws, g < 240 ∧ iform (e8rootVec g) x = 0) :
    e8Prod ws • x = x := by
  induction ws with
  | nil => simp [e8Prod]
  | cons g ws ih =>
    have hg := hws g (by simp)
    have ih' := ih (fun y hy => hws y (by simp [hy]))
    simp only [e8Prod, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul_of_iform_eq_zero (isRoot_e8rootVec hg.1) hg.2]

theorem e8_level_step (k : Fin 4) {t : Fin Tag.E8.rank → ℤ} (ht : IsRoot Tag.E8 t)
    (hc : e8Cand k t) :
    ∃ u : WeylGroup Tag.E8, (∀ j : Fin 4, j < k → u • e8s j = e8s j) ∧ u • e8s k = t := by
  obtain ⟨ia, rfl⟩ := exists_e8rootVec_of_isRoot ht
  obtain ⟨e, he, he1, hwords, happ⟩ := e8Chain_check k ia hc
  refine ⟨e8Prod e.2, fun j hj => ?_, ?_⟩
  · exact e8Prod_fix fun g hg => ⟨(hwords g hg).1, (hwords g hg).2 j hj⟩
  · rw [e8Prod_smul fun g hg => (hwords g hg).1, happ]

structure IsE8Chain (β : Fin 4 → Fin Tag.E8.rank → ℤ) : Prop where
  isRoot : ∀ k, IsRoot Tag.E8 (β k)
  gram : ∀ j k : Fin 4, iform (β j) (β k) = iform (e8s j) (e8s k)

theorem e8s_gram : ∀ j k : Fin 4, j < k →
    iform (e8s k) (e8s j) = if j.val + 1 = k.val then -1 else 0 := by
  decide +kernel

theorem exists_weyl_chain_E8 {β : Fin 4 → Fin Tag.E8.rank → ℤ} (hβ : IsE8Chain β) :
    ∃ v : WeylGroup Tag.E8, ∀ k : Fin 4, v • e8s k = β k := by
  have key : ∀ n : ℕ, n ≤ 4 → ∃ v : WeylGroup Tag.E8, ∀ j : Fin 4, j.val < n → v • e8s j = β j := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, fun j hj => absurd hj (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨v, hv⟩ := ih (by omega)
      set k : Fin 4 := ⟨n, by omega⟩ with hk
      have htroot : IsRoot Tag.E8 (v⁻¹ • β k) := IsRoot.smul (hβ.isRoot k) v⁻¹
      have hcand : e8Cand k (v⁻¹ • β k) := by
        intro j hj
        have hjn : j.val < n := hj
        have h1 : iform (v⁻¹ • β k) (e8s j) = iform (β k) (β j) := by
          rw [← hv j hjn, ← iform_smul v (v⁻¹ • β k), smul_inv_smul]
        rw [h1, hβ.gram]
        exact e8s_gram j k hj
      obtain ⟨u, hu1, hu2⟩ := e8_level_step k htroot hcand
      refine ⟨v * u, fun j hj => ?_⟩
      by_cases hjn : j.val < n
      · rw [mul_smul, hu1 j hjn, hv j hjn]
      · have : j = k := Fin.ext (by simp [hk]; omega)
        subst this
        rw [mul_smul, hu2, smul_inv_smul]
  obtain ⟨v, hv⟩ := key 4 le_rfl
  exact ⟨v, fun k => hv k k.2⟩

end

end CFSG.HardMathSupport.Timmesfeld.Torality
