module

public import CFSG.GH74.BNPair.Paths

public section

namespace CFSG.GH74.BNPair

variable {V : Type*} {G : SimpleGraph V}

theorem mem_pathFixer_iff {l : List V} {σ : Equiv.Perm V} :
    σ ∈ pathFixer G l ↔
      σ ∈ graphAut G ∧ ∀ v ∈ interiorVertices l, ∀ w, G.Adj v w → σ w = w := by
  unfold pathFixer
  rw [Subgroup.mem_inf]
  refine and_congr Iff.rfl ?_
  simp only [Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
    SimpleGraph.mem_neighborSet]

theorem pathFixer_le_graphAut (l : List V) : pathFixer G l ≤ graphAut G :=
  fun _ h => (mem_pathFixer_iff.1 h).1

theorem mem_graphAut_iff {σ : Equiv.Perm V} :
    σ ∈ graphAut G ↔ ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w :=
  Iff.rfl

theorem mem_pathFixer_map {σ : Equiv.Perm V} (hσ : σ ∈ graphAut G) {τ : Equiv.Perm V}
    (l : List V) : τ ∈ pathFixer G (l.map σ) ↔ σ⁻¹ * τ * σ ∈ pathFixer G l := by
  rw [mem_pathFixer_iff, mem_pathFixer_iff]
  have hτ : τ ∈ graphAut G ↔ σ⁻¹ * τ * σ ∈ graphAut G := by
    constructor
    · intro h
      exact mul_mem (mul_mem (inv_mem hσ) h) hσ
    · intro h
      have := mul_mem (mul_mem hσ h) (inv_mem hσ)
      simpa [mul_assoc] using this
  refine and_congr hτ ?_
  have hint : interiorVertices (l.map σ) = (interiorVertices l).map σ := by
    simp [interiorVertices, List.map_tail, List.map_dropLast]
  rw [hint]
  constructor
  · intro h v hv w hw
    have := h (σ v) (List.mem_map_of_mem hv) (σ w) ((mem_graphAut_iff.1 hσ v w).2 hw)
    simp [Equiv.Perm.mul_apply, this]
  · intro h v' hv' w' hw'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hv'
    have hw : G.Adj v (σ⁻¹ w') := by
      have h1 := (mem_graphAut_iff.1 hσ v (σ⁻¹ w')).1
      simp at h1
      exact h1 hw'
    have h2 := h v hv (σ⁻¹ w') hw
    simp only [Equiv.Perm.mul_apply] at h2
    have h3 : τ w' = w' := by
      have := congrArg σ h2
      simpa using this
    exact h3

theorem pathFixer_fixes {l : List V} (hl : IsGLSPath G l) {n : ℕ} (hn : 3 ≤ n)
    (hlen : l.length = n + 1) {σ : Equiv.Perm V} (hσ : σ ∈ pathFixer G l) :
    ∀ v ∈ l, σ v = v := by
  have hne : l ≠ [] := by
    rintro rfl
    simp at hlen
  obtain ⟨u, hu⟩ : ∃ u, l.head? = some u := ⟨l.head hne, List.head?_eq_some_head hne⟩
  obtain ⟨v, hv⟩ : ∃ v, l.getLast? = some v := ⟨l.getLast hne, List.getLast?_eq_some_getLast hne⟩
  obtain ⟨f, k, hk, hf0, hfk, hadj, hnb, hfl⟩ := hl.exists_fun hu hv
  obtain ⟨-, hσf⟩ := mem_pathFixer_iff.1 hσ
  have hkn : k = n := by omega
  have hint : ∀ j, 1 ≤ j → j + 1 ≤ k → f j ∈ interiorVertices l := by
    intro j hj1 hj2
    have h1 := getElem_mem_interiorVertices (l := l) (i := j) hj1 (by omega)
    have h2 : l[j]'(by omega) = f j := by
      have := hfl j (by omega)
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    rwa [h2] at h1
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hxi : l[i] = f i := by
    have := hfl i (by omega)
    rw [List.getElem?_eq_getElem hi] at this
    exact Option.some.inj this
  rw [hxi]
  by_cases hi0 : i = 0
  · subst hi0
    exact hσf (f 1) (hint 1 (le_refl _) (by omega)) (f 0) (hadj 0 (by omega)).symm
  by_cases hik : i = k
  · subst hik
    exact hσf (f (i - 1)) (hint (i - 1) (by omega) (by omega)) (f i)
      (by simpa [show i - 1 + 1 = i by omega] using hadj (i - 1) (by omega))
  by_cases hi1 : i = 1
  · subst hi1
    exact hσf (f 2) (hint 2 (by omega) (by omega)) (f 1) (hadj 1 (by omega)).symm
  · exact hσf (f (i - 1)) (hint (i - 1) (by omega) (by omega)) (f i)
      (by simpa [show i - 1 + 1 = i by omega] using hadj (i - 1) (by omega))

theorem mem_pathFixerSpan_of_map {σ : Equiv.Perm V} (hσ : σ ∈ graphAut G) {l : List V} {n : ℕ}
    (hl : IsGLSPath G l) (hlen : l.length = n + 1) {τ : Equiv.Perm V}
    (hτ : σ⁻¹ * τ * σ ∈ pathFixer G l) : τ ∈ pathFixerSpan G n := by
  have hl' : IsGLSPath G (l.map σ) := by
    refine IsGLSPath.map (G := G) (g := σ) (fun v w => mem_graphAut_iff.1 hσ v w) hl
  unfold pathFixerSpan
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨l.map σ, ⟨hl', by simpa using hlen⟩, (mem_pathFixer_map hσ l).2 hτ⟩

section Iso

variable {V' : Type*} {G' : SimpleGraph V'}

theorem isGLSPath_map_iso (e : G ≃g G') : ∀ l : List V, IsGLSPath G' (l.map e) ↔ IsGLSPath G l
  | [] => ⟨fun _ => IsGLSPath.nil, fun _ => IsGLSPath.nil⟩
  | [_] => ⟨fun _ => IsGLSPath.singleton _, fun _ => IsGLSPath.singleton _⟩
  | u :: v :: l => by
    have ih := isGLSPath_map_iso e (v :: l)
    simp only [List.map_cons] at ih ⊢
    rw [isGLSPath_cons_cons, isGLSPath_cons_cons, ih, e.map_adj_iff]
    refine and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · intro h w hw
      have := h (e w) (by rw [List.head?_map, hw]; rfl)
      exact fun he => this (by rw [he])
    · intro h w hw
      rw [List.head?_map] at hw
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hw
      exact fun he => h w' hw' (e.injective he)

theorem mem_pathFixer_iso (e : G ≃g G') (l : List V) (σ : Equiv.Perm V) :
    Equiv.permCongrHom e.toEquiv σ ∈ pathFixer G' (l.map e) ↔ σ ∈ pathFixer G l := by
  rw [mem_pathFixer_iff, mem_pathFixer_iff]
  have hint : interiorVertices (l.map e) = (interiorVertices l).map e := by
    simp [interiorVertices, List.map_tail, List.map_dropLast]
  have happ : ∀ v', Equiv.permCongrHom e.toEquiv σ v' = e (σ (e.symm v')) := fun v' => rfl
  refine and_congr ?_ ?_
  · constructor
    · intro h v w
      have := h (e v) (e w)
      rw [happ, happ] at this
      simpa [e.map_adj_iff] using this
    · intro h v' w'
      rw [happ, happ, e.map_adj_iff]
      have := h (e.symm v') (e.symm w')
      rw [this]
      exact e.symm.map_adj_iff
  · rw [hint]
    constructor
    · intro h v hv w hw
      have := h (e v) (List.mem_map_of_mem hv) (e w) (e.map_adj_iff.2 hw)
      rw [happ] at this
      simp only [RelIso.symm_apply_apply] at this
      exact e.injective this
    · intro h v' hv' w' hw'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hv'
      rw [happ]
      have hw : G.Adj v (e.symm w') := by
        have := (e.map_adj_iff (v := v) (w := e.symm w')).1
        simp only [RelIso.apply_symm_apply] at this
        exact this hw'
      have := h v hv (e.symm w') hw
      rw [this]
      simp

theorem pathFixerSpan_map_iso (e : G ≃g G') (n : ℕ) :
    (pathFixerSpan G n).map (Equiv.permCongrHom e.toEquiv).toMonoidHom = pathFixerSpan G' n := by
  unfold pathFixerSpan
  rw [MonoidHom.map_closure]
  congr 1
  ext τ'
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨σ, ⟨l, ⟨hl, hlen⟩, hσ⟩, rfl⟩
    exact ⟨l.map e, ⟨(isGLSPath_map_iso e l).2 hl, by simpa using hlen⟩,
      (mem_pathFixer_iso e l σ).2 hσ⟩
  · rintro ⟨l', ⟨hl', hlen'⟩, hτ'⟩
    refine ⟨(Equiv.permCongrHom e.toEquiv).symm τ', ⟨l'.map e.symm, ⟨?_, by simpa using hlen'⟩, ?_⟩,
      MulEquiv.apply_symm_apply _ _⟩
    · exact (isGLSPath_map_iso e.symm l').2 hl'
    · have hmap : (l'.map e.symm).map e = l' := by
        simp [List.map_map]
      have h1 := (mem_pathFixer_iso e (l'.map e.symm)
        ((Equiv.permCongrHom e.toEquiv).symm τ')).1
      rw [hmap, MulEquiv.apply_symm_apply] at h1
      exact h1 hτ'

end Iso

end CFSG.GH74.BNPair
