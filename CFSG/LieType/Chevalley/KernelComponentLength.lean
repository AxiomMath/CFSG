module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}

@[expose] def IsComponentWord (Ψ : Set (Fin τ.rank → ℤ)) (l : List (Fin τ.rank → ℤ)) : Prop :=
  ∀ β ∈ l, β ∈ simpleRoots Ψ

@[expose] def reflectionWordProd
    (l : List (Fin τ.rank → ℤ)) : WeylGroup τ :=
  (l.map rootReflection).prod

@[expose] def componentLength
    (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ) : ℕ :=
  sInf {n | ∃ l, IsComponentWord Ψ l ∧ l.length = n ∧ reflectionWordProd l = w}

theorem reflectionWordProd_nil
    : reflectionWordProd ([] : List (Fin τ.rank → ℤ)) = 1 := rfl

theorem reflectionWordProd_cons
    (β : Fin τ.rank → ℤ) (l : List (Fin τ.rank → ℤ)) :
    reflectionWordProd (β :: l) = rootReflection β * reflectionWordProd l := by
  simp [reflectionWordProd]

theorem reflectionWordProd_append
    (l l' : List (Fin τ.rank → ℤ)) :
    reflectionWordProd (l ++ l') = reflectionWordProd l * reflectionWordProd l' := by
  simp [reflectionWordProd]

theorem IsComponentWord.cons {β : Fin τ.rank → ℤ} {l : List (Fin τ.rank → ℤ)}
    (hβ : β ∈ simpleRoots Ψ) (hl : IsComponentWord Ψ l) : IsComponentWord Ψ (β :: l) := by
  intro γ hγ
  rcases List.mem_cons.1 hγ with rfl | h
  · exact hβ
  · exact hl γ h

theorem IsComponentWord.append {l l' : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l)
    (hl' : IsComponentWord Ψ l') : IsComponentWord Ψ (l ++ l') := fun β hβ => by
  rcases List.mem_append.1 hβ with h | h
  · exact hl β h
  · exact hl' β h

theorem IsComponentWord.reverse {l : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l) :
    IsComponentWord Ψ l.reverse := fun β hβ => hl β (List.mem_reverse.1 hβ)

theorem IsComponentWord.sublist {l l' : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l)
    (h : l'.Sublist l) : IsComponentWord Ψ l' := fun β hβ => hl β (h.subset hβ)

theorem reflectionWordProd_inv
    {l : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l) :
    (reflectionWordProd l)⁻¹ = reflectionWordProd l.reverse := by
  induction l with
  | nil => simp [reflectionWordProd]
  | cons β l ih =>
    rw [reflectionWordProd_cons, mul_inv_rev, ih (fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)),
      List.reverse_cons, reflectionWordProd_append, reflectionWordProd_cons,
      reflectionWordProd_nil, mul_one, rootReflection_inv (simpleRoots_isRoot (hl β
        List.mem_cons_self))]

theorem reflectionWordProd_mem
    {l : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l) :
    reflectionWordProd l ∈ componentWeylGroup Ψ := by
  induction l with
  | nil => exact one_mem _
  | cons β l ih =>
    rw [reflectionWordProd_cons]
    exact mul_mem (rootReflection_mem_componentWeylGroup (hl β List.mem_cons_self))
      (ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ))

theorem mem_componentWeylGroup_iff
    {w : WeylGroup τ} :
    w ∈ componentWeylGroup Ψ ↔ ∃ l, IsComponentWord Ψ l ∧ reflectionWordProd l = w := by
  refine ⟨fun hw => ?_, fun ⟨l, hl, e⟩ => e ▸ reflectionWordProd_mem hl⟩
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact ⟨[β], fun γ hγ => by rw [List.mem_singleton.1 hγ]; exact hβ, by
      simp [reflectionWordProd]⟩
  | one => exact ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl', rfl⟩ := hy
    exact ⟨l ++ l', hl.append hl', reflectionWordProd_append l l'⟩
  | inv x _ hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨l.reverse, hl.reverse, (reflectionWordProd_inv hl).symm⟩

theorem exists_reduced_word
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    ∃ l, IsComponentWord Ψ l ∧ l.length = componentLength Ψ w ∧ reflectionWordProd l = w := by
  obtain ⟨l, hl, e⟩ := mem_componentWeylGroup_iff.1 hw
  have h : componentLength Ψ w ∈
      {n | ∃ l, IsComponentWord Ψ l ∧ l.length = n ∧ reflectionWordProd l = w} :=
    Nat.sInf_mem ⟨l.length, l, hl, rfl, e⟩
  exact h

theorem componentLength_le
    {l : List (Fin τ.rank → ℤ)} (hl : IsComponentWord Ψ l) :
    componentLength Ψ (reflectionWordProd l) ≤ l.length :=
  Nat.sInf_le ⟨l, hl, rfl, rfl⟩

theorem componentLength_one
    : componentLength Ψ (1 : WeylGroup τ) = 0 :=
  Nat.eq_zero_of_le_zero (componentLength_le (l := []) fun _ h => absurd h List.not_mem_nil)

theorem eq_one_of_componentLength_eq_zero
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ)
    (h : componentLength Ψ w = 0) : w = 1 := by
  obtain ⟨l, -, hlen, e⟩ := exists_reduced_word hw
  rw [h, List.length_eq_zero_iff] at hlen
  rw [← e, hlen, reflectionWordProd_nil]

theorem componentLength_inv
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    componentLength Ψ w⁻¹ = componentLength Ψ w := by
  have key : ∀ x ∈ componentWeylGroup Ψ, componentLength Ψ x⁻¹ ≤ componentLength Ψ x := by
    intro x hx
    obtain ⟨l, hl, hlen, e⟩ := exists_reduced_word hx
    rw [← hlen, ← e, reflectionWordProd_inv hl, ← List.length_reverse]
    exact componentLength_le hl.reverse
  refine le_antisymm (key w hw) ?_
  have := key w⁻¹ (inv_mem hw)
  rwa [inv_inv] at this

theorem componentLength_rootReflection_mul_le
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ)
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    componentLength Ψ (rootReflection β * w) ≤ componentLength Ψ w + 1 := by
  obtain ⟨l, hl, hlen, e⟩ := exists_reduced_word hw
  have := componentLength_le (hl.cons hβ)
  rwa [reflectionWordProd_cons, e, List.length_cons, hlen] at this

theorem prefix_succ
    {l : List (Fin τ.rank → ℤ)} {k : ℕ} (hk : k < l.length) :
    reflectionWordProd (l.take (k + 1)) = reflectionWordProd (l.take k) * rootReflection l[k] := by
  rw [List.take_succ_eq_append_getElem hk, reflectionWordProd_append]
  simp [reflectionWordProd]

theorem exists_eraseIdx_of_mem_negRoots
    (hΨ : IsRootComponent Ψ) {l : List (Fin τ.rank → ℤ)}
    (hl : IsComponentWord Ψ l) {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ)
    (hneg : (reflectionWordProd l)⁻¹ • β ∈ negRoots Ψ) :
    ∃ j < l.length, rootReflection β * reflectionWordProd l =
      reflectionWordProd (l.eraseIdx j) := by
  classical
  have hβr := simpleRoots_isRoot hβ
  have hβpos := simpleRoot_mem_posRoots hβ
  have hlne : l ≠ [] := by
    rintro rfl
    rw [reflectionWordProd_nil, inv_one, one_smul] at hneg
    exact not_mem_negRoots_of_mem_posRoots hβpos hneg
  have hex : ∃ k, k < l.length ∧ (reflectionWordProd (l.take (k + 1)))⁻¹ • β ∉ posRoots Ψ := by
    refine ⟨l.length - 1, by
      have := List.length_pos_iff.2 hlne
      omega, ?_⟩
    have : l.length - 1 + 1 = l.length := by
      have := List.length_pos_iff.2 hlne
      omega
    rw [this, List.take_length]
    exact fun h => not_mem_negRoots_of_mem_posRoots h hneg
  set j := Nat.find hex with hjdef
  obtain ⟨hjlt, hjneg⟩ := Nat.find_spec hex
  have hδj : (reflectionWordProd (l.take j))⁻¹ • β ∈ posRoots Ψ := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, List.take_zero, reflectionWordProd_nil, inv_one, one_smul]
      exact hβpos
    · have hmin := Nat.find_min hex (show j - 1 < j by omega)
      push Not at hmin
      have : j - 1 + 1 = j := by omega
      rw [this] at hmin
      exact hmin (by omega)
  have hlj : l[j] ∈ simpleRoots Ψ := hl _ (List.getElem_mem hjlt)
  have hljr := simpleRoots_isRoot hlj
  have hδeq : (reflectionWordProd (l.take j))⁻¹ • β = l[j] := by
    by_contra hne
    apply hjneg
    rw [prefix_succ hjlt, mul_inv_rev, rootReflection_inv hljr, mul_smul]
    exact (rootReflection_mem_posRoots hΨ hlj hδj hne).1
  set P := reflectionWordProd (l.take j) with hP
  have hr : rootReflection l[j] = P⁻¹ * rootReflection β * P := by
    rw [← hδeq, rootReflection_smul_root _ hβr, inv_inv]
  set Q := reflectionWordProd (l.drop (j + 1)) with hQ
  have hsplit : reflectionWordProd l = P * rootReflection l[j] * Q := by
    conv_lhs => rw [← List.take_append_drop (j + 1) l]
    rw [reflectionWordProd_append, prefix_succ hjlt]
  have herase : reflectionWordProd (l.eraseIdx j) = P * Q := by
    rw [List.eraseIdx_eq_take_drop_succ, reflectionWordProd_append]
  refine ⟨j, hjlt, ?_⟩
  rw [hsplit, herase, hr]
  calc rootReflection β * (P * (P⁻¹ * rootReflection β * P) * Q) =
      (rootReflection β * rootReflection β) * P * Q := by group
    _ = P * Q := by rw [rootReflection_mul_self hβr, one_mul]

theorem componentLength_rootReflection_mul_of_neg
    (hΨ : IsRootComponent Ψ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) (hneg : w⁻¹ • β ∈ negRoots Ψ) :
    componentLength Ψ (rootReflection β * w) = componentLength Ψ w - 1 ∧
      1 ≤ componentLength Ψ w := by
  obtain ⟨l, hl, hlen, rfl⟩ := exists_reduced_word hw
  obtain ⟨j, hj, hj'⟩ := exists_eraseIdx_of_mem_negRoots hΨ hl hβ hneg
  have h1 : componentLength Ψ (rootReflection β * reflectionWordProd l) ≤
      componentLength Ψ (reflectionWordProd l) - 1 := by
    rw [hj']
    refine (componentLength_le (hl.sublist (List.eraseIdx_sublist l j))).trans ?_
    rw [List.length_eraseIdx_of_lt hj, hlen]
  have h2 := componentLength_rootReflection_mul_le hβ (mul_mem
    (rootReflection_mem_componentWeylGroup hβ) hw)
  rw [← mul_assoc, rootReflection_mul_self (simpleRoots_isRoot hβ), one_mul] at h2
  have h3 : 1 ≤ componentLength Ψ (reflectionWordProd l) := by
    rw [← hlen]
    rcases l with _ | ⟨γ, l⟩
    · simp at hj
    · simp
  exact ⟨by omega, h3⟩

theorem componentLength_rootReflection_mul_of_pos
    (hΨ : IsRootComponent Ψ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) (hpos : w⁻¹ • β ∈ posRoots Ψ) :
    componentLength Ψ (rootReflection β * w) = componentLength Ψ w + 1 := by
  have hβr := simpleRoots_isRoot hβ
  have hw' : rootReflection β * w ∈ componentWeylGroup Ψ :=
    mul_mem (rootReflection_mem_componentWeylGroup hβ) hw
  have hneg : (rootReflection β * w)⁻¹ • β ∈ negRoots Ψ := by
    rw [mul_inv_rev, mul_smul, rootReflection_inv hβr, rootReflection_smul_self hβr, smul_neg]
    change -(-(w⁻¹ • β)) ∈ posRoots Ψ
    rwa [neg_neg]
  obtain ⟨h1, h2⟩ := componentLength_rootReflection_mul_of_neg hΨ hβ hw' hneg
  rw [← mul_assoc, rootReflection_mul_self hβr, one_mul] at h1
  omega

theorem componentLength_rootReflection_mul
    (hΨ : IsRootComponent Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    (componentLength Ψ (rootReflection β * w) = componentLength Ψ w - 1 ↔
      w⁻¹ • β ∈ negRoots Ψ) ∧
    (w⁻¹ • β ∉ negRoots Ψ →
      componentLength Ψ (rootReflection β * w) = componentLength Ψ w + 1) := by
  have hmem := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) β (simpleRoots_subset hβ)
  have hpos : w⁻¹ • β ∉ negRoots Ψ → w⁻¹ • β ∈ posRoots Ψ := fun h =>
    (mem_posRoots_or_mem_negRoots hΨ hmem).resolve_right h
  refine ⟨⟨fun h => ?_, fun h => (componentLength_rootReflection_mul_of_neg hΨ hβ hw h).1⟩,
    fun h => componentLength_rootReflection_mul_of_pos hΨ hβ hw (hpos h)⟩
  by_contra hn
  have := componentLength_rootReflection_mul_of_pos hΨ hβ hw (hpos hn)
  omega

theorem componentLength_mul_rootReflection
    (hΨ : IsRootComponent Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    (componentLength Ψ (w * rootReflection β) = componentLength Ψ w - 1 ↔
      w • β ∈ negRoots Ψ) ∧
    (w • β ∉ negRoots Ψ →
      componentLength Ψ (w * rootReflection β) = componentLength Ψ w + 1) := by
  have hβr := simpleRoots_isRoot hβ
  have hw' : w * rootReflection β ∈ componentWeylGroup Ψ :=
    mul_mem hw (rootReflection_mem_componentWeylGroup hβ)
  have e : componentLength Ψ (w * rootReflection β) =
      componentLength Ψ (rootReflection β * w⁻¹) := by
    rw [← componentLength_inv hw', mul_inv_rev, rootReflection_inv hβr]
  have h := componentLength_rootReflection_mul hΨ hβ (inv_mem hw)
  rw [inv_inv, componentLength_inv hw] at h
  rw [e]
  exact h

theorem exists_smul_mem_negRoots
    (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) (hne : w ≠ 1) :
    ∃ β ∈ simpleRoots Ψ, w • β ∈ negRoots Ψ := by
  obtain ⟨l, hl, hlen, e⟩ := exists_reduced_word hw
  have hl0 : l ≠ [] := by
    rintro rfl
    exact hne (by rw [← e, reflectionWordProd_nil])
  obtain ⟨l', β, hl'eq⟩ := (List.eq_nil_or_concat l).resolve_left hl0
  rw [List.concat_eq_append] at hl'eq
  subst hl'eq
  have hβ : β ∈ simpleRoots Ψ := hl β (List.mem_append_right _ (List.mem_singleton_self β))
  have hl' : IsComponentWord Ψ l' := hl.sublist (List.sublist_append_left _ _)
  refine ⟨β, hβ, ?_⟩
  have hle : componentLength Ψ (w * rootReflection β) ≤ componentLength Ψ w - 1 := by
    have he : w * rootReflection β = reflectionWordProd l' := by
      rw [← e, reflectionWordProd_append, mul_assoc]
      simp [reflectionWordProd, rootReflection_mul_self (simpleRoots_isRoot hβ)]
    rw [he, ← hlen, List.length_append, List.length_singleton, Nat.add_sub_cancel]
    exact componentLength_le hl'
  by_contra hn
  have := (componentLength_mul_rootReflection hΨ hβ hw).2 hn
  omega

theorem exists_longest
    (hΨ : IsRootComponent Ψ) :
    ∃ w₀ ∈ componentWeylGroup Ψ, (fun α => w₀ • α) '' posRoots Ψ = negRoots Ψ := by
  classical
  have hfin : (componentWeylGroup Ψ : Set (WeylGroup τ)).Finite := Set.toFinite _
  obtain ⟨w₀, hw₀, hmax⟩ := hfin.exists_maximalFor (componentLength Ψ) _
    ⟨1, one_mem (componentWeylGroup Ψ)⟩
  have hsimple : ∀ β ∈ simpleRoots Ψ, w₀ • β ∈ negRoots Ψ := by
    intro β hβ
    by_contra hn
    have h := (componentLength_mul_rootReflection hΨ hβ hw₀).2 hn
    have hw' : w₀ * rootReflection β ∈ componentWeylGroup Ψ :=
      mul_mem hw₀ (rootReflection_mem_componentWeylGroup hβ)
    have := hmax hw' (by omega)
    omega
  refine ⟨w₀, hw₀, Set.Subset.antisymm ?_ fun γ hγ => ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hα
    have hcoords : ∀ β ∈ simpleRoots Ψ, ∃ d : (Fin τ.rank → ℤ) → ℤ,
        (∀ δ ∈ simpleRoots Ψ, d δ ≤ 0) ∧ w₀ • β = ∑ δ ∈ simpleRoots Ψ, d δ • δ := by
      intro β hβ
      obtain ⟨d, hd, e'⟩ := exists_nonneg_coords hΨ (hsimple β hβ)
      refine ⟨-d, fun δ hδ => by simpa using hd δ hδ, ?_⟩
      rw [← neg_neg (w₀ • β), e', ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun δ _ => by rw [Pi.neg_apply, neg_smul]
    choose! d hd e' using hcoords
    have hw₀α : w₀ • α = ∑ δ ∈ simpleRoots Ψ, (∑ β ∈ simpleRoots Ψ, c β * d β δ) • δ := by
      rw [e, Finset.smul_sum]
      simp only [smul_comm w₀ (c _)]
      rw [Finset.sum_congr rfl fun β hβ => by rw [e' β hβ]]
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have hmem := smul_mem_of_mem_componentWeylGroup hΨ hw₀ α hα.1
    exact (coords_nonpos_iff hΨ hmem hw₀α).1 fun δ hδ =>
      Finset.sum_nonpos fun β hβ => mul_nonpos_of_nonneg_of_nonpos (hc β hβ) (hd β hβ δ hδ)
  · have hγΨ := ((mem_negRoots_iff hΨ).1 hγ).1
    have hmem := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw₀) γ hγΨ
    refine ⟨w₀⁻¹ • γ, ?_, smul_inv_smul w₀ γ⟩
    rcases mem_posRoots_or_mem_negRoots hΨ hmem with h | h
    · exact h
    · exfalso
      have h1 : -(w₀⁻¹ • γ) ∈ posRoots Ψ := h
      obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ h1
      have h2 := hsimple
      have himg : w₀ • -(w₀⁻¹ • γ) ∈ negRoots Ψ := by
        have hcoords : ∀ β ∈ simpleRoots Ψ, ∃ d : (Fin τ.rank → ℤ) → ℤ,
            (∀ δ ∈ simpleRoots Ψ, d δ ≤ 0) ∧ w₀ • β = ∑ δ ∈ simpleRoots Ψ, d δ • δ := by
          intro β hβ
          obtain ⟨d, hd, e'⟩ := exists_nonneg_coords hΨ (h2 β hβ)
          refine ⟨-d, fun δ hδ => by simpa using hd δ hδ, ?_⟩
          rw [← neg_neg (w₀ • β), e', ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun δ _ => by rw [Pi.neg_apply, neg_smul]
        choose! d hd e' using hcoords
        have hw₀α : w₀ • -(w₀⁻¹ • γ) =
            ∑ δ ∈ simpleRoots Ψ, (∑ β ∈ simpleRoots Ψ, c β * d β δ) • δ := by
          rw [e, Finset.smul_sum]
          simp only [smul_comm w₀ (c _)]
          rw [Finset.sum_congr rfl fun β hβ => by rw [e' β hβ]]
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          exact Finset.sum_comm
        have hmem' := smul_mem_of_mem_componentWeylGroup hΨ hw₀ _ h1.1
        exact (coords_nonpos_iff hΨ hmem' hw₀α).1 fun δ hδ =>
          Finset.sum_nonpos fun β hβ => mul_nonpos_of_nonneg_of_nonpos (hc β hβ) (hd β hβ δ hδ)
      rw [smul_neg, smul_inv_smul] at himg
      have h3 : 0 < height γ := by
        have := himg.2
        rwa [neg_neg] at this
      have h4 : 0 < height (-γ) := hγ.2
      rw [height_neg] at h4
      omega

theorem componentLength_braid
    (hΨ : IsRootComponent Ψ) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) (hne : β ≠ γ) (hβγ : iform β γ ≠ 0) :
    componentLength Ψ (rootReflection γ * rootReflection β * rootReflection γ) = 3 := by
  have hβr := simpleRoots_isRoot hβ
  have hγr := simpleRoots_isRoot hγ
  have hrβ := rootReflection_mem_componentWeylGroup hβ
  have hrγ := rootReflection_mem_componentWeylGroup hγ
  have h1 : componentLength Ψ (rootReflection γ) = 1 := by
    have := (componentLength_mul_rootReflection hΨ hγ (one_mem _)).2 (by
      rw [one_smul]
      exact not_mem_negRoots_of_mem_posRoots (simpleRoot_mem_posRoots hγ))
    rwa [one_mul, componentLength_one] at this
  have hrγβ : rootReflection γ • β ∈ posRoots Ψ :=
    (rootReflection_mem_posRoots hΨ hγ (simpleRoot_mem_posRoots hβ) hne).1
  have h2 : componentLength Ψ (rootReflection γ * rootReflection β) = 2 := by
    have := (componentLength_mul_rootReflection hΨ hβ hrγ).2
      (not_mem_negRoots_of_mem_posRoots hrγβ)
    rw [this, h1]
  have hrβγ : rootReflection β • γ ≠ γ := by
    intro h
    rw [rootReflection_smul hβr, sub_eq_self] at h
    have hk : corootPair β γ = 0 := by
      by_contra hk
      exact hγr.ne_zero (by
        have := congrArg (fun v => v) h
        rcases smul_eq_zero.1 h with h' | h'
        · exact absurd h' hk
        · exact absurd h' hβr.ne_zero)
    have := corootPair_mul hβr γ
    rw [hk, zero_mul] at this
    omega
  have hpos : (rootReflection γ * rootReflection β) • γ ∈ posRoots Ψ := by
    rw [mul_smul]
    exact (rootReflection_mem_posRoots hΨ hγ
      (rootReflection_mem_posRoots hΨ hβ (simpleRoot_mem_posRoots hγ) hne.symm).1 hrβγ).1
  have := (componentLength_mul_rootReflection hΨ hγ (mul_mem hrγ hrβ)).2
    (not_mem_negRoots_of_mem_posRoots hpos)
  rw [this, h2]

end CFSG.LieType.Chevalley
