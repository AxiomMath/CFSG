module

public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

set_option maxRecDepth 100000

theorem rank_F4 : Tag.F4.rank = 4 := rfl

@[expose] def idx (n : ℕ) (h : n < 4 := by decide) : Fin Tag.F4.rank := ⟨n, h⟩

abbrev V4 : Type := Fin Tag.F4.rank → ℤ

@[expose] def ipF4 (u v : V4) : ℤ :=
  4 * u (idx 0) * v (idx 0) - 2 * u (idx 0) * v (idx 1) - 2 * u (idx 1) * v (idx 0)
    + 4 * u (idx 1) * v (idx 1) - 2 * u (idx 1) * v (idx 2) - 2 * u (idx 2) * v (idx 1)
    + 2 * u (idx 2) * v (idx 2) - u (idx 2) * v (idx 3) - u (idx 3) * v (idx 2)
    + 2 * u (idx 3) * v (idx 3)

theorem sum_rank_F4 (f : Fin Tag.F4.rank → ℤ) :
    ∑ i, f i = f (idx 0) + f (idx 1) + f (idx 2) + f (idx 3) := by
  have h := Fintype.sum_equiv (finCongr rank_F4) f (fun i : Fin 4 => f ((finCongr rank_F4).symm i))
    (fun i => by simp)
  rw [h, Fin.sum_univ_four]
  rfl

theorem iform_F4 (u v : V4) : iform (τ := Tag.F4) u v = ipF4 u v := by
  unfold iform
  simp only [sum_rank_F4]
  have b00 : Tag.symmetrizedCartan Tag.F4 (idx 0) (idx 0) = 4 := by decide
  have b01 : Tag.symmetrizedCartan Tag.F4 (idx 0) (idx 1) = -2 := by decide
  have b02 : Tag.symmetrizedCartan Tag.F4 (idx 0) (idx 2) = 0 := by decide
  have b03 : Tag.symmetrizedCartan Tag.F4 (idx 0) (idx 3) = 0 := by decide
  have b10 : Tag.symmetrizedCartan Tag.F4 (idx 1) (idx 0) = -2 := by decide
  have b11 : Tag.symmetrizedCartan Tag.F4 (idx 1) (idx 1) = 4 := by decide
  have b12 : Tag.symmetrizedCartan Tag.F4 (idx 1) (idx 2) = -2 := by decide
  have b13 : Tag.symmetrizedCartan Tag.F4 (idx 1) (idx 3) = 0 := by decide
  have b20 : Tag.symmetrizedCartan Tag.F4 (idx 2) (idx 0) = 0 := by decide
  have b21 : Tag.symmetrizedCartan Tag.F4 (idx 2) (idx 1) = -2 := by decide
  have b22 : Tag.symmetrizedCartan Tag.F4 (idx 2) (idx 2) = 2 := by decide
  have b23 : Tag.symmetrizedCartan Tag.F4 (idx 2) (idx 3) = -1 := by decide
  have b30 : Tag.symmetrizedCartan Tag.F4 (idx 3) (idx 0) = 0 := by decide
  have b31 : Tag.symmetrizedCartan Tag.F4 (idx 3) (idx 1) = 0 := by decide
  have b32 : Tag.symmetrizedCartan Tag.F4 (idx 3) (idx 2) = -1 := by decide
  have b33 : Tag.symmetrizedCartan Tag.F4 (idx 3) (idx 3) = 2 := by decide
  simp only [b00, b01, b02, b03, b10, b11, b12, b13, b20, b21, b22, b23, b30, b31, b32, b33, ipF4]
  ring

@[expose] def kdot (k : Fin Tag.F4.rank → ℕ) (γ : V4) : ℤ :=
  (k (idx 0) : ℤ) * γ (idx 0) + (k (idx 1) : ℤ) * γ (idx 1) + (k (idx 2) : ℤ) * γ (idx 2)
    + (k (idx 3) : ℤ) * γ (idx 3)

@[expose] def vec4 (l : List ℤ) : V4 := fun i => l.getD i 0

@[expose] def ipL (u v : List ℤ) : ℤ :=
  4 * u.getD 0 0 * v.getD 0 0 - 2 * u.getD 0 0 * v.getD 1 0 - 2 * u.getD 1 0 * v.getD 0 0
    + 4 * u.getD 1 0 * v.getD 1 0 - 2 * u.getD 1 0 * v.getD 2 0 - 2 * u.getD 2 0 * v.getD 1 0
    + 2 * u.getD 2 0 * v.getD 2 0 - u.getD 2 0 * v.getD 3 0 - u.getD 3 0 * v.getD 2 0
    + 2 * u.getD 3 0 * v.getD 3 0

@[expose] def kdL (k0 k1 k2 k3 : ℕ) (u : List ℤ) : ℤ :=
  (k0 : ℤ) * u.getD 0 0 + (k1 : ℤ) * u.getD 1 0 + (k2 : ℤ) * u.getD 2 0 + (k3 : ℤ) * u.getD 3 0

theorem ipF4_vec4 (u v : List ℤ) : ipF4 (vec4 u) (vec4 v) = ipL u v := rfl

theorem kdot_vec4 (k : Fin Tag.F4.rank → ℕ) (u : List ℤ) :
    kdot k (vec4 u) = kdL (k (idx 0)) (k (idx 1)) (k (idx 2)) (k (idx 3)) u := rfl

@[expose] def rts : List (List ℤ) := Tag.F4.artifactRoots

theorem isRoot_F4_iff (γ : V4) : IsRoot Tag.F4 γ ↔ List.ofFn γ ∈ Tag.F4.artifactRoots :=
  isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := γ)

theorem mem_rts_iff (γ : V4) :
    IsRoot Tag.F4 γ ↔ ∃ l ∈ rts, vec4 l = γ := by
  refine (isRoot_F4_iff γ).trans ?_
  constructor
  · intro h
    refine ⟨List.ofFn γ, h, ?_⟩
    funext i
    simp only [vec4, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  · rintro ⟨l, hl, rfl⟩
    have hlen : l.length = 4 := length_of_mem_artifactRoots (τ := Tag.F4) hl
    have : List.ofFn (vec4 l) = l := by
      refine List.ext_getElem (by rw [List.length_ofFn, rank_F4, hlen]) fun n h1 h2 => ?_
      simp only [List.getElem_ofFn, vec4]
      rw [List.getD_eq_getElem l 0 (by omega)]
    exact this ▸ hl

theorem vec4_injOn :
    ∀ x ∈ rts, ∀ y ∈ rts, vec4 x = vec4 y → x = y := by
  intro x hx y hy h
  have hx4 : x.length = 4 := length_of_mem_artifactRoots (τ := Tag.F4) hx
  have hy4 : y.length = 4 := length_of_mem_artifactRoots (τ := Tag.F4) hy
  refine List.ext_getElem (by omega) fun n h1 h2 => ?_
  have := congrFun h ⟨n, by rw [rank_F4]; omega⟩
  simp only [vec4] at this
  rwa [List.getD_eq_getElem x 0 h1, List.getD_eq_getElem y 0 h2] at this

theorem ncard_roots_filter (P : V4 → Prop) [DecidablePred P] :
    {γ | IsRoot Tag.F4 γ ∧ P γ}.ncard =
      (rts.filter (fun l => decide (P (vec4 l)))).length := by
  have hset : {γ | IsRoot Tag.F4 γ ∧ P γ} =
      (((rts.filter (fun l => decide (P (vec4 l)))).map vec4 : List V4).toFinset : Set V4) := by
    ext γ
    simp only [Set.mem_setOf_eq, List.coe_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hγ, hP⟩
      obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      exact ⟨l, ⟨hl, hP⟩, rfl⟩
    · rintro ⟨l, ⟨hl, hP⟩, rfl⟩
      exact ⟨(mem_rts_iff _).2 ⟨l, hl, rfl⟩, hP⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun x hx y hy hxy => vec4_injOn x (List.mem_filter.1 hx).1 y
    (List.mem_filter.1 hy).1 hxy) ?_
  exact (nodup_artifactRoots Tag.F4).filter _

abbrev classifyP (k0 k1 k2 k3 : ℕ) : Prop :=
  (∃ e ∈ rts, ∀ γ ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → ipL γ e = 0) ∨
  ((∀ γ ∈ rts, ∀ γ' ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL k0 k1 k2 k3 γ' % 3 = 0 →
      ipL γ γ = ipL γ' γ' → ipL γ γ' ≠ 0) ∧
   (∀ γ ∈ rts, ∀ γ' ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL k0 k1 k2 k3 γ' % 3 = 0 →
      ipL γ γ ≠ ipL γ' γ' → ipL γ γ' = 0) ∧
   (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0 ∧ ipL γ γ = 4)).length = 6 ∧
   (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0 ∧ ipL γ γ = 2)).length = 6)

theorem classify_all : ∀ k0 ∈ [0, 1, 2], ∀ k1 ∈ [0, 1, 2], ∀ k2 ∈ [0, 1, 2], ∀ k3 ∈ [0, 1, 2],
    (k0 ≠ 0 ∨ k1 ≠ 0 ∨ k2 ≠ 0 ∨ k3 ≠ 0) → classifyP k0 k1 k2 k3 := by
  decide +kernel

structure KernelA2A2 (k : Fin Tag.F4.rank → ℕ) : Prop where
  same : ∀ γ γ' : V4, IsRoot Tag.F4 γ → IsRoot Tag.F4 γ' → kdot k γ % 3 = 0 →
    kdot k γ' % 3 = 0 → ipF4 γ γ = ipF4 γ' γ' → ipF4 γ γ' ≠ 0
  diff : ∀ γ γ' : V4, IsRoot Tag.F4 γ → IsRoot Tag.F4 γ' → kdot k γ % 3 = 0 →
    kdot k γ' % 3 = 0 → ipF4 γ γ ≠ ipF4 γ' γ' → ipF4 γ γ' = 0
  card_long : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4}.ncard = 6
  card_short : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2}.ncard = 6

theorem exists_ne_zero_idx {k : Fin Tag.F4.rank → ℕ} (hk0 : ∃ i, k i ≠ 0) :
    k (idx 0) ≠ 0 ∨ k (idx 1) ≠ 0 ∨ k (idx 2) ≠ 0 ∨ k (idx 3) ≠ 0 := by
  obtain ⟨⟨i, hi⟩, hik⟩ := hk0
  have hi' : i < 4 := hi
  interval_cases i
  · exact Or.inl hik
  · exact Or.inr (Or.inl hik)
  · exact Or.inr (Or.inr (Or.inl hik))
  · exact Or.inr (Or.inr (Or.inr hik))

theorem classify_kernel (k : Fin Tag.F4.rank → ℕ)
    (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0) :
    (∃ e : V4, IsRoot Tag.F4 e ∧ ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → ipF4 γ e = 0) ∨
      KernelA2A2 k := by
  have hne := exists_ne_zero_idx hk0
  have hm : ∀ n : ℕ, n < 3 → n ∈ [0, 1, 2] := fun n hn => by simp; omega
  have h := classify_all (k (idx 0)) (hm _ (hk3 _)) (k (idx 1)) (hm _ (hk3 _)) (k (idx 2))
    (hm _ (hk3 _)) (k (idx 3)) (hm _ (hk3 _)) hne
  rcases h with ⟨e, he, hall⟩ | ⟨hsame, hdiff, hlong, hshort⟩
  · left
    refine ⟨vec4 e, (mem_rts_iff _).2 ⟨e, he, rfl⟩, fun γ hγ hk => ?_⟩
    obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
    rw [ipF4_vec4]
    exact hall l hl (by rwa [kdot_vec4] at hk)
  · right
    refine ⟨fun γ γ' hγ hγ' hk hk' hlen => ?_, fun γ γ' hγ hγ' hk hk' hlen => ?_, ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      obtain ⟨l', hl', rfl⟩ := (mem_rts_iff γ').1 hγ'
      rw [kdot_vec4] at hk hk'
      rw [ipF4_vec4, ipF4_vec4] at hlen
      rw [ipF4_vec4]
      exact hsame l hl l' hl' hk hk' hlen
    · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      obtain ⟨l', hl', rfl⟩ := (mem_rts_iff γ').1 hγ'
      rw [kdot_vec4] at hk hk'
      rw [ipF4_vec4, ipF4_vec4] at hlen
      rw [ipF4_vec4]
      exact hdiff l hl l' hl' hk hk' hlen
    · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4)]
      exact hlong
    · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2)]
      exact hshort

abbrev uniqueP (k0 k1 k2 k3 : ℕ) : Prop :=
  ∀ b0 ∈ [0, 1, 2], ∀ b1 ∈ [0, 1, 2], ∀ b2 ∈ [0, 1, 2], ∀ b3 ∈ [0, 1, 2],
    (∀ γ ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL b0 b1 b2 b3 γ % 3 = 0) →
      ∃ m ∈ [0, 1, 2], b0 = (m * k0) % 3 ∧ b1 = (m * k1) % 3 ∧ b2 = (m * k2) % 3 ∧
        b3 = (m * k3) % 3

theorem unique_all : ∀ k0 ∈ [0, 1, 2], ∀ k1 ∈ [0, 1, 2], ∀ k2 ∈ [0, 1, 2], ∀ k3 ∈ [0, 1, 2],
    (k0 ≠ 0 ∨ k1 ≠ 0 ∨ k2 ≠ 0 ∨ k3 ≠ 0) → uniqueP k0 k1 k2 k3 := by
  decide +kernel

theorem bound_all : ∀ γ ∈ rts, ∀ σ ∈ rts, ipL γ σ ≤ ipL σ σ ∧ -ipL σ σ ≤ ipL γ σ := by
  decide +kernel

theorem unique_of_orth_kernel (k β : Fin Tag.F4.rank → ℕ)
    (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0) (hβ3 : ∀ i, β i < 3)
    (h : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → kdot β γ % 3 = 0) :
    ∃ m : ℕ, m < 3 ∧ ∀ i, β i = (m * k i) % 3 := by
  have hne := exists_ne_zero_idx hk0
  have hm : ∀ n : ℕ, n < 3 → n ∈ [0, 1, 2] := fun n hn => by simp; omega
  have hu := unique_all (k (idx 0)) (hm _ (hk3 _)) (k (idx 1)) (hm _ (hk3 _)) (k (idx 2))
    (hm _ (hk3 _)) (k (idx 3)) (hm _ (hk3 _)) hne
    (β (idx 0)) (hm _ (hβ3 _)) (β (idx 1)) (hm _ (hβ3 _)) (β (idx 2)) (hm _ (hβ3 _))
    (β (idx 3)) (hm _ (hβ3 _))
    (fun l hl hk => by
      have := h (vec4 l) ((mem_rts_iff _).2 ⟨l, hl, rfl⟩) (by rwa [kdot_vec4])
      rwa [kdot_vec4] at this)
  obtain ⟨m, hm3, e0, e1, e2, e3⟩ := hu
  refine ⟨m, by simp at hm3; omega, fun ⟨i, hi⟩ => ?_⟩
  have hi' : i < 4 := hi
  interval_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem pairing_bound {γ σ : V4} (hγ : IsRoot Tag.F4 γ)
    (hσ : IsRoot Tag.F4 σ) : ipF4 γ σ ≤ ipF4 σ σ ∧ -ipF4 σ σ ≤ ipF4 γ σ := by
  obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
  obtain ⟨l', hl', rfl⟩ := (mem_rts_iff σ).1 hσ
  rw [ipF4_vec4, ipF4_vec4]
  exact bound_all l hl l' hl'

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
