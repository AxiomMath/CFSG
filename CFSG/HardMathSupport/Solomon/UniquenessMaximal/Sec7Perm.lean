module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped Pointwise

variable {G : Type} [Group G]

theorem Permutable.symm {A B : Subgroup G} (h : Permutable A B) : Permutable B A :=
  Eq.symm h

theorem permutable_of_mul_subset {A B : Subgroup G} (h : (A : Set G) * B ⊆ B * A) :
    Permutable A B := by
  refine Set.Subset.antisymm h ?_
  rintro _ ⟨b, hb, a, ha, rfl⟩
  have h1 : a⁻¹ * b⁻¹ ∈ (A : Set G) * B := Set.mul_mem_mul (A.inv_mem ha) (B.inv_mem hb)
  obtain ⟨b', hb', a', ha', e⟩ := h h1
  refine ⟨a'⁻¹, A.inv_mem ha', b'⁻¹, B.inv_mem hb', ?_⟩
  have : (b * a)⁻¹ = b' * a' := by rw [mul_inv_rev]; exact e.symm
  calc a'⁻¹ * b'⁻¹ = (b' * a')⁻¹ := by rw [mul_inv_rev]
    _ = b * a := by rw [← this, inv_inv]

theorem Permutable.coe_sup {A B : Subgroup G} (h : Permutable A B) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * B := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have h1 : b * a' ∈ (B : Set G) * A := Set.mul_mem_mul hb ha'
        rw [← h] at h1
        obtain ⟨a'', ha'', b'', hb'', e⟩ := h1
        have e : a'' * b'' = b * a' := e
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        calc a * a'' * (b'' * b') = a * (a'' * b'') * b' := by simp only [mul_assoc]
          _ = a * (b * a') * b' := by rw [e]
          _ = a * b * (a' * b') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have h1 : b⁻¹ * a⁻¹ ∈ (B : Set G) * A := Set.mul_mem_mul (B.inv_mem hb) (A.inv_mem ha)
        rw [← h] at h1
        obtain ⟨a', ha', b', hb', e⟩ := h1
        have e : a' * b' = b⁻¹ * a⁻¹ := e
        exact ⟨a', ha', b', hb', by show a' * b' = (a * b)⁻¹; rw [e, mul_inv_rev]⟩ }
  have hS : A ⊔ B = S := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro a ha; exact ⟨a, ha, 1, B.one_mem, mul_one a⟩
    · intro b hb; exact ⟨1, A.one_mem, b, hb, one_mul b⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  rw [hS]
  rfl

theorem mul_subset_iSup {ι : Sort*} (K : Subgroup G) (S : ι → Subgroup G)
    (h : ∀ i, ∀ s ∈ S i, ∀ k ∈ K, ∃ x ∈ ⨆ i, S i, ∃ k' ∈ K, k * s = x * k') :
    ∀ x ∈ ⨆ i, S i, ∀ k ∈ K, ∃ y ∈ ⨆ i, S i, ∃ k' ∈ K, k * x = y * k' := by
  intro x hx
  refine Subgroup.iSup_induction S
    (C := fun x => ∀ k ∈ K, ∃ y ∈ ⨆ i, S i, ∃ k' ∈ K, k * x = y * k') hx h
    (fun k hk => ⟨1, Subgroup.one_mem _, k, hk, by simp⟩) ?_
  · intro x y hx hy k hk
    obtain ⟨a, ha, k', hk', e⟩ := hx k hk
    obtain ⟨b, hb, k'', hk'', e'⟩ := hy k' hk'
    refine ⟨a * b, Subgroup.mul_mem _ ha hb, k'', hk'', ?_⟩
    calc k * (x * y) = (k * x) * y := by rw [mul_assoc]
      _ = (a * k') * y := by rw [e]
      _ = a * (k' * y) := by rw [mul_assoc]
      _ = a * (b * k'') := by rw [e']
      _ = a * b * k'' := by rw [mul_assoc]

theorem Permutable.iSup {ι : Sort*} {K : Subgroup G} {S : ι → Subgroup G}
    (h : ∀ i, Permutable K (S i)) : Permutable K (⨆ i, S i) := by
  refine permutable_of_mul_subset ?_
  rintro _ ⟨k, hk, x, hx, rfl⟩
  have key := mul_subset_iSup K S (fun i s hs k hk => by
    have : k * s ∈ (K : Set G) * (S i) := Set.mul_mem_mul hk hs
    rw [h i] at this
    obtain ⟨s', hs', k', hk', e⟩ := this
    exact ⟨s', le_iSup S i hs', k', hk', e.symm⟩) x hx k hk
  obtain ⟨y, hy, k', hk', e⟩ := key
  exact ⟨y, hy, k', hk', e.symm⟩

theorem permutable_iSup_of_forall {ι : Sort*} {K : Subgroup G} (S : ι → Subgroup G)
    (h : ∀ i, ∀ s ∈ S i, ∀ k ∈ K, ∃ x ∈ ⨆ i, S i, ∃ k' ∈ K, k * s = x * k') :
    Permutable K (⨆ i, S i) := by
  refine permutable_of_mul_subset ?_
  rintro _ ⟨k, hk, x, hx, rfl⟩
  obtain ⟨y, hy, k', hk', e⟩ := mul_subset_iSup K S h x hx k hk
  exact ⟨y, hy, k', hk', e.symm⟩


theorem permutable_of_le_sup {K₀ K O M : Subgroup G} (hK₀ : K₀ ≤ K) (hK : K ≤ K₀ ⊔ O)
    (hO : K ≤ Subgroup.normalizer (O : Set G)) (hOM : O ≤ M) (hperm : Permutable K₀ M) :
    Permutable K M := by
  refine permutable_of_mul_subset ?_
  rintro _ ⟨k, hk, m, hm, rfl⟩
  have h1 : k ∈ ((O ⊔ K₀ : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hK hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O K₀ (hK₀.trans hO)] at h1
  obtain ⟨o, ho, k₀, hk₀, rfl⟩ := h1
  have h2 : k₀ * m ∈ (K₀ : Set G) * M := Set.mul_mem_mul hk₀ hm
  rw [hperm] at h2
  obtain ⟨m', hm', k₀', hk₀', e⟩ := h2
  have e : m' * k₀' = k₀ * m := e
  refine ⟨o * m', M.mul_mem (hOM ho) hm', k₀', hK₀ hk₀', ?_⟩
  show o * m' * k₀' = o * k₀ * m
  rw [mul_assoc, e, mul_assoc]

theorem permutable_of_normalizes {K₀ I O M : Subgroup G} (hK₀ : K₀ ≤ I) (hI : I ≤ K₀ ⊔ O)
    (hO : I ≤ Subgroup.normalizer (O : Set G)) (hM : M ≤ Subgroup.normalizer (I : Set G))
    (hOM : O ≤ M) : Permutable K₀ M := by
  refine permutable_of_mul_subset ?_
  rintro _ ⟨k, hk, m, hm, rfl⟩
  have h1 : m⁻¹ * k * m ∈ I := by
    have := (Subgroup.mem_normalizer_iff.1 (hM (M.inv_mem hm)) k).1 (hK₀ hk)
    simpa using this
  have h2 : m⁻¹ * k * m ∈ ((O ⊔ K₀ : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hI h1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O K₀ (hK₀.trans hO)] at h2
  obtain ⟨o, ho, k₀, hk₀, e⟩ := h2
  have e : o * k₀ = m⁻¹ * k * m := e
  refine ⟨m * o, M.mul_mem hm (hOM ho), k₀, hk₀, ?_⟩
  show m * o * k₀ = k * m
  rw [mul_assoc, e]
  group

theorem eq_top_of_mul_eq_top [IsSimpleGroup G] {A C Y : Subgroup G} (hY : Y ≠ ⊥) (hYA : Y ≤ A)
    (hCY : C ≤ Subgroup.normalizer (Y : Set G)) (h : ∀ g : G, ∃ a ∈ A, ∃ c ∈ C, g = a * c) :
    A = ⊤ := by
  have hN : Subgroup.normalClosure (Y : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (Y : Set G))
      with h1 | h1
    · exact absurd (le_bot_iff.1 (h1 ▸ Subgroup.subset_normalClosure)) hY
    · exact h1
  have hle : Subgroup.normalClosure (Y : Set G) ≤ A := by
    refine (Subgroup.closure_le A).2 ?_
    intro z hz
    obtain ⟨y, hy, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc
    obtain ⟨a, ha, c, hc', rfl⟩ := h g
    have h1 : c * y * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hCY hc') y).1 hy
    have h2 : a * (c * y * c⁻¹) * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha (hYA h1)) (A.inv_mem ha)
    have h3 : a * c * y * (a * c)⁻¹ = a * (c * y * c⁻¹) * a⁻¹ := by group
    rw [h3]
    exact h2
  rw [hN] at hle
  exact top_le_iff.1 hle

theorem sup_ne_top_of_permutable [IsSimpleGroup G] {K M : Subgroup G} (hperm : Permutable K M)
    (hM : M ≠ ⊤) {x : G} (hx : x ∈ M) (hx1 : x ≠ 1)
    (hKx : K ≤ Subgroup.centralizer ({x} : Set G)) : K ⊔ M ≠ ⊤ := by
  intro htop
  refine hM (eq_top_of_mul_eq_top (A := M) (C := K) (Y := Subgroup.zpowers x) ?_ ?_ ?_ ?_)
  · intro h
    exact hx1 (Subgroup.zpowers_eq_bot.1 h)
  · exact (Subgroup.zpowers_le).2 hx
  · intro g hg
    have hcomm : Commute x g := (Subgroup.mem_centralizer_singleton_iff.1 (hKx hg)).symm
    have : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (hcomm.zpow_left n).eq
    exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G) this
  · intro g
    have hg : g ∈ ((M ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, htop]; exact Subgroup.mem_top g
    rw [hperm.symm.coe_sup] at hg
    obtain ⟨a, ha, c, hc, e⟩ := hg
    exact ⟨a, ha, c, hc, e.symm⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
