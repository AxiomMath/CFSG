module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Graph

public section

namespace CFSG.ClassicalInvolution.Models

section Generation

variable {K : Type} [Field K] {n : ℕ} {G : Type*} [Group G] {mat : G →* Matrix (Fin n) (Fin n) K}
  {z : Pair n → G}

theorem zMat_mul_of_disjoint {N N' : Finset (Fin n)} (h : Disjoint N N') :
    zMat K n N * zMat K n N' = zMat K n (N ∪ N') := by
  rw [zMat, zMat, zMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases ha : a ∈ N
  · have : a ∉ N' := Finset.disjoint_left.mp h ha
    simp [ha, this]
  · by_cases ha' : a ∈ N' <;> simp [ha, ha']

theorem z_mem_signSubgroup (hz : ∀ T, mat (z T) = zMat K n T.1) (T : Pair n) :
    z T ∈ signSubgroup mat := by
  rw [mem_signSubgroup, hz]
  exact isSignDiag_zMat _

theorem z_injective (h2 : (2 : K) ≠ 0) (hz : ∀ T, mat (z T) = zMat K n T.1) :
    Function.Injective z := by
  intro T T' h
  exact Subtype.ext (zMat_inj h2 (by rw [← hz, ← hz, h]))

theorem z_ne_one (h2 : (2 : K) ≠ 0) (hz : ∀ T, mat (z T) = zMat K n T.1) (T : Pair n) :
    z T ≠ 1 := by
  intro h
  have h1 : zMat K n T.1 = zMat K n ∅ := by
    rw [zMat_empty, ← hz, h, map_one]
  have h3 := zMat_inj h2 h1
  have h4 := T.2
  rw [h3] at h4
  simp at h4

theorem exists_mem_closure_z (hz : ∀ T, mat (z T) = zMat K n T.1) (m : ℕ) :
    ∀ N : Finset (Fin n), N.card = m + m →
      ∃ x ∈ Subgroup.closure (Set.range z), mat x = zMat K n N := by
  induction m with
  | zero =>
    intro N hN
    have hN0 : N = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hN0]
    exact ⟨1, Subgroup.one_mem _, by rw [zMat_empty, map_one]⟩
  | succ m ih =>
    intro N hN
    obtain ⟨a, ha⟩ : N.Nonempty := Finset.card_pos.mp (by omega)
    have hc1 : (N.erase a).card = m + m + 1 := by
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ : (N.erase a).Nonempty := Finset.card_pos.mp (by omega)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbN : b ∈ N := Finset.mem_of_mem_erase hb
    have hc2 : ((N.erase a).erase b).card = m + m := by
      rw [Finset.card_erase_of_mem hb, hc1]
      omega
    obtain ⟨x', hx', hxm⟩ := ih _ hc2
    let T₀ : Pair n := ⟨{a, b}, Finset.card_pair hba.symm⟩
    refine ⟨z T₀ * x', Subgroup.mul_mem _ (Subgroup.subset_closure ⟨T₀, rfl⟩) hx', ?_⟩
    rw [map_mul, hxm, hz]
    have hdisj : Disjoint T₀.1 ((N.erase a).erase b) := by
      rw [Finset.disjoint_left]
      intro c hc
      simp only [T₀, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp
    rw [zMat_mul_of_disjoint hdisj]
    congr 1
    ext c
    simp only [T₀, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ((rfl | rfl) | ⟨_, _, h⟩)
      · exact ha
      · exact hbN
      · exact h
    · intro h
      by_cases hca : c = a
      · exact Or.inl (Or.inl hca)
      · by_cases hcb : c = b
        · exact Or.inl (Or.inr hcb)
        · exact Or.inr ⟨hcb, hca, h⟩

theorem closure_range_z (h2 : (2 : K) ≠ 0) (hinj : Function.Injective mat)
    (hdet : ∀ x : G, (mat x).det = 1) (hz : ∀ T, mat (z T) = zMat K n T.1) :
    Subgroup.closure (Set.range z) = signSubgroup mat := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨T, rfl⟩
    exact z_mem_signSubgroup hz T
  · intro e he
    obtain ⟨N, hN⟩ := (mem_signSubgroup.mp he).exists_zMat
    have hdet' : (-1 : K) ^ N.card = 1 := by
      rw [← det_zMat, ← hN]
      exact hdet e
    have hev : Even N.card :=
      (neg_one_pow_eq_one_iff_even (by intro h; apply h2; linear_combination -h)).mp hdet'
    obtain ⟨m, hm⟩ := hev
    obtain ⟨x, hx, hxN⟩ := exists_mem_closure_z hz m N hm
    have : x = e := hinj (hxN.trans hN.symm)
    rwa [this] at hx

theorem card_signSubgroup [Finite G] (h2 : (2 : K) ≠ 0) (hz : ∀ T, mat (z T) = zMat K n T.1)
    (hn : 4 ≤ n) : 8 ≤ Nat.card (signSubgroup mat) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  let T₁ : Pair n := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair h01⟩
  let T₂ : Pair n := ⟨{⟨2, by omega⟩, ⟨3, by omega⟩}, Finset.card_pair h23⟩
  have hd : Disjoint T₁.1 T₂.1 := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [T₁, T₂, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hc hc'
    omega
  have hc4 : (T₁.1 ∪ T₂.1).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, T₁.2, T₂.2]
  let w : G := z T₁ * z T₂
  have hw : mat w = zMat K n (T₁.1 ∪ T₂.1) := by
    rw [map_mul, hz, hz, zMat_mul_of_disjoint hd]
  have hwE : w ∈ signSubgroup mat :=
    (signSubgroup mat).mul_mem (z_mem_signSubgroup hz _) (z_mem_signSubgroup hz _)
  have h1w : (1 : G) ≠ w := by
    intro h
    have h' : zMat K n ∅ = zMat K n (T₁.1 ∪ T₂.1) := by
      rw [zMat_empty, ← hw, ← h, map_one]
    have h3 := zMat_inj h2 h'
    rw [← h3] at hc4
    simp at hc4
  have hwr : w ∉ Set.range z := by
    rintro ⟨T, hT⟩
    have h' : zMat K n T.1 = zMat K n (T₁.1 ∪ T₂.1) := by
      rw [← hw, ← hT, hz]
    have h3 := zMat_inj h2 h'
    have h4 := T.2
    rw [h3, hc4] at h4
    omega
  have h1r : (1 : G) ∉ Set.range z := fun ⟨T, hT⟩ => z_ne_one h2 hz T hT
  have h1r' : (1 : G) ∉ insert w (Set.range z) := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨h1w, h1r⟩
  have hcard : (insert (1 : G) (insert w (Set.range z))).ncard = n.choose 2 + 2 := by
    rw [Set.ncard_insert_of_notMem h1r', Set.ncard_insert_of_notMem hwr,
      Set.ncard_range_of_injective (z_injective h2 hz), natCard_pair]
  have hsub : insert (1 : G) (insert w (Set.range z)) ⊆ (signSubgroup mat : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | ⟨T, rfl⟩
    · exact (signSubgroup mat).one_mem
    · exact hwE
    · exact z_mem_signSubgroup hz T
  have h6 : 6 ≤ n.choose 2 := by
    calc 6 = Nat.choose 4 2 := by decide
      _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn
  calc 8 ≤ (insert (1 : G) (insert w (Set.range z))).ncard := by omega
    _ ≤ (signSubgroup mat : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (signSubgroup mat) := (Nat.card_coe_set_eq _).symm

end Generation

end CFSG.ClassicalInvolution.Models
