module

public import CFSG.ClassicalInvolution.WeakCT.SpSpThreeGlue
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock spEmbed range_spEmbed)
open CFSG.SeitzReduction.SymplecticPilot (spBlock spBlock_singleton range_sumMap_eq_planeCoords
  commute_of_mem_spBlock_of_disjoint)

variable {F : Type} [Field F] {G : Type} [Group G]

private theorem range_comp_spEmbed_eq_map_spBlock {m k : ℕ} (κ : StatedSp m F →* G)
    {σ : Fin k → Fin m} (hσ : Function.Injective σ) {N : Finset (Fin m)}
    (h : Set.range σ = N) : (κ.comp (spEmbed σ hσ)).range = (spBlock F N).map κ := by
  rw [MonoidHom.range_comp, range_spEmbed, range_sumMap_eq_planeCoords h]
  rfl

private theorem range_comp_longBlock_eq_map_spBlock {m : ℕ} (κ : StatedSp m F →* G)
    (k : Fin m) : (κ.comp (longBlock F m k)).range = (spBlock F {k}).map κ := by
  rw [MonoidHom.range_comp, spBlock_singleton]
  rfl

private theorem commute_map_spBlock_of_disjoint {m : ℕ} (κ : StatedSp m F →* G)
    {I J : Finset (Fin m)} (h : Disjoint I J) :
    ∀ a ∈ (spBlock F I).map κ, ∀ b ∈ (spBlock F J).map κ, a * b = b * a := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, (commute_of_mem_spBlock_of_disjoint h hx hy).eq]

private theorem commute_of_map_conj {A B A' B' : Subgroup G} (h : G)
    (hA : A.map (MulAut.conj h).toMonoidHom = A') (hB : B.map (MulAut.conj h).toMonoidHom = B')
    (hc : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have hA' : (MulAut.conj h) a ∈ A' := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem _ ha
  have hB' : (MulAut.conj h) b ∈ B' := by
    rw [← hB]
    exact Subgroup.mem_map_of_mem _ hb
  refine (MulAut.conj h).injective ?_
  rw [map_mul, map_mul]
  exact hc _ hA' _ hB'

private theorem commute_map_of_commute (φ : G →* G) {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ A.map φ, ∀ b ∈ B.map φ, a * b = b * a := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h x hx y hy]

private theorem range_comp_comp {A B : Type} [Group A] [Group B] (φ : G →* G) (κ : B →* G)
    (σ : A →* B) : ((φ.comp κ).comp σ).range = (κ.comp σ).range.map φ := by
  rw [MonoidHom.comp_assoc, MonoidHom.range_comp]

private abbrev win (s : ℕ) : Fin (s + 2) → Fin (s + 4) := Fin.castLE (by omega)

private abbrev rot (s : ℕ) : Equiv.Perm (Fin (s + 4)) := finRotate (s + 4)

private abbrev mu (s : ℕ) : Equiv.Perm (Fin (s + 4)) :=
  Equiv.swap (⟨2, by omega⟩ : Fin (s + 4)) ⟨s + 2, by omega⟩

private abbrev mu3 (s : ℕ) : Equiv.Perm (Fin (s + 4)) :=
  Equiv.swap (⟨3, by omega⟩ : Fin (s + 4)) ⟨s + 3, by omega⟩

private abbrev mu' (s : ℕ) : Equiv.Perm (Fin (s + 4)) := mu s * mu3 s

private abbrev PP (s : ℕ) : Finset (Fin (s + 2)) := {0, 1}

private abbrev T0 (s : ℕ) : Finset (Fin (s + 2)) := {0, 1, ⟨s + 1, by omega⟩}

private abbrev QQ (s : ℕ) : Finset (Fin (s + 2)) :=
  {⟨s, by omega⟩, ⟨s + 1, by omega⟩}

private abbrev Tq (s : ℕ) : Finset (Fin (s + 2)) :=
  {⟨s - 1, by omega⟩, ⟨s, by omega⟩, ⟨s + 1, by omega⟩}

private abbrev RR (s : ℕ) (hs : 3 ≤ s) : Finset (Fin (s + 2)) :=
  {⟨s + 1, by omega⟩, ⟨2, by omega⟩}

private abbrev Tr (s : ℕ) (hs : 3 ≤ s) : Finset (Fin (s + 2)) :=
  {⟨s, by omega⟩, ⟨s + 1, by omega⟩, ⟨2, by omega⟩}

private abbrev RR' (s : ℕ) (hs : 3 ≤ s) : Finset (Fin (s + 2)) :=
  {⟨2, by omega⟩, ⟨3, by omega⟩}

private abbrev Tr' (s : ℕ) (hs : 3 ≤ s) : Finset (Fin (s + 2)) :=
  {⟨s + 1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩}

private theorem swap_fix {s : ℕ} (a b x : Fin (s + 4)) (ha : (x : ℕ) ≠ (a : ℕ))
    (hb : (x : ℕ) ≠ (b : ℕ)) : Equiv.swap a b x = x := by
  have h1 : x ≠ a := fun h => ha (by rw [h])
  have h2 : x ≠ b := fun h => hb (by rw [h])
  exact Equiv.swap_apply_of_ne_of_ne h1 h2

private theorem rot_win_val (s : ℕ) (i : Fin (s + 2)) :
    ((rot s (win s i) : Fin (s + 4)) : ℕ) = (i : ℕ) + 1 := by
  have hw : (win s i : Fin (s + 4)) ≠ Fin.last (s + 3) := by
    intro h
    have h1 : ((win s i : Fin (s + 4)) : ℕ) = s + 3 := by rw [h, Fin.val_last]
    rw [Fin.val_castLE] at h1
    have := i.isLt
    omega
  rw [coe_finRotate, if_neg hw, Fin.val_castLE]

private theorem rot_win_mk {s : ℕ} {k : ℕ} (hk : k < s + 1) :
    rot s (win s (⟨k, by omega⟩ : Fin (s + 2))) =
      win s (⟨k + 1, by omega⟩ : Fin (s + 2)) := by
  apply Fin.ext
  rw [rot_win_val, Fin.val_castLE, Fin.val_mk]

private theorem rot_win_last (s : ℕ) :
    rot s (win s (⟨s + 1, by omega⟩ : Fin (s + 2))) =
      (⟨s + 2, by omega⟩ : Fin (s + 4)) := by
  apply Fin.ext
  rw [rot_win_val, Fin.val_mk]

private theorem rot_mk {s : ℕ} {k : ℕ} (hk : k < s + 3) :
    rot s (⟨k, by omega⟩ : Fin (s + 4)) = (⟨k + 1, by omega⟩ : Fin (s + 4)) := by
  apply Fin.ext
  have hne : (⟨k, by omega⟩ : Fin (s + 4)) ≠ Fin.last (s + 3) := by
    intro h
    have h1 : k = s + 3 := by simpa using congrArg Fin.val h
    omega
  rw [coe_finRotate, if_neg hne, Fin.val_mk]

private theorem mu_win_s1 (s : ℕ) (hs : 3 ≤ s) :
    mu s (win s (⟨s + 1, by omega⟩ : Fin (s + 2))) =
      win s (⟨s + 1, by omega⟩ : Fin (s + 2)) :=
  swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
    (win s (⟨s + 1, by omega⟩ : Fin (s + 2)))
    (by simp only [Fin.val_castLE]; omega)
    (by simp only [Fin.val_castLE]; omega)

private theorem mu_win_s (s : ℕ) (hs : 3 ≤ s) :
    mu s (win s (⟨s, by omega⟩ : Fin (s + 2))) =
      win s (⟨s, by omega⟩ : Fin (s + 2)) :=
  swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
    (win s (⟨s, by omega⟩ : Fin (s + 2)))
    (by simp only [Fin.val_castLE]; omega)
    (by simp only [Fin.val_castLE]; omega)

private theorem mu_s2 (s : ℕ) :
    mu s (⟨s + 2, by omega⟩ : Fin (s + 4)) = (⟨2, by omega⟩ : Fin (s + 4)) :=
  Equiv.swap_apply_right _ _

private theorem rot2_win_sm1 (s : ℕ) (hs : 3 ≤ s) :
    rot s (rot s (win s (⟨s - 1, by omega⟩ : Fin (s + 2)))) =
      win s (⟨s + 1, by omega⟩ : Fin (s + 2)) := by
  rw [rot_win_mk (k := s - 1) (by omega),
    show (⟨s - 1 + 1, by omega⟩ : Fin (s + 2)) = (⟨s, by omega⟩ : Fin (s + 2)) from
      Fin.ext (by simp; omega)]
  rw [rot_win_mk (k := s) (by omega)]

private theorem rot2_win_s (s : ℕ) :
    rot s (rot s (win s (⟨s, by omega⟩ : Fin (s + 2)))) =
      (⟨s + 2, by omega⟩ : Fin (s + 4)) := by
  rw [rot_win_mk (k := s) (by omega)]
  exact rot_win_last s

private theorem rot2_win_last (s : ℕ) :
    rot s (rot s (win s (⟨s + 1, by omega⟩ : Fin (s + 2)))) =
      (⟨s + 3, by omega⟩ : Fin (s + 4)) := by
  rw [rot_win_last]
  exact rot_mk (s := s) (k := s + 2) (by omega)

private theorem mu'_s2 (s : ℕ) (hs : 3 ≤ s) :
    mu' s (⟨s + 2, by omega⟩ : Fin (s + 4)) = (⟨2, by omega⟩ : Fin (s + 4)) := by
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  have h3 : mu3 s (⟨s + 2, by omega⟩ : Fin (s + 4)) = (⟨s + 2, by omega⟩ : Fin (s + 4)) :=
    swap_fix (⟨3, by omega⟩ : Fin (s + 4)) (⟨s + 3, by omega⟩ : Fin (s + 4))
      (⟨s + 2, by omega⟩ : Fin (s + 4))
      (by simp; omega) (by simp)
  rw [h3]
  exact congrArg Fin.val (mu_s2 s)

private theorem mu'_s3 (s : ℕ) (hs : 3 ≤ s) :
    mu' s (⟨s + 3, by omega⟩ : Fin (s + 4)) = (⟨3, by omega⟩ : Fin (s + 4)) := by
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  have h3 : mu3 s (⟨s + 3, by omega⟩ : Fin (s + 4)) = (⟨3, by omega⟩ : Fin (s + 4)) :=
    Equiv.swap_apply_right _ _
  rw [h3]
  have hfix : mu s (⟨3, by omega⟩ : Fin (s + 4)) = (⟨3, by omega⟩ : Fin (s + 4)) :=
    swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
      (⟨3, by omega⟩ : Fin (s + 4))
      (by simp) (by simp; omega)
  rw [hfix]

private theorem image_eq_self_of_fixed {α : Type} {f : α → α} {S : Set α}
    (h : ∀ x ∈ S, f x = x) : f '' S = S := by
  rw [Set.image_congr (f := f) (g := id) (fun x hx => h x hx), Set.image_id]

private theorem mu_image_P (s : ℕ) (hs : 3 ≤ s) :
    mu s '' (win s '' ↑(PP s)) = win s '' ↑(PP s) := by
  refine image_eq_self_of_fixed ?_
  rintro x ⟨i, hi, rfl⟩
  simp only [PP, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
      (win s 0) (by simp only [Fin.val_castLE, Fin.val_zero]; omega)
      (by simp only [Fin.val_castLE, Fin.val_zero]; omega)
  · exact swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
      (win s 1) (by simp only [Fin.val_castLE, Fin.val_one]; omega)
      (by simp only [Fin.val_castLE, Fin.val_one]; omega)

private theorem mu_image_T0 (s : ℕ) (hs : 3 ≤ s) :
    mu s '' (win s '' ↑(T0 s)) = win s '' ↑(T0 s) := by
  refine image_eq_self_of_fixed ?_
  rintro x ⟨i, hi, rfl⟩
  simp only [T0, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
      (win s 0) (by simp only [Fin.val_castLE, Fin.val_zero]; omega)
      (by simp only [Fin.val_castLE, Fin.val_zero]; omega)
  · exact swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
      (win s 1) (by simp only [Fin.val_castLE, Fin.val_one]; omega)
      (by simp only [Fin.val_castLE, Fin.val_one]; omega)
  · exact mu_win_s1 s hs

private theorem mu_rot_image_Q (s : ℕ) (hs : 3 ≤ s) :
    mu s '' (rot s '' (win s '' ↑(QQ s))) = win s '' ↑(RR s hs) := by
  ext x
  simp only [QQ, RR, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    rcases hq with rfl | rfl
    · refine ⟨⟨s + 1, by omega⟩, Or.inl rfl, ?_⟩
      rw [rot_win_mk (k := s) (by omega), mu_win_s1 s hs]
    · refine ⟨⟨2, by omega⟩, Or.inr rfl, ?_⟩
      rw [rot_win_last, mu_s2]
      exact Fin.ext rfl
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl
    · refine ⟨rot s (win s ⟨s, by omega⟩), ⟨win s ⟨s, by omega⟩,
        ⟨⟨s, by omega⟩, Or.inl rfl, rfl⟩, rfl⟩, ?_⟩
      rw [rot_win_mk (k := s) (by omega), mu_win_s1 s hs]
    · refine ⟨rot s (win s ⟨s + 1, by omega⟩), ⟨win s ⟨s + 1, by omega⟩,
        ⟨⟨s + 1, by omega⟩, Or.inr rfl, rfl⟩, rfl⟩, ?_⟩
      rw [rot_win_last, mu_s2]
      exact (Fin.ext rfl).symm

private theorem mu_rot_image_Tq (s : ℕ) (hs : 3 ≤ s) :
    mu s '' (rot s '' (win s '' ↑(Tq s))) = win s '' ↑(Tr s hs) := by
  ext x
  simp only [Tq, Tr, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    rcases hq with rfl | rfl | rfl
    · refine ⟨⟨s, by omega⟩, Or.inl rfl, ?_⟩
      rw [rot_win_mk (k := s - 1) (by omega),
        show (⟨s - 1 + 1, by omega⟩ : Fin (s + 2)) = (⟨s, by omega⟩ : Fin (s + 2)) from
          Fin.ext (by simp; omega), mu_win_s s hs]
    · refine ⟨⟨s + 1, by omega⟩, Or.inr (Or.inl rfl), ?_⟩
      rw [rot_win_mk (k := s) (by omega), mu_win_s1 s hs]
    · refine ⟨⟨2, by omega⟩, Or.inr (Or.inr rfl), ?_⟩
      rw [rot_win_last, mu_s2]
      exact Fin.ext rfl
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl | rfl
    · refine ⟨rot s (win s ⟨s - 1, by omega⟩), ⟨win s ⟨s - 1, by omega⟩,
        ⟨⟨s - 1, by omega⟩, Or.inl rfl, rfl⟩, rfl⟩, ?_⟩
      rw [rot_win_mk (k := s - 1) (by omega),
        show (⟨s - 1 + 1, by omega⟩ : Fin (s + 2)) = (⟨s, by omega⟩ : Fin (s + 2)) from
          Fin.ext (by simp; omega), mu_win_s s hs]
    · refine ⟨rot s (win s ⟨s, by omega⟩), ⟨win s ⟨s, by omega⟩,
        ⟨⟨s, by omega⟩, Or.inr (Or.inl rfl), rfl⟩, rfl⟩, ?_⟩
      rw [rot_win_mk (k := s) (by omega), mu_win_s1 s hs]
    · refine ⟨rot s (win s ⟨s + 1, by omega⟩), ⟨win s ⟨s + 1, by omega⟩,
        ⟨⟨s + 1, by omega⟩, Or.inr (Or.inr rfl), rfl⟩, rfl⟩, ?_⟩
      rw [rot_win_last, mu_s2]
      exact (Fin.ext rfl).symm

private theorem mu'_fix_win {s : ℕ} {i : Fin (s + 2)} (h2 : (i : ℕ) ≠ 2)
    (h3 : (i : ℕ) ≠ 3) (hs2 : (i : ℕ) ≠ s + 2) (hs3 : (i : ℕ) ≠ s + 3) :
    mu' s (win s i) = win s i := by
  rw [mu', Equiv.Perm.mul_apply]
  rw [swap_fix (⟨3, by omega⟩ : Fin (s + 4)) (⟨s + 3, by omega⟩ : Fin (s + 4))
        (win s i)
        (by simpa using h3)
        (by simpa using hs3),
      swap_fix (⟨2, by omega⟩ : Fin (s + 4)) (⟨s + 2, by omega⟩ : Fin (s + 4))
        (win s i)
        (by simpa using h2)
        (by simpa using hs2)]

private theorem mu'_image_P (s : ℕ) (_hs : 3 ≤ s) :
    mu' s '' (win s '' ↑(PP s)) = win s '' ↑(PP s) := by
  refine image_eq_self_of_fixed ?_
  rintro x ⟨i, hi, rfl⟩
  simp only [PP, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine mu'_fix_win (i := (0 : Fin (s + 2))) ?_ ?_ (by omega) (by omega)
    · simp
    · simp
  · refine mu'_fix_win (i := (1 : Fin (s + 2))) ?_ ?_ (by omega) (by omega)
    · simp
    · simp

private theorem mu'_image_T0 (s : ℕ) (hs : 3 ≤ s) :
    mu' s '' (win s '' ↑(T0 s)) = win s '' ↑(T0 s) := by
  refine image_eq_self_of_fixed ?_
  rintro x ⟨i, hi, rfl⟩
  simp only [T0, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · refine mu'_fix_win (i := (0 : Fin (s + 2))) ?_ ?_ (by omega) (by omega)
    · simp
    · simp
  · refine mu'_fix_win (i := (1 : Fin (s + 2))) ?_ ?_ (by omega) (by omega)
    · simp
    · simp
  · exact mu'_fix_win (i := (⟨s + 1, by omega⟩ : Fin (s + 2)))
      (by simp; omega) (by simp; omega)
      (by simp) (by simp)

private theorem mu'_rot2_image_Q (s : ℕ) (hs : 3 ≤ s) :
    mu' s '' (rot s '' (rot s '' (win s '' ↑(QQ s)))) = win s '' ↑(RR' s hs) := by
  ext x
  simp only [QQ, RR', Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, ⟨w, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rcases hq with rfl | rfl
    · refine ⟨⟨2, by omega⟩, Or.inl rfl, ?_⟩
      rw [rot2_win_s, mu'_s2 s hs]
      exact Fin.ext rfl
    · refine ⟨⟨3, by omega⟩, Or.inr rfl, ?_⟩
      rw [rot2_win_last, mu'_s3 s hs]
      exact Fin.ext rfl
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl
    · refine ⟨rot s (rot s (win s ⟨s, by omega⟩)), ⟨rot s (win s ⟨s, by omega⟩),
        ⟨win s ⟨s, by omega⟩, ⟨⟨s, by omega⟩, Or.inl rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [rot2_win_s, mu'_s2 s hs]
      exact (Fin.ext rfl).symm
    · refine ⟨rot s (rot s (win s ⟨s + 1, by omega⟩)), ⟨rot s (win s ⟨s + 1, by omega⟩),
        ⟨win s ⟨s + 1, by omega⟩, ⟨⟨s + 1, by omega⟩, Or.inr rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [rot2_win_last, mu'_s3 s hs]
      exact (Fin.ext rfl).symm

private theorem mu'_rot2_image_Tq (s : ℕ) (hs : 3 ≤ s) :
    mu' s '' (rot s '' (rot s '' (win s '' ↑(Tq s)))) = win s '' ↑(Tr' s hs) := by
  ext x
  simp only [Tq, Tr', Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, ⟨w, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rcases hq with rfl | rfl | rfl
    · refine ⟨⟨s + 1, by omega⟩, Or.inl rfl, ?_⟩
      rw [rot2_win_sm1 s hs]
      exact (mu'_fix_win (i := (⟨s + 1, by omega⟩ : Fin (s + 2)))
        (by simp; omega) (by simp; omega)
        (by simp) (by simp)).symm
    · refine ⟨⟨2, by omega⟩, Or.inr (Or.inl rfl), ?_⟩
      rw [rot2_win_s, mu'_s2 s hs]
      exact Fin.ext rfl
    · refine ⟨⟨3, by omega⟩, Or.inr (Or.inr rfl), ?_⟩
      rw [rot2_win_last, mu'_s3 s hs]
      exact Fin.ext rfl
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl | rfl
    · refine ⟨rot s (rot s (win s ⟨s - 1, by omega⟩)),
        ⟨rot s (win s ⟨s - 1, by omega⟩),
        ⟨win s ⟨s - 1, by omega⟩, ⟨⟨s - 1, by omega⟩, Or.inl rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [rot2_win_sm1 s hs]
      exact mu'_fix_win (i := (⟨s + 1, by omega⟩ : Fin (s + 2)))
        (by simp; omega) (by simp; omega)
        (by simp) (by simp)
    · refine ⟨rot s (rot s (win s ⟨s, by omega⟩)), ⟨rot s (win s ⟨s, by omega⟩),
        ⟨win s ⟨s, by omega⟩, ⟨⟨s, by omega⟩, Or.inr (Or.inl rfl), rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [rot2_win_s, mu'_s2 s hs]
      exact (Fin.ext rfl).symm
    · refine ⟨rot s (rot s (win s ⟨s + 1, by omega⟩)), ⟨rot s (win s ⟨s + 1, by omega⟩),
        ⟨win s ⟨s + 1, by omega⟩, ⟨⟨s + 1, by omega⟩, Or.inr (Or.inr rfl), rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [rot2_win_last, mu'_s3 s hs]
      exact (Fin.ext rfl).symm

private abbrev N0 (s : ℕ) : Finset (Fin (s + 2)) := {⟨s + 1, by omega⟩}ᶜ

private abbrev N1 (s : ℕ) : Finset (Fin (s + 2)) := {0}ᶜ

private theorem range_succ_eq_N1 (s : ℕ) :
    Set.range (Fin.succ : Fin (s + 1) → Fin (s + 2)) = ↑(N1 s) := by
  rw [Fin.range_succ, N1, Finset.coe_compl, Finset.coe_singleton]

private theorem range_castSucc_eq_N0 (s : ℕ) :
    Set.range (Fin.castSucc : Fin (s + 1) → Fin (s + 2)) = ↑(N0 s) := by
  rw [Fin.range_castSucc, N0, Finset.coe_compl, Finset.coe_singleton]
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro h rfl
    simp at h
  · intro hi
    have h : (i : ℕ) < s + 1 := by
      have := i.isLt
      by_contra hge
      refine hi (Fin.ext ?_)
      show (i : ℕ) = s + 1
      omega
    exact h

private theorem rot_win_image_N0 (s : ℕ) :
    rot s '' (win s '' ↑(N0 s)) = win s '' ↑(N1 s) := by
  rw [Set.image_image]
  ext x
  simp only [N0, N1, Finset.mem_coe, Finset.mem_compl, Finset.mem_singleton, Set.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hk : (i : ℕ) < s + 1 := by
      have := i.isLt
      by_contra hge
      refine hi (Fin.ext ?_)
      show (i : ℕ) = s + 1
      omega
    have hrot : rot s (win s i) =
        win s (⟨(i : ℕ) + 1, by omega⟩ : Fin (s + 2)) := by
      apply Fin.ext
      rw [rot_win_val]
      rw [Fin.val_castLE]
    refine ⟨⟨(i : ℕ) + 1, by omega⟩, ?_, hrot.symm⟩
    intro h
    have hv : (i : ℕ) + 1 = 0 := by simpa using congrArg Fin.val h
    omega
  · rintro ⟨j, hj, rfl⟩
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      exact hj (Fin.ext h)
    have hk : (j : ℕ) - 1 < s + 1 := by
      have := j.isLt
      omega
    have hrot : rot s (win s (⟨(j : ℕ) - 1, by omega⟩ : Fin (s + 2))) =
        win s (⟨((j : ℕ) - 1) + 1, by omega⟩ : Fin (s + 2)) := by
      apply Fin.ext
      rw [rot_win_val]
      rw [Fin.val_castLE]
    refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_, ?_⟩
    · intro h
      have hidx : (⟨(j : ℕ) - 1, by omega⟩ : Fin (s + 2)) = (⟨s + 1, by omega⟩ : Fin (s + 2)) :=
        Fin.castLE_injective (by omega) h
      have hv : (j : ℕ) - 1 = s + 1 := congrArg Fin.val hidx
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
      have := j.isLt
      omega
    · rw [hrot]
      congr 1
      apply Fin.ext
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
      have := j.isLt
      simp; omega

private theorem rot_win_image_singleton_castSucc (s : ℕ) (j : Fin (s + 1)) :
    rot s '' (win s '' ↑({j.castSucc} : Finset (Fin (s + 2)))) =
      win s '' ↑({j.succ} : Finset (Fin (s + 2))) := by
  have hk : (j : ℕ) < s + 1 := j.isLt
  have hrot : rot s (win s (j.castSucc : Fin (s + 2))) = win s (j.succ : Fin (s + 2)) := by
    apply Fin.ext
    rw [rot_win_val]
    rw [Fin.val_castLE]
    rw [Fin.val_castSucc, Fin.val_succ]
  rw [Finset.coe_singleton, Set.image_singleton, Set.image_singleton,
    Finset.coe_singleton, Set.image_singleton, hrot]

variable {s : ℕ} {κ : StatedSp (s + 2) F →* G} {Y : Set (Fin (s + 4)) → Subgroup G}
  {X : Set (Fin (s + 4)) → Set (Fin (s + 4)) → Subgroup G}

private theorem card_N0 (s : ℕ) (hs : 2 ≤ s) : 3 ≤ (N0 s).card := by
  rw [N0, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  omega

private theorem card_N1 (s : ℕ) (hs : 2 ≤ s) : 3 ≤ (N1 s).card := by
  rw [N1, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  omega

private theorem ne_N0 (s : ℕ) : N0 s ≠ Finset.univ := by
  intro h
  have hmem : (⟨s + 1, by omega⟩ : Fin (s + 2)) ∈ N0 s := by
    rw [h]
    exact Finset.mem_univ _
  have hnot : (⟨s + 1, by omega⟩ : Fin (s + 2)) ∉ N0 s := by
    simp [N0]
  exact hnot hmem

private theorem ne_N1 (s : ℕ) : N1 s ≠ Finset.univ := by
  intro h
  have hmem : (0 : Fin (s + 2)) ∈ N1 s := by
    rw [h]
    exact Finset.mem_univ _
  have hnot : (0 : Fin (s + 2)) ∉ N1 s := by
    simp [N1]
  exact hnot hmem

private theorem window_overlap_short (hs : 2 ≤ s)
    (hY : ∀ N : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ →
      Y (win s '' ↑N) = (spBlock F N).map κ)
    {g : G} (hgY : ∀ S, (Y S).map (MulAut.conj g).toMonoidHom = Y (finRotate (s + 4) '' S)) :
    (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      (((MulAut.conj g).toMonoidHom.comp κ).comp
        (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range := by
  have hN0card : 3 ≤ (N0 s).card := card_N0 s hs
  have hN1card : 3 ≤ (N1 s).card := card_N1 s hs
  have hN0ne : N0 s ≠ Finset.univ := ne_N0 s
  have hN1ne : N1 s ≠ Finset.univ := ne_N1 s
  rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.succ_injective (s + 1)) (range_succ_eq_N1 s)]
  rw [range_comp_comp (MulAut.conj g).toMonoidHom κ
    (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))]
  rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.castSucc_injective (s + 1))
    (range_castSucc_eq_N0 s)]
  rw [← hY (N1 s) hN1card hN1ne, ← hY (N0 s) hN0card hN0ne, hgY]
  rw [rot_win_image_N0]

private theorem window_overlap_long (hs : 2 ≤ s)
    (hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N → I.card ≤ 2 →
      X (win s '' ↑I) (win s '' ↑N) = (spBlock F I).map κ)
    {g : G} (hgX : ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom =
      X (finRotate (s + 4) '' S) (finRotate (s + 4) '' T)) :
    ∀ j : Fin (s + 1), (κ.comp (longBlock F (s + 2) j.succ)).range =
      (((MulAut.conj g).toMonoidHom.comp κ).comp
        (longBlock F (s + 2) j.castSucc)).range := by
  intro j
  have hN0card : 3 ≤ (N0 s).card := card_N0 s hs
  have hN1card : 3 ≤ (N1 s).card := card_N1 s hs
  have hN0ne : N0 s ≠ Finset.univ := ne_N0 s
  have hN1ne : N1 s ≠ Finset.univ := ne_N1 s
  have hsucc_sub : ({j.succ} : Finset (Fin (s + 2))) ⊆ N1 s := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [N1, Finset.mem_compl, Finset.mem_singleton]
    intro hh
    have hv : (j : ℕ) + 1 = 0 := by
      simpa [Fin.val_succ] using congrArg Fin.val hh
    omega
  have hcast_sub : ({j.castSucc} : Finset (Fin (s + 2))) ⊆ N0 s := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [N0, Finset.mem_compl, Finset.mem_singleton]
    intro hh
    have hv : (j : ℕ) = s + 1 := by
      simpa using congrArg Fin.val hh
    have := j.isLt
    omega
  rw [range_comp_longBlock_eq_map_spBlock κ j.succ]
  rw [range_comp_comp (MulAut.conj g).toMonoidHom κ (longBlock F (s + 2) j.castSucc)]
  rw [range_comp_longBlock_eq_map_spBlock κ j.castSucc]
  rw [← hX (N1 s) {j.succ} hN1card hN1ne hsucc_sub (by simp),
    ← hX (N0 s) {j.castSucc} hN0card hN0ne hcast_sub (by simp)]
  rw [hgX]
  rw [rot_win_image_singleton_castSucc, rot_win_image_N0]

private theorem window_overlap (hs : 2 ≤ s)
    (hY : ∀ N : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ →
      Y (win s '' ↑N) = (spBlock F N).map κ)
    (hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N → I.card ≤ 2 →
      X (win s '' ↑I) (win s '' ↑N) = (spBlock F I).map κ)
    {g : G} (hgY : ∀ S, (Y S).map (MulAut.conj g).toMonoidHom = Y (finRotate (s + 4) '' S))
    (hgX : ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom =
      X (finRotate (s + 4) '' S) (finRotate (s + 4) '' T)) :
    (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
        (((MulAut.conj g).toMonoidHom.comp κ).comp
          (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range ∧
      ∀ j : Fin (s + 1), (κ.comp (longBlock F (s + 2) j.succ)).range =
        (((MulAut.conj g).toMonoidHom.comp κ).comp (longBlock F (s + 2) j.castSucc)).range :=
  ⟨window_overlap_short hs hY hgY, window_overlap_long hs hX hgX⟩

private theorem range_castLE_two (s : ℕ) :
    Set.range (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2)) = ↑(PP s) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · simp only [PP, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      left
      apply Fin.ext
      rfl
    · simp only [PP, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      right
      apply Fin.ext
      rfl
  · intro hx
    simp only [PP, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem range_natAdd (s : ℕ) :
    Set.range (Fin.natAdd s : Fin 2 → Fin (s + 2)) = ↑(QQ s) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [QQ, Fin.natAdd]
  · intro hx
    simp only [QQ, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp [Fin.natAdd]⟩
    · exact ⟨1, by simp [Fin.natAdd]⟩

private theorem card_T0 (s : ℕ) (hs : 3 ≤ s) : 3 ≤ (T0 s).card := by
  have h : (T0 s).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨0, 1, (⟨s + 1, by omega⟩ : Fin (s + 2)), ?_, ?_, ?_, rfl⟩
    · intro hh
      have hv : (0 : ℕ) = 1 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : (0 : ℕ) = s + 1 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : (1 : ℕ) = s + 1 := by simpa using congrArg Fin.val hh
      omega
  omega

private theorem card_Tq (s : ℕ) (hs : 3 ≤ s) : 3 ≤ (Tq s).card := by
  have h : (Tq s).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨(⟨s - 1, by omega⟩ : Fin (s + 2)), (⟨s, by omega⟩ : Fin (s + 2)),
      (⟨s + 1, by omega⟩ : Fin (s + 2)), ?_, ?_, ?_, rfl⟩
    · intro hh
      have hv : s - 1 = s := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : s - 1 = s + 1 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : s = s + 1 := by simpa using congrArg Fin.val hh
      omega
  omega

private theorem card_Tr (s : ℕ) (hs : 3 ≤ s) : 3 ≤ (Tr s hs).card := by
  have h : (Tr s hs).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨(⟨s, by omega⟩ : Fin (s + 2)), (⟨s + 1, by omega⟩ : Fin (s + 2)),
      (⟨2, by omega⟩ : Fin (s + 2)), ?_, ?_, ?_, rfl⟩
    · intro hh
      have hv : s = s + 1 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : s = 2 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : s + 1 = 2 := by simpa using congrArg Fin.val hh
      omega
  omega

private theorem card_Tr' (s : ℕ) (hs : 3 ≤ s) : 3 ≤ (Tr' s hs).card := by
  have h : (Tr' s hs).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨(⟨s + 1, by omega⟩ : Fin (s + 2)), (⟨2, by omega⟩ : Fin (s + 2)),
      (⟨3, by omega⟩ : Fin (s + 2)), ?_, ?_, ?_, rfl⟩
    · intro hh
      have hv : s + 1 = 2 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : s + 1 = 3 := by simpa using congrArg Fin.val hh
      omega
    · intro hh
      have hv : (2 : ℕ) = 3 := by simpa using congrArg Fin.val hh
      omega
  omega

private theorem ne_univ_of_card_le_three (s : ℕ) (hs : 3 ≤ s) {N : Finset (Fin (s + 2))}
    (hN : N.card ≤ 3) : N ≠ Finset.univ := by
  intro h
  have hle : (Finset.univ : Finset (Fin (s + 2))).card ≤ 3 := by
    rw [← h]
    exact hN
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

private theorem ne_T0 (s : ℕ) (hs : 3 ≤ s) : T0 s ≠ Finset.univ :=
  ne_univ_of_card_le_three s hs (by rw [T0]; exact Finset.card_le_three)

private theorem ne_Tq (s : ℕ) (hs : 3 ≤ s) : Tq s ≠ Finset.univ :=
  ne_univ_of_card_le_three s hs (by rw [Tq]; exact Finset.card_le_three)

private theorem ne_Tr (s : ℕ) (hs : 3 ≤ s) : Tr s hs ≠ Finset.univ :=
  ne_univ_of_card_le_three s hs (by rw [Tr]; exact Finset.card_le_three)

private theorem ne_Tr' (s : ℕ) (hs : 3 ≤ s) : Tr' s hs ≠ Finset.univ :=
  ne_univ_of_card_le_three s hs (by rw [Tr']; exact Finset.card_le_three)

private theorem subset_P_T0 (s : ℕ) : PP s ⊆ T0 s := by
  intro x hx
  simp only [PP, T0, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem subset_Q_Tq (s : ℕ) : QQ s ⊆ Tq s := by
  intro x hx
  simp only [QQ, Tq, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem subset_R_Tr (s : ℕ) (hs : 3 ≤ s) : RR s hs ⊆ Tr s hs := by
  intro x hx
  simp only [RR, Tr, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem subset_R'_Tr' (s : ℕ) (hs : 3 ≤ s) : RR' s hs ⊆ Tr' s hs := by
  intro x hx
  simp only [RR', Tr', Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem disjoint_P_R (s : ℕ) (hs : 3 ≤ s) : Disjoint (PP s) (RR s hs) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [PP, RR, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
    (have hv := congrArg Fin.val h
     simp only [Fin.val_zero, Fin.val_one] at hv
     omega)

private theorem disjoint_P_R' (s : ℕ) (hs : 3 ≤ s) : Disjoint (PP s) (RR' s hs) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [PP, RR', Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
    (have hv := congrArg Fin.val h
     simp only [Fin.val_zero, Fin.val_one] at hv
     omega)

private theorem card_P (s : ℕ) : (PP s).card ≤ 2 := Finset.card_le_two

private theorem card_Q (s : ℕ) : (QQ s).card ≤ 2 := Finset.card_le_two

private theorem card_R (s : ℕ) (hs : 3 ≤ s) : (RR s hs).card ≤ 2 := Finset.card_le_two

private theorem card_R' (s : ℕ) (hs : 3 ≤ s) : (RR' s hs).card ≤ 2 := Finset.card_le_two

private theorem window_cross (hs : 3 ≤ s)
    (hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N → I.card ≤ 2 →
      X (win s '' ↑I) (win s '' ↑N) = (spBlock F I).map κ)
    {g : G} (hgX : ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom =
      X (finRotate (s + 4) '' S) (finRotate (s + 4) '' T))
    {h : G} (hhX : ∀ S T, (X S T).map (MulAut.conj h).toMonoidHom =
      X (Equiv.swap (⟨2, by omega⟩ : Fin (s + 4)) ⟨s + 2, by omega⟩ '' S)
        (Equiv.swap (⟨2, by omega⟩ : Fin (s + 4)) ⟨s + 2, by omega⟩ '' T)) :
    ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (((MulAut.conj g).toMonoidHom.comp κ).comp
        (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))).range,
        a * b = b * a := by
  have hT0card : 3 ≤ (T0 s).card := card_T0 s hs
  have hT0ne : T0 s ≠ Finset.univ := ne_T0 s hs
  have hPsub : PP s ⊆ T0 s := subset_P_T0 s
  have hPcard : (PP s).card ≤ 2 := card_P s
  have hTqcard : 3 ≤ (Tq s).card := card_Tq s hs
  have hTqne : Tq s ≠ Finset.univ := ne_Tq s hs
  have hQsub : QQ s ⊆ Tq s := subset_Q_Tq s
  have hQcard : (QQ s).card ≤ 2 := card_Q s
  have hTrcard : 3 ≤ (Tr s hs).card := card_Tr s hs
  have hTrne : Tr s hs ≠ Finset.univ := ne_Tr s hs
  have hRsub : RR s hs ⊆ Tr s hs := subset_R_Tr s hs
  have hRcard : (RR s hs).card ≤ 2 := card_R s hs
  have hdisj : Disjoint (PP s) (RR s hs) := disjoint_P_R s hs
  have hA : ((κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
      (Fin.castLE_injective _))).range).map (MulAut.conj h).toMonoidHom =
      (spBlock F (PP s)).map κ := by
    rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.castLE_injective _) (range_castLE_two s)]
    rw [← hX (T0 s) (PP s) hT0card hT0ne hPsub hPcard]
    rw [hhX]
    rw [mu_image_P s hs, mu_image_T0 s hs]
  have hB : ((((MulAut.conj g).toMonoidHom.comp κ).comp
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))).range).map
      (MulAut.conj h).toMonoidHom = (spBlock F (RR s hs)).map κ := by
    rw [range_comp_comp (MulAut.conj g).toMonoidHom κ
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))]
    rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.natAdd_injective 2 s) (range_natAdd s)]
    rw [← hX (Tq s) (QQ s) hTqcard hTqne hQsub hQcard]
    rw [hgX]
    rw [hhX]
    rw [mu_rot_image_Q s hs, mu_rot_image_Tq s hs]
    rw [hX (Tr s hs) (RR s hs) hTrcard hTrne hRsub hRcard]
  exact commute_of_map_conj h hA hB
    (fun a ha b hb => commute_map_spBlock_of_disjoint κ hdisj a ha b hb)

private theorem window_cross_far (hs : 3 ≤ s)
    (hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N → I.card ≤ 2 →
      X (win s '' ↑I) (win s '' ↑N) = (spBlock F I).map κ)
    {g : G} (hgX : ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom =
      X (finRotate (s + 4) '' S) (finRotate (s + 4) '' T))
    {h : G} (hhX : ∀ S T, (X S T).map (MulAut.conj h).toMonoidHom =
      X ((Equiv.swap (⟨2, by omega⟩ : Fin (s + 4)) ⟨s + 2, by omega⟩ *
          Equiv.swap (⟨3, by omega⟩ : Fin (s + 4)) ⟨s + 3, by omega⟩) '' S)
        ((Equiv.swap (⟨2, by omega⟩ : Fin (s + 4)) ⟨s + 2, by omega⟩ *
          Equiv.swap (⟨3, by omega⟩ : Fin (s + 4)) ⟨s + 3, by omega⟩) '' T)) :
    ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (((MulAut.conj g).toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp κ)).comp
        (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))).range,
        a * b = b * a := by
  have hT0card : 3 ≤ (T0 s).card := card_T0 s hs
  have hT0ne : T0 s ≠ Finset.univ := ne_T0 s hs
  have hPsub : PP s ⊆ T0 s := subset_P_T0 s
  have hPcard : (PP s).card ≤ 2 := card_P s
  have hTqcard : 3 ≤ (Tq s).card := card_Tq s hs
  have hTqne : Tq s ≠ Finset.univ := ne_Tq s hs
  have hQsub : QQ s ⊆ Tq s := subset_Q_Tq s
  have hQcard : (QQ s).card ≤ 2 := card_Q s
  have hTr'card : 3 ≤ (Tr' s hs).card := card_Tr' s hs
  have hTr'ne : Tr' s hs ≠ Finset.univ := ne_Tr' s hs
  have hR'sub : RR' s hs ⊆ Tr' s hs := subset_R'_Tr' s hs
  have hR'card : (RR' s hs).card ≤ 2 := card_R' s hs
  have hdisj : Disjoint (PP s) (RR' s hs) := disjoint_P_R' s hs
  have hA : ((κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
      (Fin.castLE_injective _))).range).map (MulAut.conj h).toMonoidHom =
      (spBlock F (PP s)).map κ := by
    rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.castLE_injective _) (range_castLE_two s)]
    rw [← hX (T0 s) (PP s) hT0card hT0ne hPsub hPcard]
    rw [hhX]
    rw [mu'_image_P s hs, mu'_image_T0 s hs]
  have hB : ((((MulAut.conj g).toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp κ)).comp
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))).range).map
      (MulAut.conj h).toMonoidHom = (spBlock F (RR' s hs)).map κ := by
    rw [range_comp_comp (MulAut.conj g).toMonoidHom
      ((MulAut.conj g).toMonoidHom.comp κ)
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))]
    rw [range_comp_comp (MulAut.conj g).toMonoidHom κ
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2)) (Fin.natAdd_injective 2 s))]
    rw [range_comp_spEmbed_eq_map_spBlock κ (Fin.natAdd_injective 2 s) (range_natAdd s)]
    rw [← hX (Tq s) (QQ s) hTqcard hTqne hQsub hQcard]
    rw [hgX]
    rw [hgX]
    rw [hhX]
    rw [mu'_rot2_image_Q s hs, mu'_rot2_image_Tq s hs]
    rw [hX (Tr' s hs) (RR' s hs) hTr'card hTr'ne hR'sub hR'card]
  exact commute_of_map_conj h hA hB
    (fun a ha b hb => commute_map_spBlock_of_disjoint κ hdisj a ha b hb)

theorem weakCT_symplectic_two_of_three_conj_rotate (hs : 3 ≤ s) [Finite F]
    (hF : Nat.card F = 2) (hκ : Function.Injective κ)
    (hY : ∀ N : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ →
      Y ((Fin.castLE (by omega) : Fin (s + 2) → Fin (s + 4)) '' ↑N) = (spBlock F N).map κ)
    (hX : ∀ N I : Finset (Fin (s + 2)), 3 ≤ N.card → N ≠ Finset.univ → I ⊆ N → I.card ≤ 2 →
      X ((Fin.castLE (by omega) : Fin (s + 2) → Fin (s + 4)) '' ↑I)
        ((Fin.castLE (by omega) : Fin (s + 2) → Fin (s + 4)) '' ↑N) = (spBlock F I).map κ)
    (hlift : ∀ τ : Equiv.Perm (Fin (s + 4)), ∃ h : G,
      ∀ S T, (X S T).map (MulAut.conj h).toMonoidHom = X (τ '' S) (τ '' T))
    {g : G} (hgY : ∀ S, (Y S).map (MulAut.conj g).toMonoidHom = Y (finRotate (s + 4) '' S))
    (hgX : ∀ S T, (X S T).map (MulAut.conj g).toMonoidHom =
      X (finRotate (s + 4) '' S) (finRotate (s + 4) '' T)) :
    ∃ Ψ : StatedSp (s + 4) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (s + 4) F) ∧
      Ψ.range = κ.range ⊔ κ.range.map (MulAut.conj g).toMonoidHom ⊔
        κ.range.map (MulAut.conj (g * g)).toMonoidHom := by
  obtain ⟨h, hhX⟩ := hlift (Equiv.swap ⟨2, by omega⟩ ⟨s + 2, by omega⟩)
  obtain ⟨h', hh'X⟩ := hlift (Equiv.swap ⟨2, by omega⟩ ⟨s + 2, by omega⟩ *
    Equiv.swap ⟨3, by omega⟩ ⟨s + 3, by omega⟩)
  obtain ⟨hov, hplane⟩ := window_overlap (by omega) hY hX hgY hgX
  have hcross := window_cross hs hX hgX hhX
  have hfar := window_cross_far hs hX hgX hh'X
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  let σP : Fin 2 → Fin (s + 2) := Fin.castLE (Nat.le_add_left 2 s)
  let σQ : Fin 2 → Fin (s + 2) := Fin.natAdd s
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  have hov' : ((φ.comp κ).comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      ((φ.comp (φ.comp κ)).comp
        (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range := by
    rw [range_comp_comp φ κ (spEmbed Fin.succ (Fin.succ_injective (s + 1)))]
    rw [range_comp_comp φ (φ.comp κ)
      (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))]
    rw [hov]
  have hplane' : ∀ j : Fin (s + 1),
      ((φ.comp κ).comp (longBlock F (s + 2) j.succ)).range =
        ((φ.comp (φ.comp κ)).comp (longBlock F (s + 2) j.castSucc)).range := by
    intro j
    rw [range_comp_comp φ κ (longBlock F (s + 2) j.succ)]
    rw [range_comp_comp φ (φ.comp κ) (longBlock F (s + 2) j.castSucc)]
    rw [hplane j]
  have hcross' : ∀ a ∈ ((φ.comp κ).comp (spEmbed σP (Fin.castLE_injective _))).range,
      ∀ b ∈ ((φ.comp (φ.comp κ)).comp
        (spEmbed σQ (Fin.natAdd_injective 2 s))).range, a * b = b * a := by
    intro a ha b hb
    refine commute_map_of_commute φ hcross a ?_ b ?_
    · rwa [← range_comp_comp φ κ (spEmbed σP (Fin.castLE_injective _))]
    · rwa [← range_comp_comp φ (φ.comp κ) (spEmbed σQ (Fin.natAdd_injective 2 s))]
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_two_of_three_overlaps (by omega) hF hκ
    (hφ.comp hκ) (hφ.comp (hφ.comp hκ)) hov hplane hcross hov' hplane' hcross' hfar
  refine ⟨Ψ, hker, ?_⟩
  rw [hrange]
  have hφφ : φ.comp φ = (MulAut.conj (g * g)).toMonoidHom := by
    ext x
    simp [φ, MulAut.conj_apply, mul_assoc]
  have h1 : (φ.comp κ).range = κ.range.map φ := MonoidHom.range_comp φ κ
  have h2 : (φ.comp (φ.comp κ)).range = (κ.range.map φ).map φ := by
    rw [MonoidHom.range_comp, h1]
  rw [h1, h2, Subgroup.map_map, hφφ]

end CFSG.ClassicalInvolution.WeakCT
