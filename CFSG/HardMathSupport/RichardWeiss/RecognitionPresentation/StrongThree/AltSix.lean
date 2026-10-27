module

public import CFSG.Open.LocalVocabulary
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AltSixK

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open Equiv CFSG.Open
open scoped Pointwise

set_option maxRecDepth 100000

@[expose] def alt6_c1 : Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def alt6_c2 : Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def alt6_j : Perm (Fin 6) :=
  Equiv.swap 0 4 * Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 2 5

@[expose] def alt6_elems9 : Finset (Perm (Fin 6)) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image
    (fun p => alt6_c1 ^ (p.1 : ℕ) * alt6_c2 ^ (p.2 : ℕ))

theorem alt6_c1_mem : alt6_c1 ∈ alt6_elems9 := AltSixK.c1_mem
theorem alt6_c2_mem : alt6_c2 ∈ alt6_elems9 := AltSixK.c2_mem
theorem alt6_elems9_mul : ∀ x ∈ alt6_elems9, ∀ y ∈ alt6_elems9, x * y ∈ alt6_elems9 :=
  AltSixK.e9_mul
theorem alt6_elems9_inv : ∀ x ∈ alt6_elems9, x⁻¹ ∈ alt6_elems9 := AltSixK.e9_inv
theorem alt6_elems9_one : (1 : Perm (Fin 6)) ∈ alt6_elems9 := AltSixK.e9_one
theorem alt6_elems9_comm : ∀ x ∈ alt6_elems9, ∀ y ∈ alt6_elems9, x * y = y * x :=
  AltSixK.e9_comm
theorem alt6_elems9_cube : ∀ x ∈ alt6_elems9, x ^ 3 = 1 := AltSixK.e9_cube
theorem alt6_elems9_sign : ∀ x ∈ alt6_elems9, Perm.sign x = 1 := AltSixK.e9_sign
theorem alt6_j_sign : Perm.sign alt6_j = 1 := AltSixK.j_sign

theorem alt6_j_conj_ne : ∀ r ∈ alt6_elems9, r ≠ 1 →
    alt6_j * r * alt6_j⁻¹ ≠ 1 ∧ alt6_j * r * alt6_j⁻¹ ≠ r ∧ alt6_j * r * alt6_j⁻¹ ≠ r ^ 2 :=
  AltSixK.j_conj_ne

@[expose] def alt6_Q9 : Subgroup (Perm (Fin 6)) where
  carrier := {x | x ∈ alt6_elems9}
  mul_mem' := fun {a b} ha hb => alt6_elems9_mul a ha b hb
  one_mem' := alt6_elems9_one
  inv_mem' := fun {a} ha => alt6_elems9_inv a ha

@[expose] def alt6_Q0 : Subgroup (Perm (Fin 6)) := Subgroup.closure {alt6_c1, alt6_c2}

theorem alt6_Q0_eq : alt6_Q0 = alt6_Q9 := by
  apply le_antisymm
  · apply Subgroup.closure_le _ |>.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact alt6_c1_mem
    · exact alt6_c2_mem
  · intro x hx
    have hx' : x ∈ alt6_elems9 := hx
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hx'
    have h1 : alt6_c1 ∈ alt6_Q0 := Subgroup.subset_closure (by simp)
    have h2 : alt6_c2 ∈ alt6_Q0 := Subgroup.subset_closure (by simp)
    exact mul_mem (pow_mem h1 _) (pow_mem h2 _)

theorem alt6_mem_Q0_iff (x : Perm (Fin 6)) : x ∈ alt6_Q0 ↔ x ∈ alt6_elems9 := by
  rw [alt6_Q0_eq]
  rfl

theorem alt6_Q0_card : Nat.card alt6_Q0 = 9 := by
  have h : Nat.card alt6_Q0 = Nat.card {x // x ∈ alt6_elems9} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => alt6_mem_Q0_iff x))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact AltSixK.e9_card

theorem alt6_Q0_le : alt6_Q0 ≤ alternatingGroup (Fin 6) := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  exact alt6_elems9_sign x ((alt6_mem_Q0_iff x).1 hx)

@[expose] def alt6_a0 : Set (Fin 6) := {0, 1, 2}

theorem alt6_mem_a0 (x : Fin 6) : x ∈ alt6_a0 ↔ x.val < 3 := by
  fin_cases x <;> simp [alt6_a0]

abbrev alt6_PA (g : Perm (Fin 6)) : Prop :=
  (∀ x : Fin 6, x.val < 3 ↔ (g x).val < 3) ∨ (∀ x : Fin 6, x.val < 3 ↔ ¬ (g x).val < 3)

@[expose] def alt6_partStab : Subgroup (Perm (Fin 6)) :=
  MulAction.stabilizer (Perm (Fin 6)) ({alt6_a0, alt6_a0ᶜ} : Set (Set (Fin 6)))

theorem alt6_smul_eq_image (g : Perm (Fin 6)) (A : Set (Fin 6)) : g • A = (⇑g) '' A :=
  Set.ext fun y => ⟨fun h => by
      obtain ⟨x, hx, hxy⟩ := Set.mem_smul_set.1 h
      exact ⟨x, hx, hxy⟩,
    fun h => by
      obtain ⟨x, hx, hxy⟩ := h
      exact Set.mem_smul_set.2 ⟨x, hx, hxy⟩⟩

theorem alt6_image_iff (g : Perm (Fin 6)) (S T : Set (Fin 6)) :
    (⇑g) '' S = T ↔ ∀ x, x ∈ S ↔ g x ∈ T := by
  constructor
  · intro h x
    rw [← h]
    constructor
    · exact fun hx => ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [g.injective hyx] at hy
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      exact ⟨g.symm y, (h (g.symm y)).2 (by simpa using hy), by simp⟩

theorem alt6_mem_partStab_iff (g : Perm (Fin 6)) : g ∈ alt6_partStab ↔ alt6_PA g := by
  rw [alt6_partStab, MulAction.mem_stabilizer_iff, ← Set.image_smul, Set.image_insert_eq,
    Set.image_singleton, alt6_smul_eq_image, alt6_smul_eq_image, Set.pair_eq_pair_iff,
    Set.image_compl_eq (Equiv.bijective g)]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · left
      intro x
      have h := (alt6_image_iff g _ _).1 h1 x
      rw [alt6_mem_a0, alt6_mem_a0] at h
      exact h
    · right
      intro x
      have h := (alt6_image_iff g _ _).1 h1 x
      rw [alt6_mem_a0, Set.mem_compl_iff, alt6_mem_a0] at h
      exact h
  · rintro (hP | hP)
    · left
      have h1 : (⇑g) '' alt6_a0 = alt6_a0 :=
        (alt6_image_iff g _ _).2 (fun x => by
          rw [alt6_mem_a0, alt6_mem_a0]
          exact hP x)
      exact ⟨h1, by rw [h1]⟩
    · right
      have h1 : (⇑g) '' alt6_a0 = alt6_a0ᶜ :=
        (alt6_image_iff g _ _).2 (fun x => by
          rw [alt6_mem_a0, Set.mem_compl_iff, alt6_mem_a0]
          exact hP x)
      exact ⟨h1, by rw [h1, compl_compl]⟩

@[expose] def alt6_Stab0 : Subgroup (Perm (Fin 6)) := alternatingGroup (Fin 6) ⊓ alt6_partStab

theorem alt6_mem_Stab0_iff (g : Perm (Fin 6)) :
    g ∈ alt6_Stab0 ↔ Perm.sign g = 1 ∧ alt6_PA g := by
  rw [alt6_Stab0, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, alt6_mem_partStab_iff]

theorem alt6_stab0_card : Nat.card alt6_Stab0 = 36 := by
  have h : Nat.card alt6_Stab0 = Nat.card {g : Perm (Fin 6) // Perm.sign g = 1 ∧ alt6_PA g} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun g => alt6_mem_Stab0_iff g))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact AltSixK.card36

theorem alt6_elems9_PA : ∀ x ∈ alt6_elems9, alt6_PA x := AltSixK.e9_PA
theorem alt6_j_PA : alt6_PA alt6_j := AltSixK.j_PA

theorem alt6_j_normalizes : ∀ h : Perm (Fin 6),
    h ∈ alt6_elems9 ↔ alt6_j * h * alt6_j⁻¹ ∈ alt6_elems9 := AltSixK.j_normalizes

theorem alt6_cover : ∀ g : Perm (Fin 6), Perm.sign g = 1 → alt6_PA g →
    ∃ a ∈ alt6_elems9, ∃ k : Fin 4, g = a * alt6_j ^ (k : ℕ) := AltSixK.cover

theorem alt6_jPerm_mem : alt6_j ∈ alternatingGroup (Fin 6) ∧
    alt6_j ∈ Subgroup.normalizer ((alt6_Q0 : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
  refine ⟨Equiv.Perm.mem_alternatingGroup.2 alt6_j_sign, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [alt6_mem_Q0_iff, alt6_mem_Q0_iff]
  exact alt6_j_normalizes h

theorem alt6_stab0_eq : alt6_Stab0 = alt6_Q0 ⊔ Subgroup.zpowers alt6_j := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hs, hP⟩ := (alt6_mem_Stab0_iff g).1 hg
    obtain ⟨a, ha, k, rfl⟩ := alt6_cover g hs hP
    exact mul_mem (Subgroup.mem_sup_left ((alt6_mem_Q0_iff a).2 ha))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers alt6_j) _))
  · apply sup_le
    · intro x hx
      rw [alt6_mem_Q0_iff] at hx
      exact (alt6_mem_Stab0_iff x).2 ⟨alt6_elems9_sign x hx, alt6_elems9_PA x hx⟩
    · rw [Subgroup.zpowers_le]
      exact (alt6_mem_Stab0_iff alt6_j).2 ⟨alt6_j_sign, alt6_j_PA⟩

theorem alt6_zpowers_three {r h : Perm (Fin 6)} (hr : r ^ 3 = 1) (hr1 : r ≠ 1)
    (hh : h ∈ Subgroup.zpowers r) : h = 1 ∨ h = r ∨ h = r ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf r = 3 := orderOf_eq_prime hr hr1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have key : r ^ k = r ^ (k % 3) := by
    rw [← zpow_mod_orderOf r k, hord]
    norm_cast
  rw [key]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> simp [h]

theorem alt6_subgroup_Q0_classify (R : Subgroup (Perm (Fin 6))) (hR : R ≤ alt6_Q0)
    (hne : R ≠ ⊥) :
    R = alt6_Q0 ∨ ∃ r ∈ alt6_elems9, r ≠ 1 ∧ R = Subgroup.zpowers r := by
  have hd : Nat.card R ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hR
    rw [alt6_Q0_card] at this
    norm_num
    exact this
  obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  interval_cases i
  · exact absurd (Subgroup.eq_bot_of_card_eq R (by simp [hn])) hne
  · right
    obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext (by simpa using h))
    have hrQ : r ∈ alt6_elems9 := (alt6_mem_Q0_iff r).1 (hR hrR)
    have hcube : r ^ 3 = 1 := alt6_elems9_cube r hrQ
    have hord : orderOf r = 3 := orderOf_eq_prime hcube hr1'
    have hsub : Subgroup.zpowers r ≤ R := Subgroup.zpowers_le.2 hrR
    have hcard : Nat.card R ≤ Nat.card (Subgroup.zpowers r) := by
      rw [hn, Nat.card_zpowers, hord]
      norm_num
    exact ⟨r, hrQ, hr1', (Subgroup.eq_of_le_of_card_ge hsub hcard).symm⟩
  · left
    apply Subgroup.eq_of_le_of_card_ge hR
    rw [alt6_Q0_card, hn]
    norm_num

theorem alt6_Q0_normalizer_PA : ∀ x : Perm (Fin 6),
    (∀ h ∈ alt6_elems9, x * h * x⁻¹ ∈ alt6_elems9) → alt6_PA x := AltSixK.Q0_normalizer_PA

theorem alt6_normalizes_r : ∀ r ∈ alt6_elems9, r ≠ 1 → ∀ x : Perm (Fin 6),
    (x * r * x⁻¹ = r ∨ x * r * x⁻¹ = r ^ 2) → alt6_PA x := AltSixK.normalizes_r

theorem alt6_normalizer_le_stab0 : ∀ R ≤ alt6_Q0, R ≠ ⊥ →
    ∀ x ∈ alternatingGroup (Fin 6), x ∈ Subgroup.normalizer (R : Set (Perm (Fin 6))) →
      x ∈ alt6_Stab0 := by
  intro R hR hne x hxA hxN
  rw [alt6_mem_Stab0_iff]
  refine ⟨Equiv.Perm.mem_alternatingGroup.1 hxA, ?_⟩
  rcases alt6_subgroup_Q0_classify R hR hne with rfl | ⟨r, hr, hr1, rfl⟩
  · apply alt6_Q0_normalizer_PA x
    intro h hh
    have hc := (Subgroup.mem_normalizer_iff.1 hxN) h
    exact (alt6_mem_Q0_iff _).1 (hc.1 ((alt6_mem_Q0_iff h).2 hh))
  · have hxr : x * r * x⁻¹ ∈ Subgroup.zpowers r :=
      (Subgroup.mem_normalizer_iff.1 hxN) r |>.1 (Subgroup.mem_zpowers r)
    rcases alt6_zpowers_three (alt6_elems9_cube r hr) hr1 hxr with h | h | h
    · exfalso
      apply hr1
      calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
        _ = 1 := by rw [h]; simp
    · exact alt6_normalizes_r r hr hr1 x (Or.inl h)
    · exact alt6_normalizes_r r hr hr1 x (Or.inr h)

theorem alt6_actsIrr : ∀ W : Subgroup (Perm (Fin 6)), W ≤ alt6_Q0 →
    Subgroup.zpowers alt6_j ≤ Subgroup.normalizer (W : Set (Perm (Fin 6))) →
    W = ⊥ ∨ W = alt6_Q0 := by
  intro W hW hN
  have hj : alt6_j ∈ Subgroup.normalizer (W : Set (Perm (Fin 6))) :=
    Subgroup.zpowers_le.1 hN
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  rcases alt6_subgroup_Q0_classify W hW hbot with h | ⟨r, hr, hr1, rfl⟩
  · exact h
  · exfalso
    have hcjr : alt6_j * r * alt6_j⁻¹ ∈ Subgroup.zpowers r :=
      (Subgroup.mem_normalizer_iff.1 hj) r |>.1 (Subgroup.mem_zpowers r)
    rcases alt6_zpowers_three (alt6_elems9_cube r hr) hr1 hcjr with h | h | h
    · exact (alt6_j_conj_ne r hr hr1).1 h
    · exact (alt6_j_conj_ne r hr hr1).2.1 h
    · exact (alt6_j_conj_ne r hr hr1).2.2 h

theorem alt6_Q0_ne_bot : alt6_Q0 ≠ ⊥ := by
  intro h
  have h9 := alt6_Q0_card
  rw [h, Subgroup.card_bot] at h9
  norm_num at h9

theorem alt6_index_factorial_or {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (L : Subgroup G) : L.index = 1 ∨ Nat.card G ∣ L.index.factorial := by
  by_cases hL : L = ⊤
  · exact Or.inl (by rw [hL, Subgroup.index_top])
  right
  have hker : (MulAction.toPermHom G (G ⧸ L)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom G (G ⧸ L)).ker with h | h
    · exact h
    · exfalso
      apply hL
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ (MulAction.toPermHom G (G ⧸ L)).ker := by
        rw [h]
        exact Subgroup.mem_top g
      have h1 : ∀ x : G ⧸ L, g • x = x := fun x => by
        have := congrArg (fun σ : Equiv.Perm (G ⧸ L) => σ x) (MonoidHom.mem_ker.1 hg)
        simpa using this
      have h2 : (QuotientGroup.mk (g * 1) : G ⧸ L) = QuotientGroup.mk 1 :=
        h1 (QuotientGroup.mk 1)
      rw [QuotientGroup.eq] at h2
      simpa using h2
  have hdvd := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (G ⧸ L))
    ((MonoidHom.ker_eq_bot_iff _).1 hker)
  rw [Nat.card_perm] at hdvd
  exact hdvd

instance alt6_isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem alt6_A6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem alt6_stab0_maximal : ∀ H : Subgroup (Perm (Fin 6)), alt6_Stab0 < H →
    H ≤ alternatingGroup (Fin 6) → H = alternatingGroup (Fin 6) := by
  intro H hlt hHA
  have hle : alt6_Stab0 ≤ H := hlt.le
  have hne : alt6_Stab0 ≠ H := hlt.ne
  have hdvd36 : Nat.card alt6_Stab0 ∣ Nat.card H := Subgroup.card_dvd_of_le hle
  have hdvd360 : Nat.card H ∣ 360 := by
    rw [← alt6_A6_card]
    exact Subgroup.card_dvd_of_le hHA
  rw [alt6_stab0_card] at hdvd36
  obtain ⟨k, hk⟩ := hdvd36
  rw [hk] at hdvd360
  have hk10 : k ≤ 10 := by
    have := Nat.le_of_dvd (by norm_num) hdvd360
    omega
  have hLcard : Nat.card (H.subgroupOf (alternatingGroup (Fin 6))) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv
  have hLmul : Nat.card (H.subgroupOf (alternatingGroup (Fin 6))) *
      (H.subgroupOf (alternatingGroup (Fin 6))).index = 360 := by
    rw [Subgroup.card_mul_index, alt6_A6_card]
  have hidx := alt6_index_factorial_or (H.subgroupOf (alternatingGroup (Fin 6)))
  interval_cases k
  · norm_num at hdvd360
  · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by have := alt6_stab0_card; omega)) hne
  · have h5 : (H.subgroupOf (alternatingGroup (Fin 6))).index = 5 := by
      rw [hLcard, hk] at hLmul
      norm_num at hLmul
      omega
    rcases hidx with h1 | h1
    · omega
    · rw [h5, alt6_A6_card] at h1
      norm_num [Nat.factorial] at h1
  · norm_num at hdvd360
  · norm_num at hdvd360
  · have h2 : (H.subgroupOf (alternatingGroup (Fin 6))).index = 2 := by
      rw [hLcard, hk] at hLmul
      norm_num at hLmul
      omega
    rcases hidx with h1 | h1
    · omega
    · rw [h2, alt6_A6_card] at h1
      norm_num [Nat.factorial] at h1
  · norm_num at hdvd360
  · norm_num at hdvd360
  · norm_num at hdvd360
  · norm_num at hdvd360
  · exact Subgroup.eq_of_le_of_card_ge hHA (le_of_eq (by rw [alt6_A6_card, hk]))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

end
