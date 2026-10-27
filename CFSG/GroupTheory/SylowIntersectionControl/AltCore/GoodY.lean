module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStabIndex
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStabNormalizer
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStabLocalPairs
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStabLocalQuads
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def GoodY {n : ℕ} (Y : Subgroup (Perm (Fin n))) : Prop :=
  Y ≠ ⊤ ∧ Odd Y.index ∧
    normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = Y ∧
    (Even n → CharTwo (Y ⊓ alternatingGroup (Fin n))) ∧
    (n % 4 = 3 → ∃ z : Perm (Fin n), z.IsThreeCycle ∧
      twoResidual ((Y ⊓ alternatingGroup (Fin n)) ⊓
        centralizer (pCoreOf 2 (Y ⊓ alternatingGroup (Fin n)) : Set (Perm (Fin n)))) ≤
        zpowers z)

variable {n : ℕ} {s : Setoid (Fin n)}

private theorem card_fiber (x : Fin n) :
    Nat.card {y // (⟦y⟧ : Quotient s) = ⟦x⟧} = Nat.card {y // s.r x y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [Quotient.eq]
    exact ⟨fun h => s.symm h, fun h => s.symm h⟩)

private theorem card_eq_sum [Fintype (Quotient s)] :
    n = ∑ c : Quotient s, Nat.card {y // (⟦y⟧ : Quotient s) = c} := by
  classical
  have := Nat.card_congr (Equiv.sigmaFiberEquiv (fun y : Fin n => (⟦y⟧ : Quotient s)))
  rw [Nat.card_sigma, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  exact this.symm

theorem dvd_of_card_classes {d : ℕ} (hs : ∀ x, Nat.card {y // s.r x y} = d) : d ∣ n := by
  classical
  rw [card_eq_sum (s := s)]
  refine Finset.dvd_sum fun c _ => ?_
  induction c using Quotient.inductionOn with
  | h x => rw [card_fiber, hs x]

theorem exists_eq_add_of_card_classes {d e : ℕ} {b : Fin n} (hb : Nat.card {y // s.r b y} = e)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = d) : ∃ k, n = e + d * k := by
  classical
  rw [card_eq_sum (s := s), ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟦b⟧ : Quotient s)),
    card_fiber, hb]
  refine ⟨((Finset.univ : Finset (Quotient s)).erase ⟦b⟧).card, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    rw [card_fiber]
    refine hs x fun hbx => (Finset.mem_erase.mp hc).1 ?_
    exact Quotient.sound (s.symm hbx)

theorem partStab_ne_top {x x' y : Fin n} (hxx' : s.r x x') (hne : x ≠ x') (hxy : ¬ s.r x y) :
    partStab s ≠ ⊤ := by
  intro htop
  have hxy' : x ≠ y := fun h => hxy (h ▸ s.refl x)
  have hg := (mem_partStab_iff.mp (htop ▸ mem_top (swap x' y))) x x'
  rw [swap_apply_of_ne_of_ne hne hxy', swap_apply_left] at hg
  exact hxy (hg.mpr hxx')

theorem exists_rel_ne {x : Fin n} (hx : 2 ≤ Nat.card {y // s.r x y}) :
    ∃ x', s.r x x' ∧ x ≠ x' := by
  have : Nontrivial {y // s.r x y} := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne {y // s.r x y}
  by_cases hax : x = a
  · refine ⟨b, hb, fun hxb => hab ?_⟩
    exact Subtype.ext (hax.symm.trans hxb)
  · exact ⟨a, ha, hax⟩

theorem exists_not_rel {x : Fin n} (h : Nat.card {y // s.r x y} < n) : ∃ y, ¬ s.r x y := by
  by_contra hne
  push Not at hne
  have : Nat.card {y // s.r x y} = n := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hne), Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

private theorem partStab_ne_top_of_special {d e : ℕ} {b : Fin n} (hd : 2 ≤ d)
    (hb : Nat.card {y // s.r b y} = e) (he : e < n)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = d) : partStab s ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_not_rel (hb ▸ he)
  obtain ⟨x', hxx', hne⟩ := exists_rel_ne ((hs x hx).symm ▸ hd)
  exact partStab_ne_top hxx' hne fun hxb => hx (s.symm hxb)

theorem goodY_partStab_pairs (hn : 8 ≤ n) (hs : ∀ x, Nat.card {y // s.r x y} = 2) :
    GoodY (partStab s) := by
  have h2 := dvd_of_card_classes hs
  have x₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨x', hxx', hne⟩ := exists_rel_ne (s := s) (x := x₀) (hs _).ge
  obtain ⟨y, hy⟩ := exists_not_rel (s := s) (x := x₀) (by rw [hs]; omega)
  exact ⟨partStab_ne_top hxx' hne hy, odd_index_partStab_pairs hs,
    normalizer_partStab_inf_pairs (by omega) hs, fun _ => charTwo_partStab_inf_pairs (by omega) hs,
    fun h3 => absurd h2 (by omega)⟩

theorem goodY_partStab_pairsPoint (hn : 7 ≤ n) (h3 : n % 4 = 3) {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 1) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 2) :
    GoodY (partStab s) := by
  obtain ⟨k, hk⟩ := exists_eq_add_of_card_classes hb hs
  exact ⟨partStab_ne_top_of_special le_rfl hb (by omega) hs,
    odd_index_partStab_pairsPoint hb hs, normalizer_partStab_inf_pairsPoint hn hb hs,
    fun hev => absurd hev (by rw [Nat.not_even_iff_odd]; exact ⟨k, by omega⟩),
    fun _ => twoResidual_le_partStab_inf_pairsPoint hn hb hs⟩

theorem goodY_partStab_quads (hn : 8 ≤ n) (hs : ∀ x, Nat.card {y // s.r x y} = 4) :
    GoodY (partStab s) := by
  have h4 := dvd_of_card_classes hs
  have x₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨x', hxx', hne⟩ := exists_rel_ne (s := s) (x := x₀) (by rw [hs]; norm_num)
  obtain ⟨y, hy⟩ := exists_not_rel (s := s) (x := x₀) (by rw [hs]; omega)
  exact ⟨partStab_ne_top hxx' hne hy, odd_index_partStab_quads hs,
    normalizer_partStab_inf_quads hn hs, fun _ => charTwo_partStab_inf_quads hs,
    fun h3 => absurd h4 (by omega)⟩

theorem goodY_partStab_quadsPair (hn : 10 ≤ n) {b : Fin n} (hb : Nat.card {y // s.r b y} = 2)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) : GoodY (partStab s) := by
  obtain ⟨k, hk⟩ := exists_eq_add_of_card_classes hb hs
  exact ⟨partStab_ne_top_of_special (by norm_num) hb (by omega) hs,
    odd_index_partStab_quadsPair hb hs, normalizer_partStab_inf_quadsPair hn hb hs,
    fun _ => charTwo_partStab_inf_quadsPair hb hs, fun h3 => absurd h3 (by omega)⟩

theorem goodY_partStab_quadsTriple (hn : 7 ≤ n) {b : Fin n} (hb : Nat.card {y // s.r b y} = 3)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) : GoodY (partStab s) := by
  obtain ⟨k, hk⟩ := exists_eq_add_of_card_classes hb hs
  exact ⟨partStab_ne_top_of_special (by norm_num) hb (by omega) hs,
    odd_index_partStab_quadsTriple hb hs, normalizer_partStab_inf_quadsTriple hn hb hs,
    fun hev => absurd hev (by rw [Nat.not_even_iff_odd]; exact ⟨2 * k + 1, by omega⟩),
    fun _ => twoResidual_le_partStab_inf_quadsTriple hb hs⟩

private theorem two_le_of_exact {n m : ℕ} (h1 : n % 4 = 1)
    (hm : 2 ^ m ∣ n - 1 ∧ ¬ 2 ^ (m + 1) ∣ n - 1) : 2 ≤ m := by
  by_contra h
  have h4 : 4 ∣ n - 1 := by omega
  interval_cases m
  · exact hm.2 (dvd_trans (by norm_num) h4)
  · exact hm.2 (by simpa using h4)

private theorem add_le_of_exact {n m : ℕ} (h1 : n % 4 = 1)
    (hm : 2 ^ m ∣ n - 1 ∧ ¬ 2 ^ (m + 1) ∣ n - 1) (hn' : n ≠ 2 ^ m + 1) : 2 ^ m + 1 + 3 ≤ n := by
  obtain ⟨u, hu⟩ := hm.1
  have hm2 := two_le_of_exact h1 hm
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hu0 : u ≠ 0 := fun h => hm.2 (by rw [hu, h, mul_zero]; exact dvd_zero _)
  have hu1 : u ≠ 1 := fun h => hn' (by simp [h] at hu; omega)
  have hu2 : u ≠ 2 := fun h => hm.2 ⟨1, by rw [hu, h, pow_succ]; ring⟩
  have h3u : 3 ≤ u := by omega
  have hn1 : n = 2 ^ m * u + 1 := by omega
  have := Nat.mul_le_mul_left (2 ^ m) h3u
  omega

theorem goodY_setStab (hn : 7 ≤ n) (h1 : n % 4 = 1) {Γ : Finset (Fin n)} {m : ℕ}
    (hm : 2 ^ m ∣ n - 1 ∧ ¬ 2 ^ (m + 1) ∣ n - 1) (hn' : n ≠ 2 ^ m + 1)
    (hΓ : Γ.card = 1 ∨ Γ.card = 2 ^ m + 1) :
    GoodY (MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n))) := by
  have hm2 := two_le_of_exact h1 hm
  have h4m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hc3 : Γ.card + 3 ≤ n := by
    rcases hΓ with h | h
    · omega
    · rw [h]; exact add_le_of_exact h1 hm hn'
  refine ⟨fun htop => ?_, odd_index_stabilizer_finset h1 hm hΓ,
    normalizer_stabilizer_finset_inf (hΓ.imp id fun h => by omega) hc3 (by omega),
    fun hev => absurd hev (by rw [Nat.not_even_iff_odd]; exact ⟨n / 2, by omega⟩),
    fun h3 => absurd h3 (by omega)⟩
  obtain ⟨a, ha⟩ : Γ.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ Γ := by
    by_contra hall
    push Not at hall
    have : Γ = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hc3
    omega
  have hst := htop ▸ mem_top (swap a c)
  rw [MulAction.mem_stabilizer_iff] at hst
  have : c ∈ swap a c • (Γ : Set (Fin n)) := Set.mem_smul_set.mpr ⟨a, ha, by simp⟩
  rw [hst] at this
  exact hc this

private theorem card_class_of_mem {D : Set (Fin n)} (hD : ∀ x ∈ D, ∀ y, s.r x y ↔ y ∈ D)
    {x : Fin n} (hx : x ∈ D) : Nat.card {y // s.r x y} = Nat.card D :=
  Nat.card_congr (Equiv.subtypeEquivRight (hD x hx))

private theorem exists_eq_singleton {D : Set (Fin n)} (h : Nat.card D = 1) :
    ∃ p, D = {p} := by
  obtain ⟨⟨p, hp⟩, hu⟩ := Nat.card_eq_one_iff_exists.mp h
  exact ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun q hq => congrArg Subtype.val
    (hu ⟨q, hq⟩)⟩⟩

theorem goodY_stabilizer_point (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) (h1 : n % 4 = 1)
    (p : Fin n) :
    GoodY (MulAction.stabilizer (Perm (Fin n)) (({p} : Finset (Fin n)) : Set (Fin n))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine goodY_setStab hn h1 (m := padicValNat 2 (n - 1))
    ⟨pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd (by omega)⟩ (hn2 _) (Or.inl rfl)

private theorem eq_empty_of_card {D : Set (Fin n)} (h : Nat.card D = 0) : D = ∅ := by
  rcases Nat.card_eq_zero.mp h with h | h
  · exact Set.isEmpty_coe_sort.mp h
  · exact absurd h (not_infinite_iff_finite.mpr inferInstance)

private theorem exists_mem_of_card {D : Set (Fin n)} (h : 0 < Nat.card D) : ∃ b, b ∈ D := by
  obtain ⟨⟨b, hb⟩⟩ := (Nat.card_pos_iff.mp h).1
  exact ⟨b, hb⟩

private theorem goodY_of_classes_four (hn : 7 ≤ n) {D : Set (Fin n)}
    (hD : ∀ x ∈ D, ∀ y, s.r x y ↔ y ∈ D) (hDcard : Nat.card D = n % 4)
    (hcls : ∀ x, x ∉ D → Nat.card {y // s.r x y} = 4) (h1 : n % 4 ≠ 1) :
    GoodY (partStab s) := by
  have hDc : ∀ x ∈ D, Nat.card {y // s.r x y} = n % 4 := fun x hx =>
    (card_class_of_mem hD hx).trans hDcard
  have hoff : ∀ b ∈ D, ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4 := fun b hb x hx =>
    hcls x fun h => hx ((hD b hb x).mpr h)
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 4
  · have hDe := eq_empty_of_card hDcard
    exact goodY_partStab_quads (by omega) fun x => hcls x (by simp [hDe])
  · exact absurd rfl h1
  · obtain ⟨b, hb⟩ := exists_mem_of_card (D := D) (by omega : 0 < Nat.card D)
    exact goodY_partStab_quadsPair (by omega) (hDc b hb) (hoff b hb)
  · obtain ⟨b, hb⟩ := exists_mem_of_card (D := D) (by omega : 0 < Nat.card D)
    exact goodY_partStab_quadsTriple hn (hDc b hb) (hoff b hb)

private theorem goodY_of_classes_two (hn : 7 ≤ n) {D : Set (Fin n)}
    (hD : ∀ x ∈ D, ∀ y, s.r x y ↔ y ∈ D) (hDcard : Nat.card D = n % 2)
    (hcls : ∀ x, x ∉ D → Nat.card {y // s.r x y} = 2) (h1 : n % 4 ≠ 1) :
    GoodY (partStab s) := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1'
  · have hDe := eq_empty_of_card (D := D) (hDcard.trans h0)
    exact goodY_partStab_pairs (by omega) fun x => hcls x (by simp [hDe])
  · obtain ⟨b, hb⟩ := exists_mem_of_card (D := D) (by omega : 0 < Nat.card D)
    exact goodY_partStab_pairsPoint hn (by omega)
      ((card_class_of_mem hD hb).trans (hDcard.trans h1'))
      fun x hx => hcls x fun h => hx ((hD b hb x).mpr h)

theorem exists_goodY_of_classes (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) {D : Set (Fin n)}
    {i : ℕ} (hi : i = 1 ∨ i = 2) (hD : ∀ x ∈ D, ∀ y, s.r x y ↔ y ∈ D)
    (hDcard : Nat.card D = n % 2 ^ i) (hcls : ∀ x, x ∉ D → Nat.card {y // s.r x y} = 2 ^ i)
    {good : Perm (Fin n) → Prop} (hgs : ∀ a, good a → a ∈ partStab s)
    (hgD : ∀ a, good a → ∀ x, a x ∈ D ↔ x ∈ D) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧ ∀ a, good a → a ∈ Y := by
  by_cases h1 : n % 4 = 1
  · have hD1 : Nat.card D = 1 := by
      rw [hDcard]
      rcases hi with rfl | rfl <;> omega
    obtain ⟨p, rfl⟩ := exists_eq_singleton hD1
    refine ⟨_, goodY_stabilizer_point hn hn2 h1 p, fun a ha => ?_⟩
    rw [MulAction.mem_stabilizer_iff, Finset.coe_singleton, Set.smul_set_singleton,
      Set.singleton_eq_singleton_iff]
    exact (hgD a ha p).mpr rfl
  refine ⟨partStab s, ?_, fun a ha => hgs a ha⟩
  rcases hi with rfl | rfl
  · exact goodY_of_classes_two hn hD (by simpa using hDcard) (by simpa using hcls) h1
  · exact goodY_of_classes_four hn hD (by simpa using hDcard) (by simpa using hcls) h1

end CFSG.GroupTheory.AltCore
