module

public import CFSG.Certificates.Kernel.M11Local.Sound
public import Certificates.Data.ONanSmallM11
public import CFSG.GH74.KGroups.M11

public section

namespace CFSG.KC.M11L

open Equiv CFSG.KC.Misc.Clos CFSG.GH74.KGroups CFSG.Blueprint Certificates.ONanSmallM11
  CFSG.Sporadic.Mathieu

theorem evalW_mem (w : List Bool) : evalW m11gA m11gB w ∈ NativeSporadic.M11 := by
  rw [m11_eq]
  induction w with
  | nil => exact one_mem _
  | cons c w ih =>
    cases c
    · change m11gA * evalW m11gA m11gB w ∈ _
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _)) ih
    · change m11gB * evalW m11gA m11gB w ∈ _
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) ih

theorem m11_free :
    ∀ g ∈ NativeSporadic.M11, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1 := by
  intro g hg h0 h1 h2 h3
  have hQ := M11.Q_ok
  have hbase : M11.Q.base.toList = [1, 0, 2, 3] := rfl
  have hmem : g ∈ M11.Q.levelSubgroup M11.Q.baseCount := by
    rw [M11.Q.mem_levelSubgroup_iff hQ M11.Q.baseCount le_rfl]
    refine ⟨M11.Q_subgroup.symm ▸ hg, fun b hb => ?_⟩
    rw [List.take_of_length_le (by simp), hbase] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    exacts [h1, h0, h2, h3]
  rw [M11.Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem exists_smul_four_of_card {G : Subgroup (Equiv.Perm (Fin 11))} (hcard : Nat.card G = 7920)
    (hfree : ∀ g ∈ G, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1) :
    ∀ u v w z : Fin 11, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : G, g • (0 : Fin 11) = u ∧ g • (1 : Fin 11) = v ∧ g • (2 : Fin 11) = w ∧
        g • (3 : Fin 11) = z := by
  classical
  let c : Fin 4 ↪ Fin 11 := Fin.castLEEmb (by norm_num)
  let f : G → (Fin 4 ↪ Fin 11) := fun g => c.trans (g : Equiv.Perm (Fin 11)).toEmbedding
  have hfinj : Function.Injective f := by
    intro g h hgh
    have h0 : (g : Equiv.Perm (Fin 11)) 0 = (h : Equiv.Perm (Fin 11)) 0 :=
      DFunLike.congr_fun hgh 0
    have h1 : (g : Equiv.Perm (Fin 11)) 1 = (h : Equiv.Perm (Fin 11)) 1 :=
      DFunLike.congr_fun hgh 1
    have h2 : (g : Equiv.Perm (Fin 11)) 2 = (h : Equiv.Perm (Fin 11)) 2 :=
      DFunLike.congr_fun hgh 2
    have h3 : (g : Equiv.Perm (Fin 11)) 3 = (h : Equiv.Perm (Fin 11)) 3 :=
      DFunLike.congr_fun hgh 3
    have hmem : (h : Equiv.Perm (Fin 11))⁻¹ * (g : Equiv.Perm (Fin 11)) ∈ G :=
      G.mul_mem (G.inv_mem h.2) g.2
    have key := hfree _ hmem
      (by rw [Equiv.Perm.mul_apply, h0]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h1]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h2]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h3]; exact Equiv.symm_apply_apply _ _)
    apply Subtype.ext
    exact (inv_mul_eq_one.1 key).symm
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_embedding_eq]
    simp [Nat.descFactorial]
  intro u v w z huv huw huz hvw hvz hwz
  let t : Fin 4 ↪ Fin 11 := ⟨![u, v, w, z], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> tauto⟩
  obtain ⟨g, hg⟩ := hbij.2 t
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact DFunLike.congr_fun hg 0
  · exact DFunLike.congr_fun hg 1
  · exact DFunLike.congr_fun hg 2
  · exact DFunLike.congr_fun hg 3

theorem isPretransitive_duads_of_four {G : Subgroup (Equiv.Perm (Fin 11))}
    (h4 : ∀ u v w z : Fin 11, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : G, g • (0 : Fin 11) = u ∧ g • (1 : Fin 11) = v ∧ g • (2 : Fin 11) = w ∧
        g • (3 : Fin 11) = z) :
    MulAction.IsPretransitive G (Set.powersetCard (Fin 11) 2) := by
  have hext : ∀ a b : Fin 11, a ≠ b → ∃ c d : Fin 11, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
    decide
  have h2 : MulAction.IsMultiplyPretransitive G (Fin 11) 2 := by
    refine MulAction.is_two_pretransitive_iff.2 fun {a b a' b'} hab hab' => ?_
    obtain ⟨c, d, hca, hcb, hda, hdb, hcd⟩ := hext a b hab
    obtain ⟨c', d', hca', hcb', hda', hdb', hcd'⟩ := hext a' b' hab'
    obtain ⟨g, g0, g1, -, -⟩ := h4 a b c d hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb)
      (Ne.symm hdb) hcd
    obtain ⟨g', g0', g1', -, -⟩ := h4 a' b' c' d' hab' (Ne.symm hca') (Ne.symm hda')
      (Ne.symm hcb') (Ne.symm hdb') hcd'
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · rw [mul_smul, inv_smul_eq_iff.2 g0.symm, g0']
    · rw [mul_smul, inv_smul_eq_iff.2 g1.symm, g1']
  exact Set.powersetCard.isPretransitive_of_isMultiplyPretransitive G h2

theorem m11_four :
    ∀ u v w z : Fin 11, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : ↥NativeSporadic.M11, g • (0 : Fin 11) = u ∧ g • (1 : Fin 11) = v ∧
        g • (2 : Fin 11) = w ∧ g • (3 : Fin 11) = z :=
  exists_smul_four_of_card M11.card_M11 m11_free

theorem mem_stabilizer_duad_iff (g : ↥NativeSporadic.M11) :
    g ∈ MulAction.stabilizer ↥NativeSporadic.M11 (duad (0 : Fin 11) 1 (by decide)) ↔
      (((g : Equiv.Perm (Fin 11)) 0 = 0 ∧ (g : Equiv.Perm (Fin 11)) 1 = 1) ∨
        ((g : Equiv.Perm (Fin 11)) 0 = 1 ∧ (g : Equiv.Perm (Fin 11)) 1 = 0)) := by
  rw [MulAction.mem_stabilizer_iff]
  have key := smul_duad (G := ↥NativeSporadic.M11) g (0 : Fin 11) 1 (by decide)
  constructor
  · intro h
    have h' := Subtype.ext_iff.1 (key.symm.trans h)
    change ({g • (0 : Fin 11), g • (1 : Fin 11)} : Finset (Fin 11)) = {0, 1} at h'
    have h'' := congrArg (fun s : Finset (Fin 11) => (s : Set (Fin 11))) h'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff] at h''
    exact h''
  · intro h
    apply key.trans
    apply Subtype.ext
    change ({g • (0 : Fin 11), g • (1 : Fin 11)} : Finset (Fin 11)) = {0, 1}
    rw [← Finset.coe_inj]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff]
    exact h

theorem card_stabilizer_duad :
    Nat.card (MulAction.stabilizer ↥NativeSporadic.M11 (duad (0 : Fin 11) 1 (by decide))) =
      144 := by
  have := isPretransitive_duads_of_four m11_four
  have hidx := MulAction.index_stabilizer_of_transitive ↥NativeSporadic.M11
    (duad (0 : Fin 11) 1 (by decide))
  rw [Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin] at hidx
  have h := Subgroup.index_mul_card
    (MulAction.stabilizer ↥NativeSporadic.M11 (duad (0 : Fin 11) 1 (by decide)))
  rw [hidx, M11.card_M11] at h
  rw [show Nat.choose 11 2 = 55 by decide] at h
  omega

@[expose] def eSub : Subgroup (Equiv.Perm (Fin 11)) := Subgroup.closure {m11x, m11y}

theorem mem_eSub_iff (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E)
    (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E) {g : Equiv.Perm (Fin 11)} : g ∈ eSub ↔ g ∈ m11E := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl <;> simp [m11E]
    | one => simp [m11E]
    | mul a b _ _ ha hb => exact hmul a ha b hb
    | inv a _ ha => exact hinv a ha
  · intro hg
    have hx : m11x ∈ eSub := Subgroup.subset_closure (Set.mem_insert _ _)
    have hy : m11y ∈ eSub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hx
    · exact pow_mem hx 2
    · exact hy
    · exact mul_mem hx hy
    · exact mul_mem (pow_mem hx 2) hy
    · exact pow_mem hy 2
    · exact mul_mem hx (pow_mem hy 2)
    · exact mul_mem (pow_mem hx 2) (pow_mem hy 2)

theorem eSub_le (hx : m11x ∈ NativeSporadic.M11) (hy : m11y ∈ NativeSporadic.M11) :
    eSub ≤ NativeSporadic.M11 := by
  rw [eSub, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  exacts [hx, hy]

@[expose] def eT : Subgroup ↥NativeSporadic.M11 := eSub.subgroupOf NativeSporadic.M11

theorem card_eT (hx : m11x ∈ NativeSporadic.M11) (hy : m11y ∈ NativeSporadic.M11)
    (hnodup : m11E.Nodup) (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E)
    (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E) : Nat.card eT = 9 := by
  rw [eT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (eSub_le hx hy)).toEquiv]
  have h : (eSub : Set (Equiv.Perm (Fin 11))) = (m11E.toFinset : Set (Equiv.Perm (Fin 11))) := by
    ext g
    simp [mem_eSub_iff hmul hinv]
  have h1 : Nat.card eSub = (eSub : Set (Equiv.Perm (Fin 11))).ncard :=
    Nat.card_congr (Equiv.refl _)
  rw [h1, h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
  rfl

theorem mem_normalizer_eT_iff (hx : m11x ∈ NativeSporadic.M11) (hy : m11y ∈ NativeSporadic.M11)
    (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E)
    {g : ↥NativeSporadic.M11} :
    g ∈ Subgroup.normalizer ((eT : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ↔
      ((g : Equiv.Perm (Fin 11)) * m11x * (g : Equiv.Perm (Fin 11))⁻¹ ∈ m11E ∧
        (g : Equiv.Perm (Fin 11)) * m11y * (g : Equiv.Perm (Fin 11))⁻¹ ∈ m11E) := by
  have hmemT : ∀ k : ↥NativeSporadic.M11, k ∈ eT ↔ (k : Equiv.Perm (Fin 11)) ∈ eSub :=
    fun _ => Iff.rfl
  have hxT : (⟨m11x, hx⟩ : ↥NativeSporadic.M11) ∈ eT := by
    rw [hmemT]; exact (mem_eSub_iff hmul hinv).2 (by simp [m11E])
  have hyT : (⟨m11y, hy⟩ : ↥NativeSporadic.M11) ∈ eT := by
    rw [hmemT]; exact (mem_eSub_iff hmul hinv).2 (by simp [m11E])
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hxT
    have h2 := (Subgroup.mem_normalizer_iff.1 hg _).1 hyT
    rw [hmemT, mem_eSub_iff hmul hinv] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ h ∈ eSub,
        (g : Equiv.Perm (Fin 11)) * h * (g : Equiv.Perm (Fin 11))⁻¹ ∈ eSub := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem s hs =>
        rcases hs with rfl | rfl
        · exact (mem_eSub_iff hmul hinv).2 h1
        · exact (mem_eSub_iff hmul hinv).2 h2
      | one => simp [one_mem]
      | mul a b _ _ ha hb =>
        have : (g : Equiv.Perm (Fin 11)) * (a * b) * (g : Equiv.Perm (Fin 11))⁻¹ =
            ((g : Equiv.Perm (Fin 11)) * a * (g : Equiv.Perm (Fin 11))⁻¹) *
              ((g : Equiv.Perm (Fin 11)) * b * (g : Equiv.Perm (Fin 11))⁻¹) := by group
        rw [this]
        exact mul_mem ha hb
      | inv a _ ha =>
        have : (g : Equiv.Perm (Fin 11)) * a⁻¹ * (g : Equiv.Perm (Fin 11))⁻¹ =
            ((g : Equiv.Perm (Fin 11)) * a * (g : Equiv.Perm (Fin 11))⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem ha
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [SetLike.mem_coe, hmemT] at hn ⊢
    simpa using key _ hn

theorem eq_zero_or_one_of_fix
    (hfix : ∀ e ∈ m11E, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i)
    {e : Equiv.Perm (Fin 11)} (he : e ∈ m11E) (he1 : e ≠ 1) {j : Fin 11} (hj : e j = j) :
    j = 0 ∨ j = 1 := by
  by_contra hne
  rw [not_or] at hne
  have h2 : 2 ≤ (j : ℕ) := by
    have h0 : (j : ℕ) ≠ 0 := fun h => hne.1 (Fin.ext h)
    have h1 : (j : ℕ) ≠ 1 := fun h => hne.2 (Fin.ext h)
    omega
  exact (hfix e he he1).2.2 j h2 hj

theorem duad_of_conj_mem (hx1 : m11x ≠ 1)
    (hfix : ∀ e ∈ m11E, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i)
    {g : Equiv.Perm (Fin 11)} (hg : g * m11x * g⁻¹ ∈ m11E) :
    (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0) := by
  have hxE : m11x ∈ m11E := by simp [m11E]
  have hx01 := hfix m11x hxE hx1
  have hc1 : g * m11x * g⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have : m11x = g⁻¹ * (g * m11x * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hfixg : ∀ i : Fin 11, m11x i = i → (g * m11x * g⁻¹) (g i) = g i := by
    intro i hi
    simp [Equiv.Perm.mul_apply, hi]
  have hg0 := eq_zero_or_one_of_fix hfix hg hc1 (hfixg 0 hx01.1)
  have hg1 := eq_zero_or_one_of_fix hfix hg hc1 (hfixg 1 hx01.2.1)
  have hne : g 0 ≠ g 1 := fun h => absurd (g.injective h) (by decide)
  rcases hg0 with h0 | h0 <;> rcases hg1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (h0.trans h1.symm) hne

theorem normalizer_eT_eq (hx : m11x ∈ NativeSporadic.M11)
    (hy : m11y ∈ NativeSporadic.M11) (hs : m11s ∈ NativeSporadic.M11) (hnodup : m11E.Nodup)
    (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E)
    (hx1 : m11x ≠ 1)
    (hfix : ∀ e ∈ m11E, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i)
    (hs8 : m11s ^ 8 = 1) (hs4 : m11s ^ 4 ≠ 1) (hsx : m11s * m11x * m11s⁻¹ ∈ m11E)
    (hsy : m11s * m11y * m11s⁻¹ ∈ m11E) :
    Subgroup.normalizer ((eT : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) =
      MulAction.stabilizer ↥NativeSporadic.M11 (duad (0 : Fin 11) 1 (by decide)) := by
  set N := Subgroup.normalizer ((eT : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11)
    with hNdef
  have hNleH : N ≤ MulAction.stabilizer ↥NativeSporadic.M11 (duad (0 : Fin 11) 1 (by decide)) :=
    fun g hg => (mem_stabilizer_duad_iff g).2
      (duad_of_conj_mem hx1 hfix ((mem_normalizer_eT_iff hx hy hmul hinv).1 hg).1)
  have hH := card_stabilizer_duad
  have hcardT := card_eT hx hy hnodup hmul hinv
  have hsN : (⟨m11s, hs⟩ : ↥NativeSporadic.M11) ∈ N :=
    (mem_normalizer_eT_iff hx hy hmul hinv).2 ⟨hsx, hsy⟩
  have hord : orderOf (⟨m11s, hs⟩ : ↥NativeSporadic.M11) = 8 := by
    have h4' : ¬ (⟨m11s, hs⟩ : ↥NativeSporadic.M11) ^ 4 = 1 := fun h => by
      have := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact hs4 this
    have h8' : (⟨m11s, hs⟩ : ↥NativeSporadic.M11) ^ 8 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs8)
    have e4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    have e8 : (2 : ℕ) ^ (2 + 1) = 8 := by norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (n := 2) (by rw [e4]; exact h4') (by rw [e8]; exact h8')
    rwa [e8] at h
  have h9 : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := eT))
    rwa [hcardT] at this
  have h8 : 8 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).2 hsN)
    rwa [Nat.card_zpowers, hord] at this
  have h144 : Nat.card N ∣ 144 := by
    have := Subgroup.card_dvd_of_le hNleH
    rwa [hH] at this
  have h72 : 72 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h8
  have hM : Nat.card ↥NativeSporadic.M11 = 7920 := M11.card_M11
  have hcardN : Nat.card N = 144 := by
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hle : Nat.card N ≤ 144 := Nat.le_of_dvd (by norm_num) h144
    obtain ⟨k, hk⟩ := h72
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hP : IsPGroup 3 eT := IsPGroup.of_card (n := 2) (by rw [hcardT]; norm_num)
      have hidxT : ¬ 3 ∣ eT.index := by
        have h := eT.index_mul_card
        rw [hM, hcardT] at h
        have : eT.index = 880 := by omega
        rw [this]
        norm_num
      let S : Sylow 3 ↥NativeSporadic.M11 := hP.toSylow hidxT
      have hST : (S : Subgroup ↥NativeSporadic.M11) = eT := IsPGroup.toSylow_coe hP hidxT
      have hNS : Nat.card (Sylow 3 ↥NativeSporadic.M11) = N.index := by
        have := S.card_eq_index_normalizer
        have hset : (S : Set ↥NativeSporadic.M11) = (eT : Set ↥NativeSporadic.M11) :=
          congrArg (fun K : Subgroup ↥NativeSporadic.M11 => (K : Set ↥NativeSporadic.M11)) hST
        rwa [hset] at this
      have hidxN : N.index = 110 := by
        have h := N.index_mul_card
        rw [hM, hk] at h
        omega
      have hmod := card_sylow_modEq_one 3 ↥NativeSporadic.M11
      rw [hNS, hidxN] at hmod
      exact absurd hmod (by decide)
    · omega
  exact Subgroup.eq_of_le_of_card_ge hNleH (by rw [hH, hcardN])

theorem centralizer_le (hx : m11x ∈ NativeSporadic.M11)
    (hy : m11y ∈ NativeSporadic.M11) (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E)
    (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E) (hxy : m11x * m11y = m11y * m11x) (hx1 : m11x ≠ 1)
    (hfix : ∀ e ∈ m11E, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i)
    (hreg : ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ m11E, e 2 = i) :
    ∀ g ∈ NativeSporadic.M11, g * m11x = m11x * g → g * m11y = m11y * g → g ∈ m11E := by
  have hcommL : ∀ g : Equiv.Perm (Fin 11), Commute g m11x → Commute g m11y →
      ∀ c ∈ m11E, Commute g c := by
    intro g hgx hgy c hc
    simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Commute.one_right g
    · exact hgx
    · exact hgx.pow_right 2
    · exact hgy
    · exact hgx.mul_right hgy
    · exact (hgx.pow_right 2).mul_right hgy
    · exact hgy.pow_right 2
    · exact hgx.mul_right (hgy.pow_right 2)
    · exact (hgx.pow_right 2).mul_right (hgy.pow_right 2)
  have hxC := hcommL m11x (Commute.refl _) hxy
  have hyC := hcommL m11y hxy.symm (Commute.refl _)
  have hLcomm : ∀ c ∈ m11E, ∀ d ∈ m11E, Commute c d := fun c hc d hd =>
    hcommL c (hxC c hc).symm (hyC c hc).symm d hd
  have hlt2 : ∀ j : Fin 11, ¬ 2 ≤ (j : ℕ) → j = 0 ∨ j = 1 := by decide
  have hxE : m11x ∈ m11E := by simp [m11E]
  have hx01 := hfix m11x hxE hx1
  intro g hg hgx hgy
  have hxg : ∀ i, m11x i = i → m11x (g i) = g i := by
    intro i hi
    have := congrArg (fun p : Equiv.Perm (Fin 11) => p i) hgx
    simp only [Equiv.Perm.mul_apply, hi] at this
    exact this.symm
  have hg0 := eq_zero_or_one_of_fix hfix hxE hx1 (hxg 0 hx01.1)
  have hg1 := eq_zero_or_one_of_fix hfix hxE hx1 (hxg 1 hx01.2.1)
  have h2 : 2 ≤ ((g 2 : Fin 11) : ℕ) := by
    by_contra hlt
    have hn0 : g 2 ≠ g 0 := fun h => absurd (g.injective h) (by decide)
    have hn1 : g 2 ≠ g 1 := fun h => absurd (g.injective h) (by decide)
    have hn01 : g 0 ≠ g 1 := fun h => absurd (g.injective h) (by decide)
    rcases hlt2 (g 2) hlt with h2 | h2 <;> rcases hg0 with h0 | h0 <;>
      rcases hg1 with h1 | h1 <;>
      first
      | exact absurd (h2.trans h0.symm) hn0
      | exact absurd (h2.trans h1.symm) hn1
      | exact absurd (h0.trans h1.symm) hn01
  obtain ⟨e, he, he2⟩ := hreg (g 2) h2
  have hgc := hcommL g hgx hgy
  obtain ⟨k, hkdef⟩ : ∃ k, k = e⁻¹ * g := ⟨_, rfl⟩
  have hfixk : ∀ i : Fin 11, 2 ≤ (i : ℕ) → k i = i := by
    intro i hi
    obtain ⟨e', he', rfl⟩ := hreg i hi
    have h1 : g (e' 2) = e' (g 2) := by
      have := congrArg (fun p : Equiv.Perm (Fin 11) => p 2) (hgc e' he').eq
      simpa only [Equiv.Perm.mul_apply] using this
    have h3 : e' (e 2) = e (e' 2) := by
      have := congrArg (fun p : Equiv.Perm (Fin 11) => p 2) (hLcomm e he e' he').eq
      simpa only [Equiv.Perm.mul_apply] using this.symm
    rw [hkdef, Equiv.Perm.mul_apply, h1, ← he2, h3]
    exact e.symm_apply_apply _
  have heM : e ∈ NativeSporadic.M11 := eSub_le hx hy ((mem_eSub_iff hmul hinv).2 he)
  have hkM : k ∈ NativeSporadic.M11 := hkdef ▸ mul_mem (inv_mem heM) hg
  obtain ⟨u, hu0, hu1, hu2, hu3⟩ := m11_four 2 3 4 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  change (u : Equiv.Perm (Fin 11)) 0 = 2 at hu0
  change (u : Equiv.Perm (Fin 11)) 1 = 3 at hu1
  change (u : Equiv.Perm (Fin 11)) 2 = 4 at hu2
  change (u : Equiv.Perm (Fin 11)) 3 = 5 at hu3
  have hconj : ∀ (i : Fin 11) (j : Fin 11), (u : Equiv.Perm (Fin 11)) i = j → 2 ≤ (j : ℕ) →
      ((u : Equiv.Perm (Fin 11))⁻¹ * k * u) i = i := by
    intro i j hij hj
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hij, hfixk j hj, Equiv.Perm.inv_eq_iff_eq,
      hij]
  have hw := m11_free ((u : Equiv.Perm (Fin 11))⁻¹ * k * u)
    (mul_mem (mul_mem (inv_mem u.2) hkM) u.2) (hconj 0 2 hu0 (by decide))
    (hconj 1 3 hu1 (by decide)) (hconj 2 4 hu2 (by decide)) (hconj 3 5 hu3 (by decide))
  have hk1 : k = 1 := by
    have e1 : k = (u : Equiv.Perm (Fin 11)) * ((u : Equiv.Perm (Fin 11))⁻¹ * k * u) *
        (u : Equiv.Perm (Fin 11))⁻¹ := by group
    rw [e1, hw]
    group
  rw [hkdef] at hk1
  have hge : e = g := inv_mul_eq_one.1 hk1
  exact hge ▸ he

theorem m11_facts_of_check {wx wy ws : List Bool}
    (h : m11K (pcode m11x) (pcode m11y) (pcode m11s) (pcode m11gA) (pcode m11gB) wx wy ws =
      true) :
    m11x ∈ NativeSporadic.M11 ∧ m11y ∈ NativeSporadic.M11 ∧
    m11s ∈ NativeSporadic.M11 ∧ m11E.Nodup ∧
    (∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) ∧ (∀ a ∈ m11E, a⁻¹ ∈ m11E) ∧
    m11x ^ 3 = 1 ∧ m11y ^ 3 = 1 ∧ m11x * m11y = m11y * m11x ∧ m11x ≠ 1 ∧
    m11y ∉ ([1, m11x, m11x ^ 2] : List (Equiv.Perm (Fin 11))) ∧
    (∀ g ∈ NativeSporadic.M11, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1) ∧
    (∀ g ∈ NativeSporadic.M11, (g * m11x * g⁻¹ ∈ m11E ∧ g * m11y * g⁻¹ ∈ m11E) ↔
      ((g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0))) ∧
    (∀ g ∈ NativeSporadic.M11, g * m11x = m11x * g → g * m11y = m11y * g → g ∈ m11E) ∧
    (∀ v ∈ m11E, v ≠ 1 → ∀ t ∈ m11E, t ≠ 1 → ∃ n ∈ NativeSporadic.M11,
      ((n 0 = 0 ∧ n 1 = 1) ∨ (n 0 = 1 ∧ n 1 = 0)) ∧ n * v * n⁻¹ = t) ∧
    (((m11s 0 = 0 ∧ m11s 1 = 1) ∨ (m11s 0 = 1 ∧ m11s 1 = 0)) ∧ m11s ^ 8 = 1 ∧ m11s ^ 4 ≠ 1 ∧
      ∀ t ∈ m11E, t ≠ 1 → m11s * t * m11s⁻¹ ≠ t) := by
  obtain ⟨hwx, hwy, hws, hnodup, hinv, hmul, hx3, hy3, hxy, hx1, hyn, hfix, hreg, hsd, hs8, hs4,
    hsx, hsy, hstor, htrans⟩ := m11K_sound h
  have hx : m11x ∈ NativeSporadic.M11 := hwx ▸ evalW_mem wx
  have hy : m11y ∈ NativeSporadic.M11 := hwy ▸ evalW_mem wy
  have hs : m11s ∈ NativeSporadic.M11 := hws ▸ evalW_mem ws
  refine ⟨hx, hy, hs, hnodup, hmul, hinv, hx3, hy3, hxy, hx1, hyn, m11_free, ?_,
    centralizer_le hx hy hmul hinv hxy hx1 hfix hreg, ?_, ⟨hsd, hs8, hs4, hstor⟩⟩
  · intro g hg
    have e1 := mem_normalizer_eT_iff hx hy hmul hinv (g := ⟨g, hg⟩)
    rw [normalizer_eT_eq hx hy hs hnodup hmul hinv hx1 hfix hs8 hs4 hsx hsy,
      mem_stabilizer_duad_iff] at e1
    exact e1.symm
  · intro v hv hv1 t ht ht1
    obtain ⟨k, -, hkd, hkt⟩ := htrans v hv hv1 t ht ht1
    exact ⟨m11s ^ k, pow_mem hs k, hkd, hkt⟩

end CFSG.KC.M11L

end
