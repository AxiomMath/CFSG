module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltPair
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAct
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoClassical

section Perm

variable {n : ℕ} (hn : 8 ≤ n)

abbrev InS {n : ℕ} (i : Fin n) : Prop := (i : ℕ) ≠ 1 ∧ (i : ℕ) ≠ 2 ∧ (i : ℕ) ≠ 3

@[expose] def altS (n : ℕ) : Subgroup (Perm (Fin n)) :=
  (alternatingGroup {i : Fin n // InS i}).map Perm.ofSubtype

theorem mem_altS_iff {π : Perm (Fin n)} :
    π ∈ altS n ↔ (∀ i : Fin n, ¬ InS i → π i = i) ∧ sign π = 1 :=
  SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff

theorem altS_le (n : ℕ) : altS n ≤ alternatingGroup (Fin n) := fun _ h =>
  mem_alternatingGroup.mpr (mem_altS_iff.mp h).2

theorem card_S (n : ℕ) (hn : 4 ≤ n) : Fintype.card {i : Fin n // InS i} = n - 3 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin n => InS i) =
      Finset.univ \ {⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or, InS]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]

@[expose] noncomputable def altSEquiv (n : ℕ) (hn : 4 ≤ n) :
    altS n ≃* alternatingGroup (Fin (n - 3)) :=
  ((alternatingGroup {i : Fin n // InS i}).equivMapOfInjective _
    Perm.ofSubtype_injective).symm.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (card_S n hn)))

@[expose] def p123n : Perm (Fin n) :=
  swap ⟨1, by omega⟩ ⟨3, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩

theorem p123n_isThreeCycle : (p123n hn).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff])

theorem p123n_mem : p123n hn ∈ alternatingGroup (Fin n) :=
  (p123n_isThreeCycle hn).mem_alternatingGroup

theorem p123n_val (i : Fin n) : ((p123n hn i : Fin n) : ℕ) =
    if (i : ℕ) = 1 then 2 else if (i : ℕ) = 2 then 3 else if (i : ℕ) = 3 then 1 else (i : ℕ) := by
  simp only [p123n, Perm.mul_apply, swap_apply_def, Fin.ext_iff]
  split_ifs <;> simp_all

theorem p123n_apply_of_inS {i : Fin n} (hi : InS i) : p123n hn i = i :=
  Fin.ext (by rw [p123n_val]; obtain ⟨h1, h2, h3⟩ := hi; simp [h1, h2, h3])

theorem inS_iff_p123n_fix (i : Fin n) : InS i ↔ p123n hn i = i := by
  constructor
  · exact p123n_apply_of_inS hn
  · intro h
    have h' := congrArg Fin.val h
    rw [p123n_val] at h'
    refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
    · rw [ite_eq_left h1] at h'; omega
    · rw [ite_eq_right (by omega), ite_eq_left h2] at h'; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h3] at h'; omega

theorem inS_apply_iff {σ : Perm (Fin n)} (hσ : σ * p123n hn = p123n hn * σ) (i : Fin n) :
    InS (σ i) ↔ InS i := by
  rw [inS_iff_p123n_fix hn, inS_iff_p123n_fix hn, ← Perm.mul_apply, ← hσ, Perm.mul_apply]
  exact σ.injective.eq_iff

theorem commute_p123n_of_mem_altS {x : Perm (Fin n)} (hx : x ∈ altS n) :
    x * p123n hn = p123n hn * x := by
  have hx' := (mem_altS_iff.mp hx).1
  refine Perm.Disjoint.commute (fun i => ?_) |>.eq
  by_cases hi : InS i
  · exact Or.inr (p123n_apply_of_inS hn hi)
  · exact Or.inl (hx' i hi)

theorem swap_mul_swap_mem_altS {s a b : Fin n} (hs : InS s) (ha : InS a) (hb : InS b)
    (hsa : s ≠ a) (hsb : s ≠ b) : swap s a * swap s b ∈ altS n := by
  rw [mem_altS_iff]
  refine ⟨fun i hi => ?_, ?_⟩
  · have his : i ≠ s := fun h => hi (h ▸ hs)
    have hia : i ≠ a := fun h => hi (h ▸ ha)
    have hib : i ≠ b := fun h => hi (h ▸ hb)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne his hib, swap_apply_of_ne_of_ne his hia]
  · rw [Perm.sign_mul, sign_swap hsa, sign_swap hsb]
    rfl

theorem fix_of_commute_two_threeCycles {α : Type*} [DecidableEq α] {φ : Perm α} {s a b c d : α}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) (hsc : s ≠ c) (hsd : s ≠ d) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h1 : φ * (swap s a * swap s b) = (swap s a * swap s b) * φ)
    (h2 : φ * (swap s c * swap s d) = (swap s c * swap s d) * φ) : φ s = s := by
  have hmoved : ∀ {x y : α}, s ≠ x → s ≠ y → x ≠ y →
      φ * (swap s x * swap s y) = (swap s x * swap s y) * φ →
        φ s = s ∨ φ s = x ∨ φ s = y := by
    intro x y hsx hsy hxy h
    by_contra hne
    push Not at hne
    have e1 : (swap s x * swap s y) (φ s) = φ s := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hne.1 hne.2.2,
        swap_apply_of_ne_of_ne hne.1 hne.2.1]
    have e2 : (swap s x * swap s y) (φ s) = φ ((swap s x * swap s y) s) := by
      rw [← Perm.mul_apply, ← h, Perm.mul_apply]
    rw [e2, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hsy.symm hxy.symm] at e1
    exact hsy.symm (φ.injective e1)
  rcases hmoved hsa hsb hab h1 with h | h | h
  · exact h
  · rcases hmoved hsc hsd hcd h2 with h' | h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hac
    · exact absurd (h.symm.trans h') had
  · rcases hmoved hsc hsd hcd h2 with h' | h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hbc
    · exact absurd (h.symm.trans h') hbd

include hn in
theorem exists_four_inS (s : Fin n) : ∃ a b c d : Fin n, InS a ∧ InS b ∧ InS c ∧ InS d ∧
    s ≠ a ∧ s ≠ b ∧ s ≠ c ∧ s ≠ d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have key : ∀ x y z u : ℕ, ∀ (hx : x < n) (hy : y < n) (hz : z < n) (hu : u < n),
      x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 → y ≠ 1 ∧ y ≠ 2 ∧ y ≠ 3 → z ≠ 1 ∧ z ≠ 2 ∧ z ≠ 3 →
        u ≠ 1 ∧ u ≠ 2 ∧ u ≠ 3 → (s : ℕ) ≠ x → (s : ℕ) ≠ y → (s : ℕ) ≠ z → (s : ℕ) ≠ u →
          x ≠ y → x ≠ z → x ≠ u → y ≠ z → y ≠ u → z ≠ u →
            ∃ a b c d : Fin n, InS a ∧ InS b ∧ InS c ∧ InS d ∧
              s ≠ a ∧ s ≠ b ∧ s ≠ c ∧ s ≠ d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    intro x y z u hx hy hz hu h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨u, hu⟩, h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;> simp [Fin.ext_iff] <;> omega
  by_cases h0 : (s : ℕ) = 0
  · exact key 4 5 6 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · by_cases h4 : (s : ℕ) = 4
    · exact key 0 5 6 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · by_cases h5 : (s : ℕ) = 5
      · exact key 0 4 6 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact key 0 4 5 (if (s : ℕ) = 6 then 7 else 6) (by omega) (by omega) (by omega)
          (by split_ifs <;> omega) (by omega) (by omega) (by omega) (by split_ifs <;> omega)
          (by omega) (by omega) (by omega) (by split_ifs <;> omega) (by omega) (by omega)
          (by split_ifs <;> omega) (by omega) (by split_ifs <;> omega)
          (by split_ifs <;> omega)

include hn in
theorem fix_of_commute_altS {σ : Perm (Fin n)} (hσ : ∀ x ∈ altS n, σ * x = x * σ) {s : Fin n}
    (hs : InS s) : σ s = s := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hsa, hsb, hsc, hsd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_inS hn s
  exact fix_of_commute_two_threeCycles hsa hsb hab hsc hsd hcd hac had hbc hbd
    (hσ _ (swap_mul_swap_mem_altS hs ha hb hsa hsb))
    (hσ _ (swap_mul_swap_mem_altS hs hc hd hsc hsd))

theorem eq_one_of_commute_p123n_altS {σ : Perm (Fin n)} (h1 : σ * p123n hn = p123n hn * σ)
    (h2 : ∀ x ∈ altS n, σ * x = x * σ) {k : ℕ} (hk : σ ^ (2 ^ k) = 1) : σ = 1 := by
  have hfix : ∀ i : Fin n, InS i → σ i = i := fun i hi => fix_of_commute_altS hn h2 hi
  set l1 : Fin n := ⟨1, by omega⟩
  set l2 : Fin n := ⟨2, by omega⟩
  set l3 : Fin n := ⟨3, by omega⟩
  have hp1 : p123n hn l1 = l2 := Fin.ext (by rw [p123n_val]; simp [l1, l2])
  have hp2 : p123n hn l2 = l3 := Fin.ext (by rw [p123n_val]; simp [l2, l3])
  have hp3 : p123n hn l3 = l1 := Fin.ext (by rw [p123n_val]; simp [l1, l3])
  have hcomm : ∀ i, σ (p123n hn i) = p123n hn (σ i) := fun i => by
    rw [← Perm.mul_apply, h1, Perm.mul_apply]
  have hσ1 : (σ l1 : ℕ) = 1 ∨ (σ l1 : ℕ) = 2 ∨ (σ l1 : ℕ) = 3 := by
    by_contra h
    push Not at h
    have hS : InS (σ l1) := ⟨h.1, h.2.1, h.2.2⟩
    have := σ.injective (hfix _ hS)
    rw [this] at hS
    exact hS.1 rfl
  have hall : ∀ i : Fin n, ¬ InS i → i = l1 ∨ i = l2 ∨ i = l3 := by
    intro i hi
    simp only [InS, not_and_or, not_not] at hi
    rcases hi with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have h3' : ¬ (σ ^ 3 = 1 ∧ σ ≠ 1) := by
    rintro ⟨h3, h1'⟩
    have hdvd := orderOf_dvd_of_pow_eq_one hk
    rw [orderOf_eq_prime h3 h1'] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by decide)
  rcases hσ1 with h | h | h
  ·
    have e1 : σ l1 = l1 := Fin.ext h
    have e2 : σ l2 = l2 := by rw [← hp1, hcomm, e1]
    have e3 : σ l3 = l3 := by rw [← hp2, hcomm, e2]
    refine Equiv.ext fun i => ?_
    by_cases hi : InS i
    · exact hfix i hi
    · rcases hall i hi with rfl | rfl | rfl
      · exact e1
      · exact e2
      · exact e3
  ·
    exfalso
    have e1 : σ l1 = l2 := Fin.ext h
    have e2 : σ l2 = l3 := by rw [← hp1, hcomm, e1, hp2]
    have e3 : σ l3 = l1 := by rw [← hp2, hcomm, e2, hp3]
    have hσp : σ = p123n hn := by
      refine Equiv.ext fun i => ?_
      by_cases hi : InS i
      · rw [hfix i hi, p123n_apply_of_inS hn hi]
      · rcases hall i hi with rfl | rfl | rfl
        · rw [e1, hp1]
        · rw [e2, hp2]
        · rw [e3, hp3]
    apply h3'
    rw [hσp, ← (p123n_isThreeCycle hn).orderOf]
    exact ⟨pow_orderOf_eq_one _, (p123n_isThreeCycle hn).ne_one⟩
  ·
    exfalso
    have e1 : σ l1 = l3 := Fin.ext h
    have e2 : σ l2 = l1 := by rw [← hp1, hcomm, e1, hp3]
    have e3 : σ l3 = l2 := by rw [← hp2, hcomm, e2, hp1]
    have hσp : σ = p123n hn * p123n hn := by
      refine Equiv.ext fun i => ?_
      by_cases hi : InS i
      · rw [hfix i hi, Perm.mul_apply, p123n_apply_of_inS hn hi, p123n_apply_of_inS hn hi]
      · rcases hall i hi with rfl | rfl | rfl
        · rw [e1, Perm.mul_apply, hp1, hp2]
        · rw [e2, Perm.mul_apply, hp2, hp3]
        · rw [e3, Perm.mul_apply, hp3, hp1]
    apply h3'
    have hp3' : p123n hn ^ 3 = 1 := by
      rw [← (p123n_isThreeCycle hn).orderOf]
      exact pow_orderOf_eq_one _
    refine ⟨?_, fun h1' => ?_⟩
    · rw [hσp, ← sq, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hp3', one_pow]
    · have : σ l1 = l1 := by rw [h1']; rfl
      rw [e1] at this
      exact absurd (congrArg Fin.val this) (by simp [l1, l3])

theorem nat_card_kleinFour : Nat.card kleinFour = 4 := by
  have hinj : Function.Injective kOf := by
    intro i j h
    revert i j
    decide
  have hbij : Function.Bijective (fun i : Fin 4 => (⟨kOf i, kOf_mem i⟩ : kleinFour)) :=
    ⟨fun i j h => hinj (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hx
      exact ⟨i, rfl⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem nat_card_rootV (h4 : 4 ≤ n) : Nat.card (rootV n) = 4 := by
  rw [rootV, dite_eq_left h4]
  have hle : kleinFour.map (viaEmbeddingHom (fourEmb h4)) ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨k, hk, rfl⟩
    exact viaEmbeddingHom_mem_alternatingGroup' _ (kleinFour_le_alternatingGroup hk)
  rw [show ((kleinFour.map (viaEmbeddingHom (fourEmb h4))).comap
      (alternatingGroup (Fin n)).subtype) =
        (kleinFour.map (viaEmbeddingHom (fourEmb h4))).subgroupOf (alternatingGroup (Fin n))
      from rfl, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    card_map_of_injective (viaEmbeddingHom_injective _), nat_card_kleinFour]

theorem fourEmb_ne {h4 : 4 ≤ n} (i : Fin 4) {j : ℕ} (hj : j < n) (h4j : 4 ≤ j) :
    (fourEmb h4 i : Fin n) ≠ ⟨j, hj⟩ := fun h => by
  have h1 : ((fourEmb h4 i : Fin n) : ℕ) = j := congrArg Fin.val h
  rw [fourEmb_apply] at h1
  have h2 := i.isLt
  omega

end Perm

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

namespace NormPair

variable (np : NormPair A R T g n) (hn : 8 ≤ n)

@[expose] noncomputable def wE : G := ((np.equivA.symm ⟨p123n hn, p123n_mem hn⟩ : A) : G)

omit [Finite G] in
theorem wE_mem : np.wE hn ∈ A := (np.equivA.symm _).2

omit [Finite G] in
theorem ψA_wE : np.ψA ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ = p123n hn := by
  have := np.equivA_coe (np.equivA.symm ⟨p123n hn, p123n_mem hn⟩)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] noncomputable def LE : Subgroup G :=
  (((altS n).subgroupOf (alternatingGroup (Fin n))).map np.equivA.symm.toMonoidHom).map A.subtype

omit [Finite G] in
theorem mem_LE_iff {x : G} :
    x ∈ np.LE ↔ ∃ hx : x ∈ A, np.ψA ⟨x, le_normalizer hx⟩ ∈ altS n := by
  rw [LE, np.mem_map_equivA, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (altS_le n)]

omit [Finite G] in
theorem LE_le_A : np.LE ≤ A := fun _ hx => (np.mem_LE_iff.mp hx).1

omit [Finite G] in
theorem commute_wE_of_mem_LE {x : G} (hx : x ∈ np.LE) : x * np.wE hn = np.wE hn * x := by
  obtain ⟨hxA, hxS⟩ := np.mem_LE_iff.mp hx
  have h1 := commute_p123n_of_mem_altS hn hxS
  have : (⟨x, le_normalizer hxA⟩ * ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ :
      normalizer (A : Set G)) = ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ * ⟨x, le_normalizer hxA⟩ :=
    np.injA (mul_mem hxA (np.wE_mem hn)) (mul_mem (np.wE_mem hn) hxA)
      (by rw [map_mul, map_mul, np.ψA_wE hn, h1])
  exact congrArg Subtype.val this

omit [Finite G] in
theorem LE_le_centralizer : np.LE ≤ centralizer (zpowers (np.wE hn) : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  exact ((Commute.zpow_left (np.commute_wE_of_mem_LE hn hx).symm k)).eq

omit [Finite G] in
@[expose] noncomputable def LEEquiv : np.LE ≃* alternatingGroup (Fin (n - 3)) :=
  ((((((altS n).subgroupOf (alternatingGroup (Fin n))).map
    np.equivA.symm.toMonoidHom).equivMapOfInjective A.subtype A.subtype_injective).symm.trans
      (((altS n).subgroupOf (alternatingGroup (Fin n))).equivMapOfInjective _
        np.equivA.symm.injective).symm).trans (Subgroup.subgroupOfEquivOfLe (altS_le n))).trans
          (altSEquiv n (by have := hn; omega))

omit [Finite G] in
include hn in
theorem isQuasisimple_LE : CFSG.Open.IsQuasisimple np.LE :=
  Lemma22.isQuasisimple_of_mulEquiv (np.LEEquiv hn).symm
    (CatalogueBAlternating.alternating_quasisimple (by simp; omega))

theorem normalizer_inf_le_normalizer_LE :
    normalizer (A : Set G) ⊓ centralizer (zpowers (np.wE hn) : Set G) ≤
      normalizer (np.LE : Set G) := by
  intro x hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
  set σ := np.ψA ⟨x, hxN⟩ with hσdef
  have hxw : np.wE hn * x = x * np.wE hn := mem_centralizer_iff.mp hxC _ (mem_zpowers _)
  have hσp : σ * p123n hn = p123n hn * σ := by
    have h := congrArg np.ψA (show (⟨x, hxN⟩ * ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ :
        normalizer (A : Set G)) = ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ * ⟨x, hxN⟩ from
      Subtype.ext hxw.symm)
    rwa [map_mul, map_mul, np.ψA_wE hn] at h
  apply mem_normalizer_of_conj_mem
  intro ℓ hℓ
  obtain ⟨hℓA, hℓS⟩ := np.mem_LE_iff.mp hℓ
  have hmem : x * ℓ * x⁻¹ ∈ A := (mem_normalizer_iff.mp hxN ℓ).mp hℓA
  refine np.mem_LE_iff.mpr ⟨hmem, ?_⟩
  have e : np.ψA ⟨x * ℓ * x⁻¹, le_normalizer hmem⟩ = σ * np.ψA ⟨ℓ, le_normalizer hℓA⟩ * σ⁻¹ := by
    rw [show (⟨x * ℓ * x⁻¹, le_normalizer hmem⟩ : normalizer (A : Set G)) =
      ⟨x, hxN⟩ * ⟨ℓ, le_normalizer hℓA⟩ * ⟨x, hxN⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
  rw [e, mem_altS_iff]
  obtain ⟨hfix, hsign⟩ := mem_altS_iff.mp hℓS
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' : ¬ InS (σ⁻¹ i) := by
      rw [← inS_apply_iff hn hσp, perm_apply_inv]
      exact hi
    rw [Perm.mul_apply, Perm.mul_apply, hfix _ hi', perm_apply_inv]
  · rw [Perm.sign_mul, Perm.sign_mul, hsign, Perm.sign_inv, mul_one, Int.units_mul_self]

omit [Finite G] in
include np in
theorem card_R (h4 : 4 ≤ n) : Nat.card R = 4 := by
  rw [← np.map_rootV_B, card_map_of_injective (Subgroup.subtype_injective _),
    card_map_of_injective (f := np.equivB.symm.toMonoidHom) np.equivB.symm.injective,
    nat_card_rootV h4]

variable (hc : Sec3 A R T g)
include hc

theorem R_le_X : R ≤ centralizer (zpowers (np.wE hn) : Set G) ⊓ centralizer (np.LE : Set G) ⊓
    normalizer (R : Set G) := by
  intro r hr
  have hrK := hc.sylowR.le hr
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, le_normalizer hr⟩
  · rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact mem_centralizer_iff.mp hrK _ (zpow_mem (np.wE_mem hn) k)
  · rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_iff.mp hrK _ (np.LE_le_A hh)

theorem isSylowOf_R_LE :
    IsSylowOf 2 R (centralizer (zpowers (np.wE hn) : Set G) ⊓ centralizer (np.LE : Set G) ⊓
      normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer (zpowers (np.wE hn) : Set G) ⊓ centralizer (np.LE : Set G) ⊓
    normalizer (R : Set G) with hXdef
  have hRK := hc.sylowR
  have hRX : R ≤ X := np.R_le_X hn hc
  have h2 : ∀ x ∈ X, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ centralizer (A : Set G) := by
    intro x hx k hk
    obtain ⟨⟨hxW, hxL⟩, hxR⟩ := hx
    have hxN : x ∈ normalizer (A : Set G) := normalizer_R_le hc hxR
    set σ := np.ψA ⟨x, hxN⟩ with hσdef
    have hσp : σ * p123n hn = p123n hn * σ := by
      have hxw : np.wE hn * x = x * np.wE hn := mem_centralizer_iff.mp hxW _ (mem_zpowers _)
      have h := congrArg np.ψA (show (⟨x, hxN⟩ * ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ :
          normalizer (A : Set G)) = ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩ * ⟨x, hxN⟩ from
        Subtype.ext hxw.symm)
      rwa [map_mul, map_mul, np.ψA_wE hn] at h
    have hσS : ∀ τ ∈ altS n, σ * τ = τ * σ := by
      intro τ hτ
      obtain ⟨ℓ, hℓA, hℓτ⟩ := np.hψA.exists_eq τ (altS_le n hτ)
      have hℓL : ℓ ∈ np.LE := np.mem_LE_iff.mpr ⟨hℓA, by rw [hℓτ]; exact hτ⟩
      have hxℓ : ℓ * x = x * ℓ := mem_centralizer_iff.mp hxL ℓ hℓL
      have h := congrArg np.ψA (show (⟨x, hxN⟩ * ⟨ℓ, le_normalizer hℓA⟩ :
          normalizer (A : Set G)) = ⟨ℓ, le_normalizer hℓA⟩ * ⟨x, hxN⟩ from Subtype.ext hxℓ.symm)
      rwa [map_mul, map_mul, hℓτ] at h
    have hσk : σ ^ (2 ^ k) = 1 := by
      rw [hσdef, ← map_pow]
      have : (⟨x, hxN⟩ : normalizer (A : Set G)) ^ (2 ^ k) = 1 := Subtype.ext hk
      rw [this, map_one]
    have hσ1 := eq_one_of_commute_p123n_altS hn hσp hσS hσk
    exact (np.hψA.eq_one_iff _).mp hσ1
  obtain ⟨P, hRP⟩ := (hRK.isPGroup.comap_subtype (K := X)).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup X).map X.subtype with hP'def
  have hP' : IsSylowOf 2 P' X := ⟨P, rfl⟩
  have hRP' : R ≤ P' := fun r hr => ⟨⟨r, hRX hr⟩, hRP hr, rfl⟩
  have hP'K : P' ≤ centralizer (A : Set G) := by
    intro x hx
    obtain ⟨k, hk⟩ := hP'.isPGroup ⟨x, hx⟩
    exact h2 x (hP'.le hx) k (congrArg Subtype.val hk)
  have heq := hRK.eq_of_le hRP' hP'K hP'.isPGroup
  rw [← heq]
  exact hP'

theorem wE_mem_centralizer : np.wE hn ∈ centralizer (rightConjugate A g : Set G) := by
  have h4 : 4 ≤ n := by omega
  apply np.YT_le hc (by omega) (y := ⟨np.wE hn, le_normalizer (np.wE_mem hn)⟩) (np.wE_mem hn)
  rw [np.ψA_wE hn]
  refine mem_rootAltP_of_fix h4 (p123n_mem hn) fun i hi => ?_
  exact p123n_apply_of_inS hn ⟨by omega, by omega, by omega⟩

theorem B_le_centralizer_W :
    rightConjugate A g ≤ centralizer (zpowers (np.wE hn) : Set G) := by
  intro b hb
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hwb : b * np.wE hn = np.wE hn * b :=
    mem_centralizer_iff.mp (np.wE_mem_centralizer hn hc) b hb
  exact ((Commute.zpow_left hwb.symm k)).eq

theorem standard_LE
    (hn9 : 9 ≤ n) (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34) :
    standardComponentIsStandard
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))) := by
  rcases lemma37_bender_of_le h4 h32 h34 hc.hyp hc.sylowR (W := zpowers (np.wE hn))
      (L := np.LE) (zpowers_le.mpr (np.wE_mem hn)) (np.isQuasisimple_LE hn)
      (le_inf np.LE_le_A (np.LE_le_centralizer hn)) (np.normalizer_inf_le_normalizer_LE hn)
      (np.isSylowOf_R_LE hn hc) with h | ⟨c, -, -, -, -, k, -, hk, ⟨e⟩⟩
  · exact h
  · exfalso
    rw [np.card_R (by omega)] at hk
    have hk2 : k = 2 := by
      have : 2 ^ k = 2 ^ 2 := hk
      exact Nat.pow_right_injective (le_refl 2) this
    subst hk2
    have hL := Nat.card_congr (np.LEEquiv hn).toEquiv
    have : Nontrivial (Fin (n - 3)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 2 (by norm_num),
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hL
    have h6 : (6 : ℕ).factorial ≤ (n - 3).factorial := Nat.factorial_le (by omega)
    have h6' : (6 : ℕ).factorial = 720 := rfl
    norm_num at hL
    omega

omit hc in
include hn in
theorem le_centralizer_of_le_normalizer_LE
    (hBN : rightConjugate A g ≤ normalizer (np.LE : Set G)) :
    rightConjugate A g ≤ centralizer (np.LE : Set G) := by
  set B := rightConjugate A g with hBdef
  set φ : B →* MulAut np.LE := (np.LE.normalizerMonoidHom).comp (Subgroup.inclusion hBN)
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  have : IsSimpleGroup B := np.equivB.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    have hcard := Nat.card_le_card_of_injective φ hinj
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr np.equivB.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin,
      Nat.card_congr (MulAut.congr (np.LEEquiv hn)).toEquiv] at hcard
    by_cases h9 : n = 9
    · subst h9
      rw [show (9 : ℕ) - 3 = 6 from rfl, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
        at hcard
      norm_num [Nat.factorial] at hcard
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [show k + 3 - 3 = k by omega,
        ← Nat.card_congr (conjPermEquiv (n := k) (by omega)).toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
      have heven : (k + 3).factorial / 2 * 2 = (k + 3).factorial :=
        Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
      have hexp : (k + 3).factorial = (k + 3) * ((k + 2) * ((k + 1) * k.factorial)) := by
        rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      have hge : 3 * (2 * (1 * k.factorial)) ≤ (k + 3) * ((k + 2) * ((k + 1) * k.factorial)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl))
      have hpos := Nat.factorial_pos k
      omega
  · intro b hb
    have hb' : (⟨b, hb⟩ : B) ∈ φ.ker := h ▸ mem_top _
    rw [MonoidHom.mem_ker] at hb'
    rw [mem_centralizer_iff]
    intro ℓ hℓ
    have h1 := congrArg (fun α : MulAut np.LE => ((α ⟨ℓ, hℓ⟩ : np.LE) : G)) hb'
    simp only [MulAut.one_apply] at h1
    change b * ℓ * b⁻¹ = ℓ at h1
    calc ℓ * b = (b * ℓ * b⁻¹) * b := by rw [h1]
      _ = b * ℓ := by group

include hn in
theorem false_of_le_centralizer_LE (hBL : rightConjugate A g ≤ centralizer (np.LE : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ n := by omega
  set B := rightConjugate A g with hBdef
  have hBC := np.B_le_centralizer_W hn hc
  have hs := restrictO_swap01_mul_swap h4 (a := ⟨4, by omega⟩) (b := ⟨5, by omega⟩) (by simp)
    (by simp)
  have hmem := mul_swap_mem_alternatingGroup (fourEmb h4) (a := ⟨4, by omega⟩)
    (b := ⟨5, by omega⟩) (by simp [Fin.ext_iff]) (show (0 : Fin 4) ≠ 1 by decide)
  rw [viaEmbeddingHom_swap] at hmem
  obtain ⟨x, hxB, hxe⟩ := np.hψB.exists_eq _ hmem
  have hxR : x ∈ normalizer (R : Set G) :=
    np.mem_normalizer_R h4 (x := ⟨x, le_normalizer hxB⟩) hxB
      (by rw [hxe]; exact normalizesV_of_stabO h4 hs.1)
  have hx2 : x * x = 1 := by
    have h1 : (⟨x, le_normalizer hxB⟩ * ⟨x, le_normalizer hxB⟩ :
        normalizer (B : Set G)) = 1 := np.injB (mul_mem hxB hxB) (one_mem _) (by
      rw [map_mul, hxe, map_one np.ψB, ← sq]
      exact PresentationLocal.swap_mul_swap_sq_eq_one (fourEmb_ne 0 _ le_rfl)
        (fourEmb_ne 0 _ (by norm_num)) (fourEmb_ne 1 _ le_rfl) (fourEmb_ne 1 _ (by norm_num)))
    exact congrArg Subtype.val h1
  have hxnR : x ∉ R := by
    intro hxR'
    have hV := np.ψB_mem_of_R (r := ⟨x, le_normalizer hxB⟩) hxR'
    have hfix := apply_eq_of_mem_rootVP h4 hV (i := ⟨4, by omega⟩) (by simp)
    rw [hxe, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne
      (fourEmb_ne 0 _ (by norm_num)).symm (fourEmb_ne 1 _ (by norm_num)).symm] at hfix
    exact absurd (congrArg Fin.val hfix) (by simp)
  have hzp : IsPGroup 2 (zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hx2])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hsup : IsPGroup 2 ↥(R ⊔ zpowers x) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup hzp (zpowers_le.mpr hxR)
  have hle : R ⊔ zpowers x ≤ centralizer (zpowers (np.wE hn) : Set G) ⊓
      centralizer (np.LE : Set G) ⊓ normalizer (R : Set G) :=
    sup_le (np.R_le_X hn hc) (zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hBC hxB, hBL hxB⟩, hxR⟩))
  have heq := (np.isSylowOf_R_LE hn hc).eq_of_le le_sup_left hle hsup
  exact hxnR (heq ▸ (le_sup_right (a := R) (mem_zpowers x)))

theorem not_normal_LE :
    ¬ (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))).Normal := by
  intro hN
  have hBC := np.B_le_centralizer_W hn hc
  have hBN : rightConjugate A g ≤ normalizer (np.LE : Set G) := by
    intro b hb
    apply mem_normalizer_of_conj_mem
    intro ℓ hℓ
    exact hN.conj_mem ⟨ℓ, np.LE_le_centralizer hn hℓ⟩ hℓ ⟨b, hBC hb⟩
  exact np.false_of_le_centralizer_LE hn hc (np.le_centralizer_of_le_normalizer_LE hn hBN)

theorem rankTwoHyp_LE_of (hK : Assembly.KProper Blueprint.Catalog G) (h32 : Lemma32)
    (hstd : standardComponentIsStandard
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G)))) :
    RankTwoStandard.RankTwoHyp (centralizer (zpowers (np.wE hn) : Set G))
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))) where
  kProper := LocalAnalysis.ComponentInitial.kProper_subgroup
    (fun e h => SectionRank.catalog_of_mulEquiv e h) hK _
  standard := hstd
  not_normal := np.not_normal_LE hn hc
  rank := by
    have hRE := h32 G A hc.hyp R hc.sylowR
    set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
    have hRX := np.R_le_X hn hc
    have hRC : R ≤ C := fun r hr => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hRX hr)).1).1
    have hRL : R ≤ centralizer (np.LE : Set G) := fun r hr =>
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hRX hr)).1).2
    refine SectionRank.le_pRank one_lt_two (E := R.subgroupOf C) (fun x hx => ?_) ?_ ?_
    · rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hRL (mem_subgroupOf.mp hx)) (y : G)
        (mem_subgroupOf.mp hy))
    · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · have h := congrArg Subtype.val
          (hRE.1.is_comm.comm ⟨((a : C) : G), a.2⟩ ⟨((b : C) : G), b.2⟩)
        exact h
      · rw [Subgroup.coe_pow]
        exact hRE.2 _ (mem_subgroupOf.mp hx)
    · rw [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv, np.card_R (by omega)]
      norm_num

theorem rankTwoHyp_LE
    (hn9 : 9 ≤ n) (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h34 : Asc08Lemma34) :
    RankTwoStandard.RankTwoHyp (centralizer (zpowers (np.wE hn) : Set G))
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))) :=
  np.rankTwoHyp_LE_of hn hc hK h32 (np.standard_LE hn hc hn9 h4 h32 h34)

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
