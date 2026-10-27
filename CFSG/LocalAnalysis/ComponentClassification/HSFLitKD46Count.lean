module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Ktk
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Fus

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] {t : X}

theorem cls_self_eq (t : X) : cls t t = {t} := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff, mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact mem_cls_self _

theorem mem_cls_comm {a b : X} (h : a ∈ cls t b) : b ∈ cls t a := by
  rw [cls_eq_of_mem h]
  exact mem_cls_self b

theorem cls_disjoint_or_eq (a b : X) : Disjoint (cls t a) (cls t b) ∨ cls t a = cls t b := by
  by_cases h : Disjoint (cls t a) (cls t b)
  · exact Or.inl h
  · right
    obtain ⟨c, hca, hcb⟩ := Set.not_disjoint_iff.mp h
    rw [← cls_eq_of_mem hca, cls_eq_of_mem hcb]

theorem t_mem_cls_iff {b : X} : t ∈ cls t b ↔ b = t := by
  constructor
  · intro h
    have := mem_cls_comm h
    rwa [cls_self_eq, Set.mem_singleton_iff] at this
  · intro h
    rw [h]
    exact mem_cls_self _

@[expose] def Om (t : X) : Set X := {a | IsConj t a ∧ t * a = a * t}

theorem cls_sub_Om {b : X} (hb : ConjTo t b) (hbC : b ∈ centralizer ({t} : Set X)) :
    cls t b ⊆ Om t := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨h, hh⟩ := hb
  refine ⟨isConj_iff.mpr ⟨g * h, by rw [← hh]; group⟩, ?_⟩
  exact (mem_centralizer_singleton_iff.mp (mul_mem (mul_mem hg hbC) (inv_mem hg))).symm

theorem conjTo_of_mem_Om_cls {a b : X} (ha : a ∈ Om t) (hab : a ∈ cls t b) : ConjTo t b := by
  obtain ⟨g, -, rfl⟩ := hab
  obtain ⟨h, hh⟩ := isConj_iff.mp ha.1
  refine ⟨g⁻¹ * h, ?_⟩
  calc g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
    _ = b := by rw [hh]; group

open Classical in
theorem Om_inter_cls (b : X) (hbC : b ∈ centralizer ({t} : Set X)) :
    Om t ∩ cls t b = (if ConjTo t b then cls t b else ∅) := by
  classical
  split_ifs with h
  · exact Set.inter_eq_right.mpr (cls_sub_Om h hbC)
  · ext a
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun ha hab => h (conjTo_of_mem_Om_cls ha hab)

theorem sq_of_mem_Om {a : X} (ht : t ^ 2 = 1) (ha : a ∈ Om t) : a ^ 2 = 1 := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp ha.1
  rw [conj_pow, ht]
  group

variable [Finite X] {L : Subgroup X} {A : L2Data t L} {C : A.CaseKD} (S : KDBase A C)

theorem k_mem_C' : S.k ∈ centralizer ({t} : Set X) := A.T_le_centralizer (k_mem_T S)

theorem tk_mem_C : t * S.k ∈ centralizer ({t} : Set X) :=
  mul_mem L2K.t_mem_C (k_mem_C' S)

theorem tz_mem_C : t * S.z ∈ centralizer ({t} : Set X) :=
  mul_mem L2K.t_mem_C (A.T_le_centralizer (z_mem_T S))

theorem d_mem_C : S.d ∈ centralizer ({t} : Set X) := A.T_le_centralizer (d_mem_T S)

theorem dt_mem_C : S.d * t ∈ centralizer ({t} : Set X) := mul_mem (d_mem_C S) L2K.t_mem_C

theorem mem_Om_cases {a : X} (ha : a ∈ Om t) :
    a = t ∨ a ∈ cls t (t * S.z) ∨ a ∈ cls t S.k ∨ a ∈ cls t (t * S.k) ∨
      (S.d ^ 2 = 1 ∧ (a ∈ cls t S.d ∨ a ∈ cls t (S.d * t))) := by
  have haC : a ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr ha.2.symm
  have ha2 := sq_of_mem_Om (t_sq' (A := A)) ha
  obtain ⟨g, hg, hgB | ⟨hgT, hgE⟩⟩ := exists_conj_B_or_out S haC ha2
  ·
    have hb : g * a * g⁻¹ ∈ cls t a := ⟨g, hg, rfl⟩
    have hcls : cls t a = cls t (g * a * g⁻¹) := (cls_eq_of_mem hb).symm
    have ha' : a ∈ cls t (g * a * g⁻¹) := by rw [← hcls]; exact mem_cls_self a
    have hconj : ConjTo t (g * a * g⁻¹) := conjTo_of_mem_Om_cls ha ha'
    obtain ⟨c, hc, hdk⟩ := d_conj_k S
    obtain ⟨i, j, l, hi, hj, hl, he⟩ := eq_of_mem_B S hgB
    rw [he] at ha' hconj
    have hdC := d_mem_C S
    have hzt := z_comm_t S
    have hdzk : ∀ j : ℕ, S.d * (S.z * t ^ j * S.k) * S.d⁻¹ = t ^ c * t ^ j * S.k := by
      intro j
      have h1 : S.d * (S.z * t ^ j * S.k) * S.d⁻¹ =
          (S.d * S.z * S.d⁻¹) * (S.d * t * S.d⁻¹) ^ j * (S.d * S.k * S.d⁻¹) := by
        rw [conj_pow]; group
      rw [h1, d_conj_z S, d_conj_t S, hdk]
      have hzz : S.z * t ^ j * (S.z * t ^ c * S.k) = (S.z * S.z) * t ^ c * t ^ j * S.k := by
        have hc' : Commute t S.z := hzt.symm
        have h2 : t ^ j * S.z = S.z * t ^ j := (hc'.pow_left j).eq
        calc S.z * t ^ j * (S.z * t ^ c * S.k) = S.z * (t ^ j * S.z) * t ^ c * S.k := by group
          _ = S.z * (S.z * t ^ j) * t ^ c * S.k := by rw [h2]
          _ = (S.z * S.z) * t ^ c * t ^ j * S.k := by
              rw [mul_assoc (S.z * S.z) (t ^ c), ← pow_add, add_comm, pow_add]; group
      rw [hzz, ← pow_two, z_sq S, one_mul]
    rcases pow_lt_two_eq (g := S.z) hi with hi' | hi' <;>
      rcases pow_lt_two_eq (g := t) hj with hj' | hj' <;>
      rcases pow_lt_two_eq (g := S.k) hl with hl' | hl' <;>
      rw [hi', hj', hl'] at ha' hconj
    · exfalso
      obtain ⟨h, hh⟩ := hconj
      apply t_ne_one' (A := A)
      calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
        _ = 1 := by rw [hh]; group
    · right; right; left
      simpa using ha'
    · left
      have h1 : a ∈ cls t t := by simpa using ha'
      rwa [cls_self_eq, Set.mem_singleton_iff] at h1
    · right; right; right; left
      simpa using ha'
    · exfalso
      exact not_conjTo_z S (by simpa using hconj)
    ·
      have h1 : S.z * S.k ∈ cls t (t ^ c * S.k) :=
        ⟨S.d⁻¹, inv_mem hdC, by
          have := hdzk 0
          rw [pow_zero, mul_one, mul_one] at this
          rw [inv_inv, ← this]; group⟩
      have h2 : a ∈ cls t (t ^ c * S.k) := by
        rw [← cls_eq_of_mem h1]
        simpa using ha'
      rcases pow_lt_two_eq (g := t) hc with hc' | hc' <;> rw [hc'] at h2
      · right; right; left; simpa using h2
      · right; right; right; left; exact h2
    · right; left
      rw [← hzt]
      simpa using ha'
    ·
      have h1 : S.z * t * S.k ∈ cls t (t ^ c * t * S.k) :=
        ⟨S.d⁻¹, inv_mem hdC, by
          have := hdzk 1
          simp only [pow_one] at this
          rw [inv_inv, ← this]; group⟩
      have h2 : a ∈ cls t (t ^ c * t * S.k) := by
        rw [← cls_eq_of_mem h1]
        simpa using ha'
      rcases pow_lt_two_eq (g := t) hc with hc' | hc' <;> rw [hc'] at h2
      · right; right; right; left; simpa using h2
      · right; right; left
        rw [← pow_two, t_sq' (A := A), one_mul] at h2
        exact h2
  ·
    have hf2 : (g * a * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ha2]; group
    obtain ⟨r, hr, hrd⟩ := exists_conj_d S hgT hgE hf2
    have hrC : r ∈ centralizer ({t} : Set X) := A.T_le_centralizer hr.1
    have hmem : r * (g * a * g⁻¹) * r⁻¹ ∈ cls t a := ⟨r * g, mul_mem hrC hg, by group⟩
    have hd2 : S.d ^ 2 = 1 := by
      have h' : (r * (g * a * g⁻¹) * r⁻¹) ^ 2 = 1 := by rw [conj_pow, hf2]; group
      rcases hrd with h | h <;> rw [h] at h'
      · exact h'
      · rwa [(Commute.mul_pow (comm_t (d_mem_T S)).symm.symm 2), t_sq' (A := A), mul_one] at h'
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hd2, ?_⟩)))
    rcases hrd with h | h <;> rw [h] at hmem
    · left; exact mem_cls_comm hmem
    · right; exact mem_cls_comm hmem

omit [Finite X] in
theorem tauX_cls {a b : X} (hb : b ∈ centralizer ({t} : Set X)) (h : a ∈ cls t b) :
    tauX A a = tauX A b := by
  obtain ⟨g, hg, rfl⟩ := h
  exact tauX_conj hg hb

omit [Finite X] in
theorem tauX_t : tauX A t = 1 := by
  rw [tauX_of_mem_T A.t_mem_T (show ψX A t = aff8 1 0 by rw [ψX_t, aff8_one])]
  rfl

theorem tauX_tz : tauX A (t * S.z) = 1 := by
  rw [tauX_of_mem_T (mul_mem A.t_mem_T (z_mem_T S))
    (show ψX A (t * S.z) = aff8 1 4 by rw [ψX_mul A.t_mem_T (z_mem_T S), ψX_t, ψ_z, one_mul])]
  rfl

theorem tauX_k : tauX A S.k = Multiplicative.ofAdd (0, 1) := by
  rw [tauX_of_mem_T (k_mem_T S) (ψ_k S)]
  rfl

theorem tauX_tk : tauX A (t * S.k) = Multiplicative.ofAdd (0, 1) := by
  rw [tauX_of_mem_T (mul_mem A.t_mem_T (k_mem_T S))
    (show ψX A (t * S.k) = k8 by rw [ψX_mul A.t_mem_T (k_mem_T S), ψX_t, ψ_k, one_mul])]
  rfl

theorem tauX_d : tauX A S.d = Multiplicative.ofAdd (1, 0) := by
  rw [tauX_of_mem_T (d_mem_T S) (ψ_d S)]
  rfl

theorem tauX_dt : tauX A (S.d * t) = Multiplicative.ofAdd (1, 0) := by
  rw [tauX_of_mem_T (mul_mem (d_mem_T S) A.t_mem_T)
    (show ψX A (S.d * t) = d8 by rw [ψX_mul (d_mem_T S) A.t_mem_T, ψX_t, ψ_d, mul_one])]
  rfl

omit [Finite X] in
include A in
theorem not_conjTo_of_sq_ne {b : X} (hb : b ^ 2 ≠ 1) : ¬ ConjTo t b := by
  rintro ⟨g, rfl⟩
  apply hb
  rw [conj_pow, t_sq' (A := A)]
  group

open Classical in
theorem card_Om_modEq : (Om t).ncard ≡ 1 + (if ConjTo t (t * S.z) then 1 else 0) +
    2 * ((if ConjTo t S.k then 1 else 0) + (if ConjTo t (t * S.k) then 1 else 0)) [MOD 4] := by
  have htOm : t ∈ Om t := ⟨IsConj.refl t, rfl⟩
  have hΩ : Om t = (insert t (Om t ∩ cls t (t * S.z)) ∪
      ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k)))) ∪
      ((Om t ∩ cls t S.d) ∪ (Om t ∩ cls t (S.d * t))) := by
    apply le_antisymm
    · intro a ha
      rcases mem_Om_cases S ha with h | h | h | h | ⟨-, h | h⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨ha, h⟩))
      · exact Or.inl (Or.inr (Or.inl ⟨ha, h⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨ha, h⟩))
      · exact Or.inr (Or.inl ⟨ha, h⟩)
      · exact Or.inr (Or.inr ⟨ha, h⟩)
    · intro a ha
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_inter_iff] at ha
      rcases ha with ((rfl | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)) | (⟨h, -⟩ | ⟨h, -⟩)
      · exact htOm
      all_goals exact h
  have hτ0 : ∀ a ∈ insert t (Om t ∩ cls t (t * S.z)), tauX A a = 1 := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ⟨-, h⟩
    · exact tauX_t
    · rw [tauX_cls (tz_mem_C S) h, tauX_tz S]
  have hτ1 : ∀ a ∈ (Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k)),
      tauX A a = Multiplicative.ofAdd (0, 1) := by
    rintro a (⟨-, h⟩ | ⟨-, h⟩)
    · rw [tauX_cls (k_mem_C' S) h, tauX_k S]
    · rw [tauX_cls (tk_mem_C S) h, tauX_tk S]
  have hτ2 : ∀ a ∈ (Om t ∩ cls t S.d) ∪ (Om t ∩ cls t (S.d * t)),
      tauX A a = Multiplicative.ofAdd (1, 0) := by
    rintro a (⟨-, h⟩ | ⟨-, h⟩)
    · rw [tauX_cls (d_mem_C S) h, tauX_d S]
    · rw [tauX_cls (dt_mem_C S) h, tauX_dt S]
  have hd01 : Disjoint (insert t (Om t ∩ cls t (t * S.z)))
      ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k))) := Set.disjoint_left.mpr fun a h0 h1 => by
    have := (hτ0 a h0).symm.trans (hτ1 a h1)
    exact absurd this (by decide)
  have hd2 : Disjoint (insert t (Om t ∩ cls t (t * S.z)) ∪
      ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k))))
      ((Om t ∩ cls t S.d) ∪ (Om t ∩ cls t (S.d * t))) := Set.disjoint_left.mpr fun a h01 h2 => by
    rcases h01 with h0 | h1
    · exact absurd ((hτ0 a h0).symm.trans (hτ2 a h2)) (by decide)
    · exact absurd ((hτ1 a h1).symm.trans (hτ2 a h2)) (by decide)
  rw [hΩ, Set.ncard_union_eq hd2, Set.ncard_union_eq hd01]
  have ht0 : t ∉ Om t ∩ cls t (t * S.z) := fun h => by
    have := t_mem_cls_iff.mp h.2
    exact z_ne_one S (mul_left_cancel (this.trans (mul_one t).symm))
  have hP₀ : (insert t (Om t ∩ cls t (t * S.z))).ncard ≡
      1 + (if ConjTo t (t * S.z) then 1 else 0) [MOD 4] := by
    rw [Set.ncard_insert_of_notMem ht0, Om_inter_cls _ (tz_mem_C S), add_comm 1]
    split_ifs with h
    · refine Nat.ModEq.add_right 1 ?_
      have hz : ∀ g ∈ centralizer ({t} : Set X), g * S.x ^ 2 * g⁻¹ ≠ t * S.x ^ 2 := by
        intro g hg hgz
        apply not_conjTo_z S
        obtain ⟨h', hh'⟩ := h
        refine ⟨g⁻¹ * h', ?_⟩
        calc g⁻¹ * h' * t * (g⁻¹ * h')⁻¹ = g⁻¹ * (h' * t * h'⁻¹) * g := by group
          _ = S.z := by rw [hh', show t * S.z = g * S.z * g⁻¹ from hgz.symm]; group
      rw [ncard_cls_t_mul]
      exact S.card_conj_z hz
    · rw [Set.ncard_empty]
  have hdk : Disjoint (Om t ∩ cls t S.k) (Om t ∩ cls t (t * S.k)) := by
    rcases cls_disjoint_or_eq (t := t) S.k (t * S.k) with h | h
    · exact h.mono Set.inter_subset_right Set.inter_subset_right
    · exfalso
      have : t * S.k ∈ cls t S.k := by rw [h]; exact mem_cls_self _
      obtain ⟨g, hg, hgk⟩ := this
      exact not_conj_k_tk S hg hgk
  have hP₁ : ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k))).ncard ≡
      2 * ((if ConjTo t S.k then 1 else 0) + (if ConjTo t (t * S.k) then 1 else 0)) [MOD 4] := by
    rw [Set.ncard_union_eq hdk, Om_inter_cls _ (k_mem_C' S), Om_inter_cls _ (tk_mem_C S),
      mul_add]
    refine Nat.ModEq.add ?_ ?_
    · split_ifs
      · exact (ncard_cls_k S).trans (by rfl)
      · rw [Set.ncard_empty]
    · split_ifs
      · exact (ncard_cls_tk S).trans (by rfl)
      · rw [Set.ncard_empty]
  have hP₂ : ((Om t ∩ cls t S.d) ∪ (Om t ∩ cls t (S.d * t))).ncard ≡ 0 [MOD 4] := by
    by_cases hd2 : S.d ^ 2 = 1
    · have h0 : ∀ b ∈ ({S.d, S.d * t} : Set X), (Om t ∩ cls t b).ncard ≡ 0 [MOD 4] := by
        intro b hb
        have hbC : b ∈ centralizer ({t} : Set X) := by
          rcases hb with rfl | hb
          · exact d_mem_C S
          · rw [Set.mem_singleton_iff.mp hb]; exact dt_mem_C S
        rw [Om_inter_cls _ hbC]
        split_ifs
        · rcases hb with rfl | hb
          · exact ncard_cls_d S hd2
          · rw [Set.mem_singleton_iff.mp hb]; exact ncard_cls_dt S hd2
        · rw [Set.ncard_empty]
      rcases cls_disjoint_or_eq (t := t) S.d (S.d * t) with h | h
      · rw [Set.ncard_union_eq (h.mono Set.inter_subset_right Set.inter_subset_right)]
        exact (h0 _ (Or.inl rfl)).add (h0 _ (Or.inr rfl))
      · rw [h, Set.union_self]
        exact h0 _ (Or.inr rfl)
    · have hn1 : ¬ ConjTo t S.d := not_conjTo_of_sq_ne (A := A) hd2
      have hn2 : ¬ ConjTo t (S.d * t) := by
        refine not_conjTo_of_sq_ne (A := A) ?_
        rwa [(Commute.mul_pow (comm_t (d_mem_T S)) 2), t_sq' (A := A), mul_one]
      rw [Om_inter_cls _ (d_mem_C S), Om_inter_cls _ (dt_mem_C S)]
      simp only [hn1, hn2, ↓reduceIte, Set.union_self, Set.ncard_empty]
      rfl
  have := (hP₀.add hP₁).add hP₂
  rwa [add_zero] at this

theorem card_Om_modEq_index [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (ht : t ^ 2 = 1) : (Om t).ncard ≡ (centralizer ({t} : Set X)).index [MOD 4] := by
  have hcong := card_conj_modEq_card_conj_centralizer (eq_one_of_isSimpleGroup hnab) ht t
  have hclass : {a | IsConj t a}.ncard = (centralizer ({t} : Set X)).index := by
    have := relIndex_inf_centralizer_eq_ncard (⊤ : Subgroup X) t
    rw [top_inf_eq, relIndex_top_right] at this
    rw [this]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, mem_top, true_and, isConj_iff]
  rw [hclass] at hcong
  exact hcong

end CFSG.ComponentClassification.HSFLit.KD46
