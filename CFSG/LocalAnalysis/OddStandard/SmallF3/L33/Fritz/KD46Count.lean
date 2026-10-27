module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Ktk
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCong
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Fus

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

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

variable [Finite X] {L : Subgroup X} {A : SDData t L} {C : A.CaseKD} (S : KDBase A C)

theorem t_mul_k_ne_t : t * S.k ≠ t := fun h => by
  have := ψ_k S
  rw [show S.k = 1 from mul_left_cancel (h.trans (mul_one t).symm), ψX_one] at this
  exact absurd this.symm (by decide)

theorem k_mem_C' : S.k ∈ centralizer ({t} : Set X) := A.T_le_centralizer (k_mem_T S)

theorem tk_mem_C : t * S.k ∈ centralizer ({t} : Set X) :=
  mul_mem SD.t_mem_C (k_mem_C' S)

theorem tz_mem_C : t * S.z ∈ centralizer ({t} : Set X) :=
  mul_mem SD.t_mem_C (A.T_le_centralizer (z_mem_T S))

theorem disjoint_cls_of_parity {a b : X} (h : (cls t a).ncard % 2 ≠ (cls t b).ncard % 2) :
    Disjoint (cls t a) (cls t b) := by
  rcases cls_disjoint_or_eq (t := t) a b with h' | h'
  · exact h'
  · exact absurd (by rw [h']) h

theorem mem_Om_cases {a : X} (ha : a ∈ Om t) :
    a = t ∨ a ∈ cls t (t * S.z) ∨ a ∈ cls t S.k ∨ a ∈ cls t (t * S.k) := by
  have haC : a ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr ha.2.symm
  have ha2 := sq_of_mem_Om (t_sq' (A := A)) ha
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1] at ha
    exact t_ne_one (A := A) (isConj_one_left.mp ha.1)
  obtain ⟨g, hg, h⟩ := S.inv_classes a haC ha2 ha1
  have hback : ∀ b, g * a * g⁻¹ = b → a ∈ cls t b := fun b hb =>
    ⟨g⁻¹, inv_mem hg, by rw [← hb]; group⟩
  rcases h with h | h | h | h | h
  · left
    have := hback _ h
    rw [cls_self_eq, Set.mem_singleton_iff] at this
    exact this
  · exact (not_conjTo_z S (conjTo_of_mem_Om_cls ha (hback _ h))).elim
  · exact Or.inr (Or.inl (hback _ h))
  · exact Or.inr (Or.inr (Or.inl (hback _ h)))
  · exact Or.inr (Or.inr (Or.inr (hback _ h)))

open Classical in
theorem card_Om_modEq : (Om t).ncard ≡ 1 + (if ConjTo t (t * S.z) then 1 else 0) +
    2 * ((if ConjTo t S.k then 1 else 0) + (if ConjTo t (t * S.k) then 1 else 0)) [MOD 4] := by
  have htOm : t ∈ Om t := ⟨IsConj.refl t, rfl⟩
  have hΩ : Om t = insert t (Om t ∩ cls t (t * S.z)) ∪
      ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k))) := by
    apply le_antisymm
    · intro a ha
      rcases mem_Om_cases S ha with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨ha, h⟩)
      · exact Or.inr (Or.inl ⟨ha, h⟩)
      · exact Or.inr (Or.inr ⟨ha, h⟩)
    · intro a ha
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_inter_iff] at ha
      rcases ha with (rfl | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)
      · exact htOm
      all_goals exact h
  have hodd : (cls t (t * S.z)).ncard % 2 = 1 := Nat.odd_iff.mp (odd_ncard_cls_tz S)
  have hk2 : (cls t S.k).ncard % 2 = 0 := by
    have := ncard_cls_k S
    unfold Nat.ModEq at this
    omega
  have htk2 : (cls t (t * S.k)).ncard % 2 = 0 := by
    have := ncard_cls_tk S
    unfold Nat.ModEq at this
    omega
  have hd1k : Disjoint (cls t (t * S.z)) (cls t S.k) := disjoint_cls_of_parity (by omega)
  have hd1tk : Disjoint (cls t (t * S.z)) (cls t (t * S.k)) := disjoint_cls_of_parity (by omega)
  have hd01 : Disjoint (insert t (Om t ∩ cls t (t * S.z)))
      ((Om t ∩ cls t S.k) ∪ (Om t ∩ cls t (t * S.k))) := by
    rw [Set.disjoint_left]
    intro a h0 h1
    rcases Set.mem_insert_iff.mp h0 with rfl | ⟨-, h0⟩
    · rcases h1 with ⟨-, h⟩ | ⟨-, h⟩
      · exact k_ne_t S (t_mem_cls_iff.mp h)
      · exact t_mul_k_ne_t S (t_mem_cls_iff.mp h)
    · rcases h1 with ⟨-, h⟩ | ⟨-, h⟩
      · exact Set.disjoint_left.mp hd1k h0 h
      · exact Set.disjoint_left.mp hd1tk h0 h
  rw [hΩ, Set.ncard_union_eq hd01]
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
  exact hP₀.add hP₁

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

end CFSG.OddStandard.SmallF3.L33.KD.KD46
