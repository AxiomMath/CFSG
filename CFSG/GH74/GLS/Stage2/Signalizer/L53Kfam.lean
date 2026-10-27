module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.KInftyNat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_gen {S : Set (Subgroup G)} {B : Subgroup G} (hB : B ∈ S) : B ≤ gen S := by
  intro x hx
  exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨B, hB, hx⟩)

theorem gen_le {S : Set (Subgroup G)} {H : Subgroup G} (h : ∀ B ∈ S, B ≤ H) : gen S ≤ H := by
  unfold gen
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx
  exact h B hB hxB

theorem gen_mono {S S' : Set (Subgroup G)} (h : S ⊆ S') : gen S ≤ gen S' :=
  gen_le fun _ hB => le_gen (h hB)

theorem Klow_anti {P Q R : Subgroup G} (h : R ≤ Q) : Klow P Q ⊆ Klow P R := by
  rintro _ ⟨hB, hQ, hall⟩
  exact ⟨hB, h.trans hQ, fun A hA hAR hBA => hall A hA (hAR.trans h) hBA⟩

theorem Kup_anti {P Q R : Subgroup G} (h : R ≤ Q) : Kup P Q ⊆ Kup P R := by
  rintro B ⟨hB, hQ⟩
  exact ⟨hB, (Subgroup.commutator_mono_right h).trans hQ⟩

theorem Kfam_succ_even (P : Subgroup G) {n : ℕ} (hn : Even n) :
    Kfam P (n + 1) = Klow P (gen (Kfam P n)) := by
  show (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))) = _
  simp only [hn, ↓reduceIte]

theorem Kfam_succ_odd (P : Subgroup G) {n : ℕ} (hn : ¬ Even n) :
    Kfam P (n + 1) = Kup P (gen (Kfam P n)) := by
  show (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))) = _
  simp only [hn, ↓reduceIte]

theorem Kfam_subset_classTwo (P : Subgroup G) (n : ℕ) : Kfam P n ⊆ classTwo P := by
  cases n with
  | zero => exact fun B hB => hB
  | succ n =>
    show (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))) ⊆ classTwo P
    split_ifs
    · exact fun B hB => hB.1
    · exact fun B hB => hB.1

theorem Kfam_mono_aux (P : Subgroup G) (j : ℕ) :
    Kfam P (2 * j + 2) ⊆ Kfam P (2 * j) ∧ Kfam P (2 * j + 1) ⊆ Kfam P (2 * j + 3) := by
  induction j with
  | zero =>
    have h2 : Kfam P 2 ⊆ Kfam P 0 := Kfam_subset_classTwo P 2
    refine ⟨h2, ?_⟩
    have e1 : Kfam P 1 = Klow P (gen (Kfam P 0)) := Kfam_succ_even P (by decide)
    have e3 : Kfam P 3 = Klow P (gen (Kfam P 2)) := Kfam_succ_even P (by decide)
    rw [show 2 * 0 + 1 = 1 from rfl, show 2 * 0 + 3 = 3 from rfl, e1, e3]
    exact Klow_anti (gen_mono h2)
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hodd : ∀ m, ¬ Even (2 * m + 1) := fun m => by simp
    have heven : ∀ m, Even (2 * m + 2) := fun m => ⟨m + 1, by ring⟩
    have h1 : Kfam P (2 * (j + 1) + 2) ⊆ Kfam P (2 * (j + 1)) := by
      have e1 : Kfam P (2 * (j + 1) + 2) = Kup P (gen (Kfam P (2 * j + 3))) := by
        rw [show 2 * (j + 1) + 2 = (2 * j + 3) + 1 by ring]
        exact Kfam_succ_odd P (hodd (j + 1))
      have e2 : Kfam P (2 * (j + 1)) = Kup P (gen (Kfam P (2 * j + 1))) := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
        exact Kfam_succ_odd P (hodd j)
      rw [e1, e2]
      exact Kup_anti (gen_mono ih2)
    refine ⟨h1, ?_⟩
    have e1 : Kfam P (2 * (j + 1) + 1) = Klow P (gen (Kfam P (2 * j + 2))) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring]
      exact Kfam_succ_even P (heven j)
    have e2 : Kfam P (2 * (j + 1) + 3) = Klow P (gen (Kfam P (2 * j + 4))) := by
      rw [show 2 * (j + 1) + 3 = (2 * j + 4) + 1 by ring]
      exact Kfam_succ_even P (by simpa [mul_add] using heven (j + 1))
    rw [e1, e2]
    have : gen (Kfam P (2 * j + 4)) ≤ gen (Kfam P (2 * j + 2)) :=
      gen_mono (by simpa [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, mul_add] using h1)
    exact Klow_anti this

theorem Kfam_even_antitone (P : Subgroup G) : Antitone (fun j : ℕ => Kfam P (2 * j)) :=
  antitone_nat_of_succ_le fun j => by
    have := (Kfam_mono_aux P j).1
    simpa [mul_add] using this

theorem Kfam_odd_monotone (P : Subgroup G) : Monotone (fun j : ℕ => Kfam P (2 * j + 1)) :=
  monotone_nat_of_le_succ fun j => by
    have := (Kfam_mono_aux P j).2
    simpa [mul_add, add_assoc] using this

theorem exists_stable_of_antitone {α : Type*} [PartialOrder α] [Finite α] {a : ℕ → α}
    (ha : Antitone a) : ∃ J, ∀ j, J ≤ j → a j = a J := by
  obtain ⟨m, hm⟩ := (Set.toFinite (Set.range a)).exists_minimal (Set.range_nonempty a)
  obtain ⟨J, rfl⟩ := hm.prop
  exact ⟨J, fun j hj => hm.eq_of_le ⟨j, rfl⟩ (ha hj)⟩

theorem exists_stable_of_monotone {α : Type*} [PartialOrder α] [Finite α] {a : ℕ → α}
    (ha : Monotone a) : ∃ J, ∀ j, J ≤ j → a j = a J := by
  obtain ⟨m, hm⟩ := (Set.toFinite (Set.range a)).exists_maximal (Set.range_nonempty a)
  obtain ⟨J, rfl⟩ := hm.prop
  exact ⟨J, fun j hj => hm.eq_of_ge ⟨j, rfl⟩ (ha hj)⟩

theorem exists_stable [Finite G] (P : Subgroup G) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j, J ≤ j →
      Kfam P (2 * j) = Kfam P (2 * J) ∧ Kfam P (2 * j + 1) = Kfam P (2 * J + 1) := by
  obtain ⟨J₁, hJ₁⟩ := exists_stable_of_antitone (Kfam_even_antitone P)
  obtain ⟨J₂, hJ₂⟩ := exists_stable_of_monotone (Kfam_odd_monotone P)
  refine ⟨max J₁ J₂ + 1, by omega, fun j hj => ⟨?_, ?_⟩⟩
  · have h1 := hJ₁ j (by omega)
    have h2 := hJ₁ (max J₁ J₂ + 1) (by omega)
    rw [h1, h2]
  · have h1 := hJ₂ j (by omega)
    have h2 := hJ₂ (max J₁ J₂ + 1) (by omega)
    rw [h1, h2]

theorem iInter_Kfam_eq [Finite G] (P : Subgroup G) {J : ℕ}
    (hJ : ∀ j, J ≤ j → Kfam P (2 * j) = Kfam P (2 * J)) :
    (⋂ i : ℕ, Kfam P (2 * i)) = Kfam P (2 * J) := by
  ext B
  simp only [Set.mem_iInter]
  constructor
  · intro h; exact h J
  · intro h i
    by_cases hi : J ≤ i
    · rw [hJ i hi]; exact h
    · exact Kfam_even_antitone P (le_of_lt (not_le.mp hi)) h

theorem iUnion_Kfam_eq [Finite G] (P : Subgroup G) {J : ℕ}
    (hJ : ∀ j, J ≤ j → Kfam P (2 * j + 1) = Kfam P (2 * J + 1)) :
    (⋃ i : ℕ, Kfam P (2 * i + 1)) = Kfam P (2 * J + 1) := by
  ext B
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : J ≤ i
    · rw [← hJ i h]; exact hi
    · exact Kfam_odd_monotone P (le_of_lt (not_le.mp h)) hi
  · intro h; exact ⟨J, h⟩

theorem Klow_restrict {S T Q B : Subgroup G} (hTS : T ≤ S) (hBT : B ≤ T) (h : B ∈ Klow S Q) :
    B ∈ Klow T Q := by
  obtain ⟨⟨_, hB2⟩, hQ, hall⟩ := h
  exact ⟨⟨hBT, hB2⟩, hQ, fun A hA hAQ hBA => hall A ⟨hA.1.trans hTS, hA.2⟩ hAQ hBA⟩

theorem Klow_extend {S T Q B : Subgroup G} (hTS : T ≤ S) (hBT : B ≤ T) (hQT : Q ≤ T)
    (h : B ∈ Klow T Q) : B ∈ Klow S Q := by
  obtain ⟨⟨_, hB2⟩, hQ, hall⟩ := h
  exact ⟨⟨hBT.trans hTS, hB2⟩, hQ, fun A hA hAQ hBA => hall A ⟨hAQ.trans hQT, hA.2⟩ hAQ hBA⟩

theorem sandwich [Finite G] {S T : Subgroup G} (hTS : T ≤ S)
    (hle : ∀ m, 1 ≤ m → gen (Kfam S m) ≤ T) (m : ℕ) :
    (Even m → Kfam T m ⊆ Kfam S m ∧ (⋂ i : ℕ, Kfam S (2 * i)) ⊆ Kfam T m) ∧
      (¬ Even m → Kfam S m ⊆ Kfam T m ∧ Kfam T m ⊆ ⋃ i : ℕ, Kfam S (2 * i + 1)) := by
  obtain ⟨J, hJ1, hJ⟩ := exists_stable S
  have hI : (⋂ i : ℕ, Kfam S (2 * i)) = Kfam S (2 * J) :=
    iInter_Kfam_eq S fun j hj => (hJ j hj).1
  have hU : (⋃ i : ℕ, Kfam S (2 * i + 1)) = Kfam S (2 * J + 1) :=
    iUnion_Kfam_eq S fun j hj => (hJ j hj).2
  have hTT : ∀ n, gen (Kfam T n) ≤ T := fun n => gen_le fun B hB => (Kfam_subset_classTwo T n hB).1
  induction m with
  | zero =>
    refine ⟨fun _ => ⟨fun B hB => ⟨hB.1.trans hTS, hB.2⟩, ?_⟩, fun h => absurd (⟨0, rfl⟩ : Even 0) h⟩
    intro B hB
    have h2 : B ∈ Kfam S (2 * 1) := Set.mem_iInter.mp hB 1
    have h0 : B ∈ Kfam S (2 * 0) := Set.mem_iInter.mp hB 0
    exact ⟨(le_gen h2).trans (hle (2 * 1) (by omega)), h0.2⟩
  | succ m ih =>
    by_cases hm : Even m
    · have hm' : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using hm
      refine ⟨fun h => absurd h hm', fun _ => ⟨?_, ?_⟩⟩
      · intro B hB
        rw [Kfam_succ_even S hm] at hB
        rw [Kfam_succ_even T hm]
        have hBT : B ≤ T := (le_gen (by rw [Kfam_succ_even S hm]; exact hB)).trans
          (hle (m + 1) (by omega))
        exact Klow_restrict hTS hBT (Klow_anti (gen_mono (ih.1 hm).1) hB)
      · intro B hB
        rw [Kfam_succ_even T hm] at hB
        have hκ : gen (Kfam S (2 * J)) ≤ gen (Kfam T m) := by
          rw [← hI]; exact gen_mono (ih.1 hm).2
        have h1 : B ∈ Klow T (gen (Kfam S (2 * J))) := Klow_anti hκ hB
        have h2 : B ∈ Klow S (gen (Kfam S (2 * J))) :=
          Klow_extend hTS hB.1.1 (hle (2 * J) (by omega)) h1
        rw [Set.mem_iUnion]
        refine ⟨J, ?_⟩
        rw [Kfam_succ_even S (⟨J, by ring⟩ : Even (2 * J))] at *
        exact h2
    · have hm' : Even (m + 1) := by simpa [Nat.even_add_one] using hm
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hm' h⟩
      · intro B hB
        rw [Kfam_succ_odd T hm] at hB
        rw [Kfam_succ_odd S hm]
        refine ⟨⟨hB.1.1.trans hTS, hB.1.2⟩, ?_⟩
        exact (Subgroup.commutator_mono_right (gen_mono (ih.2 hm).1)).trans hB.2
      · intro B hB
        have h2 : B ∈ Kfam S (2 * (J + 1)) := Set.mem_iInter.mp hB (J + 1)
        have hBT : B ≤ T := (le_gen h2).trans (hle (2 * (J + 1)) (by omega))
        have hB2 : B ∈ classTwo S := Kfam_subset_classTwo S _ h2
        rw [Kfam_succ_odd T hm]
        have hlam : gen (Kfam T m) ≤ gen (Kfam S (2 * J + 1)) := by
          rw [← hU]; exact gen_mono (ih.2 hm).2
        have e : Kfam S (2 * (J + 1)) = Kup S (gen (Kfam S (2 * J + 1))) := by
          rw [show 2 * (J + 1) = (2 * J + 1) + 1 by ring]
          exact Kfam_succ_odd S (by simp)
        rw [e] at h2
        exact ⟨⟨hBT, hB2.2⟩, (Subgroup.commutator_mono_right hlam).trans h2.2⟩

theorem kInfty_eq_gen [Finite G] (P : Subgroup G) {J : ℕ}
    (hJ : ∀ j, J ≤ j → Kfam P (2 * j) = Kfam P (2 * J)) : kInfty P = gen (Kfam P (2 * J)) := by
  unfold kInfty; rw [iInter_Kfam_eq P hJ]

theorem kLowInfty_eq_gen [Finite G] (P : Subgroup G) {J : ℕ}
    (hJ : ∀ j, J ≤ j → Kfam P (2 * j + 1) = Kfam P (2 * J + 1)) :
    kLowInfty P = gen (Kfam P (2 * J + 1)) := by
  unfold kLowInfty; rw [iUnion_Kfam_eq P hJ]

theorem kInfty_eq_of_le [Finite G] {S T : Subgroup G} (hTS : T ≤ S)
    (hle : ∀ m, 1 ≤ m → gen (Kfam S m) ≤ T) :
    kInfty S = kInfty T ∧ kLowInfty S = kLowInfty T := by
  obtain ⟨J₁, -, hJ₁⟩ := exists_stable S
  obtain ⟨J₂, -, hJ₂⟩ := exists_stable T
  have hIS : (⋂ i : ℕ, Kfam S (2 * i)) = Kfam S (2 * J₁) :=
    iInter_Kfam_eq S fun i hi => (hJ₁ i hi).1
  have hUS : (⋃ i : ℕ, Kfam S (2 * i + 1)) = Kfam S (2 * J₁ + 1) :=
    iUnion_Kfam_eq S fun i hi => (hJ₁ i hi).2
  have hKS := kInfty_eq_gen S fun i hi => (hJ₁ i hi).1
  have hKT := kInfty_eq_gen T fun i hi => (hJ₂ i hi).1
  have hLS := kLowInfty_eq_gen S fun i hi => (hJ₁ i hi).2
  have hLT := kLowInfty_eq_gen T fun i hi => (hJ₂ i hi).2
  obtain ⟨j, hj⟩ : ∃ j, j = max J₁ J₂ := ⟨_, rfl⟩
  have hj1 : J₁ ≤ j := hj ▸ le_max_left _ _
  have hj2 : J₂ ≤ j := hj ▸ le_max_right _ _
  have hev := (sandwich hTS hle (2 * j)).1 ⟨j, by ring⟩
  have hSj : Kfam S (2 * j) = Kfam S (2 * J₁) := (hJ₁ j hj1).1
  have hTj : Kfam T (2 * j) = Kfam T (2 * J₂) := (hJ₂ j hj2).1
  have e : Kfam S (2 * j) = Kfam T (2 * j) :=
    Set.Subset.antisymm (by rw [hSj, ← hIS]; exact hev.2) hev.1
  have hodd := (sandwich hTS hle (2 * j + 1)).2 (by simp)
  have hSj' : Kfam S (2 * j + 1) = Kfam S (2 * J₁ + 1) := (hJ₁ j hj1).2
  have hTj' : Kfam T (2 * j + 1) = Kfam T (2 * J₂ + 1) := (hJ₂ j hj2).2
  have e' : Kfam S (2 * j + 1) = Kfam T (2 * j + 1) :=
    Set.Subset.antisymm hodd.1 (by rw [hSj', ← hUS]; exact hodd.2)
  refine ⟨?_, ?_⟩
  · rw [hKS, hKT, ← hSj, ← hTj, e]
  · rw [hLS, hLT, ← hSj', ← hTj', e']

theorem mapS_conj_eq {P : Subgroup G} {x : G} (hx : x ∈ normalizer (P : Set G)) :
    mapS (MulAut.conj x) P = P := by
  ext y
  rw [mem_mapS_iff]
  simp only [MulAut.conj_symm_apply]
  have := Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * y * x)
  rw [this]
  have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  rw [e]

theorem kLowInfty_map (φ : G ≃* G) (P : Subgroup G) :
    kLowInfty (mapS φ P) = mapS φ (kLowInfty P) := by
  unfold kLowInfty
  apply gen_mapS φ
  intro B
  simp only [Set.mem_iUnion]
  exact exists_congr fun i => mapS_mem_Kfam φ P (2 * i + 1) B

theorem normalizer_le_kLowInfty (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer ((kLowInfty P : Subgroup G) : Set G) := by
  intro x hx
  have h1 := kLowInfty_map (MulAut.conj x) P
  rw [mapS_conj_eq hx] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h2 : (MulAut.conj x) y ∈ mapS (MulAut.conj x) (kLowInfty P) ↔ y ∈ kLowInfty P :=
    apply_mem_mapS_iff _
  rw [← h1] at h2
  simpa [MulAut.conj_apply] using h2.symm

theorem normal_of_le [Finite G] {S T : Subgroup G} (hTn : T.Normal) (hTS : T ≤ S)
    (hle : ∀ m, 1 ≤ m → gen (Kfam S m) ≤ T) :
    (kInfty S).Normal ∧ (kLowInfty S).Normal := by
  obtain ⟨h1, h2⟩ := kInfty_eq_of_le hTS hle
  have hT : normalizer (T : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hTn
  rw [h1, h2]
  refine ⟨Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_),
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)⟩
  · have := normalizer_le_kInfty T
    rwa [hT] at this
  · have := normalizer_le_kLowInfty T
    rwa [hT] at this

end CFSG.GH74.GLS.Stage2.Signalizer.L53
