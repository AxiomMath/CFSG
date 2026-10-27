module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFHArith

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

structure HNFOrbitData (G : Type) [Group G] (u : G) (β : Fin 9 → G) : Prop where
  card_C : Nat.card ↥(centralizer ({u} : Set G)) = 177408000
  card_G : Nat.card G = 273030912000000
  beta_zero : β 0 = u
  beta_class : ∀ i, ∃ g : G, β i = g * u * g⁻¹
  lower : ∀ i, hnfS i ≤ (conjOrb (centralizer ({u} : Set G)) (β i)).ncard
  disjoint : ∀ i j, i ≠ j → Disjoint (conjOrb (centralizer ({u} : Set G)) (β i))
    (conjOrb (centralizer ({u} : Set G)) (β j))

section Main

variable [Finite G] {u : G} {β : Fin 9 → G}

omit [Finite G] in
private theorem card_class (hD : HNFOrbitData G u β) :
    (conjOrb ⊤ u).ncard = 1539000 := by
  have h := ncard_conjOrb_mul (⊤ : Subgroup G) u
  rw [top_inf_eq, hD.card_C, Subgroup.card_top, hD.card_G] at h
  omega

omit [Finite G] in
private theorem card_centralizer_of_mem (hD : HNFOrbitData G u β) {v : G}
    (hv : v ∈ conjOrb ⊤ u) : Nat.card ↥(centralizer ({v} : Set G)) = 177408000 := by
  have h := ncard_conjOrb_mul (⊤ : Subgroup G) v
  rw [top_inf_eq, Subgroup.card_top, hD.card_G, conjOrb_eq_of_mem hv, card_class hD] at h
  omega

omit [Finite G] in
private theorem orbit_subset_class (hD : HNFOrbitData G u β) (i : Fin 9) :
    conjOrb (centralizer ({u} : Set G)) (β i) ⊆ conjOrb ⊤ u := by
  obtain ⟨g, hg⟩ := hD.beta_class i
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c * g, mem_top _, by rw [hg]; simp [mul_assoc]⟩

theorem HNFOrbitData.card_orbit (hD : HNFOrbitData G u β) (i : Fin 9) :
    (conjOrb (centralizer ({u} : Set G)) (β i)).ncard = hnfS i := by
  set C := centralizer ({u} : Set G)
  have hunion : (⋃ i, conjOrb C (β i)).ncard = ∑ i, (conjOrb C (β i)).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) (fun i j hij => hD.disjoint i j hij),
      finsum_eq_sum_of_fintype]
  have hsub : (⋃ i, conjOrb C (β i)) ⊆ conjOrb ⊤ u := Set.iUnion_subset (orbit_subset_class hD)
  have hle : ∑ i, (conjOrb C (β i)).ncard ≤ ∑ i, hnfS i := by
    rw [← hunion, hnfS_sum, ← card_class hD]
    exact Set.ncard_le_ncard hsub
  have hlow : ∑ i, hnfS i ≤ ∑ i, (conjOrb C (β i)).ncard :=
    Finset.sum_le_sum fun i _ => hD.lower i
  have hsum : ∑ i, hnfS i = ∑ i, (conjOrb C (β i)).ncard := le_antisymm hlow hle
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hD.lower j)).1 hsum i (Finset.mem_univ i)).symm

theorem HNFOrbitData.iUnion_orbit (hD : HNFOrbitData G u β) :
    (⋃ i, conjOrb (centralizer ({u} : Set G)) (β i)) = conjOrb ⊤ u := by
  set C := centralizer ({u} : Set G)
  have hunion : (⋃ i, conjOrb C (β i)).ncard = ∑ i, (conjOrb C (β i)).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) (fun i j hij => hD.disjoint i j hij),
      finsum_eq_sum_of_fintype]
  have hsub : (⋃ i, conjOrb C (β i)) ⊆ conjOrb ⊤ u := Set.iUnion_subset (orbit_subset_class hD)
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [hunion, card_class hD, ← hnfS_sum]
  exact (Finset.sum_congr rfl fun i _ => (hD.card_orbit i).symm).le

theorem HNFOrbitData.ncard_eq_sum (hD : HNFOrbitData G u β) {S : Set G} (hS : S ⊆ conjOrb ⊤ u) :
    S.ncard = ∑ i, (S ∩ conjOrb (centralizer ({u} : Set G)) (β i)).ncard := by
  have hS' : S = ⋃ i, S ∩ conjOrb (centralizer ({u} : Set G)) (β i) := by
    rw [← Set.inter_iUnion, hD.iUnion_orbit]
    exact (Set.inter_eq_left.2 hS).symm
  conv_lhs => rw [hS']
  rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _), finsum_eq_sum_of_fintype]
  intro i j hij
  exact (hD.disjoint i j hij).mono Set.inter_subset_right Set.inter_subset_right

omit [Finite G] in
theorem HNFOrbitData.orbit_zero (hD : HNFOrbitData G u β) :
    conjOrb (centralizer ({u} : Set G)) (β 0) = {u} := by
  rw [hD.beta_zero]
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    have := mem_centralizer_singleton_iff.1 hc
    rw [Set.mem_singleton_iff, this]
    simp
  · rintro rfl
    exact mem_conjOrb_self _ _

private theorem valid_trace (hD : HNFOrbitData G u β) {K X : Subgroup G}
    (hKC : K ≤ centralizer ({u} : Set G))
    (hidx : (K.subgroupOf (centralizer ({u} : Set G))).index = 2) (hKX : K ≤ X) (v : G) :
    hnfValid fun i => (conjOrb X v ∩ conjOrb (centralizer ({u} : Set G)) (β i)).ncard := by
  intro i
  have h := ncard_kinvariant_subset hKC hidx (β := β i)
    (S := conjOrb X v ∩ conjOrb (centralizer ({u} : Set G)) (β i)) Set.inter_subset_right
    (fun k hk y hy => ⟨conj_mem_conjOrb hy.1 (hKX hk), conj_mem_conjOrb hy.2 (hKC hk)⟩)
  rw [hD.card_orbit i] at h
  exact h

theorem hnf_overgroup (hD : HNFOrbitData G u β) (hno : ∀ X : Subgroup G, X.index ≠ 2)
    {K : Subgroup G} (hKC : K ≤ centralizer ({u} : Set G))
    (hidx : (K.subgroupOf (centralizer ({u} : Set G))).index = 2) :
    ∀ X : Subgroup G, K ≤ X → X ≤ centralizer ({u} : Set G) ∨ X = ⊤ := by
  intro X hKX
  set C := centralizer ({u} : Set G) with hC
  have hKcard : Nat.card K = 88704000 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf C)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hD.card_C] at h1
    omega
  have hNcard : Nat.card ↥(X ⊓ C) = 88704000 ∨ Nat.card ↥(X ⊓ C) = 177408000 := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_inf hKX hKC)
    have hdvd : Nat.card ↥(X ⊓ C) ∣ Nat.card ↥C := Subgroup.card_dvd_of_le inf_le_right
    rw [hD.card_C, hm, hKcard] at hdvd
    have hm2 : m ∣ 2 := by
      have : 88704000 * m ∣ 88704000 * 2 := by simpa using hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with rfl | rfl
    · left; rw [hm, hKcard]
    · right; rw [hm, hKcard]
  set O := conjOrb X u with hO
  have hOsub : O ⊆ conjOrb ⊤ u := conjOrb_mono le_top u
  have hXcard : O.ncard * Nat.card ↥(X ⊓ C) = Nat.card X := ncard_conjOrb_mul X u
  have hXG : Nat.card X ∣ Nat.card G := Subgroup.card_subgroup_dvd_card X
  have huO : u ∈ O := mem_conjOrb_self X u
  set a : Fin 9 → ℕ := fun i => (O ∩ conjOrb C (β i)).ncard with ha
  have hav : hnfValid a := valid_trace hD hKC hidx hKX u
  have hΓ0 : conjOrb C (β 0) = {u} := hD.orbit_zero
  have ha0 : a 0 = 1 := by
    simp only [ha, hΓ0]
    rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 huO)]
    simp
  have hsumO : ∑ i, a i = O.ncard := (hD.ncard_eq_sum hOsub).symm
  have hdvdG : (∑ i, a i) * Nat.card ↥(X ⊓ C) ∣ 273030912000000 := by
    rw [hsumO, hXcard, ← hD.card_G]
    exact hXG
  rcases hnf_arith_main a _ hav ha0 hNcard hdvdG with h | h | ⟨hcu, hbad⟩
  ·
    left
    have hOu : ∀ x ∈ O, x = u := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hD.iUnion_orbit ▸ hOsub hx)
      by_cases hi0 : i = 0
      · subst hi0
        rw [hΓ0] at hi
        exact hi
      · exfalso
        have hpos : 0 < i := Fin.pos_iff_ne_zero.2 hi0
        have := h i hpos
        have hempty : O ∩ conjOrb C (β i) = ∅ := by
          have : (O ∩ conjOrb C (β i)).ncard = 0 := h i hpos
          exact (Set.ncard_eq_zero (Set.toFinite _)).1 this
        exact (Set.eq_empty_iff_forall_notMem.1 hempty) x ⟨hx, hi⟩
    intro x hx
    have := hOu (x * u * x⁻¹) ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h2 : x * u = u * x := by
      calc x * u = (x * u * x⁻¹) * x := by simp
        _ = u * x := by rw [this]
    exact h2
  ·
    right
    have hO : O.ncard = 1539000 := by
      rw [← hsumO, ← hnfS_sum]
      exact Finset.sum_congr rfl fun i _ => h i
    rcases hNcard with hN | hN
    · exfalso
      have h1 : Nat.card X = 1539000 * 88704000 := by rw [← hXcard, hO, hN]
      have h2 := Subgroup.card_mul_index X
      rw [h1, hD.card_G] at h2
      have : X.index = 2 := by omega
      exact hno X this
    · have h1 : Nat.card X = Nat.card G := by rw [← hXcard, hO, hN, hD.card_G]
      exact (Subgroup.card_eq_iff_eq_top X).1 h1
  ·
    exfalso
    have hOcard : O.ncard = 6480 := by
      rw [← hsumO, hbad]
      simp [Fin.sum_univ_succ]
    have hXc : Nat.card X = 6480 * 88704000 := by rw [← hXcard, hOcard, hcu]
    have ha1 : a 1 = 704 := by rw [hbad]; rfl
    have hΓ1 : (conjOrb C (β 1)).ncard = 1408 := hD.card_orbit 1
    have hnot : ¬ conjOrb C (β 1) ⊆ O := by
      intro hsub
      have : O ∩ conjOrb C (β 1) = conjOrb C (β 1) := Set.inter_eq_right.2 hsub
      have h2 : a 1 = 1408 := by simp only [ha, this]; exact hΓ1
      omega
    obtain ⟨v, hv1, hvO⟩ := Set.not_subset.1 hnot
    have hvD : v ∈ conjOrb ⊤ u := orbit_subset_class hD 1 hv1
    set B := conjOrb X v with hB
    have hBsub : B ⊆ conjOrb ⊤ u := (conjOrb_mono le_top v).trans (conjOrb_eq_of_mem hvD).subset
    have hBO : Disjoint O B := disjoint_conjOrb_of_not_mem hvO
    set b : Fin 9 → ℕ := fun i => (B ∩ conjOrb C (β i)).ncard with hb
    have hbv : hnfValid b := valid_trace hD hKC hidx hKX v
    have hb0 : b 0 = 0 := by
      simp only [hb, hΓ0]
      have : u ∉ B := fun h => (Set.disjoint_left.1 hBO huO) h
      simp [this]
    have hb1 : 0 < b 1 := by
      simp only [hb]
      exact Set.ncard_pos (Set.toFinite _) |>.2 ⟨v, mem_conjOrb_self X v, hv1⟩
    have hle : ∀ i, (![1, 704, 0, 5775, 0, 0, 0, 0, 0] : Fin 9 → ℕ) i + b i ≤ hnfS i := by
      intro i
      have h1 : a i + b i ≤ hnfS i := by
        have hd : Disjoint (O ∩ conjOrb C (β i)) (B ∩ conjOrb C (β i)) :=
          (hBO.mono Set.inter_subset_left Set.inter_subset_left)
        have hu := Set.ncard_union_eq hd
        have hs : (O ∩ conjOrb C (β i)) ∪ (B ∩ conjOrb C (β i)) ⊆ conjOrb C (β i) :=
          Set.union_subset Set.inter_subset_right Set.inter_subset_right
        have := Set.ncard_le_ncard hs
        rw [hu, hD.card_orbit i] at this
        exact this
      have h2 : a i = (![1, 704, 0, 5775, 0, 0, 0, 0, 0] : Fin 9 → ℕ) i := by rw [hbad]
      rw [← h2]
      exact h1
    have hsumB : ∑ i, b i = B.ncard := (hD.ncard_eq_sum hBsub).symm
    have hBcard : B.ncard * Nat.card ↥(X ⊓ centralizer ({v} : Set G)) = Nat.card X :=
      ncard_conjOrb_mul X v
    have hCv : Nat.card ↥(X ⊓ centralizer ({v} : Set G)) ∣ 177408000 := by
      rw [← card_centralizer_of_mem hD hvD]
      exact Subgroup.card_dvd_of_le inf_le_right
    refine hnf_arith_bad b hbv hb0 hb1 hle ⟨?_, ?_⟩
    · rw [hsumB, ← hXc, ← hBcard]
      exact Dvd.intro _ rfl
    · rw [hsumB, ← hXc, ← hBcard]
      have : B.ncard * Nat.card ↥(X ⊓ centralizer ({v} : Set G)) / B.ncard =
          Nat.card ↥(X ⊓ centralizer ({v} : Set G)) := by
        have hpos : 0 < B.ncard := by
          have : B.ncard ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hBcard
            have := (Nat.card_pos (α := X))
            omega
          omega
        exact Nat.mul_div_cancel_left _ hpos
      rw [this]
      exact hCv

end Main

end CFSG.EvenSporadicStandard.Solomon78
