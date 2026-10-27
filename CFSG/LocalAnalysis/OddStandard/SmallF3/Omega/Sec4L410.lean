module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Gl7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L410Param

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec4L410_relIndex_ne_zero_of_finite {G : Type} [Group G] [Finite G]
    (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

private theorem sec4L410_zpowers_eq_one_or_of_orderOf_two {H : Type} [Group H] {t : H}
    (ht : orderOf t = 2) {p : H} (hp : p ∈ Subgroup.zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem sec4L410_mem_sup_zpowers_cases {G : Type} [Group G] {t u x : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (hut : u * t = t * u)
    (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers t) :
    x = 1 ∨ x = u ∨ x = t ∨ x = t * u := by
  have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_left (show Commute u t from hut) i).zpow_right j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp hx
  rcases sec4L410_zpowers_eq_one_or_of_orderOf_two hu ha with rfl | rfl <;>
    rcases sec4L410_zpowers_eq_one_or_of_orderOf_two ht hb with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inr hut))

theorem sec4_relIndex_le_two [Finite G] {A : Subgroup G} {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : t ≠ u) (htA : t ∈ A) (huA : u ∈ A)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (h49 : (∀ m ∈ normalizer (A : Set G), m * u = u * m → m * t = t * m) ∨
      ((∃ h : G, h⁻¹ * t * h = t * u) ∧ ∀ m ∈ normalizer (A : Set G), m * u = u * m →
        m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G))) :
    ((normalizer (A : Set G) ⊓ centralizer ({u} : Set G)) ⊓ centralizer ({t} : Set G)).relIndex
      (normalizer (A : Set G) ⊓ centralizer ({u} : Set G)) ≤ 2 := by
  let H : Subgroup G := normalizer (A : Set G) ⊓ centralizer ({u} : Set G)
  haveI : IsMulCommutative ↥A := hA.1
  have hut : u * t = t * u :=
    congrArg Subtype.val (mul_comm' (⟨u, huA⟩ : A) ⟨t, htA⟩)
  change (H ⊓ centralizer ({t} : Set G)).relIndex H ≤ 2
  rw [sec4_relIndex_centralizer_eq_card H t]
  rcases h49 with hcomm | ⟨_hex, hnorm⟩
  · have hset : conjClassIn H t = ({t} : Set G) := by
      ext y
      constructor
      · rintro ⟨m, hm, rfl⟩
        refine Set.mem_singleton_iff.mpr ?_
        rw [hcomm m hm.1
          (Subgroup.mem_centralizer_iff.mp hm.2 u (Set.mem_singleton u)).symm]
        group
      · intro hy
        refine ⟨1, H.one_mem, ?_⟩
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        simp
    rw [hset, Nat.card_coe_set_eq, Set.ncard_singleton]
    norm_num
  · have hsub : conjClassIn H t ⊆ ({t, t * u} : Set G) := by
      rintro y ⟨m, hm, rfl⟩
      have hmc : m * u = u * m :=
        (Subgroup.mem_centralizer_iff.mp hm.2 u (Set.mem_singleton u)).symm
      have hmD : m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G) :=
        hnorm m hm.1 hmc
      have hsD : m * t * m⁻¹ ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers t : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hmD t).mp
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      have ht1 : t ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at ht
        exact absurd ht (by decide)
      have hs1 : m * t * m⁻¹ ≠ 1 := by
        intro h1
        apply ht1
        calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
          _ = m⁻¹ * 1 * m := by rw [h1]
          _ = 1 := by group
      have hsu : m * t * m⁻¹ ≠ u := by
        intro h1
        apply htu
        calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
          _ = m⁻¹ * u * m := by rw [h1]
          _ = u := by rw [mul_assoc, ← hmc, inv_mul_cancel_left]
      rcases sec4L410_mem_sup_zpowers_cases ht hu hut hsD with h1 | h2 | h3 | h4
      · exact absurd h1 hs1
      · exact absurd h2 hsu
      · rw [h3]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · rw [h4]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
    have htu' : t ≠ t * u := by
      intro h1
      have hu1 : u = 1 :=
        mul_left_cancel (show t * u = t * 1 by rw [mul_one]; exact h1.symm)
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by decide)
    have hbound : (conjClassIn H t).ncard ≤ 2 := by
      calc (conjClassIn H t).ncard ≤ ({t, t * u} : Set G).ncard := Set.ncard_le_ncard hsub
        _ = 2 := Set.ncard_pair htu'
    simpa only [Nat.card_coe_set_eq] using hbound

theorem sec4_counting_contradiction [Finite G] {M X Y U : Subgroup G} (hUX : U ≤ X)
    (hXM : X ≤ M) (hUY : U ≤ Y) (hYM : Y ≤ M)
    (hX : X.relIndex M = 36 ∨ X.relIndex M = 64) (hY : Y.relIndex M = 7 ∨ Y.relIndex M = 28)
    (hU : U.relIndex Y ≤ 2) : False := by
  have h1 : U.relIndex X * X.relIndex M = U.relIndex M :=
    Subgroup.relIndex_mul_relIndex (H := U) (K := X) (L := M) hUX hXM
  have h2 : U.relIndex Y * Y.relIndex M = U.relIndex M :=
    Subgroup.relIndex_mul_relIndex (H := U) (K := Y) (L := M) hUY hYM
  have hk : 0 < U.relIndex X :=
    Nat.pos_of_ne_zero (sec4L410_relIndex_ne_zero_of_finite U X)
  have hj : 0 < U.relIndex Y :=
    Nat.pos_of_ne_zero (sec4L410_relIndex_ne_zero_of_finite U Y)
  rcases hX with hX | hX <;> rcases hY with hY | hY <;>
    · rw [hX] at h1
      rw [hY] at h2
      rw [mul_comm] at h1 h2
      omega

theorem asc82Lemma410Ctx_of (h46b : Asc82Lemma46b) (h47 : Asc82Lemma47) (h48a : Asc82Lemma48a)
    (h48b : Asc82Lemma48b) (h49 : Asc82Lemma49) (hAD : Asc82ADataExists) :
    Asc82Lemma410Ctx := by
  intro G _ _ t L S z hctx
  obtain ⟨A, B, φ, hD⟩ := hAD G t L S z hctx
  let M : Subgroup G := normalizer (A : Set G)
  have hAmax : IsMaxElemAbelianIn (SLC S L) A := hD.isMax
  have hAel : CFSG.Open.IsElemAbelian 2 A := hAmax.2.1
  have hcardA : Nat.card A = 2 ^ 7 := Sec4AData.card_A hctx hD
  have htA : t ∈ A := by
    rw [hD.A_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have h47' : ∃ h : G, h⁻¹ * t * h = t * z := h47 G t L S z hctx
  have h46 : conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn M t :=
    (h46b G t L S z hctx A hAmax).2
  have h48 : conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z :=
    h48a G t L S z hctx
  have hbn : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
    intro m hm b hb
    have h := (h48b G t L S z hctx A hAmax).2 m hm b (by rw [hD.B_eq]; exact hb)
    rwa [hD.B_eq] at h
  have hdvd : Nat.card (conjClassIn M t) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) :=
    sec4_orbit_card_dvd_gl7 hAel hcardA htA
  have hDelta : Nat.card (conjClassIn M t) = 36 ∨ Nat.card (conjClassIn M t) = 43 ∨
      Nat.card (conjClassIn M t) = 57 ∨ Nat.card (conjClassIn M t) = 64 :=
    sec4_Delta_card hctx hD h47' h46 hbn
  have hndvd := sec4_not_dvd_gl7
  have hDelta' : Nat.card (conjClassIn M t) = 36 ∨ Nat.card (conjClassIn M t) = 64 := by
    rcases hDelta with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hdvd) hndvd.1
    · exact absurd (h ▸ hdvd) hndvd.2
    · exact Or.inr h
  have hex : Nonempty {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ vecWeight v = 6} := by
    refine (Nat.card_pos_iff.mp ?_).1
    rw [card_evenVec_weight_six]
    norm_num
  obtain ⟨v6, hv6even, hv6wt⟩ := Classical.choice hex
  have hv60 : v6 ≠ 0 := by
    intro h0
    have hw0 : vecWeight v6 = 0 := by rw [h0]; simp [vecWeight]
    omega
  set u : G := φ v6 with hu_def
  have hu2 : orderOf u = 2 := by
    rw [hu_def]
    exact IsPermModuleVia.orderOf_eq_two hD.bdata.perm hv6even hv60
  have hu6 : InducesTypeSome L u 7 1 6 (-1) := by
    rw [hu_def]
    exact (hD.bdata.type6 v6 hv6even hv60).mp hv6wt
  have uB : u ∈ B := by
    rw [hu_def]
    exact IsPermModuleVia.mem hD.bdata.perm hv6even
  have uAL : u ∈ A ⊓ L := by
    rw [hD.B_eq]
    exact uB
  have uA : u ∈ A := (Subgroup.mem_inf.mp uAL).1
  have htL : t ∉ L := sec4_t_not_mem hctx.toSec4Setting
  have htu : t ≠ u := by
    intro h
    apply htL
    rw [h]
    exact uAL.2
  have hGamma : Nat.card (conjClassIn M (φ v6)) = 7 ∨ Nat.card (conjClassIn M (φ v6)) = 28 :=
    sec4_Gamma_card hctx hD h48 hbn hv6even hv6wt
  have hGamma' : Nat.card (conjClassIn M u) = 7 ∨ Nat.card (conjClassIn M u) = 28 := by
    rwa [hu_def]
  have h49' := h49 G t L S z hctx A hAmax u uAL hu2 hu6
  have hle2 := sec4_relIndex_le_two hctx.involution hu2 htu htA uA hAel h49'
  let X : Subgroup G := M ⊓ centralizer ({t} : Set G)
  let Y : Subgroup G := M ⊓ centralizer ({u} : Set G)
  let U : Subgroup G := Y ⊓ centralizer ({t} : Set G)
  have hUX : U ≤ X := le_inf (le_trans inf_le_left inf_le_left) inf_le_right
  have hXM : X ≤ M := inf_le_left
  have hUY : U ≤ Y := inf_le_left
  have hYM : Y ≤ M := inf_le_left
  have hX : X.relIndex M = 36 ∨ X.relIndex M = 64 := by
    change (M ⊓ centralizer ({t} : Set G)).relIndex M = 36 ∨
      (M ⊓ centralizer ({t} : Set G)).relIndex M = 64
    rw [sec4_relIndex_centralizer_eq_card M t]
    exact hDelta'
  have hY : Y.relIndex M = 7 ∨ Y.relIndex M = 28 := by
    change (M ⊓ centralizer ({u} : Set G)).relIndex M = 7 ∨
      (M ⊓ centralizer ({u} : Set G)).relIndex M = 28
    rw [sec4_relIndex_centralizer_eq_card M u]
    exact hGamma'
  have hU : U.relIndex Y ≤ 2 := hle2
  exact sec4_counting_contradiction hUX hXM hUY hYM hX hY hU

end CFSG.OddStandard.SmallF3.Omega
