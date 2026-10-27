module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma1
public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma2
public import CFSG.LocalAnalysis.ABGTheoremB.IV2
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J W : Subgroup G}

section Components

omit [Finite G] in
theorem comp_subset (X : Subgroup G) (j : Fin 3) : comp σ X j ⊆ X := fun _ hu => hu.1

omit [Finite G] in
theorem comp_subset_Ns (X : Subgroup G) (j : Fin 3) : comp σ X j ⊆ σ.Ns j := fun _ hu =>
  Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm

omit [Finite G] in
theorem zpow_mem_comp {X : Subgroup G} {j : Fin 3} {u : G} (hu : u ∈ comp σ X j) (k : ℤ) :
    u ^ k ∈ comp σ X j := by
  obtain ⟨huX, h1, h2⟩ := hu
  refine ⟨X.zpow_mem huX k, (Commute.zpow_right h1 k), ?_⟩
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h2, inv_zpow]

theorem conj_mem_comp (hσ : σ.IsValid) {X : Subgroup G}
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) {j : Fin 3} {t u : G} (ht : t ∈ σ.T)
    (hu : u ∈ comp σ X j) : t * u * t⁻¹ ∈ comp σ X j := by
  have := Conjugacy.isKleinFour_T hσ
  obtain ⟨huX, h1, h2⟩ := hu
  have hj := Conjugacy.xs_mem_T (σ := σ) j
  have hj1 := Conjugacy.xs_mem_T (σ := σ) (j + 1)
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hTX ht) u).mp huX, ?_, ?_⟩
  · have hat : Commute (σ.xs j) t := kleinFour_comm hj ht
    exact (hat.mul_right h1).mul_right hat.inv_right
  · have hbt : σ.xs (j + 1) * t = t * σ.xs (j + 1) := kleinFour_comm hj1 ht
    calc σ.xs (j + 1) * (t * u * t⁻¹) * (σ.xs (j + 1))⁻¹ =
          (σ.xs (j + 1) * t) * u * (σ.xs (j + 1) * t)⁻¹ := by group
      _ = (t * σ.xs (j + 1)) * u * (t * σ.xs (j + 1))⁻¹ := by rw [hbt]
      _ = t * (σ.xs (j + 1) * u * (σ.xs (j + 1))⁻¹) * t⁻¹ := by group
      _ = t * u⁻¹ * t⁻¹ := by rw [h2]
      _ = (t * u * t⁻¹)⁻¹ := by group

theorem T_le_normalizer_closure_comp (hσ : σ.IsValid) {X : Subgroup G}
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) (j : Fin 3) :
    σ.T ≤ Subgroup.normalizer (Subgroup.closure (comp σ X j) : Set G) := by
  intro t ht
  apply DataConstruction.mem_normalizer_of_conjSub_le
  rw [TotallyInverted.conjSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨u, hu, rfl⟩
  exact Subgroup.subset_closure (conj_mem_comp hσ hTX ht hu)

theorem commutator_closure_comp_eq (hσ : σ.IsValid) {X : Subgroup G} (hX : Odd (Nat.card X))
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) (j : Fin 3) :
    ⁅Subgroup.closure (comp σ X j), σ.T⁆ = Subgroup.closure (comp σ X j) := by
  set Y := Subgroup.closure (comp σ X j)
  have hTY := T_le_normalizer_closure_comp hσ hTX j
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro y hy t ht
    rw [commutatorElement_def, show y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) by group]
    exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hTY ht) y⁻¹).mp (Y.inv_mem hy))
  · rw [Subgroup.closure_le]
    intro u hu
    obtain ⟨m, hm⟩ : Odd (orderOf u) := hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hu.1)
    set v := u ^ (m + 1) with hv
    have hvc : v ∈ comp σ X j := by
      have := zpow_mem_comp hu ((m + 1 : ℕ) : ℤ)
      rwa [zpow_natCast] at this
    have hv2 : v * v = u := by
      rw [hv, ← pow_add, show m + 1 + (m + 1) = orderOf u + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hcomm : ⁅v, σ.xs (j + 1)⁆ = u := by
      rw [commutatorElement_def]
      have h2 := hvc.2.2
      have e : σ.xs (j + 1) * v⁻¹ * (σ.xs (j + 1))⁻¹ = v := by
        rw [show σ.xs (j + 1) * v⁻¹ * (σ.xs (j + 1))⁻¹ =
          (σ.xs (j + 1) * v * (σ.xs (j + 1))⁻¹)⁻¹ by group, h2, inv_inv]
      rw [show v * σ.xs (j + 1) * v⁻¹ * (σ.xs (j + 1))⁻¹ =
        v * (σ.xs (j + 1) * v⁻¹ * (σ.xs (j + 1))⁻¹) by group, e, hv2]
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure hvc)
      (Conjugacy.xs_mem_T (j + 1))

theorem le_Ns_of_comp_eq_one (hσ : σ.IsValid) {X : Subgroup G} (hX : Odd (Nat.card X))
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) {c : Fin 3}
    (htriv : ∀ k : Fin 3, k ≠ c → ∀ u ∈ comp σ X k, u = 1) : X ≤ σ.Ns c := by
  intro x hx
  have hx' : x ∈ (X : Set G) := hx
  rw [Conjugacy.coe_eq_mul_comp hσ hX hTX] at hx'
  obtain ⟨_, ⟨_, ⟨a, ha, u0, hu0, rfl⟩, u1, hu1, rfl⟩, u2, hu2, rfl⟩ := hx'
  have haN : a ∈ σ.Ns c := Conjugacy.C_le_Ns c ha.2
  have hmem : ∀ k : Fin 3, ∀ u ∈ comp σ X k, u ∈ σ.Ns c := by
    intro k u hu
    by_cases hk : k = c
    · subst hk
      exact comp_subset_Ns X k hu
    · rw [htriv k hk u hu]
      exact Subgroup.one_mem _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haN (hmem 0 u0 hu0))
    (hmem 1 u1 hu1)) (hmem 2 u2 hu2)

end Components

theorem orderOf_xs (hσ : σ.IsValid) (j : Fin 3) : orderOf (σ.xs j) = 2 := by
  have := Conjugacy.isKleinFour_T hσ
  exact kleinFour_orderOf (Conjugacy.xs_mem_T j) (Conjugacy.xs_ne_one hσ j)

theorem lemmaV43_i (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (h46 : LemmaII46Input σ J) (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (hW : W ∈ σ.familyW J) {r : ℕ} (hr : r.Prime) (hrW : r ∣ Nat.card W) {X : Subgroup G}
    (hXr : IsPGroup r X) (hTX : σ.T ≤ Subgroup.normalizer (X : Set G))
    (hXW : Odd (Nat.card (X ⊔ W : Subgroup G))) {j : Fin 3} (hj : ∃ u ∈ comp σ X j, u ≠ 1)
    (hWj : ¬ W ≤ oddCoreIn (σ.Ns j)) :
    comp σ X j ⊆ oddCoreIn (σ.Ns j) ∧ σ.Ordinary r ∧ σ.Inverted r := by
  have : Fact r.Prime := ⟨hr⟩
  have hXodd : Odd (Nat.card X) := odd_card_of_le le_sup_left hXW
  set Y := Subgroup.closure (comp σ X j) with hYdef
  have hYX : Y ≤ X := (Subgroup.closure_le X).mpr (comp_subset X j)
  have hYr : IsPGroup r Y := hXr.to_le hYX
  have hTY := T_le_normalizer_closure_comp hσ hTX j
  have hYcomm := commutator_closure_comp_eq hσ hXodd hTX j
  have hYNj : Y ≤ σ.Ns j := (Subgroup.closure_le _).mpr (comp_subset_Ns X j)
  obtain ⟨g, hgT, hgj, hWL⟩ := lemmaV42 hσ hII hJ h31 hN' h42 hW j
  have hgT' : g⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hgT
  have hNj : σ.Ns j = conjSub g σ.N := (conjSub_N hgj).symm
  have hONj : oddCoreIn (σ.Ns j) = conjSub g σ.ON := (conjSub_ON hgj).symm
  have hYO : Y ≤ oddCoreIn (σ.Ns j) := by
    by_contra hYO
    set W' := conjSub g⁻¹ W
    set Y' := conjSub g⁻¹ Y
    have hW'C : W' ≤ oddCoreIn σ.C ⊓ σ.L := by
      refine le_inf ?_ ?_
      · rw [← conjSub_oddCoreIn_C hgT']
        exact DataConstruction.conjSub_mono (W_le_oddCoreIn_C hσ hJ hW)
      · rw [← DataConstruction.conjSub_inv_conjSub g σ.L]
        exact DataConstruction.conjSub_mono hWL
    have hW'O : ¬ W' ≤ σ.ON := by
      intro h
      apply hWj
      rw [hONj, ← DataConstruction.conjSub_conjSub_inv g W]
      exact DataConstruction.conjSub_mono h
    have hY'N : Y' ≤ σ.N := by
      rw [← DataConstruction.conjSub_inv_conjSub g σ.N, ← hNj]
      exact DataConstruction.conjSub_mono hYNj
    have hY'r : IsPGroup r Y' := DataConstruction.isPGroup_conjSub hYr g⁻¹
    have hY'comm : ⁅Y', σ.T⁆ = Y' := by
      have e : ⁅conjSub g⁻¹ Y, conjSub g⁻¹ σ.T⁆ = conjSub g⁻¹ ⁅Y, σ.T⁆ :=
        (Subgroup.map_commutator Y σ.T _).symm
      rw [DataConstruction.conjSub_eq_self_of_mem hgT', hYcomm] at e
      exact e
    have hY'O : ¬ Y' ≤ σ.ON := by
      intro h
      apply hYO
      rw [hONj, ← DataConstruction.conjSub_conjSub_inv g Y]
      exact DataConstruction.conjSub_mono h
    have heven := h46 W hW r hr hrW W' hW'C hW'O Y' hY'N hY'r hY'comm hY'O
    have hconj : W' ⊔ Y' ⊔ σ.ON = conjSub g⁻¹ (W ⊔ Y ⊔ oddCoreIn (σ.Ns j)) := by
      rw [DataConstruction.conjSub_sup, DataConstruction.conjSub_sup, hONj,
        DataConstruction.conjSub_inv_conjSub]
    rw [hconj, DataConstruction.card_conjSub] at heven
    have hWYodd : Odd (Nat.card (W ⊔ Y : Subgroup G)) :=
      odd_card_of_le (sup_le le_sup_right (hYX.trans le_sup_left)) hXW
    have hWYN : W ⊔ Y ≤ Subgroup.normalizer (oddCoreIn (σ.Ns j) : Set G) :=
      (sup_le ((W_le_C hσ hJ hW).trans (Conjugacy.C_le_Ns j)) hYNj).trans
        (le_normalizer_oddCoreIn _)
    have hodd := odd_card_sup_of_le_normalizer_of_odd hWYN (odd_card_oddCoreIn (σ.Ns j)) hWYodd
    rw [sup_comm] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨u, hu, hu1⟩ := hj
  have huY : u ∈ Y := Subgroup.subset_closure hu
  have hYbot : Y ≠ ⊥ := fun h => hu1 (by rw [h] at huY; exact Subgroup.mem_bot.mp huY)
  have hrON : r ∣ Nat.card σ.ON := by
    have h1 : r ∣ Nat.card Y := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYr
      rw [hk]
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact absurd (Subgroup.card_eq_one.mp hk) hYbot
      · exact dvd_pow_self r (Nat.succ_ne_zero k)
    have h2 : Nat.card σ.ON = Nat.card (oddCoreIn (σ.Ns j)) := by
      rw [hONj, DataConstruction.card_conjSub]
    rw [h2]
    exact h1.trans (Subgroup.card_dvd_of_le hYO)
  have hrCL : r ∣ Nat.card (σ.C ⊓ σ.L : Subgroup G) :=
    hrW.trans (Subgroup.card_dvd_of_le (le_inf (W_le_C hσ hJ hW) (W_le_L hJ hW)))
  have hrp : r ≠ σ.p := fun h => h31.coprime W hW (h ▸ hrW)
  have hord : σ.Ordinary r := by
    by_contra hexc
    exact hrp (h21 r ⟨hr, hrON, hrCL, hexc⟩)
  refine ⟨fun v hv => hYO (Subgroup.subset_closure hv), hord, ?_⟩
  set Y'' := conjSub g⁻¹ Y
  have hY''O : Y'' ≤ σ.ON := by
    rw [← DataConstruction.conjSub_inv_conjSub g σ.ON, ← hONj]
    exact DataConstruction.conjSub_mono hYO
  have hTY'' : σ.T ≤ Subgroup.normalizer (Y'' : Set G) := by
    rw [← DataConstruction.conjSub_eq_self_of_mem hgT']
    exact DataConstruction.le_normalizer_conjSub hTY
  obtain ⟨R, hR, hY''R, hTR⟩ := exists_isSylowOf_normalized_ge_of_odd hr (isPGroup_T hσ)
    ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON hY''O
    (DataConstruction.isPGroup_conjSub hYr g⁻¹)
    hTY''
  rcases hord.2 with hcen | hinv
  · exfalso
    have hc := (σ.centralized_or_inverted_of_T_invariant hσ hr hR hTR).1 hcen
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ R := hY''R (DataConstruction.conj_mem_conjSub huY)
    have ht : g⁻¹ * σ.xs (j + 1) * g⁻¹⁻¹ ∈ σ.T :=
      (Subgroup.mem_normalizer_iff.mp hgT' _).mp (Conjugacy.xs_mem_T (j + 1))
    have hxu := Subgroup.mem_centralizer_iff.mp (hc ht) _ hu'
    have h2 := hu.2.2
    have hcomm : σ.xs (j + 1) * u = u * σ.xs (j + 1) := by
      calc σ.xs (j + 1) * u = g * ((g⁻¹ * σ.xs (j + 1) * g⁻¹⁻¹) * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by
            group
        _ = g * ((g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * σ.xs (j + 1) * g⁻¹⁻¹)) * g⁻¹ := by rw [← hxu]
        _ = u * σ.xs (j + 1) := by group
    have hu2 : u * u = 1 := by
      have e : σ.xs (j + 1) * u * (σ.xs (j + 1))⁻¹ = u := by rw [hcomm]; group
      rw [e] at h2
      rw [show u * u = u * u⁻¹ from congrArg (u * ·) h2, mul_inv_cancel]
    have hodd : Odd (orderOf u) := hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hu.1)
    exact hu1 (Omnibus.eq_one_of_sq_eq_one hodd (by rw [sq]; exact hu2))
  · exact hinv

theorem lemmaV43_ii (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (h46 : LemmaII46Input σ J) (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (hQF : Sec10.QGroupFourFusion G) (hW : W ∈ σ.familyW J) {r : ℕ} (hr : r.Prime)
    (hrW : r ∣ Nat.card W) {X : Subgroup G} (hXr : IsPGroup r X)
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) (hXW : Odd (Nat.card (X ⊔ W : Subgroup G))) :
    ∃ i : Fin 3, X ≤ σ.Ns i := by
  have : Fact r.Prime := ⟨hr⟩
  have hXodd : Odd (Nat.card X) := odd_card_of_le le_sup_left hXW
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hrW
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one hrW)
  by_cases hmain : ∃ j : Fin 3, (∃ u ∈ comp σ X j, u ≠ 1) ∧ ¬ W ≤ oddCoreIn (σ.Ns j)
  · obtain ⟨j, ⟨u, hu, hu1⟩, hWj⟩ := hmain
    obtain ⟨hcompO, hord, -⟩ :=
      lemmaV43_i hσ hII hJ h31 hN' h42 h46 h21 hW hr hrW hXr hTX hXW ⟨u, hu, hu1⟩ hWj
    refine ⟨j, ?_⟩
    by_contra hXj
    obtain ⟨g, hgT, hgj⟩ := exists_conj_x_eq_xs hσ hII j
    have hgT' : g⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hgT
    have hONj : oddCoreIn (σ.Ns j) = conjSub g σ.ON := (conjSub_ON hgj).symm
    have hNj : σ.Ns j = conjSub g σ.N := (conjSub_N hgj).symm
    set Y := Subgroup.closure (comp σ X j)
    have hYO : Y ≤ oddCoreIn (σ.Ns j) := (Subgroup.closure_le _).mpr hcompO
    have hYr : IsPGroup r Y := hXr.to_le ((Subgroup.closure_le X).mpr (comp_subset X j))
    set Y'' := conjSub g⁻¹ Y
    have hY''O : Y'' ≤ σ.ON := by
      rw [← DataConstruction.conjSub_inv_conjSub g σ.ON, ← hONj]
      exact DataConstruction.conjSub_mono hYO
    have hTY'' : σ.T ≤ Subgroup.normalizer (Y'' : Set G) := by
      rw [← DataConstruction.conjSub_eq_self_of_mem hgT']
      exact DataConstruction.le_normalizer_conjSub (T_le_normalizer_closure_comp hσ hTX j)
    obtain ⟨R, hR, hY''R, hTR⟩ := exists_isSylowOf_normalized_ge_of_odd hr (isPGroup_T hσ)
      ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON hY''O
      (DataConstruction.isPGroup_conjSub hYr g⁻¹) hTY''
    have hrON : r ∣ Nat.card σ.ON := by
      have hR1 : R ≠ ⊥ := by
        intro h
        have : g⁻¹ * u * g⁻¹⁻¹ ∈ R :=
          hY''R (DataConstruction.conj_mem_conjSub (Subgroup.subset_closure hu))
        rw [h, Subgroup.mem_bot] at this
        apply hu1
        calc u = g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ := by group
          _ = 1 := by rw [this]; group
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR.isPGroup
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hR.le)
      rw [hk]
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact absurd (Subgroup.card_eq_one.mp hk) hR1
      · exact dvd_pow_self r (Nat.succ_ne_zero k)
    have hu'R : g⁻¹ * u * g⁻¹⁻¹ ∈ R :=
      hY''R (DataConstruction.conj_mem_conjSub (Subgroup.subset_closure hu))
    have hu'1 : g⁻¹ * u * g⁻¹⁻¹ ≠ 1 := by
      intro h
      apply hu1
      calc u = g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h23 := (σ.ordinary_element_centralizer hσ hII hr hrON hord hR hTR hu'R hu'1).2
    have hxj := orderOf_xs hσ j
    have hxjX : σ.xs j ∈ Subgroup.normalizer (X : Set G) := hTX (Conjugacy.xs_mem_T j)
    have hlt : X ⊓ Subgroup.centralizer {σ.xs j} < X := by
      refine lt_of_le_of_ne inf_le_left (fun h => hXj ?_)
      rw [← h]
      exact inf_le_right
    obtain ⟨y, hy, hy1, hyc⟩ := exists_inverted_centralizing_fixed hXr hXodd hxj hxjX hlt
    set Xj : Subgroup G := X ⊓ Subgroup.centralizer {σ.xs j}
    set Z : Subgroup G := X ⊓ Subgroup.centralizer (Xj : Set G)
    have huXj : u ∈ Xj := ⟨hu.1, comp_subset_Ns X j hu⟩
    have hZu : Z ≤ Subgroup.centralizer ({u} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hz.2) u huXj).symm
    have hTXj : σ.T ≤ Subgroup.normalizer (Xj : Set G) := by
      have := Conjugacy.isKleinFour_T hσ
      refine (le_inf hTX fun t ht => ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      apply Subgroup.le_normalizer
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact kleinFour_comm ht (Conjugacy.xs_mem_T j)
    have hTZ : σ.T ≤ Subgroup.normalizer (Z : Set G) :=
      (le_inf hTX (le_normalizer_centralizer hTXj)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hZr : IsPGroup r Z := hXr.to_le inf_le_left
    have hZ'u : conjSub g⁻¹ Z ≤ Subgroup.centralizer ({g⁻¹ * u * g⁻¹⁻¹} : Set G) := by
      rw [← DataConstruction.conjSub_centralizer_singleton]
      exact DataConstruction.conjSub_mono hZu
    have hTZ' : σ.T ≤ Subgroup.normalizer (conjSub g⁻¹ Z : Set G) := by
      rw [← DataConstruction.conjSub_eq_self_of_mem hgT']
      exact DataConstruction.le_normalizer_conjSub hTZ
    have hZ'N := h23 _ hZ'u (DataConstruction.isPGroup_conjSub hZr g⁻¹) hTZ'
    have hZNj : Z ≤ σ.Ns j := by
      rw [hNj, ← DataConstruction.conjSub_conjSub_inv g Z]
      exact DataConstruction.conjSub_mono hZ'N
    have hyZ : y ∈ Z := ⟨hy.1, hyc⟩
    have hyc' : σ.xs j * y = y * σ.xs j :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hZNj hyZ)).symm
    have hyinv := hy.2
    have hy2 : y * y = 1 := by
      have e : σ.xs j * y * (σ.xs j)⁻¹ = y := by rw [hyc']; group
      rw [e] at hyinv
      rw [show y * y = y * y⁻¹ from congrArg (y * ·) hyinv, mul_inv_cancel]
    have hodd : Odd (orderOf y) := hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hy.1)
    exact hy1 (Omnibus.eq_one_of_sq_eq_one hodd (by rw [sq]; exact hy2))
  ·
    push Not at hmain
    have hatmost : ∀ a b : Fin 3, (∃ u ∈ comp σ X a, u ≠ 1) → (∃ u ∈ comp σ X b, u ≠ 1) →
        a = b := fun a b ha hb =>
      lemmaV41 hσ hII hJ h31 hQF hW hW1 (hmain a ha) (hmain b hb)
    by_cases h0 : ∃ u ∈ comp σ X 0, u ≠ 1
    · refine ⟨0, le_Ns_of_comp_eq_one hσ hXodd hTX fun k hk u hu => ?_⟩
      by_contra hu1
      exact hk (hatmost k 0 ⟨u, hu, hu1⟩ h0)
    by_cases h1 : ∃ u ∈ comp σ X 1, u ≠ 1
    · refine ⟨1, le_Ns_of_comp_eq_one hσ hXodd hTX fun k hk u hu => ?_⟩
      by_contra hu1
      exact hk (hatmost k 1 ⟨u, hu, hu1⟩ h1)
    refine ⟨2, le_Ns_of_comp_eq_one hσ hXodd hTX fun k hk u hu => ?_⟩
    by_contra hu1
    fin_cases k
    · exact h0 ⟨u, hu, hu1⟩
    · exact h1 ⟨u, hu, hu1⟩
    · exact hk rfl

end CFSG.ABGTheoremB.V4
