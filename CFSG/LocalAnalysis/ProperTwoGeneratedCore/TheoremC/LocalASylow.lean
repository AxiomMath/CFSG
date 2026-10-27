module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalAQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X}

section Quasi

variable {a : X ⧸ CFSG.Open.pCore 2 X}

omit [Finite X] in
theorem quasiPreimage_isPGroup (ha : orderOf a = 2) : IsPGroup 2 (quasiPreimage a) :=
  (isPGroup_zpowers_of_orderOf_eq_two ha).comap_of_ker_isPGroup _
    (by rw [QuotientGroup.ker_mk']; exact twoCore_isPGroup X)

omit [Finite X] in
theorem twoCore_le_quasiPreimage (a : X ⧸ CFSG.Open.pCore 2 X) :
    CFSG.Open.pCore 2 X ≤ quasiPreimage a := fun x hx => by
  rw [Subgroup.mem_comap, (mk_twoCore_eq_one_iff x).mpr hx]
  exact Subgroup.one_mem _

omit [Finite X] in
theorem quasiPreimage_not_le (ha : orderOf a = 2) :
    ¬ quasiPreimage a ≤ CFSG.Open.pCore 2 X := by
  intro h
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X) a
  have hv : v ∈ quasiPreimage (QuotientGroup.mk' (CFSG.Open.pCore 2 X) v) :=
    Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  rw [(mk_twoCore_eq_one_iff v).mpr (h hv), orderOf_one] at ha
  exact absurd ha (by decide)

omit [Finite X] in
theorem mul_self_mem_of_mem_quasiPreimage (ha : orderOf a = 2) :
    ∀ y ∈ quasiPreimage a, y * y ∈ CFSG.Open.pCore 2 X := by
  intro y hy
  rw [← mk_twoCore_eq_one_iff, map_mul]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hy)
  have haa : a ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two]
    simpa only [ha] using pow_orderOf_eq_one a
  rw [← hk, ← zpow_add, ← two_mul, zpow_mul, haa, one_zpow]

omit [Finite X] in
theorem lever_mem_normalizer (ha : orderOf a = 2)
    (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z)) :
    z ∈ Subgroup.normalizer (quasiPreimage a : Set X) :=
  (mem_normalizer_quasiPreimage_iff ha z).mpr haz.symm

theorem quasiPreimage_le (hc : CoreConfig Y u z)
    (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z)) : quasiPreimage a ≤ Y := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X) a
  set D := quasiPreimage (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z)
  have hzD : z ∈ D := Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  have huD : u ∈ D := twoCore_le_quasiPreimage _ hc.mem_twoCore
  have hDY : D ≤ Y := fun d hd => (hc.mk_mem_map_iff d).mp
    (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hc.lever_mem) (Subgroup.mem_comap.mp hd))
  have hrank : 2 ≤ CFSG.Open.pRank 2 D :=
    two_le_pRank_of_commuting_involutions hzD huD hc.lever_order hc.order hc.lever_ne
      (hc.commute_center z)
  have hvY : v ∈ Y := hc.normalizer_le D hDY hrank
    ((mem_normalizer_quasiPreimage_iff hc.orderOf_mk_lever v).mpr haz)
  intro y hy
  rw [← hc.mk_mem_map_iff]
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hvY) (Subgroup.mem_comap.mp hy)

omit [Finite X] in
theorem normalizer_quasiPreimage_not_le (ha : orderOf a = 2)
    (hesc : ¬ Subgroup.centralizer ({a} : Set (X ⧸ CFSG.Open.pCore 2 X)) ≤
      Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))) :
    ¬ Subgroup.normalizer (quasiPreimage a : Set X) ≤ Y := by
  intro hN
  apply hesc
  intro c hc'
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X) c
  have hnN := (mem_normalizer_quasiPreimage_iff ha n).mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hc')
  exact Subgroup.mem_map_of_mem _ (hN hnN)

theorem pRank_quasiPreimage (hc : CoreConfig Y u z) (ha : orderOf a = 2)
    (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z))
    (hesc : ¬ Subgroup.centralizer ({a} : Set (X ⧸ CFSG.Open.pCore 2 X)) ≤
      Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))) :
    CFSG.Open.pRank 2 (quasiPreimage a) = 1 := by
  apply le_antisymm
  · by_contra h
    exact normalizer_quasiPreimage_not_le ha hesc
      (hc.normalizer_le _ (quasiPreimage_le hc haz) (by omega))
  · refine CFSG.SectionRank.le_pRank (by decide)
      (Subgroup.zpowers_le.mpr (twoCore_le_quasiPreimage a hc.mem_twoCore))
      (involution_zpowers_elementary u hc.order) ?_
    rw [Nat.card_zpowers, hc.order, pow_one]

end Quasi

theorem exists_sylow_le (hc : CoreConfig Y u z) {a : X ⧸ CFSG.Open.pCore 2 X}
    (ha : orderOf a = 2) (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z)) :
    ∃ (R : Subgroup X) (z' : X), R ≤ Subgroup.normalizer (quasiPreimage a : Set X) ∧ R ≤ Y ∧
      IsPGroup 2 R ∧
      (∀ R' : Subgroup X, R' ≤ Subgroup.normalizer (quasiPreimage a : Set X) → IsPGroup 2 R' →
        Nat.card R' ≤ Nat.card R) ∧
      z' ∈ R ∧ (∀ r ∈ R, Commute r z') ∧ z' ∈ involutionPointClass z ∧ quasiPreimage a ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := quasiPreimage a
  set N := Subgroup.normalizer (V : Set X)
  have hzN : z ∈ N := lever_mem_normalizer ha haz
  have hzp : IsPGroup 2 (Subgroup.zpowers (⟨z, hzN⟩ : N)) :=
    isPGroup_zpowers_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk]; exact hc.lever_order)
  obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
  set R := (S : Subgroup N).map N.subtype with hR
  have hRN : R ≤ N := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := S.isPGroup'.map N.subtype
  have hRmax : ∀ R' : Subgroup X, R' ≤ N → IsPGroup 2 R' → Nat.card R' ≤ Nat.card R := by
    intro R' hR'N hR'
    rw [hR, Subgroup.card_map_of_injective N.subtype_injective]
    exact card_le_card_sylow_of_le S hR'N hR'
  have hzR : z ∈ R := Subgroup.mem_map.mpr ⟨⟨z, hzN⟩, hzS (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨P, hPY, -, -, hzc⟩ := hc.sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P hR2
  have hgY : g ∈ Y :=
    hc.mem_of_conj_mem hc.lever_mem hc.lever_order hc.lever_ne (hPY (hg z hzR))
  have hRY : R ≤ Y := by
    intro r hr
    have h := Y.mul_mem (Y.mul_mem hgY (hPY (hg r hr))) (Y.inv_mem hgY)
    convert h using 1
    group
  set z' := g * z * g⁻¹
  have hz'c : ∀ r ∈ R, Commute r z' := by
    intro r hr
    have h1 : Commute (g⁻¹ * r * g) z := hzc _ (hg r hr)
    calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1.eq]
      _ = g * z * g⁻¹ * r := by group
  have hz'cl : z' ∈ involutionPointClass z := conj_mem_involutionPointClass' g
  have hz'2 : orderOf z' = 2 := order_two_of_mem_pointClass hc.lever_order hz'cl
  have hVR : V ≤ R := by
    have hsup : IsPGroup 2 (R ⊔ V : Subgroup X) :=
      hR2.to_sup_of_normal_right' (quasiPreimage_isPGroup ha) hRN
    have heq : R = R ⊔ V :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (hRmax _ (sup_le hRN Subgroup.le_normalizer) hsup)
    rw [heq]
    exact le_sup_right
  have hz'N : z' ∈ N := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hz'c y (hVR hy)).eq
  have hz'R : z' ∈ R := by
    have hsup : IsPGroup 2 (R ⊔ Subgroup.zpowers z' : Subgroup X) :=
      hR2.to_sup_of_normal_right' (isPGroup_zpowers_of_orderOf_eq_two hz'2) fun r hr =>
        Subgroup.centralizer_le_normalizer _
          (zpowers_le_centralizer_zpowers (hz'c r hr) (Subgroup.mem_zpowers r))
    have heq : R = R ⊔ Subgroup.zpowers z' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left
        (hRmax _ (sup_le hRN (Subgroup.zpowers_le.mpr hz'N)) hsup)
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z')
  exact ⟨R, z', hRN, hRY, hR2, hRmax, hz'R, hz'c, hz'cl, hVR⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
