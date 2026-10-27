module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CriticalCenterExponentFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCExponentObstruction

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open scoped commutatorElement

namespace SteinbergBK

variable {G : Type*} [Group G]

theorem map_center_map_subtype_eq {Q : Subgroup G} (D : Subgroup Q) :
    ((center D).map D.subtype).map Q.subtype =
      (center (D.map Q.subtype)).map (D.map Q.subtype).subtype := by
  rw [CFSG.SectionRank.Ccomm.map_center_subtype, CFSG.SectionRank.Ccomm.map_center_subtype]
  ext x
  constructor
  · rintro ⟨q, ⟨hqD, hqc⟩, rfl⟩
    exact ⟨mem_map_of_mem _ hqD, (coe_mem_centralizer_map_iff (Z₀ := D) q).mpr hqc⟩
  · rintro ⟨⟨q, hqD, rfl⟩, hqc⟩
    exact ⟨q, ⟨hqD, (coe_mem_centralizer_map_iff (Z₀ := D) q).mp hqc⟩, rfl⟩

theorem conjugate_one_eq (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff_conj_mem, one_mul, inv_one, mul_one]

theorem mem_normalizer_conjugate_iff {H : Subgroup G} (g x : G) :
    x ∈ normalizer ((conjugate H g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_conjugate_eq, mem_normalizer_iff_conjugate_eq, conjugate_conjugate]
  constructor
  · intro h
    calc conjugate H (g * x * g⁻¹) = conjugate (conjugate H (g * x)) g⁻¹ := by
          rw [conjugate_conjugate]
      _ = conjugate (conjugate H g) g⁻¹ := by rw [h]
      _ = H := by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one_eq]
  · intro h
    calc conjugate H (g * x) = conjugate (conjugate H (g * x * g⁻¹)) g := by
          rw [conjugate_conjugate, inv_mul_cancel_right]
      _ = conjugate H g := by rw [h]

theorem normalizer_conjugate_eq_centralizer {Y : Subgroup G} {z : G}
    (h : normalizer (Y : Set G) = centralizer {z}) (g : G) :
    normalizer ((conjugate Y g : Subgroup G) : Set G) = centralizer {g⁻¹ * z * g} := by
  ext x
  rw [mem_normalizer_conjugate_iff, h, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [hx]
      _ = g⁻¹ * z * g * x := by group
  · intro hx
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hx]
      _ = z * (g * x * g⁻¹) := by group

theorem commutator_zpowers_eq_of_noncentral {L : Subgroup G} {z : G}
    (hLz : ⁅L, L⁆ = zpowers z) (hz : orderOf z = 2) {a : G} (haL : a ∈ L)
    (hnc : ∃ y ∈ L, a * y ≠ y * a) : ⁅zpowers a, L⁆ = zpowers z := by
  refine le_antisymm ?_ ?_
  · rw [← hLz]
    exact commutator_mono (zpowers_le.mpr haL) le_rfl
  · obtain ⟨y, hyL, hay⟩ := hnc
    have h1 : ⁅a, y⁆ ∈ ⁅zpowers a, L⁆ := commutator_mem_commutator (mem_zpowers a) hyL
    have h2 : ⁅a, y⁆ ∈ zpowers z := by
      rw [← hLz]
      exact commutator_mem_commutator haL hyL
    rcases eq_one_or_eq_of_mem_zpowers hz h2 with h3 | h3
    · exfalso
      apply hay
      rw [commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    · rw [zpowers_le, ← h3]
      exact h1

end SteinbergBK

open SteinbergBK

theorem gf2_higher_critical_center_involution_fusion_exclusion
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G}
    (hzQ : z ∈ (center Q).map Q.subtype) (hz : orderOf z = 2) {D : Subgroup Q}
    (hD : ThompsonCritical D) {Y : Subgroup G}
    (hY : Y = ((center D).map D.subtype).map Q.subtype) (hY8 : 8 ≤ Nat.card Y) :
    Set.range (fun g : G => g⁻¹ * z * g) ∩ (D.map Q.subtype : Set G) = {z} ∧
    ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      g⁻¹ * z * g ∉ D.map Q.subtype ∧ ¬ conjugate Y g ≤ M ∧ ⁅Y, conjugate Y g⁆ ≠ ⊥ ∧
        ∃ y ∈ Y, (g⁻¹ * z * g) * y * (g⁻¹ * z * g)⁻¹ ≠ y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z₁, -, -, -, -, hMNQ, -, -⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ rfl
  obtain ⟨-, hcc⟩ :=
    gf2_critical_center_and_exponent_four_reduction hchar he hM hsym hB hBM hQ hzQ hz rfl
  obtain ⟨⟨E, R, hEZ, -, -, -, -, -, -, hcases, -, -⟩, -, hcyc, -, hzY, huniqY, hcZ, hNY, hMC,
    -, -, -, -, hconj, -⟩ := hcc D hD _ rfl Y hY
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact CFSG.pCore_isPGroup.map _
  set D' := D.map Q.subtype with hD'def
  have hD'Q : D' ≤ Q := map_subtype_le D
  have hYD' : Y ≤ D' := by
    rw [hY]
    exact map_mono (map_subtype_le _)
  have hconj_ord : ∀ g : G, orderOf (g⁻¹ * z * g) = 2 := fun g => by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1]
    exact hz
  have eY : ((center D).map D.subtype) ≃* Y := by
    rw [hY]
    exact equivMapOfInjective _ Q.subtype Q.subtype_injective
  have hYcyc : IsCyclic Y := isCyclic_of_surjective eY.toMonoidHom eY.surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ2.to_le (hYD'.trans hD'Q))
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    have : Nat.card Y ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have hMND : M ≤ normalizer (D' : Set G) :=
    hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hD.1)
  have hfus : ∀ g : G, g⁻¹ * z * g ∈ D' → g⁻¹ * z * g = z := by
    intro g hgD
    by_contra hne
    obtain ⟨hsupM, -, -, hXcyc, hXcard, -⟩ := (hconj g).2.2.2.2 hgD hne
    rcases hcases with ⟨rfl, -, hDZ, -⟩ | ⟨hEx, -, hEZi, hEc⟩
    ·
      apply hne
      have h1 : g⁻¹ * z * g ∈ Y := by
        rw [hY, ← hDZ]
        exact hgD
      exact huniqY _ h1 (hconj_ord g)
    ·
      set E' := E.map Q.subtype with hE'def
      have hED : E ≤ D := le_sup_left.trans hEZ.le
      have hE'D' : E' ≤ D' := map_mono hED
      have hE'x : IsExtraspecialPGroup 2 E' :=
        isExtraspecialPGroup_congr_mulEquiv (E.equivMapOfInjective _ Q.subtype_injective) hEx
      have hDEY : D' = E' ⊔ Y := by
        rw [hD'def, hY, ← Subgroup.map_sup, hEZ]
      have hEY : E' ⊓ Y = zpowers z := by
        rw [hE'def, hY, ← map_inf_eq _ _ _ Q.subtype_injective, hEZi]
      have hZE : (center E').map E'.subtype = zpowers z := by
        rw [hE'def, ← map_center_map_subtype_eq, hEc]
      obtain ⟨T₀, hT₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) 2 (n := 2)
        (by rw [hk]; exact pow_dvd_pow 2 (by omega))
      set T := T₀.map Y.subtype with hTdef
      have hTY : T ≤ Y := map_subtype_le _
      have hT4 : Nat.card T = 4 := by
        rw [hTdef, card_map_of_injective Y.subtype_injective, hT₀]
        norm_num
      obtain ⟨-, -, hLnab, hL4, -, hLcomm, -, hLinv, -, hNL⟩ :=
        extraspecial_cyclic_product_characteristic_exponent_four_layer (D := D') (E := E')
          (Y := Y) (T := T) (hQ2.to_le hD'Q)
          (by rw [hY]; exact map_center_map_subtype_eq D) hYcyc (by omega : 2 ≤ k) hk hzY hz
          hE'D' hE'x hDEY hEY hZE hTY hT4
      set L := E' ⊔ T with hLdef
      have hLD' : L ≤ D' := sup_le hE'D' (hTY.trans hYD')
      obtain ⟨haL, hanc⟩ := hLinv _ hgD (hconj_ord g) hne
      have hnc : ∃ y ∈ L, (g⁻¹ * z * g) * y ≠ y * (g⁻¹ * z * g) := by
        by_contra hall
        push Not at hall
        apply hanc
        refine ⟨⟨_, haL⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
        exact (hall y y.2).symm
      have hLnab' : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := ⟨_, haL, hnc⟩
      have haLc := commutator_zpowers_eq_of_noncentral hLcomm hz haL hnc
      have hXM : conjugate Y g ≤ M := le_sup_right.trans hsupM
      have hXL : conjugate Y g ≤ normalizer (L : Set G) := hXM.trans (hMND.trans hNL)
      have hX1 : conjugate Y g ≠ ⊥ := by
        intro h
        rw [h, card_bot] at hXcard
        omega
      have hX2 : IsPGroup 2 (conjugate Y g) := IsPGroup.of_card (hXcard.trans hk)
      have hNX : normalizer ((conjugate Y g : Subgroup G) : Set G) =
          centralizer {g⁻¹ * z * g} :=
        normalizer_conjugate_eq_centralizer (hNY.trans hMC) g
      have hle := (cyclic_involution_normalizer_exponent_obstruction (hQ2.to_le (hLD'.trans hD'Q))
        hLnab' hLcomm hz (e := 2) (by norm_num) (fun x hx => by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hL4 x hx) hXL hX1 hX2
        (inv_mul_mul_mem_conjugate hzY) (hconj_ord g) haLc hNX).2.2.1
      rw [hXcard] at hle
      omega
  refine ⟨?_, fun g hgQ hne => ?_⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨g, rfl⟩, hx⟩
      exact hfus g hx
    · rintro rfl
      exact ⟨⟨1, by group⟩, hYD' hzY⟩
  · have hnD : g⁻¹ * z * g ∉ D' := fun h => hne (hfus g h)
    have hnM : ¬ conjugate Y g ≤ M := fun h => hnD (((hconj g).2.2.2.1 hgQ).mp h)
    refine ⟨hnD, hnM, fun h => hnM (((hconj g).2.1).mpr h), ?_⟩
    by_contra hall
    push Not at hall
    apply hnD
    have h1 : (⟨_, hgQ⟩ : Q) ∈ centralizer (((center D).map D.subtype : Subgroup Q) : Set Q) := by
      rw [← coe_mem_centralizer_map_iff, ← hY, mem_centralizer_iff]
      intro y hy
      have h2 := hall y hy
      calc y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y * (g⁻¹ * z * g)⁻¹ * (g⁻¹ * z * g) := by
            rw [h2]
        _ = (g⁻¹ * z * g) * y := by group
    rw [hcZ] at h1
    exact ⟨_, h1, rfl⟩

end CFSG.LocalAnalysis.GorensteinLyons
