module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Count

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

section Abstract

variable {A : Type} [Group A] [Finite A]

theorem exists_radicals (c : L34Cover A) (hNZ : standardComponentOddCore A ≤ center A)
    (T : Sylow 2 A) :
    ∃ H : Fin 2 → Subgroup A,
      (∀ M : Subgroup A, M ≤ T → IsElemAbelian 2 M → Nat.card M = 16 * Nat.card c.π.ker →
        ∃ j, M = H j) ∧
      ∀ j, (T : Subgroup A) ≤ normalizer (H j : Set A) ∧
        normalizer (H j : Set A) ≤
          ⁅normalizer (H j : Set A), normalizer (H j : Set A)⁆ ⊔ centralizer (H j : Set A) ∧
        (centralizer (H j : Set A)).relIndex (normalizer (H j : Set A)) = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N with hpdef
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective N
  have hTN : (T : Subgroup A) ⊓ N = ⊥ := inf_eq_bot_of_isPGroup T.isPGroup' hN
  obtain ⟨π', hsurj', hker', hTb⟩ := exists_std_cover c T
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  obtain ⟨hH, hprod, -, -, -, -, -, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ₀, -, -, hσ₀, -⟩, -⟩ := hlevi 0
  obtain ⟨⟨-, -, -, -, -, -, hEA, -, -, -, -⟩, ⟨-, hnormT, -⟩, -⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ₀ hσ₀
  set TX := (projUnip c.k).comap π' with hTX
  set HX : Fin 2 → Subgroup (A ⧸ N) := fun i => (projRad c.k i).comap π' with hHX
  have hkpos : 0 < Nat.card π'.ker := Nat.card_pos
  have hHXT : ∀ i, HX i ≤ TX := by
    intro i x hx
    have h : x ∈ ((HX 0 : Set (A ⧸ N)) * (HX 1 : Set (A ⧸ N))) := by
      fin_cases i
      · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
      · exact ⟨1, one_mem _, x, hx, one_mul x⟩
    rw [hprod] at h
    exact h
  have hTXN : ∀ i, TX ≤ normalizer (HX i : Set (A ⧸ N)) := by
    intro i
    have h := hnormT ▸ (le_normalizer : TX ≤ normalizer (TX : Set (A ⧸ N)))
    fin_cases i
    · exact h.trans inf_le_left
    · exact h.trans inf_le_right
  have hHX2 : ∀ i, ∀ x ∈ HX i, x * x = 1 := fun i x hx => by
    have := (hH i).1
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := HX i) x hx
  have hCX : ∀ i, centralizer (HX i : Set (A ⧸ N)) = HX i := by
    intro i
    refine le_antisymm (fun x hx => ?_) fun x hx => mem_centralizer_iff.mpr fun y hy => ?_
    · have : CharP c.k 2 := charP_two_of_card c.card_k
      have h16 : 5 ≤ Nat.card (projRad c.k i) := by rw [card_projRad, c.card_k]; omega
      refine mem_projRad_of_commute c.card_k i le_rfl h16 fun b hb => ?_
      obtain ⟨y, rfl⟩ := hsurj' b
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx y hb).symm]
    · have h1 := hHX2 i (y * x) (mul_mem hy hx)
      have h2 := hHX2 i y hy
      have h3 := hHX2 i x hx
      calc y * x = (y * x)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = x⁻¹ * y⁻¹ := mul_inv_rev y x
        _ = x * y := by rw [inv_eq_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right h2]
  set H : Fin 2 → Subgroup A := fun j => (T : Subgroup A) ⊓ (HX j).comap p with hHdef
  have hHle : ∀ j, H j ≤ T := fun j => inf_le_left
  have hmapH : ∀ j, (H j).map p = HX j := fun j =>
    map_inf_comap_eq (hTb ▸ hHXT j)
  have hH2 : ∀ j, ∀ m ∈ H j, m * m = 1 := by
    intro j m hm
    have h1 : p (m * m) = 1 := by
      rw [map_mul]
      exact hHX2 j _ (hmapH j ▸ ⟨m, hm, rfl⟩)
    have h2 : m * m ∈ (T : Subgroup A) ⊓ N :=
      ⟨mul_mem (hHle j hm) (hHle j hm), (QuotientGroup.eq_one_iff _).mp h1⟩
    rwa [hTN, mem_bot] at h2
  have hNZ' : ∀ n ∈ N, ∀ a : A, n * a = a * n := fun n hn a =>
    (mem_center_iff.mp (hNZ hn) a).symm
  have hnorm : ∀ j, normalizer (H j : Set A) = (normalizer (HX j : Set (A ⧸ N))).comap p := by
    intro j
    ext a
    constructor
    · intro ha
      refine mem_normalizer_fintype fun x hx => ?_
      rw [SetLike.mem_coe, ← hmapH j] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      exact ⟨a * m * a⁻¹, (mem_normalizer_iff.mp ha m).mp hm, by simp⟩
    · intro ha
      refine mem_normalizer_fintype fun m hm => ?_
      have hpm : p (a * m * a⁻¹) ∈ HX j := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp ha (p m)).mp (hmapH j ▸ ⟨m, hm, rfl⟩)
      rw [← hmapH j] at hpm
      obtain ⟨m', hm', hpm'⟩ := hpm
      set n := m'⁻¹ * (a * m * a⁻¹) with hn
      have hnN : n ∈ N := QuotientGroup.eq.mp hpm'
      have hnn : n * n = 1 := by
        have e1 : a * m * a⁻¹ = m' * n := by rw [hn]; group
        have e2 : (a * m * a⁻¹) * (a * m * a⁻¹) = 1 := by
          calc (a * m * a⁻¹) * (a * m * a⁻¹) = a * (m * m) * a⁻¹ := by group
            _ = 1 := by rw [hH2 j m hm, mul_one, mul_inv_cancel]
        have e3 : (m' * n) * (m' * n) = n * n := by
          calc (m' * n) * (m' * n) = m' * (n * m') * n := by group
            _ = m' * (m' * n) * n := by rw [hNZ' n hnN m']
            _ = (m' * m') * (n * n) := by group
            _ = n * n := by rw [hH2 j m' hm', one_mul]
        rw [← e3, ← e1, e2]
      have hn1 : n = 1 := by
        have h1 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hnn)
        have h2 : Odd (orderOf n) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hnN)
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact orderOf_eq_one_iff.mp h
        · rw [h] at h2
          exact absurd h2 (by decide)
      have : a * m * a⁻¹ = m' := by
        rw [hn, inv_mul_eq_one] at hn1
        exact hn1.symm
      rw [this]
      exact hm'
  have hcent : ∀ j, centralizer (H j : Set A) =
      (centralizer (HX j : Set (A ⧸ N))).comap p := by
    intro j
    ext a
    constructor
    · intro ha
      refine mem_centralizer_iff.mpr fun x hx => ?_
      rw [SetLike.mem_coe, ← hmapH j] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp ha m hm]
    · intro ha
      have haN : a ∈ normalizer (H j : Set A) := by
        rw [hnorm j]
        exact Subgroup.centralizer_le_normalizer _ ha
      refine mem_centralizer_iff.mpr fun m hm => ?_
      have hw : a * m * a⁻¹ * m⁻¹ ∈ (T : Subgroup A) ⊓ N := by
        refine ⟨hHle j (mul_mem ((mem_normalizer_iff.mp haN m).mp hm) (inv_mem hm)), ?_⟩
        apply (QuotientGroup.eq_one_iff _).mp
        have h := mem_centralizer_iff.mp ha (p m) (hmapH j ▸ ⟨m, hm, rfl⟩)
        change p (a * m * a⁻¹ * m⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
        group
      rw [hTN, mem_bot] at hw
      calc m * a = a * m * a⁻¹ * m⁻¹ * (m * a) := by rw [hw, one_mul]
        _ = a * m := by group
  refine ⟨H, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  ·
    intro M hMT hM hcard
    have hpM : IsElemAbelian 2 (M.map p) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        simp only [coe_mul]
        rw [← map_mul, ← map_mul]
        exact congrArg p (congrArg Subtype.val (hM.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hM.2 x hx, map_one]
    have hpM' : CFSG.IsElementaryAbelian 2 ↥(M.map p) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hpM
    have hpMT : M.map p ≤ TX := hTb ▸ map_mono hMT
    have hcardM : Nat.card (M.map p) = Nat.card M := card_map_mk'_of_le T.2 hN hMT
    have key : ∀ j, M.map p ≤ HX j → M = H j := by
      intro j hj
      refine eq_of_map_eq T.2 hN hMT (hHle j) ?_
      rw [hmapH j]
      refine Subgroup.eq_of_le_of_card_ge hj ?_
      rw [hcardM, hcard, (hH j).2, hker']
    rcases hEA _ hpMT hpM' with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  ·
    intro t ht
    rw [hnorm j]
    exact hTXN j (hTb ▸ ⟨t, ht, rfl⟩)
  ·
    obtain ⟨⟨σ, -, -, -, hσ, -⟩, -⟩ := hlevi j
    have hperf : Group.IsPerfect (CFSG.LieType.Chevalley.SL2 c.k) := by
      have := Fintype.ofFinite c.k
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (Finset.univ : Finset c.k).card by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, c.card_k])
      exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
    set NX := normalizer (HX j : Set (A ⧸ N)) with hNX
    have hσNX : σ.range ≤ NX := le_sup_right.trans hσ.le
    have hσcomm : σ.range = ⁅σ.range, σ.range⁆ := by
      rw [MonoidHom.range_eq_map, ← map_commutator]
      exact congrArg (map σ) hperf.commutator_eq_top.symm
    have hNXle : NX ≤ centralizer (HX j : Set (A ⧸ N)) ⊔ ⁅NX, NX⁆ :=
      calc NX = HX j ⊔ σ.range := hσ.symm
        _ ≤ centralizer (HX j : Set (A ⧸ N)) ⊔ ⁅NX, NX⁆ :=
          sup_le_sup (hCX j).ge (hσcomm.le.trans (Subgroup.commutator_mono hσNX hσNX))
    have hmapN : (normalizer (H j : Set A)).map p = NX := by
      rw [hnorm j]
      exact map_comap_eq_self_of_surjective hp _
    have hcomap : ⁅NX, NX⁆.comap p =
        ⁅normalizer (H j : Set A), normalizer (H j : Set A)⁆ ⊔ N := by
      rw [← hmapN, ← map_commutator, comap_map_eq, QuotientGroup.ker_mk']
    have hNC : N ≤ centralizer (H j : Set A) := fun n hn =>
      mem_centralizer_iff.mpr fun m _ => (hNZ' n hn m).symm
    calc normalizer (H j : Set A) = NX.comap p := hnorm j
      _ ≤ (centralizer (HX j : Set (A ⧸ N)) ⊔ ⁅NX, NX⁆).comap p := comap_mono hNXle
      _ = centralizer (H j : Set A) ⊔ ⁅NX, NX⁆.comap p := by
          rw [hcent j]
          exact (Subgroup.comap_sup_eq (f := p) _ _ hp).symm
      _ = centralizer (H j : Set A) ⊔
          (⁅normalizer (H j : Set A), normalizer (H j : Set A)⁆ ⊔ N) := by rw [hcomap]
      _ ≤ ⁅normalizer (H j : Set A), normalizer (H j : Set A)⁆ ⊔ centralizer (H j : Set A) :=
          sup_le le_sup_right (sup_le le_sup_left (hNC.trans le_sup_right))
  ·
    obtain ⟨-, hcardN, -⟩ := hlevi j
    rw [hcent j, hnorm j, relIndex_comap, map_comap_eq_self_of_surjective hp, hCX j]
    have h := Subgroup.relIndex_mul_card (HX j) (normalizer (HX j : Set (A ⧸ N)))
    rw [inf_eq_left.mpr le_normalizer, hcardN, (hH j).2] at h
    have h' : (HX j).relIndex (normalizer (HX j : Set (A ⧸ N))) * 16 = 960 :=
      Nat.eq_of_mul_eq_mul_right hkpos (by rw [mul_assoc, h])
    omega

end Abstract

section Transfer

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem map_normalizer_subgroupOf {D : Subgroup G} (hDA : D ≤ A) :
    (normalizer ((D.subgroupOf A : Subgroup ↥A) : Set ↥A)).map A.subtype =
      A ⊓ normalizer (D : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, mem_normalizer_fintype fun d hd => ?_⟩
    have h := (mem_normalizer_iff.mp ha ⟨d, hDA hd⟩).mp hd
    exact h
  · rintro ⟨hxA, hx⟩
    refine ⟨⟨x, hxA⟩, mem_normalizer_fintype fun d hd => ?_, rfl⟩
    exact (mem_normalizer_iff.mp hx (d : G)).mp hd

omit [Finite G] in
theorem map_centralizer_subgroupOf {D : Subgroup G} (hDA : D ≤ A) :
    (centralizer ((D.subgroupOf A : Subgroup ↥A) : Set ↥A)).map A.subtype =
      A ⊓ centralizer (D : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp ha ⟨d, hDA hd⟩ hd)
  · rintro ⟨hxA, hx⟩
    refine ⟨⟨x, hxA⟩, mem_centralizer_iff.mpr fun d hd => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.mp hx (d : G) hd

theorem radical_of_le (c : L34Cover ↥A) (hNZ : standardComponentOddCore ↥A ≤ center ↥A)
    {S D : Subgroup G} (hS : IsSylowOf 2 S A) (hDS : D ≤ S) (hD : IsElemAbelian 2 D)
    (hcard : Nat.card D = 16 * Nat.card c.π.ker) :
    S ≤ normalizer (D : Set G) ∧
      A ⊓ normalizer (D : Set G) ≤
        ⁅A ⊓ normalizer (D : Set G), A ⊓ normalizer (D : Set G)⁆ ⊔ centralizer (D : Set G) ∧
      (A ⊓ centralizer (D : Set G)).relIndex (A ⊓ normalizer (D : Set G)) = 60 := by
  obtain ⟨T, rfl⟩ := hS
  have hDA : D ≤ A := hDS.trans (map_subtype_le _)
  have hMT : D.subgroupOf A ≤ T := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hDS (mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcardM : Nat.card (D.subgroupOf A) = 16 * Nat.card c.π.ker := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  obtain ⟨H, hcls, hfacts⟩ := exists_radicals c hNZ T
  obtain ⟨j, hj⟩ := hcls _ hMT (isElemAbelian_subgroupOf hD A) hcardM
  obtain ⟨hTN, hperf, hidx⟩ := hfacts j
  rw [← hj] at hTN hperf hidx
  rw [← map_normalizer_subgroupOf hDA, ← map_centralizer_subgroupOf hDA]
  refine ⟨?_, ?_, ?_⟩
  · exact (map_mono hTN).trans (by rw [map_normalizer_subgroupOf hDA]; exact inf_le_right)
  · refine (map_mono hperf).trans ?_
    rw [Subgroup.map_sup, map_commutator, map_centralizer_subgroupOf hDA]
    exact sup_le_sup_left inf_le_right _
  · rw [relIndex_map_map_of_injective _ _ A.subtype_injective]
    exact hidx

theorem eq_or_eq_of_isElemAbelian (c : L34Cover ↥A)
    (hNZ : standardComponentOddCore ↥A ≤ center ↥A) {S M₁ M₂ M₃ : Subgroup G}
    (hS : IsSylowOf 2 S A) (h₁ : M₁ ≤ S) (h₂ : M₂ ≤ S) (h₃ : M₃ ≤ S) (he₁ : IsElemAbelian 2 M₁)
    (he₂ : IsElemAbelian 2 M₂) (he₃ : IsElemAbelian 2 M₃)
    (hc₁ : Nat.card M₁ = 16 * Nat.card c.π.ker) (hc₂ : Nat.card M₂ = 16 * Nat.card c.π.ker)
    (hc₃ : Nat.card M₃ = 16 * Nat.card c.π.ker) : M₃ = M₁ ∨ M₃ = M₂ ∨ M₁ = M₂ := by
  obtain ⟨T, rfl⟩ := hS
  obtain ⟨H, hcls, -⟩ := exists_radicals c hNZ T
  have key : ∀ {M : Subgroup G}, M ≤ (T : Subgroup ↥A).map A.subtype → IsElemAbelian 2 M →
      Nat.card M = 16 * Nat.card c.π.ker → ∃ j, M.subgroupOf A = H j := by
    intro M hMS hM hcard
    have hMA : M ≤ A := hMS.trans (map_subtype_le _)
    have hMT : M.subgroupOf A ≤ T := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hMS (mem_subgroupOf.mp hx)
      rwa [show y = x from Subtype.ext hyx] at hy
    refine hcls _ hMT (isElemAbelian_subgroupOf hM A) ?_
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMA).toEquiv
  have hinj : ∀ {M M' : Subgroup G}, M ≤ (T : Subgroup ↥A).map A.subtype →
      M' ≤ (T : Subgroup ↥A).map A.subtype → M.subgroupOf A = M'.subgroupOf A → M = M' := by
    intro M M' hM hM' h
    rw [subgroupOf_inj, inf_eq_left.mpr (hM.trans (map_subtype_le _)),
      inf_eq_left.mpr (hM'.trans (map_subtype_le _))] at h
    exact h
  obtain ⟨j₁, hj₁⟩ := key h₁ he₁ hc₁
  obtain ⟨j₂, hj₂⟩ := key h₂ he₂ hc₂
  obtain ⟨j₃, hj₃⟩ := key h₃ he₃ hc₃
  have hj : j₃ = j₁ ∨ j₃ = j₂ ∨ j₁ = j₂ := by
    fin_cases j₁ <;> fin_cases j₂ <;> fin_cases j₃ <;> simp
  rcases hj with h | h | h
  · exact Or.inl (hinj h₃ h₁ (by rw [hj₃, hj₁, h]))
  · exact Or.inr (Or.inl (hinj h₃ h₂ (by rw [hj₃, hj₂, h])))
  · exact Or.inr (Or.inr (hinj h₁ h₂ (by rw [hj₁, hj₂, h])))

end Transfer

section Component

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G}

theorem radical_of_component (h11 : Step11) (hB : Base G A) (hL : TypeL34 (rankTwoQuot A))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRA : R ≤ A) (hR4 : Nat.card R = 4)
    {E : Subgroup G} (hEA : E ≤ A) (hE : IsElemAbelian 2 E) (hE64 : Nat.card E = 64) :
    (∀ S : Subgroup G, IsSylowOf 2 S A → E ≤ S → S ≤ normalizer (E : Set G)) ∧
      A ⊓ normalizer (E : Set G) ≤
        ⁅A ⊓ normalizer (E : Set G), A ⊓ normalizer (E : Set G)⁆ ⊔ centralizer (E : Set G) ∧
      (A ⊓ centralizer (E : Set G)).relIndex (A ⊓ normalizer (E : Set G)) = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hB.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hB hL
  have hNZ := oddCore_le_center hstd.1.1 hstd.1.2
  have hker : Nat.card c.π.ker = 4 := by
    rw [card_ker_eq_card_inf c hR, inf_eq_left.mpr hRA, hR4]
  have hcard : Nat.card E = 16 * Nat.card c.π.ker := by rw [hE64, hker]
  obtain ⟨S, hS, hES⟩ := AschbacherTheorem3.exists_isSylowOf_le
    (isPGroup_two_of_isElemAbelian hE) hEA
  obtain ⟨-, hperf, hidx⟩ := radical_of_le c hNZ hS hES hE hcard
  exact ⟨fun S' hS' hES' => (radical_of_le c hNZ hS' hES' hE hcard).1, hperf, hidx⟩

theorem eq_or_eq_of_component (h11 : Step11) (hB : Base G A) (hL : TypeL34 (rankTwoQuot A))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRA : R ≤ A) (hR4 : Nat.card R = 4)
    {S M₁ M₂ M : Subgroup G} (hS : IsSylowOf 2 S A) (h₁ : M₁ ≤ S) (h₂ : M₂ ≤ S) (h : M ≤ S)
    (he₁ : IsElemAbelian 2 M₁) (he₂ : IsElemAbelian 2 M₂) (he : IsElemAbelian 2 M)
    (hc₁ : Nat.card M₁ = 64) (hc₂ : Nat.card M₂ = 64) (hc : Nat.card M = 64) (hne : M₁ ≠ M₂) :
    M = M₁ ∨ M = M₂ := by
  have hstd := hB.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hB hL
  have hNZ := oddCore_le_center hstd.1.1 hstd.1.2
  have hker : Nat.card c.π.ker = 4 := by
    rw [card_ker_eq_card_inf c hR, inf_eq_left.mpr hRA, hR4]
  rcases eq_or_eq_of_isElemAbelian c hNZ hS h₁ h₂ h he₁ he₂ he (by rw [hc₁, hker])
    (by rw [hc₂, hker]) (by rw [hc, hker]) with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · exact absurd h' hne

end Component

end CFSG.ComponentClassification.AS81
