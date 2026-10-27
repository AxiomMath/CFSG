module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStanding

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem zpowers_subgroupOf {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    (zpowers x).subgroupOf H = zpowers (⟨x, hx⟩ : H) := by
  apply map_injective H.subtype_injective
  rw [subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_of_le_left (zpowers_le.mpr hx)]
  rfl

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem t_mem [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : t ∈ S := by
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.config.orderOf_eq, pow_one])
  have hle : S ≤ normalizer (zpowers t : Set X) := fun x hx => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute x t := mem_centralizer_singleton_iff.mp (hS.le hx)
    exact (hc.zpow_right j).eq.symm
  have heq := hS.eq_of_le (le_sup_left : S ≤ S ⊔ zpowers t)
    (sup_le hS.le (zpowers_le.mpr htH)) (hS.isPGroup.to_sup_of_normal_right' ht2 hle)
  rw [← heq]
  exact mem_sup_right (mem_zpowers t)

theorem lift_involution [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {u s d : X} (hu : u ∈ S) (hs : s ∈ S)
    (hd : d ∈ S ⊓ L) (hs2 : s ^ 2 = 1)
    (hcomm : ∀ d' (hd' : d' ∈ S ⊓ L), h.rho ⟨d', hS.le hd'.1⟩ * h.rho ⟨u, hS.le hu⟩ =
      h.rho ⟨u, hS.le hu⟩ * h.rho ⟨d', hS.le hd'.1⟩)
    (hu2 : h.rho ⟨u, hS.le hu⟩ ^ 2 = 1)
    (hsd : h.rho ⟨s, hS.le hs⟩ = h.rho ⟨d, hS.le hd.1⟩ * h.rho ⟨u, hS.le hu⟩) :
    (∀ d' ∈ S ⊓ L, d' * u = u * d') ∧ u ^ 2 = 1 := by
  have hD : ∀ d' (hd' : d' ∈ S ⊓ L), d' * u = u * d' := fun d' hd' =>
    h.commute_of_rho_commute hS hd'.1 hu hd'.2 (hcomm d' hd')
  refine ⟨hD, ?_⟩
  have hxS : (d * u)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem (S.mul_mem hd.1 hu)) hs
  have hx1 : h.rho ⟨(d * u)⁻¹ * s, hS.le hxS⟩ = 1 := by
    have : (⟨(d * u)⁻¹ * s, hS.le hxS⟩ : ↥(centralizer ({t} : Set X))) =
        ((⟨d, hS.le hd.1⟩ : ↥(centralizer ({t} : Set X))) * ⟨u, hS.le hu⟩)⁻¹ *
          ⟨s, hS.le hs⟩ := rfl
    rw [this, map_mul, map_inv, map_mul, hsd, inv_mul_cancel]
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (h.mem_zpowers_of_rho_eq_one hS hxS hx1)
  have hs' : s = d * u * t ^ j := by rw [hj]; group
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hdt : Commute d t := mem_centralizer_singleton_iff.mp (hS.le hd.1)
  have hut : Commute u t := mem_centralizer_singleton_iff.mp (hS.le hu)
  have htd : Commute d (t ^ j) := hdt.zpow_right j
  have htu : Commute u (t ^ j) := hut.zpow_right j
  have hdu : Commute d u := hD d hd
  have htj2 : (t ^ j) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  rw [hs', (htd.mul_left htu).mul_pow, hdu.mul_pow, htj2, mul_one] at hs2
  have hu2t : u ^ 2 ∈ zpowers t := by
    refine h.mem_zpowers_of_rho_eq_one hS (S.pow_mem hu 2) ?_
    have : (⟨u ^ 2, hS.le (S.pow_mem hu 2)⟩ : ↥(centralizer ({t} : Set X))) =
        (⟨u, hS.le hu⟩ : ↥(centralizer ({t} : Set X))) ^ 2 := rfl
    rw [this, map_pow, hu2]
  have hu2L : u ^ 2 ∈ L := by
    rw [eq_inv_of_mul_eq_one_right hs2]
    exact L.inv_mem (L.pow_mem hd.2 2)
  exact h.eq_one_of_mem_zpowers_of_mem hu2t hu2L


structure Lift (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (w : X) : Prop where
  mem : w ∈ S
  data : SylowAutData ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho) (h.rho ⟨w, hS.le mem⟩)
  orderOf_eq : orderOf w = orderOf (h.rho ⟨w, hS.le mem⟩)
  comm_D : ∀ d ∈ S ⊓ L, d * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * d
  sq_u : (w ^ (orderOf w / 2)) ^ 2 = 1

theorem exists_lift [Finite X] (hKG : AutPSL2SylowInput) (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    (∃ w, Lift h hS w) ∧
      ∀ Q : Subgroup (MulAut (Bar L)), Q ≤ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho →
        ∃ s : Finset (MulAut (Bar L)), s.card ≤ 3 ∧
          Subgroup.closure (s : Set (MulAut (Bar L))) = Q := by
  classical
  have hSH : S ≤ centralizer ({t} : Set X) := hS.le
  have hSyl := h.isSylowOf_rho hS
  have hR := h.map_rho_inf_innAut hS
  obtain ⟨Q, hQ⟩ := id hS
  obtain ⟨s, hsQ, hs2, φ, hφind, hφfield⟩ := h.dihedral.field Q
  rw [hQ] at hsQ
  have hφ : φ = (h.rho ⟨s, hSH hsQ⟩)⁻¹ := by
    rw [h.rho_apply]
    exact (isInducedAut_iff L s _ φ).mp hφind
  have hφSb : φ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho := by
    rw [hφ]
    exact inv_mem ⟨⟨s, hSH hsQ⟩, hsQ, rfl⟩
  obtain ⟨⟨v, hvdata⟩, hgen⟩ :=
    hKG (Bar L) p f h.config.prime h.config.ne_two
      (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
      h.config.lieModel h.rho.range h.innAut_le_range ⟨φ, hSyl.le hφSb, hφfield⟩ _ hSyl.le
      hSyl.exists_sylow_eq_subgroupOf
  refine ⟨?_, hgen⟩
  have hvSb' := hvdata.mem
  obtain ⟨⟨w, hwH⟩, hwS, hwv⟩ := hvdata.mem
  change w ∈ S at hwS
  have hv1 : v ≠ 1 := fun hv => hvdata.not_mem_inn (hv ▸ one_mem _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hSyl.isPGroup ⟨v, hvSb'⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hv1
    · exact hk0
  set m := orderOf v / 2 with hm
  have hm2 : orderOf v = 2 * m := by
    rw [hm, hk, ← pow_sub_mul_pow 2 hk1, pow_one, Nat.mul_div_cancel _ two_pos, mul_comm]
  have hv02 : (v ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← hm2, pow_orderOf_eq_one]
  have huS : w ^ m ∈ S := S.pow_mem hwS m
  have hρu : h.rho ⟨w ^ m, hSH huS⟩ = v ^ m := by
    rw [← hwv, ← map_pow]
    rfl
  obtain ⟨r, hrR, hφr⟩ := hvdata.fieldInv φ hφSb hφfield
  rw [hR] at hrR
  obtain ⟨⟨d, hdH⟩, hdD, rfl⟩ := hrR
  change d ∈ S ⊓ L at hdD
  have hsinv2 : s⁻¹ ^ 2 = 1 := by
    rw [inv_pow, (orderOf_eq_prime_iff.mp hs2).1, inv_one]
  obtain ⟨hDu, hu2⟩ := h.lift_involution hS huS (S.inv_mem hsQ) hdD hsinv2
    (fun d' hd' => by
      rw [hρu]
      have hmem : h.rho ⟨d', hS.le hd'.1⟩ ∈
          (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
        rw [hR]
        exact ⟨⟨d', hS.le hd'.1⟩, hd', rfl⟩
      exact hvdata.comm_v₀ _ hmem)
    (by rw [hρu]; exact hv02)
    (by
      have : (⟨s⁻¹, hSH (S.inv_mem hsQ)⟩ : ↥(centralizer ({t} : Set X))) =
          (⟨s, hSH hsQ⟩)⁻¹ := rfl
      rw [this, map_inv, ← hφ, hφr, hρu])
  have hw_ord : orderOf w = orderOf v := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [hm2, mul_comm, pow_mul, hu2]
    · have := orderOf_map_dvd h.rho ⟨w, hwH⟩
      rwa [hwv, Subgroup.orderOf_mk] at this
  have hwm : orderOf w / 2 = m := by rw [hw_ord]
  refine ⟨w, hwS, ?_, ?_, ?_, ?_⟩
  · rw [show (⟨w, hSH hwS⟩ : ↥(centralizer ({t} : Set X))) = ⟨w, hwH⟩ from rfl, hwv]
    exact hvdata
  · rw [show (⟨w, hSH hwS⟩ : ↥(centralizer ({t} : Set X))) = ⟨w, hwH⟩ from rfl, hwv]
    exact hw_ord
  · rw [hwm]
    exact hDu
  · rw [hwm]
    exact hu2

theorem lemma41_of_lift [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {w : X} (hL : Lift h hS w)
    (hgen : ∀ Q : Subgroup (MulAut (Bar L)),
      Q ≤ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho →
        ∃ s : Finset (MulAut (Bar L)), s.card ≤ 3 ∧
          Subgroup.closure (s : Set (MulAut (Bar L))) = Q) :
    w ≠ 1 ∧ orderOf (w ^ (orderOf w / 2)) = 2 ∧
      (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w = ⊥ ∧
      (∃ φ : Bar L ≃* Bar L, IsInducedAut L w φ ∧ IsFieldAutPSL2Any φ) ∧
      Nat.card S ≤ 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ∧
      (∀ d ∈ S ⊓ L, d * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * d) ∧
      S ⊓ centralizer {w ^ (orderOf w / 2)} = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
      (S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w →
        S ⊓ centralizer (S : Set X) =
          zpowers t ⊔ ((S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X))) ∧
      (∀ Q : Subgroup X, Q ≤ S →
        ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = Q) ∧
      ¬ IsSylowOf 2 S ⊤ := by
  classical
  have hSH : S ≤ centralizer ({t} : Set X) := hS.le
  have hSyl := h.isSylowOf_rho hS
  have hR := h.map_rho_inf_innAut hS
  have hwS := hL.mem
  have hwH := hSH hwS
  set v := h.rho ⟨w, hwH⟩ with hwv'
  have hwv : h.rho ⟨w, hwH⟩ = v := rfl
  have hvdata : SylowAutData ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho) v := hL.data
  have hvSb' := hvdata.mem
  have hvR := hvdata.not_mem_inn
  have hvfield := hvdata.field
  have hvR' := hvdata.disj
  have hindex := hvdata.relIndex_le
  have hCv0 := hvdata.centralizer_v₀
  have hZ := hvdata.center_of_ne
  have hv1 : v ≠ 1 := fun hv => hvR (hv ▸ one_mem _)
  have hw_ord : orderOf w = orderOf v := hL.orderOf_eq
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hSyl.isPGroup ⟨v, hvSb'⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hv1
    · exact hk0
  set m := orderOf v / 2 with hm
  have hm2 : orderOf v = 2 * m := by
    rw [hm, hk, ← pow_sub_mul_pow 2 hk1, pow_one, Nat.mul_div_cancel _ two_pos, mul_comm]
  have hmpos : 0 < m := by
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right two_pos hk1
    omega
  have hv0 : orderOf (v ^ m) = 2 := by
    rw [orderOf_pow_of_dvd hmpos.ne' ⟨2, by rw [hm2]; ring⟩, hm2,
      Nat.mul_div_cancel _ hmpos]
  have hwm : orderOf w / 2 = m := by rw [hw_ord]
  have huS : w ^ m ∈ S := S.pow_mem hwS m
  have hρu : h.rho ⟨w ^ m, hSH huS⟩ = v ^ m := by
    rw [← hwv, ← map_pow]
    rfl
  have hDu : ∀ d ∈ S ⊓ L, d * w ^ m = w ^ m * d := by
    have := hL.comm_D
    rwa [hwm] at this
  have hu2 : (w ^ m) ^ 2 = 1 := by
    have := hL.sq_u
    rwa [hwm] at this
  have hu1 : w ^ m ≠ 1 := by
    intro h1
    have : h.rho ⟨w ^ m, hSH huS⟩ = 1 := by
      rw [show (⟨w ^ m, hSH huS⟩ : ↥(centralizer ({t} : Set X))) = 1 from Subtype.ext h1,
        map_one]
    rw [hρu] at this
    rw [this, orderOf_one] at hv0
    exact absurd hv0 (by norm_num)
  have hu_ord : orderOf (w ^ m) = 2 := orderOf_eq_prime hu2 hu1
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have htS : t ∈ S := h.t_mem hS
  have hTD : zpowers t ⊔ (S ⊓ L) ≤ S := sup_le (zpowers_le.mpr htS) inf_le_left
  have hT : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ S := sup_le hTD (zpowers_le.mpr hwS)
  have hTDmap : ((zpowers t ⊔ (S ⊓ L)).subgroupOf (centralizer ({t} : Set X))).map h.rho =
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
    rw [subgroupOf_sup (zpowers_le.mpr htH) (inf_le_left.trans hSH), Subgroup.map_sup,
      zpowers_subgroupOf htH, MonoidHom.map_zpowers, h.rho_t, zpowers_one_eq_bot, bot_sup_eq,
      hR]
  have hTmap : ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf
      (centralizer ({t} : Set X))).map h.rho =
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) ⊔ zpowers v := by
    rw [subgroupOf_sup (hTD.trans hSH) (zpowers_le.mpr hwH), Subgroup.map_sup, hTDmap,
      zpowers_subgroupOf hwH, MonoidHom.map_zpowers, hwv]
  have hzt : ∀ y ∈ zpowers t, y = 1 ∨ y = t := by
    have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rcases Int.even_or_odd' k with ⟨m', rfl | rfl⟩
    · left
      rw [zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow, one_mul,
        zpow_one]
  have hgen4 : ∀ Q : Subgroup X, Q ≤ S →
      ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = Q := by
    intro Q hQS
    obtain ⟨s₀, hs₀card, hs₀⟩ := hgen ((Q.subgroupOf (centralizer ({t} : Set X))).map h.rho)
      (map_mono fun x hx => hQS hx)
    have hlift : ∀ φ' ∈ s₀, ∃ q : ↥(centralizer ({t} : Set X)), (q : X) ∈ Q ∧
        h.rho q = φ' := by
      intro φ' hφ'
      have hmem : φ' ∈ (Q.subgroupOf (centralizer ({t} : Set X))).map h.rho :=
        hs₀ ▸ subset_closure hφ'
      obtain ⟨q, hqQ, hq'⟩ := hmem
      exact ⟨q, hqQ, hq'⟩
    choose! lift hliftQ hliftρ using hlift
    let s₁ : Finset X := s₀.image (fun φ' => (lift φ' : X)) ∪ (if t ∈ Q then {t} else ∅)
    have hs₁Q : (s₁ : Set X) ⊆ Q := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨φ', hφ', rfl⟩ := Finset.mem_image.mp hy
        exact hliftQ φ' hφ'
      · by_cases htQ : t ∈ Q
        · simp only [htQ, ↓reduceIte, Finset.mem_singleton] at hy
          rw [hy]
          exact htQ
        · simp only [htQ, ↓reduceIte, Finset.notMem_empty] at hy
    refine ⟨s₁, ?_, le_antisymm (closure_le _ |>.mpr hs₁Q) ?_⟩
    · calc s₁.card ≤ (s₀.image (fun φ' => (lift φ' : X))).card +
            (if t ∈ Q then ({t} : Finset X) else ∅).card := Finset.card_union_le _ _
        _ ≤ 3 + 1 := by
          gcongr
          · exact Finset.card_image_le.trans hs₀card
          · split_ifs <;> simp
        _ = 4 := rfl
    · intro x hx
      have hxH := hSH (hQS hx)
      have hle : (Q.subgroupOf (centralizer ({t} : Set X))).map h.rho ≤
          ((closure (s₁ : Set X)).subgroupOf (centralizer ({t} : Set X))).map h.rho := by
        rw [← hs₀, closure_le]
        intro φ' hφ'
        refine ⟨lift φ', subset_closure ?_, hliftρ φ' hφ'⟩
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hφ')
      obtain ⟨⟨y, hyH⟩, hyC, hyx⟩ := hle ⟨⟨x, hxH⟩, hx, rfl⟩
      change y ∈ closure (s₁ : Set X) at hyC
      have hyQ : y ∈ Q := (closure_le _).mpr hs₁Q hyC
      have hyx' : h.rho ⟨y⁻¹ * x, hSH (hQS (Q.mul_mem (Q.inv_mem hyQ) hx))⟩ = 1 := by
        have : (⟨y⁻¹ * x, hSH (hQS (Q.mul_mem (Q.inv_mem hyQ) hx))⟩ :
            ↥(centralizer ({t} : Set X))) = (⟨y, hyH⟩)⁻¹ * ⟨x, hxH⟩ := rfl
        rw [this, map_mul, map_inv, hyx, inv_mul_cancel]
      rcases hzt _ (h.mem_zpowers_of_rho_eq_one hS (hQS (Q.mul_mem (Q.inv_mem hyQ) hx)) hyx')
        with h1 | h1
      · rw [show x = y * (y⁻¹ * x) by group, h1, mul_one]
        exact hyC
      · have htQ : t ∈ Q := h1 ▸ Q.mul_mem (Q.inv_mem hyQ) hx
        have hts : t ∈ closure (s₁ : Set X) := subset_closure (Finset.mem_union_right _
          (by simp only [htQ, ↓reduceIte, Finset.mem_singleton]))
        rw [show x = y * (y⁻¹ * x) by group, h1]
        exact mul_mem hyC hts
  rw [hwm]
  refine ⟨fun hw1 => hu1 (by rw [hw1, one_pow]), hu_ord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx2
    have hxH : w ^ i ∈ centralizer ({t} : Set X) := zpow_mem hwH i
    have h1 : h.rho ⟨w ^ i, hxH⟩ ∈ zpowers v ⊓
        ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) := by
      have hρwi : h.rho ⟨w ^ i, hxH⟩ = v ^ i := by
        rw [← hwv, ← map_zpow]
        rfl
      refine ⟨hρwi ▸ zpow_mem (mem_zpowers v) i, ?_⟩
      rw [← hTDmap]
      exact ⟨⟨w ^ i, hxH⟩, hx1, rfl⟩
    rw [hvR', mem_bot] at h1
    have hρwi : h.rho ⟨w ^ i, hxH⟩ = v ^ i := by
      rw [← hwv, ← map_zpow]
      rfl
    rw [hρwi, ← orderOf_dvd_iff_zpow_eq_one, ← hw_ord, orderOf_dvd_iff_zpow_eq_one] at h1
    exact h1
  ·
    refine ⟨(h.rho ⟨w, hwH⟩)⁻¹, ?_, ?_⟩
    · rw [isInducedAut_iff L w (h.centralizer_le_normalizer hwH), h.rho_apply]
    · rw [hwv]
      exact hvfield.inv
  ·
    have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
    have h1 := h.card_eq_two_mul hS le_rfl htS
    have h2 := h.card_eq_two_mul hS hT htT
    rw [hTmap] at h2
    have h3 := Subgroup.relIndex_mul_card
      ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) ⊔ zpowers v)
      ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho)
    rw [inf_of_le_left (sup_le inf_le_left (zpowers_le.mpr hvSb'))] at h3
    have h4 : Nat.card ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho) ≤
        2 * Nat.card ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) ⊔
          zpowers v : Subgroup (MulAut (Bar L))) := by
      rw [← h3]
      exact Nat.mul_le_mul_right _ hindex
    rw [h1, h2]
    omega
  ·
    exact hDu
  ·
    apply le_antisymm
    · rintro x ⟨hxS, hxc⟩
      have hxH := hSH hxS
      have hρx : h.rho ⟨x, hxH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
          centralizer {v ^ m} := by
        refine ⟨⟨⟨x, hxH⟩, hxS, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← hρu, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp hxc)
      rw [hCv0, ← hTmap] at hρx
      obtain ⟨⟨y, hyH⟩, hyT, hyx⟩ := hρx
      change y ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w at hyT
      have hyS : y ∈ S := hT hyT
      have hyx' : h.rho ⟨y⁻¹ * x, hSH (S.mul_mem (S.inv_mem hyS) hxS)⟩ = 1 := by
        have : (⟨y⁻¹ * x, hSH (S.mul_mem (S.inv_mem hyS) hxS)⟩ :
            ↥(centralizer ({t} : Set X))) = (⟨y, hyH⟩)⁻¹ * ⟨x, hxH⟩ := rfl
        rw [this, map_mul, map_inv, hyx, inv_mul_cancel]
      have hyxt := h.mem_zpowers_of_rho_eq_one hS (S.mul_mem (S.inv_mem hyS) hxS) hyx'
      rw [show x = y * (y⁻¹ * x) by group]
      exact mul_mem hyT (mem_sup_left (mem_sup_left hyxt))
    · refine le_inf hT (sup_le (sup_le ?_ ?_) ?_)
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (hSH huS)).symm
      · exact fun d hd => mem_centralizer_singleton_iff.mpr (hDu d hd)
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr (Commute.self_pow w m).eq
  ·
    intro hST
    have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
    have hSbT : (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ≠
        (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) ⊔ zpowers v := by
      intro heq
      apply hST
      have h1 := h.card_eq_two_mul hS le_rfl htS
      have h2 := h.card_eq_two_mul hS hT htT
      rw [hTmap, ← heq] at h2
      exact (Subgroup.eq_of_le_of_card_ge hT (by omega)).symm
    have hZ' := hZ hSbT
    have hρD : ∀ d (hd : d ∈ S ⊓ L), h.rho ⟨d, hSH hd.1⟩ ∈
        (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := fun d hd => by
      rw [hR]
      exact ⟨⟨d, hSH hd.1⟩, hd, rfl⟩
    apply le_antisymm
    · rintro x ⟨hxS, hxc⟩
      have hxH := hSH hxS
      have hρx : h.rho ⟨x, hxH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
          centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho :
            Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
        refine ⟨⟨⟨x, hxH⟩, hxS, rfl⟩, mem_centralizer_iff.mpr ?_⟩
        rintro _ ⟨⟨y, hyH⟩, hyS, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_iff.mp hxc y hyS)
      rw [hZ'] at hρx
      obtain ⟨hρxR, hρxc⟩ := hρx
      have hρxD := hρxR
      rw [hR] at hρxD
      obtain ⟨⟨d, hdH⟩, hdD, hdx⟩ := hρxD
      change d ∈ S ⊓ L at hdD
      have hdZ : d ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
        refine ⟨hdD, mem_centralizer_iff.mpr fun d' hd' => ?_⟩
        have hc := mem_centralizer_iff.mp hρxc _ (hρD d' hd')
        rw [← hdx] at hc
        exact h.commute_of_rho_commute hS hd'.1 hdD.1 hd'.2 hc
      have hdx' : h.rho ⟨d⁻¹ * x, hSH (S.mul_mem (S.inv_mem hdD.1) hxS)⟩ = 1 := by
        have : (⟨d⁻¹ * x, hSH (S.mul_mem (S.inv_mem hdD.1) hxS)⟩ :
            ↥(centralizer ({t} : Set X))) = (⟨d, hdH⟩)⁻¹ * ⟨x, hxH⟩ := rfl
        rw [this, map_mul, map_inv, hdx, inv_mul_cancel]
      have hdxt := h.mem_zpowers_of_rho_eq_one hS (S.mul_mem (S.inv_mem hdD.1) hxS) hdx'
      rw [show x = d * (d⁻¹ * x) by group]
      rw [sup_comm]
      exact mul_mem (mem_sup_left hdZ) (mem_sup_right hdxt)
    · refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact ⟨htS, mem_centralizer_iff.mpr fun y hy =>
          (mem_centralizer_singleton_iff.mp (hSH hy))⟩
      · rintro d ⟨hdD, hdc⟩
        refine ⟨hdD.1, mem_centralizer_iff.mpr fun y hy => ?_⟩
        have hρdZ : h.rho ⟨d, hSH hdD.1⟩ ∈
            (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
              centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho :
                Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
          rw [hZ']
          refine ⟨hρD d hdD, mem_centralizer_iff.mpr ?_⟩
          rintro _ ⟨hφ1, hφ2⟩
          have hφD := (show _ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
            innAut (Bar L) from ⟨hφ1, hφ2⟩)
          rw [hR] at hφD
          obtain ⟨⟨d', hd'H⟩, hd'D, rfl⟩ := hφD
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (mem_centralizer_iff.mp hdc d' hd'D)
        have hc := mem_centralizer_iff.mp hρdZ.2 _ ⟨⟨y, hSH hy⟩, hy, rfl⟩
        exact (h.commute_of_rho_commute hS hdD.1 hy hdD.2 hc.symm).symm
  · exact hgen4
  ·
    intro hSyl'
    apply h.sect
    intro P hP
    have hcard : Nat.card S = 2 ^ (Nat.card X).factorization 2 := by
      rw [hSyl'.card_eq, card_top]
    obtain ⟨P', hPP'⟩ := hP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard S hcard) P'
    have hPS : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ ((g • Sylow.ofCard S hcard : Sylow 2 X) : Subgroup X) := by
        rw [hg]
        exact hPP' hy
      rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        at hy'
      have hconj : (MulAut.conj g⁻¹).toMonoidHom y = (MulAut.conj g)⁻¹ • y := by
        simp [MulAut.smul_def]
      rw [hconj]
      exact hy'
    obtain ⟨s', hs'card, hs'⟩ := hgen4 _ hPS
    refine ⟨s'.image (MulAut.conj g), Finset.card_image_le.trans hs'card, ?_⟩
    have himg : ((s'.image (MulAut.conj g) : Finset X) : Set X) =
        ⇑((MulAut.conj g).toMonoidHom) '' (s' : Set X) := by
      rw [Finset.coe_image]
      rfl
    rw [himg, ← MonoidHom.map_closure, hs', Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
    group

theorem lemma41 [Finite X] (hKG : AutPSL2SylowInput) (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    ∃ w ∈ S, w ≠ 1 ∧ orderOf (w ^ (orderOf w / 2)) = 2 ∧
      (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w = ⊥ ∧
      (∃ φ : Bar L ≃* Bar L, IsInducedAut L w φ ∧ IsFieldAutPSL2Any φ) ∧
      Nat.card S ≤ 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ∧
      (∀ d ∈ S ⊓ L, d * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * d) ∧
      S ⊓ centralizer {w ^ (orderOf w / 2)} = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
      (S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w →
        S ⊓ centralizer (S : Set X) =
          zpowers t ⊔ ((S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X))) ∧
      (∀ Q : Subgroup X, Q ≤ S →
        ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = Q) ∧
      ¬ IsSylowOf 2 S ⊤ := by
  obtain ⟨⟨w, hL⟩, hgen⟩ := h.exists_lift hKG hS
  exact ⟨w, hL.mem, h.lemma41_of_lift hS hL hgen⟩

end Standing

end CFSG.ComponentClassification.HarrisLit
