module

public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem klein_centralizer_twelve_core {G : Type*} [Group G] [Finite G] (V W₀ : Subgroup G)
    (hV : IsKleinFour V) (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 12)
    (hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G)) (hW₀ : Nat.card W₀ = 3) :
    (CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype = W₀ ∧
      V ⊔ W₀ = Subgroup.centralizer (V : Set G) ∧ Disjoint V W₀ ∧
      Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W₀ : Set G) ∧
      ∀ x ∈ Subgroup.centralizer (V : Set G), x ^ 3 = 1 → x ∈ W₀ := by
  set D := Subgroup.centralizer (V : Set G) with hDdef
  have hV4 : Nat.card V = 4 := hV.card_four
  have hVcomm : ∀ a b : V, a * b = b * a := mul_comm_of_exponent_two hV.exponent_two
  have hVD : V ≤ D := fun x hx y hy => by
    have h := hVcomm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val h
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₀comm : ∀ a b : W₀, a * b = b * a := by
    have : IsCyclic W₀ := isCyclic_of_prime_card hW₀
    exact fun a b => (IsCyclic.isMulCommutative (α := W₀)).is_comm.comm a b
  have hsup : V ⊔ W₀ = D := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hVD hW₀D)
    rw [hD]
    have h4 : 4 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hV4 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3' : 3 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hW₀ ▸ Subgroup.card_dvd_of_le le_sup_right
    have h12 : 12 ∣ Nat.card (V ⊔ W₀ : Subgroup G) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3'
    exact Nat.le_of_dvd Nat.card_pos h12
  have hVW : V ≤ Subgroup.centralizer (W₀ : Set G) := Subgroup.le_centralizer_iff.mpr hW₀D
  have hDW : D ≤ Subgroup.centralizer (W₀ : Set G) := by
    rw [← hsup]
    refine sup_le hVW fun x hx y hy => ?_
    exact congrArg Subtype.val (hW₀comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hDD : D ≤ Subgroup.centralizer (D : Set G) := by
    intro x hx y hy
    rw [← hsup] at hy
    have hyc : y ∈ Subgroup.centralizer ({x} : Set G) := by
      have hle : V ⊔ W₀ ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun v hv => ?_) (fun w hw => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hx v hv
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hDW hx w hw
      exact hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc
  have hDcomm : ∀ a b : D, a * b = b * a := fun a b =>
    Subtype.ext (hDD b.2 a a.2)
  have hW₀n : (W₀.subgroupOf D).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hDcomm g x, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hW₀card : Nat.card (W₀.subgroupOf D) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₀D).toEquiv, hW₀]
  have hle : W₀.subgroupOf D ≤ CFSG.pPrimeCore 2 D :=
    le_sSup ⟨hW₀n, by rw [hW₀card]; norm_num⟩
  have hcore : CFSG.pPrimeCore 2 D = W₀.subgroupOf D := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hW₀card]
    have hdvd : Nat.card (CFSG.pPrimeCore 2 D) ∣ 12 := hD ▸ Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 D)) := CFSG.pPrimeCore_coprime_card
    have hpos : 0 < Nat.card (CFSG.pPrimeCore 2 D) := Nat.card_pos
    have h12 : Nat.card (CFSG.pPrimeCore 2 D) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (CFSG.pPrimeCore 2 D) <;>
      first | omega | (exfalso; revert hcop; decide)
  have hWeq : (CFSG.pPrimeCore 2 D).map D.subtype = W₀ := by
    rw [hcore, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW₀D]
  refine ⟨hWeq, hsup, ?_, hDW, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hxV hxW
    have h1 : orderOf x ∣ 4 := hV4 ▸ Subgroup.orderOf_dvd_natCard V hxV
    have h2 : orderOf x ∣ 3 := hW₀ ▸ Subgroup.orderOf_dvd_natCard W₀ hxW
    have h3 : orderOf x ∣ Nat.gcd 4 3 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 4 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  · intro x hx hx3
    let x' : D := ⟨x, hx⟩
    have hQ : Nat.card (D ⧸ W₀.subgroupOf D) = 4 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (W₀.subgroupOf D)
      rw [hD, hW₀card] at h
      omega
    have hq4 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4 = 1 := by
      rw [← hQ]
      exact pow_card_eq_one'
    have hq3 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, QuotientGroup.mk_one]
    have hq1 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) = 1 := by
      have : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) =
          (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4 *
            ((QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 3)⁻¹ := by group
      rw [this, hq4, hq3, inv_one, mul_one]
    rw [QuotientGroup.eq_one_iff] at hq1
    exact hq1

theorem conj_eq_or_inv_of_mem_normalizer_of_card_three {G : Type*} [Group G] {W : Subgroup G}
    (hW : Nat.card W = 3) {h : G} (hh : h ∈ Subgroup.normalizer (W : Set G)) :
    (∀ w ∈ W, h * w * h⁻¹ = w) ∨ (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have : IsCyclic W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hg3 : orderOf (g : G) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  have hgen : ∀ w ∈ W, ∃ j : ℤ, (g : G) ^ j = w := by
    intro w hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
  have hc : h * (g : G) * h⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hh _).mp g.2
  obtain ⟨k, hk⟩ := hgen _ hc
  rw [← zpow_mod_orderOf, hg3] at hk
  have hk0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg3
    norm_num at hg3
  obtain h0 | h1 | h2 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  · exfalso
    rw [h0, zpow_zero] at hk
    apply hg1
    have := congrArg (fun x => h⁻¹ * x * h) hk
    simpa [mul_assoc] using this.symm
  · left
    intro w hw
    obtain ⟨j, rfl⟩ := hgen w hw
    rw [h1, zpow_one] at hk
    rw [← conj_zpow, ← hk]
  · right
    intro w hw
    obtain ⟨j, rfl⟩ := hgen w hw
    rw [h2] at hk
    have hinv : (g : G) ^ (2 : ℤ) = (g : G)⁻¹ := by
      have h3' : (g : G) ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one _
      rw [eq_inv_iff_mul_eq_one, zpow_two, ← h3', pow_three, mul_assoc]
    rw [← conj_zpow, ← hk, hinv, inv_zpow]

theorem inf_normalizer_eq_of_card_three {G : Type*} [Group G] [Finite G] (C X W : Subgroup G)
    (hC : Nat.card C = 240) (hWC : W ≤ C) (hW : Nat.card W = 3) (hXC : X ≤ C)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hX : Nat.card X = 24)
    (hnot : ¬ C ≤ Subgroup.normalizer (W : Set G)) :
    C ⊓ Subgroup.normalizer (W : Set G) = X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWcard : Nat.card (W.subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv, hW]
  have hfac : (Nat.card C).factorization 3 = 1 := by
    rw [hC, show (240 : ℕ) = 3 ^ 1 * 80 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let P : Sylow 3 C := Sylow.ofCard (W.subgroupOf C) (by rw [hWcard, hfac, pow_one])
  have hmod0 := card_sylow_modEq_one 3 C
  rw [Sylow.card_eq_index_normalizer P] at hmod0
  have hmod : (Subgroup.normalizer ((W.subgroupOf C : Subgroup C) : Set C)).index ≡ 1 [MOD 3] :=
    hmod0
  have hnorm : Subgroup.normalizer ((W.subgroupOf C : Subgroup C) : Set C) =
      (Subgroup.normalizer (W : Set G)).subgroupOf C := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_normalizer_eq_of_le_range]
    rw [Subgroup.range_subtype]
    exact hWC
  have hYcard : Nat.card ((Subgroup.normalizer (W : Set G)).subgroupOf C) =
      Nat.card (C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hcm := Subgroup.card_mul_index
    (Subgroup.normalizer ((W.subgroupOf C : Subgroup C) : Set C))
  rw [hnorm, hYcard, hC] at hcm
  rw [hnorm] at hmod
  have hXY : X ≤ C ⊓ Subgroup.normalizer (W : Set G) := le_inf hXC hXW
  obtain ⟨m, hm⟩ : 24 ∣ Nat.card (C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) :=
    hX ▸ Subgroup.card_dvd_of_le hXY
  have hi1 : ((Subgroup.normalizer (W : Set G)).subgroupOf C).index ≠ 1 := by
    intro h1
    apply hnot
    intro c hc
    have htop := Subgroup.index_eq_one.mp h1
    have : (⟨c, hc⟩ : C) ∈ (Subgroup.normalizer (W : Set G)).subgroupOf C :=
      htop ▸ Subgroup.mem_top _
    exact this
  rw [hm] at hcm
  have hmi : m * ((Subgroup.normalizer (W : Set G)).subgroupOf C).index = 10 := by
    have : 24 * (m * ((Subgroup.normalizer (W : Set G)).subgroupOf C).index) = 24 * 10 := by
      rw [← mul_assoc, hcm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hm10 : m ≤ 10 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmi)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmi)
  unfold Nat.ModEq at hmod
  have hm1 : m = 1 := by
    interval_cases m <;> omega
  apply (Subgroup.eq_of_le_of_card_ge hXY _).symm
  rw [hm, hX, hm1]

theorem exists_sylow_eq_of_order_four_square {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {t : G} (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (H P₀ : Subgroup G) (hP₀H : P₀ ≤ H) (hP₀ : Nat.card P₀ = 8) {d : G} (hdP : d ∈ P₀)
    (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hCH : Nat.card (Subgroup.centralizer {t} ⊓ H : Subgroup G) ∣ 24) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = P₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₀' : Nat.card (P₀.subgroupOf H) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀H).toEquiv, hP₀]
  have hP₀p : IsPGroup 2 (P₀.subgroupOf H) := IsPGroup.of_card (n := 3) (by rw [hP₀']; norm_num)
  obtain ⟨T, hT⟩ := hP₀p.exists_le_sylow
  have hTp : IsPGroup 2 ((T : Subgroup H).map H.subtype) := T.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hTp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hmemS : ∀ x ∈ (T : Subgroup H).map H.subtype, g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x hx
    have h : x ∈ ((g • S : Sylow 2 G) : Subgroup G) := hg ▸ hS' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] using h
  have hdT : d ∈ (T : Subgroup H).map H.subtype :=
    ⟨⟨d, hP₀H hdP⟩, hT (show (⟨d, hP₀H hdP⟩ : H) ∈ P₀.subgroupOf H from hdP), rfl⟩
  have hgC : g ∈ Subgroup.centralizer {t} := by
    have hy := hmemS d hdT
    have hy4 : orderOf (g⁻¹ * d * g) = 4 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) d
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, hd4]
    have hy2 := hS4 _ hy hy4
    have hconj : g⁻¹ * t * g = t := by
      calc g⁻¹ * t * g = g⁻¹ * d ^ 2 * g := by rw [hd2]
        _ = (g⁻¹ * d * g) ^ 2 := by rw [sq, sq]; group
        _ = t := hy2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = g * (g⁻¹ * t * g) := by rw [hconj]
      _ = t * g := by group
  have hTC : (T : Subgroup H).map H.subtype ≤ Subgroup.centralizer {t} ⊓ H := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxS := hSC (hmemS x hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxS hgC ⊢
      have hg' : g⁻¹ * t = t * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgC, mul_assoc, mul_inv_cancel, mul_one]
      calc x * t = g * (g⁻¹ * x * g) * (g⁻¹ * t) := by group
        _ = g * (g⁻¹ * x * g) * (t * g⁻¹) := by rw [hg']
        _ = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxS]
        _ = (g * t) * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (t * g) * (g⁻¹ * x * g) * g⁻¹ := by rw [hgC]
        _ = t * x := by group
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
  have hTcard : Nat.card ((T : Subgroup H).map H.subtype) = Nat.card T :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hT8 : Nat.card T ∣ 8 := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have h24 : 2 ^ k ∣ 24 := hk ▸ hTcard ▸ (Subgroup.card_dvd_of_le hTC).trans hCH
    have hk3 : k ≤ 3 := by
      by_contra hk
      push Not at hk
      have : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 hk).trans h24
      norm_num at this
    rw [hk]
    exact (pow_dvd_pow 2 hk3).trans (by norm_num)
  have hTeq : P₀.subgroupOf H = T := by
    apply Subgroup.eq_of_le_of_card_ge hT
    rw [hP₀']
    exact Nat.le_of_dvd (by norm_num) hT8
  refine ⟨T, ?_⟩
  rw [← hTeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀H]

theorem centralizer_zpowers_sup_zpowers {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))).symm
  · intro x hx y hy
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    have hle : (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) ≤
        Subgroup.centralizer {x} := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_singleton_iff.mp hxa)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_singleton_iff.mp hxb)).symm
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact this

theorem relIndex_centralizer_eq_two_of_inverts {G : Type*} [Group G] {W L : Subgroup G}
    (hW : Nat.card W = 3) (hL : L ≤ Subgroup.normalizer (W : Set G)) {d : G} (hdL : d ∈ L)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) :
    (Subgroup.centralizer (W : Set G)).relIndex L = 2 ∧
      (∀ h ∈ L, h ∉ Subgroup.centralizer (W : Set G) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      d ∉ Subgroup.centralizer (W : Set G) := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [hbot, Subgroup.card_bot] at hW
    norm_num at hW
  have hw₁3 : w₁ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := W) (x := ⟨w₁, hw₁⟩)
    rw [hW] at h
    exact congrArg Subtype.val h
  have hw₁inv : w₁⁻¹ ≠ w₁ := by
    intro h
    apply hw₁1
    have h2 : w₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel w₁
    calc w₁ = w₁ ^ 3 * (w₁ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw₁3, h2, inv_one, mul_one]
  have hinvK : ∀ h : G, (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) →
      h ∉ Subgroup.centralizer (W : Set G) := by
    intro h hinv hK
    apply hw₁inv
    rw [← hinv w₁ hw₁, (Subgroup.mem_centralizer_iff.mp hK w₁ hw₁).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  have hcentK : ∀ h : G, (∀ w ∈ W, h * w * h⁻¹ = w) → h ∈ Subgroup.centralizer (W : Set G) := by
    intro h hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hc w hw
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hdich := fun b (hb : b ∈ L) =>
    conj_eq_or_inv_of_mem_normalizer_of_card_three hW (hL hb)
  refine ⟨?_, fun h hh hK w hw => ?_, hinvK d hdW⟩
  · rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨d, hdL, fun b hb => ?_⟩
    rcases hdich b hb with hc | hi
    · have hbd : ∀ w ∈ W, b * d * w * (b * d)⁻¹ = w⁻¹ := fun w hw => by
        calc b * d * w * (b * d)⁻¹ = b * (d * w * d⁻¹) * b⁻¹ := by group
          _ = b * w⁻¹ * b⁻¹ := by rw [hdW w hw]
          _ = (b * w * b⁻¹)⁻¹ := by group
          _ = w⁻¹ := by rw [hc w hw]
      exact Or.inr ⟨hcentK b hc, hinvK _ hbd⟩
    · have hbd : ∀ w ∈ W, b * d * w * (b * d)⁻¹ = w := fun w hw => by
        calc b * d * w * (b * d)⁻¹ = b * (d * w * d⁻¹) * b⁻¹ := by group
          _ = b * w⁻¹ * b⁻¹ := by rw [hdW w hw]
          _ = (b * w * b⁻¹)⁻¹ := by group
          _ = w := by rw [hi w hw, inv_inv]
      exact Or.inl ⟨hcentK _ hbd, hinvK b hi⟩
  · rcases hdich h hh with hc | hi
    · exact absurd (hcentK h hc) hK
    · exact hi w hw

theorem three_torus_inversion_normalizer_of_data {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {t s₀ : G} (V : Subgroup G)
    (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (hV : IsKleinFour V) (hs₀2 : orderOf s₀ = 2) (hs₀t : s₀ ≠ t)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set G)) = 240)
    (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 12)
    (W₀ : Subgroup G) (hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G)) (hW₀ : Nat.card W₀ = 3)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (W₀ : Set G))
    (hM : Nat.card (Subgroup.normalizer (V : Set G)) = 72)
    (hCM : Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 24)
    {d : G} (hdC : d ∈ Subgroup.centralizer ({t} : Set G))
    (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hds : d * s₀ * d⁻¹ = t * s₀) (hdW : ∀ w ∈ W₀, d * w * d⁻¹ = w⁻¹) :
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    IsCyclic W ∧ Nat.card W = 3 ∧
      (V ⊔ W = D ∧ Disjoint V W ∧ ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) ∧ Nat.card D = 12 ∧
      Subgroup.centralizer ({t} : Set G) ⊓ K = D ∧
      Subgroup.centralizer ({t} : Set G) ⊓ H = Subgroup.centralizer ({t} : Set G) ⊓ M ∧
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ H : Subgroup G) = 24 ∧
      (∃ d ∈ Subgroup.centralizer ({t} : Set G) ⊓ H, orderOf d = 4 ∧ d ^ 2 = t ∧
        d * s₀ * d⁻¹ = t * s₀ ∧ (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
        Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
        Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      M ≤ H ∧ Nat.card M = 72 ∧ Nat.card (K ⊓ M : Subgroup G) = 36 ∧ K ⊓ D = D := by
  intro D W H K M
  obtain ⟨hWeq, hsup, hdisj, hDK, hchar⟩ := klein_centralizer_twelve_core V W₀ hV hD hW₀D hW₀
  have hW : W = W₀ := hWeq
  have hH : H = Subgroup.normalizer (W₀ : Set G) := by rw [← hW]
  have hK : K = Subgroup.centralizer (W₀ : Set G) := by rw [← hW]
  have hMM : M = Subgroup.normalizer (V : Set G) := rfl
  have hDD : D = Subgroup.centralizer (V : Set G) := rfl
  rw [hH, hK, hMM, hW, hDD]
  clear hH hK hMM hDD hWeq hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htV : t ∈ V := hVdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := hVdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hVD : V ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_left
  have hDC : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  have hsD : s₀ ∈ Subgroup.centralizer (V : Set G) := hVD hsV
  have hKH : Subgroup.centralizer (W₀ : Set G) ≤ Subgroup.normalizer (W₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hsK : s₀ ∈ Subgroup.centralizer (W₀ : Set G) := hDK hsD
  have hW₀C : W₀ ≤ Subgroup.centralizer ({t} : Set G) := hW₀D.trans hDC
  have hW3 : ∀ w ∈ W₀, w ^ 3 = 1 := fun w hw => by
    have h := pow_card_eq_one' (G := W₀) (x := ⟨w, hw⟩)
    rw [hW₀] at h
    exact congrArg Subtype.val h
  have hMH : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W₀ : Set G) := by
    have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀ := by
      intro g hg w hw
      have hgD := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V hg
      apply hchar
      · exact (Subgroup.mem_normalizer_iff.mp hgD w).mp (hW₀D hw)
      · rw [conj_pow, hW3 w hw, mul_one, mul_inv_cancel]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key g hg w, fun hw => ?_⟩
    have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hw
    simpa [mul_assoc] using h
  have hdH : d ∈ Subgroup.normalizer (W₀ : Set G) := hMH hdM
  obtain ⟨hKH2, hinvH, hdK⟩ := relIndex_centralizer_eq_two_of_inverts hW₀ le_rfl hdH hdW
  have hCH : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    inf_normalizer_eq_of_card_three _ _ W₀ hC hW₀C hW₀ inf_le_left
      (inf_le_right.trans hMH) hCM hnot
  have hCHcard : Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.normalizer (W₀ : Set G) : Subgroup G) = 24 := by
    rw [hCH, hCM]
  have hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) =
      Subgroup.centralizer (V : Set G) := by
    have hle : Subgroup.centralizer (V : Set G) ≤
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) := le_inf hDC hDK
    have hle2 : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) ≤
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) :=
      inf_le_inf_left _ hKH
    obtain ⟨k, hk⟩ : 12 ∣ Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer (W₀ : Set G) : Subgroup G) := hD ▸ Subgroup.card_dvd_of_le hle
    have h24 := Subgroup.card_dvd_of_le hle2
    rw [hCHcard, hk] at h24
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 12) (by simpa using h24)
    have hk1 : k = 1 := by
      have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk2
      interval_cases k
      · simp at hk2
      · rfl
      · exfalso
        apply hdK
        have heq := Subgroup.eq_of_le_of_card_ge hle2 (by rw [hCHcard, hk])
        have hmem : d ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) :=
          Subgroup.mem_inf.mpr ⟨hdC, hdH⟩
        rw [← heq] at hmem
        exact (Subgroup.mem_inf.mp hmem).2
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hD, hk, hk1]
  have hs₀sq : s₀ ^ 2 = 1 := by rw [← hs₀2]; exact pow_orderOf_eq_one s₀
  have hs₀inv : s₀⁻¹ = s₀ := by rw [inv_eq_iff_mul_eq_one, ← sq, hs₀sq]
  have hd4' : d ^ 4 = 1 := by rw [← hd4]; exact pow_orderOf_eq_one d
  have hts : s₀ * t = t * s₀ := by
    have h := hDC hsD
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hds' : d * s₀ = t * s₀ * d := by rw [← hds]; group
  have hrel : s₀ * d * s₀⁻¹ = d⁻¹ := by
    calc s₀ * d * s₀⁻¹ = s₀ * (d * s₀) := by rw [hs₀inv, mul_assoc]
      _ = s₀ * (t * s₀ * d) := by rw [hds']
      _ = (s₀ * t) * s₀ * d := by group
      _ = (t * s₀) * s₀ * d := by rw [hts]
      _ = t * (s₀ * s₀) * d := by group
      _ = t * d := by rw [← sq, hs₀sq, mul_one]
      _ = d ^ 2 * d := by rw [hd2]
      _ = d⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← hd4']
        group
  have hnotmem : s₀ ∉ Subgroup.zpowers d := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hd4] at hk
    have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
    obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
        k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
    · rw [h, zpow_zero] at hk
      rw [← hk, orderOf_one] at hs₀2
      norm_num at hs₀2
    · rw [h, zpow_one] at hk
      rw [← hk, hd4] at hs₀2
      norm_num at hs₀2
    · rw [h] at hk
      apply hs₀t
      rw [← hk, ← hd2]
      exact zpow_natCast d 2
    · rw [h] at hk
      have h3 : orderOf (d ^ 3) = 4 := by
        rw [Nat.Coprime.orderOf_pow (by rw [hd4]; norm_num), hd4]
      rw [← hk, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, h3] at hs₀2
      norm_num at hs₀2
  have hdih : Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃*
      DihedralGroup 4) :=
    MatrixFourGroupNormalizer.generatedDihedral_equiv d s₀ hd4 hs₀sq hrel hnotmem
  have hP₀card : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 := by
    obtain ⟨e⟩ := hdih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hP₀H : Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (W₀ : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hdH) (Subgroup.zpowers_le.mpr (hKH hsK))
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_order_four_square S hSC hS4 _ _ hP₀H hP₀card
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) hd4 hd2 (by rw [hCHcard])
  have hVK : V ≤ Subgroup.centralizer (W₀ : Set G) := hVD.trans hDK
  have hV4 : Nat.card V = 4 := hV.card_four
  have hPcard : Nat.card (P : Subgroup (Subgroup.normalizer (W₀ : Set G))) = 8 := by
    rw [← hP₀card, ← hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hHcard := Subgroup.card_mul_index (P : Subgroup (Subgroup.normalizer (W₀ : Set G)))
  rw [hPcard] at hHcard
  have hPodd := P.not_dvd_index
  have hKcard := Subgroup.card_mul_index
    ((Subgroup.centralizer (W₀ : Set G)).subgroupOf (Subgroup.normalizer (W₀ : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hKcard
  have hKH2' : ((Subgroup.centralizer (W₀ : Set G)).subgroupOf
      (Subgroup.normalizer (W₀ : Set G))).index = 2 := hKH2
  rw [hKH2'] at hKcard
  have hVcard := Subgroup.card_mul_index (V.subgroupOf (Subgroup.centralizer (W₀ : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4] at hVcard
  have hVidx : (V.subgroupOf (Subgroup.centralizer (W₀ : Set G))).index =
      (P : Subgroup (Subgroup.normalizer (W₀ : Set G))).index := by
    omega
  have hVp : IsPGroup 2 (V.subgroupOf (Subgroup.centralizer (W₀ : Set G))) :=
    IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4]; norm_num)
  let PV : Sylow 2 (Subgroup.centralizer (W₀ : Set G)) := hVp.toSylow (by rw [hVidx]; exact hPodd)
  have hPV : (PV : Subgroup (Subgroup.centralizer (W₀ : Set G))).map
      (Subgroup.centralizer (W₀ : Set G)).subtype = V := by
    change (V.subgroupOf (Subgroup.centralizer (W₀ : Set G))).map _ = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVK]
  obtain ⟨hKM2, -, -⟩ := relIndex_centralizer_eq_two_of_inverts hW₀ hMH hdM hdW
  have hKMcard : Nat.card (Subgroup.centralizer (W₀ : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 36 := by
    have h := Subgroup.card_mul_index
      ((Subgroup.centralizer (W₀ : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)))
    have hc : Nat.card ((Subgroup.centralizer (W₀ : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G))) = Nat.card (Subgroup.centralizer (W₀ : Set G) ⊓
          Subgroup.normalizer (V : Set G) : Subgroup G) := by
      rw [← Subgroup.inf_subgroupOf_left, inf_comm,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    have hri : ((Subgroup.centralizer (W₀ : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G))).index = 2 := hKM2
    rw [hc, hri, hM] at h
    omega
  refine ⟨isCyclic_of_prime_card hW₀, hW₀, ⟨hsup, hdisj, fun v hv w hw => hW₀D hw v hv⟩, hD,
    hCK, hCH, hCHcard, ⟨d, Subgroup.mem_inf.mpr ⟨hdC, hdH⟩, hd4, hd2, hds, hdW, hdih, hP₀card,
    P, hP⟩, ⟨PV, hPV⟩, hKH2, hinvH, hMH, hM, hKMcard, inf_eq_right.mpr hDK⟩

theorem parameter_five_trivial_core_four_group_data {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (hN : N t = ⊥) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Nat.card (C t) = 240 ∧ Nat.card (ActualFourGroupCentralizer.D s) = 12 ∧
      Nat.card (ActualFourGroupCentralizer.R s) = 3 ∧
      Nat.card (ActualFourGroupNormalizer.K s) = 24 ∧
      (ActualFourGroupCentralizer.D s).map (C t).subtype =
        C t ⊓ Subgroup.centralizer {(s : G)} ∧
      (ActualFourGroupCentralizer.V s).map (C t).subtype =
        Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) ∧
      ∃ d : ActualFourGroupNormalizer.K s, orderOf d = 4 ∧
        d ^ 2 = ActualFourGroupNormalizer.tInK s ∧
        (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
        ∀ x : ActualFourGroupCentralizer.R s,
          (d : C t) * ((x : ActualFourGroupCentralizer.D s) : C t) * (d : C t)⁻¹ =
            ((x : ActualFourGroupCentralizer.D s) : C t)⁻¹ := by
  obtain ⟨⟨-, F, hF, hFfin, A, a, hcard, hAodd, hAf, -, -, -, -, haF, -, -, -, hdata⟩, hnorm⟩ :=
    ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action n hn S fS hG t ht
      hnonab hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel
  obtain ⟨Psi, hz, hu, hcent, -, hDmap, hVmap, -⟩ := hdata s hs hst
  obtain ⟨⟨x, y, hxy⟩, hND⟩ := hnorm F A _ _ s hs hst Psi hz hu hcard hAodd haF
  have hdat := hND x y hxy
  have hNcard : Nat.card (N t) = 1 := by rw [hN, Subgroup.card_bot]
  have hN0 : Nat.card (ActualFourGroupCentralizer.N0 s) = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.card_subgroup_dvd_card _)
  have hN0i : (ActualFourGroupCentralizer.N0 s).index = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.index_dvd_card _)
  have hA1 : Nat.card A = 1 := Nat.eq_one_of_dvd_one hAf
  have hq : Nat.card F = 5 := by rw [hcard, pow_one]
  have hT : MatrixTorus.torusSize (5 ^ 1) = 6 := by decide
  have hT' : MatrixTorus.torusSize (Nat.card F) = 6 := by rw [hq]; decide
  refine ⟨?_, ?_, ?_, ?_, hDmap, hVmap, ?_⟩
  · rw [hcent.C_card, hN0, hN0i, hA1]
    norm_num
  · rw [hcent.D_card, hN0, hA1, hT]
  · rw [hcent.R_card, hN0, hA1, hT]
  · rw [hdat.K_card, hN0, hA1, hT']
  obtain ⟨d, hd4, hd2, hds, -, -, -, -, e, -, -, hinv, -⟩ := hdat.actual_lift_and_action
  refine ⟨d, hd4, hd2, hds, fun r => ?_⟩
  have hN0R : ActualFourGroupCentralizer.N0InR s = ⊥ := by
    have h := hcent.kernel_original
    rw [hN, bot_inf_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (fun a b hab => Subtype.ext (Subtype.ext hab))).mp h
  have hAtriv : ∀ σ : A, σ = 1 := fun σ => by
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    exact Subsingleton.elim _ _
  set q : ActualFourGroupCentralizer.R s ⧸ ActualFourGroupCentralizer.N0InR s :=
    QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r with hq_def
  have heq : e q = SemidirectProduct.inl (e q).left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (e q)]
    rw [hAtriv (e q).right, map_one, mul_one]
  have hconj : ActualFourGroupNormalizer.conjugationOnOddQuotient s d q = q⁻¹ := by
    apply e.injective
    have h := hinv (e q).left
    rw [← heq, MulEquiv.symm_apply_apply] at h
    calc e (ActualFourGroupNormalizer.conjugationOnOddQuotient s d q)
        = SemidirectProduct.inl (e q).left⁻¹ := h
      _ = (SemidirectProduct.inl (e q).left)⁻¹ := map_inv _ _
      _ = (e q)⁻¹ := by rw [← heq]
      _ = e q⁻¹ := (map_inv e q).symm
  have h2 : ActualFourGroupNormalizer.conjugationOnR s d r = r⁻¹ := by
    have h1 : QuotientGroup.mk (s := ActualFourGroupCentralizer.N0InR s)
        (show KleinFourOddKernel.oddKernel s from ActualFourGroupNormalizer.conjugationOnR s d r) =
        QuotientGroup.mk (s := ActualFourGroupCentralizer.N0InR s)
          (show KleinFourOddKernel.oddKernel s from r⁻¹) := hconj
    rw [QuotientGroup.eq, hN0R, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  rw [← ActualFourGroupNormalizer.conjugationOnR_value, h2]
  rfl

end CFSG.Semidihedral.Principal
