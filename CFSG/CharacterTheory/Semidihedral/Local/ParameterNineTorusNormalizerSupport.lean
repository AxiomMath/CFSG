module

public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimpleSupport
public import CFSG.LinearAlgebra.SL2OrderFifteen
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem klein_centralizer_twenty_core {G : Type*} [Group G] [Finite G] (V W₀ : Subgroup G)
    (hV : IsKleinFour V) (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 20)
    (hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G)) (hW₀ : Nat.card W₀ = 5) :
    (CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype = W₀ ∧
      V ⊔ W₀ = Subgroup.centralizer (V : Set G) ∧ Disjoint V W₀ ∧
      Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W₀ : Set G) ∧
      ∀ x ∈ Subgroup.centralizer (V : Set G), x ^ 5 = 1 → x ∈ W₀ := by
  set D := Subgroup.centralizer (V : Set G) with hDdef
  have hV4 : Nat.card V = 4 := hV.card_four
  have hVcomm : ∀ a b : V, a * b = b * a := mul_comm_of_exponent_two hV.exponent_two
  have hVD : V ≤ D := fun x hx y hy => by
    have h := hVcomm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val h
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hW₀comm : ∀ a b : W₀, a * b = b * a := by
    have : IsCyclic W₀ := isCyclic_of_prime_card hW₀
    exact fun a b => (IsCyclic.isMulCommutative (α := W₀)).is_comm.comm a b
  have hsup : V ⊔ W₀ = D := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hVD hW₀D)
    rw [hD]
    have h4 : 4 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hV4 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h5' : 5 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hW₀ ▸ Subgroup.card_dvd_of_le le_sup_right
    have h20 : 20 ∣ Nat.card (V ⊔ W₀ : Subgroup G) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 5) h4 h5'
    exact Nat.le_of_dvd Nat.card_pos h20
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
  have hW₀card : Nat.card (W₀.subgroupOf D) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₀D).toEquiv, hW₀]
  have hle : W₀.subgroupOf D ≤ CFSG.pPrimeCore 2 D :=
    le_sSup ⟨hW₀n, by rw [hW₀card]; norm_num⟩
  have hcore : CFSG.pPrimeCore 2 D = W₀.subgroupOf D := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hW₀card]
    have hdvd : Nat.card (CFSG.pPrimeCore 2 D) ∣ 20 := hD ▸ Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 D)) := CFSG.pPrimeCore_coprime_card
    have hpos : 0 < Nat.card (CFSG.pPrimeCore 2 D) := Nat.card_pos
    have h20 : Nat.card (CFSG.pPrimeCore 2 D) ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (CFSG.pPrimeCore 2 D) <;>
      first | omega | (exfalso; revert hcop; decide)
  have hWeq : (CFSG.pPrimeCore 2 D).map D.subtype = W₀ := by
    rw [hcore, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW₀D]
  refine ⟨hWeq, hsup, ?_, hDW, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hxV hxW
    have h1 : orderOf x ∣ 4 := hV4 ▸ Subgroup.orderOf_dvd_natCard V hxV
    have h2 : orderOf x ∣ 5 := hW₀ ▸ Subgroup.orderOf_dvd_natCard W₀ hxW
    have h3 : orderOf x ∣ Nat.gcd 4 5 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 4 5 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  · intro x hx hx5
    let x' : D := ⟨x, hx⟩
    have hQ : Nat.card (D ⧸ W₀.subgroupOf D) = 4 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (W₀.subgroupOf D)
      rw [hD, hW₀card] at h
      omega
    have hq4 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4 = 1 := by
      rw [← hQ]
      exact pow_card_eq_one'
    have hq5 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : x' ^ 5 = 1 := Subtype.ext (by simpa using hx5)
      rw [this, QuotientGroup.mk_one]
    have hq1 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) = 1 := by
      have : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) =
          (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 5 *
            ((QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4)⁻¹ := by group
      rw [this, hq4, hq5, inv_one, mul_one]
    rw [QuotientGroup.eq_one_iff] at hq1
    exact hq1

theorem exists_generator_of_card_five {G : Type*} [Group G] {W : Subgroup G}
    (hW : Nat.card W = 5) :
    ∃ g ∈ W, orderOf g = 5 ∧ ∀ w ∈ W, ∃ j : ℤ, g ^ j = w := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have : IsCyclic W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  refine ⟨g, g.2, ?_, fun w hw => ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩

theorem conj_eq_of_pow_three_of_card_five {G : Type*} [Group G] {W : Subgroup G}
    (hW : Nat.card W = 5) {y : G} (hy : y ∈ Subgroup.normalizer (W : Set G)) (hy3 : y ^ 3 = 1) :
    ∀ w ∈ W, y * w * y⁻¹ = w := by
  obtain ⟨g, hgW, hg5, hgen⟩ := exists_generator_of_card_five hW
  have hc : y * g * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hy g).mp hgW
  obtain ⟨k, hk⟩ := hgen _ hc
  have hpow : ∀ j : ℕ, y ^ j * g * (y ^ j)⁻¹ = g ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * g * (y ^ (j + 1))⁻¹ = y * (y ^ j * g * (y ^ j)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = y * g ^ (k ^ j) * y⁻¹ := by rw [ih]
        _ = (y * g * y⁻¹) ^ (k ^ j) := by rw [conj_zpow]
        _ = g ^ (k ^ (j + 1)) := by rw [← hk, ← zpow_mul, pow_succ', mul_comm]
  have h3 := hpow 3
  rw [hy3, one_mul, inv_one, mul_one] at h3
  have hdvd : ((orderOf g : ℕ) : ℤ) ∣ k ^ 3 - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, zpow_one, ← h3, mul_inv_cancel]
  rw [hg5] at hdvd
  have hk1 : ((k : ℤ) : ZMod 5) = 1 := by
    have h1 : ((k ^ 3 - 1 : ℤ) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hdvd
    push_cast at h1
    have h2 : ((k : ℤ) : ZMod 5) ^ 3 = 1 := sub_eq_zero.mp h1
    revert h2
    generalize ((k : ℤ) : ZMod 5) = a
    revert a
    decide
  have hgk : g ^ k = g := by
    have h1 : ((5 : ℕ) : ℤ) ∣ k - 1 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 k 5).mp (by rw [hk1]; push_cast; rfl)
      exact this
    rw [← hg5, orderOf_dvd_iff_zpow_eq_one, zpow_sub, zpow_one, mul_inv_eq_one] at h1
    exact h1
  intro w hw
  obtain ⟨j, rfl⟩ := hgen w hw
  rw [← conj_zpow, ← hk, hgk]

theorem inf_normalizer_eq_of_card_five {G : Type*} [Group G] [Finite G] (C X W : Subgroup G)
    (hC : Nat.card C = 1440) (hWC : W ≤ C) (hW : Nat.card W = 5) (hXC : X ≤ C)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hX : Nat.card X = 40)
    (hnot : ¬ C ≤ Subgroup.normalizer (W : Set G)) (h15 : ∀ x ∈ C, orderOf x ≠ 15) :
    C ⊓ Subgroup.normalizer (W : Set G) = X := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hWcard : Nat.card (W.subgroupOf C) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv, hW]
  have hfac : (Nat.card C).factorization 5 = 1 := by
    rw [hC, show (1440 : ℕ) = 5 ^ 1 * 288 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let P : Sylow 5 C := Sylow.ofCard (W.subgroupOf C) (by rw [hWcard, hfac, pow_one])
  have hmod0 := card_sylow_modEq_one 5 C
  rw [Sylow.card_eq_index_normalizer P] at hmod0
  have hmod : (Subgroup.normalizer ((W.subgroupOf C : Subgroup C) : Set C)).index ≡ 1 [MOD 5] :=
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
  obtain ⟨m, hm⟩ : 40 ∣ Nat.card (C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) :=
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
  have hmi : m * ((Subgroup.normalizer (W : Set G)).subgroupOf C).index = 36 := by
    have : 40 * (m * ((Subgroup.normalizer (W : Set G)).subgroupOf C).index) = 40 * 36 := by
      rw [← mul_assoc, hcm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hm36 : m ≤ 36 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmi)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmi)
  unfold Nat.ModEq at hmod
  have hm16 : m = 1 ∨ m = 6 := by
    interval_cases m <;> omega
  rcases hm16 with hm1 | hm6
  · apply (Subgroup.eq_of_le_of_card_ge hXY _).symm
    rw [hm, hX, hm1]
  · exfalso
    have hcard240 : Nat.card (C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) = 240 := by
      rw [hm, hm6]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := (C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G)) 3 (by rw [hcard240]; norm_num)
    have hy' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
    have hy3 : (y : G) ^ 3 = 1 := by
      rw [← hy']
      exact pow_orderOf_eq_one _
    have hyc := conj_eq_of_pow_three_of_card_five hW (Subgroup.mem_inf.mp y.2).2 hy3
    obtain ⟨g, hgW, hg5, -⟩ := exists_generator_of_card_five hW
    have hcomm : Commute (y : G) g := mul_inv_eq_iff_eq_mul.mp (hyc g hgW)
    have hord : orderOf ((y : G) * g) = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy', hg5]; norm_num), hy', hg5]
    exact h15 _ (C.mul_mem (Subgroup.mem_inf.mp y.2).1 (hWC hgW)) hord

theorem exists_sylow_eq_of_order_four_square_of_not_dvd {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {t : G} (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (H P₀ : Subgroup G) (hP₀H : P₀ ≤ H) (hP₀ : Nat.card P₀ = 8) {d : G} (hdP : d ∈ P₀)
    (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hCH : ¬ 2 ^ 4 ∣ Nat.card (Subgroup.centralizer {t} ⊓ H : Subgroup G)) :
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
    have hdvd : 2 ^ k ∣ Nat.card (Subgroup.centralizer {t} ⊓ H : Subgroup G) :=
      hk ▸ hTcard ▸ Subgroup.card_dvd_of_le hTC
    have hk3 : k ≤ 3 := by
      by_contra hk
      exact hCH ((pow_dvd_pow 2 (by omega : 4 ≤ k)).trans hdvd)
    rw [hk]
    exact (pow_dvd_pow 2 hk3).trans (by norm_num)
  have hTeq : P₀.subgroupOf H = T := by
    apply Subgroup.eq_of_le_of_card_ge hT
    rw [hP₀']
    exact Nat.le_of_dvd (by norm_num) hT8
  refine ⟨T, ?_⟩
  rw [← hTeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀H]

theorem relIndex_centralizer_eq_two_of_inverts_card_five {G : Type*} [Group G] {W L : Subgroup G}
    (hW : Nat.card W = 5) (hL : L ≤ Subgroup.normalizer (W : Set G)) {d : G} (hdL : d ∈ L)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹)
    (h4 : ¬ 4 ∣ (Subgroup.centralizer (W : Set G)).relIndex L) :
    (Subgroup.centralizer (W : Set G)).relIndex L = 2 ∧
      (∀ h ∈ L, h ∉ Subgroup.centralizer (W : Set G) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      d ∉ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have : IsCyclic W := isCyclic_of_prime_card hW
  obtain ⟨g, hgW, hg5, -⟩ := exists_generator_of_card_five hW
  have hdK : d ∉ Subgroup.centralizer (W : Set G) := by
    intro hK
    have h1 := hdW g hgW
    rw [← Subgroup.mem_centralizer_iff.mp hK g hgW, mul_inv_cancel_right] at h1
    have h2 : g ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel g
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hg5] at h3
    norm_num at h3
  let φ : L →* MulAut W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hL)
  have hφ : ∀ (x : L) (w : W), ((φ x w : W) : G) = (x : G) * w * (x : G)⁻¹ := fun x w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hker : φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      have h1 := hφ x ⟨w, hw⟩
      rw [h] at h1
      change w = (x : G) * w * (x : G)⁻¹ at h1
      calc w * x = (x : G) * w * (x : G)⁻¹ * x := by rw [← h1]
        _ = x * w := by group
    · intro h
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [hφ, MulAut.one_apply, ← h w w.2, mul_inv_cancel_right]
  have hrel : (Subgroup.centralizer (W : Set G)).relIndex L = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hdvd : Nat.card φ.range ∣ 4 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [IsCyclic.card_mulAut, hW, Nat.totient_prime (by norm_num)] at h
  have hφd : φ ⟨d, hdL⟩ ≠ 1 := by
    intro h
    apply hdK
    have h1 : (⟨d, hdL⟩ : L) ∈ φ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have h2 : Nat.card φ.range = 2 := by
    have hne1 : Nat.card φ.range ≠ 1 := by
      intro h1
      apply hφd
      have h2 := Subgroup.card_eq_one.mp h1
      have h3 : φ ⟨d, hdL⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [h2, Subgroup.mem_bot] at h3
      exact h3
    have h4' : ¬ 4 ∣ Nat.card φ.range := hrel ▸ h4
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hle : Nat.card φ.range ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card φ.range <;> omega
  refine ⟨hrel.trans h2, fun h hh hK w hw => ?_, hdK⟩
  have hφh : φ ⟨h, hh⟩ ≠ 1 := by
    intro h1
    apply hK
    have h3 : (⟨h, hh⟩ : L) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h3
    exact h3
  have heq : φ ⟨h, hh⟩ = φ ⟨d, hdL⟩ :=
    eq_of_card_eq_two h2 ⟨_, rfl⟩ ⟨_, rfl⟩ hφh hφd
  have h1 := hφ ⟨h, hh⟩ ⟨w, hw⟩
  rw [heq, hφ] at h1
  rw [← h1]
  exact hdW w hw

theorem parameter_nine_trivial_core_four_group_data {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 3 2)
    (hN : N t = ⊥) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Nat.card (C t) = 1440 ∧ Nat.card (ActualFourGroupCentralizer.D s) = 20 ∧
      Nat.card (ActualFourGroupCentralizer.R s) = 5 ∧
      Nat.card (ActualFourGroupNormalizer.K s) = 40 ∧
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
      hnonab hcentral hnc 3 2 (by norm_num) (by decide) (by norm_num) hmodel
  obtain ⟨Psi, hz, hu, hcent, -, hDmap, hVmap, -⟩ := hdata s hs hst
  obtain ⟨⟨x, y, hxy⟩, hND⟩ := hnorm F A _ _ s hs hst Psi hz hu hcard hAodd haF
  have hdat := hND x y hxy
  have hNcard : Nat.card (N t) = 1 := by rw [hN, Subgroup.card_bot]
  have hN0 : Nat.card (ActualFourGroupCentralizer.N0 s) = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.card_subgroup_dvd_card _)
  have hN0i : (ActualFourGroupCentralizer.N0 s).index = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.index_dvd_card _)
  have hA1 : Nat.card A = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hAf with h | h
    · exact h
    · rw [h] at hAodd
      exact absurd hAodd (by decide)
  have hq : Nat.card F = 9 := by rw [hcard]; norm_num
  have hT : MatrixTorus.torusSize (3 ^ 2) = 10 := by decide
  have hT' : MatrixTorus.torusSize (Nat.card F) = 10 := by rw [hq]; decide
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

theorem no_order_fifteen_of_parameter_nine
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 3 2)
    (hN : N t = ⊥) (hC : Nat.card (C t) = 1440) (x : C t) : orderOf x ≠ 15 := by
  intro hx
  have hpackage := actual_simple_layer_matrix_data n hn S0 f0 hG t ht hnonab hcentral hnc 3 2
    (by norm_num) (by decide) (by norm_num) hmodel
  obtain ⟨F, hF, hFfin, A, rho, data⟩ := hpackage
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hF9 : Nat.card F = 9 := by rw [data.field_card]; norm_num
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF9]; norm_num)
  have hT₀ : Nat.card ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) = 720 := by
    rw [Nat.card_congr eta.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF9]
    norm_num
  have hH : Nat.card (H t) = 1440 := by
    change Nat.card (C t ⧸ N t) = 1440
    rw [← Subgroup.index_eq_card, hN, Subgroup.index_bot, hC]
  have hidx : ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).index = 2 := by
    have h := Subgroup.card_mul_index ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    rw [hT₀, hH] at h
    omega
  have hnu : Function.Injective (nu t) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  have hord : orderOf (nu t x) = 15 := by rw [orderOf_injective _ hnu, hx]
  have hmem : nu t x ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    have h2 := Subgroup.sq_mem_of_index_two hidx (nu t x)
    have h16 : (nu t x ^ 2) ^ 8 = nu t x := by
      rw [← pow_mul, show 2 * 8 = 15 + 1 by norm_num, pow_succ, ← hord, pow_orderOf_eq_one,
        one_mul]
    rw [← h16]
    exact Subgroup.pow_mem _ h2 8
  have h15 : orderOf (eta ⟨nu t x, hmem⟩) = 15 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]
  exact CFSG.LinearAlgebra.orderOf_ne_fifteen_of_charP_three _ h15

theorem five_torus_inversion_normalizer_of_data {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {t s₀ : G} (V : Subgroup G)
    (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (hV : IsKleinFour V) (hs₀2 : orderOf s₀ = 2) (hs₀t : s₀ ≠ t)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set G)) = 1440)
    (h15 : ∀ x ∈ Subgroup.centralizer ({t} : Set G), orderOf x ≠ 15)
    (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 20)
    (W₀ : Subgroup G) (hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G)) (hW₀ : Nat.card W₀ = 5)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (W₀ : Set G))
    (hM : Nat.card (Subgroup.normalizer (V : Set G)) = 120)
    (hCM : Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 40)
    {d : G} (hdC : d ∈ Subgroup.centralizer ({t} : Set G))
    (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hds : d * s₀ * d⁻¹ = t * s₀) (hdW : ∀ w ∈ W₀, d * w * d⁻¹ = w⁻¹) :
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    IsCyclic W ∧ Nat.card W = 5 ∧
      (V ⊔ W = D ∧ Disjoint V W ∧ ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) ∧ Nat.card D = 20 ∧
      Subgroup.centralizer ({t} : Set G) ⊓ K = D ∧
      Subgroup.centralizer ({t} : Set G) ⊓ H = Subgroup.centralizer ({t} : Set G) ⊓ M ∧
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ H : Subgroup G) = 40 ∧
      (∃ d ∈ Subgroup.centralizer ({t} : Set G) ⊓ H, orderOf d = 4 ∧ d ^ 2 = t ∧
        d * s₀ * d⁻¹ = t * s₀ ∧ (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
        Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
        Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      M ≤ H ∧ Nat.card M = 120 ∧ Nat.card (K ⊓ M : Subgroup G) = 60 ∧ K ⊓ D = D ∧
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K ∧
        Subgroup.normalizer (Subgroup.zpowers w : Set G) = H) ∧
      (∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ ≠ 1 → w₂ ≠ 1 → (IsConj w₁ w₂ ↔ w₂ = w₁ ∨ w₂ = w₁⁻¹)) ∧
      Set.ncard {c : ConjClasses G | ∃ w ∈ W, w ≠ 1 ∧ ConjClasses.mk w = c} = 2 := by
  intro D W H K M
  obtain ⟨hWeq, hsup, hdisj, hDK, hchar⟩ := klein_centralizer_twenty_core V W₀ hV hD hW₀D hW₀
  have hW : W = W₀ := hWeq
  have hH : H = Subgroup.normalizer (W₀ : Set G) := by rw [← hW]
  have hK : K = Subgroup.centralizer (W₀ : Set G) := by rw [← hW]
  have hMM : M = Subgroup.normalizer (V : Set G) := rfl
  have hDD : D = Subgroup.centralizer (V : Set G) := rfl
  rw [hH, hK, hMM, hW, hDD]
  clear hH hK hMM hDD hWeq hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
  have hW5 : ∀ w ∈ W₀, w ^ 5 = 1 := fun w hw => by
    have h := pow_card_eq_one' (G := W₀) (x := ⟨w, hw⟩)
    rw [hW₀] at h
    exact congrArg Subtype.val h
  obtain ⟨g, hgW, hg5, hgen⟩ := exists_generator_of_card_five hW₀
  have hdK : d ∉ Subgroup.centralizer (W₀ : Set G) := by
    intro hK
    have h1 := hdW g hgW
    rw [← Subgroup.mem_centralizer_iff.mp hK g hgW, mul_inv_cancel_right] at h1
    have h2 : g ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel g
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hg5] at h3
    norm_num at h3
  have hMH : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W₀ : Set G) := by
    have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀ := by
      intro g hg w hw
      have hgD := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V hg
      apply hchar
      · exact (Subgroup.mem_normalizer_iff.mp hgD w).mp (hW₀D hw)
      · rw [conj_pow, hW5 w hw, mul_one, mul_inv_cancel]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key g hg w, fun hw => ?_⟩
    have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hw
    simpa [mul_assoc] using h
  have hdH : d ∈ Subgroup.normalizer (W₀ : Set G) := hMH hdM
  have hCH : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    inf_normalizer_eq_of_card_five _ _ W₀ hC hW₀C hW₀ inf_le_left
      (inf_le_right.trans hMH) hCM hnot h15
  have hCHcard : Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.normalizer (W₀ : Set G) : Subgroup G) = 40 := by
    rw [hCH, hCM]
  have hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) =
      Subgroup.centralizer (V : Set G) := by
    have hle : Subgroup.centralizer (V : Set G) ≤
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) := le_inf hDC hDK
    have hle2 : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W₀ : Set G) ≤
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) :=
      inf_le_inf_left _ hKH
    obtain ⟨k, hk⟩ : 20 ∣ Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer (W₀ : Set G) : Subgroup G) := hD ▸ Subgroup.card_dvd_of_le hle
    have h40 := Subgroup.card_dvd_of_le hle2
    rw [hCHcard, hk] at h40
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20) (by simpa using h40)
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
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_order_four_square_of_not_dvd S hSC hS4 _ _ hP₀H hP₀card
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) hd4 hd2 (by rw [hCHcard]; norm_num)
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
  have hK4 : 4 ∣ Nat.card (Subgroup.centralizer (W₀ : Set G)) :=
    hV4 ▸ Subgroup.card_dvd_of_le hVK
  have hnot4 : ¬ 4 ∣ (Subgroup.centralizer (W₀ : Set G)).relIndex
      (Subgroup.normalizer (W₀ : Set G)) := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hK4
    have hb' : ((Subgroup.centralizer (W₀ : Set G)).subgroupOf
        (Subgroup.normalizer (W₀ : Set G))).index = 4 * b := hb
    rw [ha, hb', ← hHcard] at hKcard
    apply hPodd
    refine ⟨a * b, ?_⟩
    have h1 : 8 * (2 * (a * b)) = 8 * (P : Subgroup (Subgroup.normalizer (W₀ : Set G))).index := by
      rw [← hKcard]
      ring
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm
  obtain ⟨hKH2, hinvH, -⟩ :=
    relIndex_centralizer_eq_two_of_inverts_card_five hW₀ le_rfl hdH hdW hnot4
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
  have hDM : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W₀ : Set G) ⊓
      Subgroup.normalizer (V : Set G) := le_inf hDK (Subgroup.centralizer_le_normalizer _)
  have hKMmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (W₀ : Set G))
    (Subgroup.normalizer (V : Set G))
  rw [hM] at hKMmul
  have hnot4M : ¬ 4 ∣ (Subgroup.centralizer (W₀ : Set G)).relIndex
      (Subgroup.normalizer (V : Set G)) := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ : 20 ∣ Nat.card (Subgroup.centralizer (W₀ : Set G) ⊓
        Subgroup.normalizer (V : Set G) : Subgroup G) := hD ▸ Subgroup.card_dvd_of_le hDM
    rw [hb, ha] at hKMmul
    have h1 : 80 * (b * a) = 120 := by rw [← hKMmul]; ring
    omega
  obtain ⟨hKM2, -, -⟩ :=
    relIndex_centralizer_eq_two_of_inverts_card_five hW₀ hMH hdM hdW hnot4M
  have hKMcard : Nat.card (Subgroup.centralizer (W₀ : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 60 := by
    rw [hKM2] at hKMmul
    omega
  have hgen' : ∀ w ∈ W₀, w ≠ 1 → Subgroup.zpowers w = W₀ := by
    intro w hw hw1
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
    rw [hW₀, Nat.card_zpowers]
    have h1 : orderOf w ∣ 5 := hW₀ ▸ Subgroup.orderOf_dvd_natCard W₀ hw
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · rw [h]
  have hcentw : ∀ w ∈ W₀, w ≠ 1 → Subgroup.centralizer {w} =
      Subgroup.centralizer (W₀ : Set G) := by
    intro w hw hw1
    rw [← hgen' w hw hw1]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left hx.symm j)).eq
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx w (Subgroup.mem_zpowers w)).symm
  have hconj : ∀ w₁ ∈ W₀, ∀ w₂ ∈ W₀, w₁ ≠ 1 → w₂ ≠ 1 →
      (IsConj w₁ w₂ ↔ w₂ = w₁ ∨ w₂ = w₁⁻¹) := by
    intro w₁ hw₁ w₂ hw₂ hw₁1 hw₂1
    constructor
    · intro hc
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      have hcH : c ∈ Subgroup.normalizer (W₀ : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          rw [← hgen' w₁ hw₁ hw₁1] at hh
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          rw [← conj_zpow, hc]
          exact Subgroup.zpow_mem _ hw₂ j
        · intro hh
          rw [← hgen' w₂ hw₂ hw₂1] at hh
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hh
          have h1 : h = w₁ ^ j := by
            have h2 : c * h * c⁻¹ = c * w₁ ^ j * c⁻¹ := by rw [← hj, ← hc, conj_zpow]
            simpa using h2
          rw [h1]
          exact Subgroup.zpow_mem _ hw₁ j
      by_cases hcK : c ∈ Subgroup.centralizer (W₀ : Set G)
      · left
        rw [← hc, ← Subgroup.mem_centralizer_iff.mp hcK w₁ hw₁, mul_inv_cancel_right]
      · right
        rw [← hc]
        exact hinvH c hcH hcK w₁ hw₁
    · rintro (h | h)
      · rw [h]
      · rw [h]
        exact isConj_iff.mpr ⟨d, hdW w₁ hw₁⟩
  have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg5; norm_num at hg5
  have hg2W : g ^ 2 ∈ W₀ := Subgroup.pow_mem _ hgW 2
  have hg21 : g ^ 2 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hg5] at h1
    norm_num at h1
  have hg3 : g ^ 3 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hg5] at h1
    norm_num at h1
  have hg4 : g ^ 4 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hg5] at h1
    norm_num at h1
  have hg5' : g ^ 5 = 1 := by
    rw [← hg5]
    exact pow_orderOf_eq_one g
  have hclasses : {c : ConjClasses G | ∃ w ∈ W₀, w ≠ 1 ∧ ConjClasses.mk w = c} =
      {ConjClasses.mk g, ConjClasses.mk (g ^ 2)} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, hw1, rfl⟩
      obtain ⟨j, rfl⟩ := hgen w hw
      have hj : g ^ j = g ^ (j % 5).toNat := by
        rw [← zpow_natCast, ← zpow_mod_orderOf, hg5]
        congr 1
        omega
      have hr : (j % 5).toNat < 5 := by omega
      rw [hj] at hw1 ⊢
      interval_cases hr' : (j % 5).toNat
      · exact absurd (pow_zero g) hw1
      · left
        rw [pow_one]
      · right
        rfl
      · right
        rw [ConjClasses.mk_eq_mk_iff_isConj]
        refine (hconj _ (Subgroup.pow_mem _ hgW 3) _ hg2W hg3 hg21).mpr (Or.inr ?_)
        rw [eq_inv_iff_mul_eq_one, ← pow_add]
        exact hg5'
      · left
        rw [ConjClasses.mk_eq_mk_iff_isConj]
        refine (hconj _ (Subgroup.pow_mem _ hgW 4) _ hgW hg4 hg1).mpr (Or.inr ?_)
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hg5'
    · rintro (rfl | rfl)
      · exact ⟨g, hgW, hg1, rfl⟩
      · exact ⟨g ^ 2, hg2W, hg21, rfl⟩
  have hne : ConjClasses.mk g ≠ ConjClasses.mk (g ^ 2) := by
    rw [Ne, ConjClasses.mk_eq_mk_iff_isConj, hconj g hgW (g ^ 2) hg2W hg1 hg21]
    rintro (h | h)
    · apply hg1
      have h1 : g * g = g * 1 := by rw [← sq, h, mul_one]
      exact mul_left_cancel h1
    · have h1 : g ^ 3 = 1 := by
        rw [pow_succ, h, inv_mul_cancel]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hg5] at h2
      norm_num at h2
  refine ⟨isCyclic_of_prime_card hW₀, hW₀, ⟨hsup, hdisj, fun v hv w hw => hW₀D hw v hv⟩, hD,
    hCK, hCH, hCHcard, ⟨d, Subgroup.mem_inf.mpr ⟨hdC, hdH⟩, hd4, hd2, hds, hdW, hdih, hP₀card,
    P, hP⟩, ⟨PV, hPV⟩, hKH2, hinvH, hMH, hM, hKMcard, inf_eq_right.mpr hDK,
    fun w hw hw1 => ⟨hcentw w hw hw1, by rw [hgen' w hw hw1]⟩, hconj, ?_⟩
  rw [hclasses]
  exact Set.ncard_pair hne

end CFSG.Semidihedral.Local
