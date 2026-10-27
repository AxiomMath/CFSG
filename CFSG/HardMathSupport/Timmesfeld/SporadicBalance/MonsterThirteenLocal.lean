module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Core
public import Certificates.Certificate16957

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem card_inf_centralizer_conj {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (g a : H) :
    Nat.card (K ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set H) : Subgroup H) =
      Nat.card (K ⊓ Subgroup.centralizer ({a} : Set H) : Subgroup H) := by
  refine Nat.card_congr ((MulAut.conj g⁻¹).toEquiv.subtypeEquiv fun y => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hK, hc⟩
    refine ⟨by simpa using (inferInstance : K.Normal).conj_mem _ hK g⁻¹, ?_⟩
    calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hc]
      _ = a * (g⁻¹ * y * g) := by group
  · rintro ⟨hK, hc⟩
    refine ⟨?_, ?_⟩
    · have := (inferInstance : K.Normal).conj_mem _ hK g
      simpa [mul_assoc] using this
    · calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g * a * g⁻¹ * y := by group

theorem card_inf_centralizer_conj₂ {G : Type*} [Group G] (h u f : G) :
    Nat.card (Subgroup.centralizer ({h * u * h⁻¹} : Set G) ⊓
      Subgroup.centralizer ({h * f * h⁻¹} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({f} : Set G) :
        Subgroup G) := by
  refine Nat.card_congr ((MulAut.conj h⁻¹).toEquiv.subtypeEquiv fun y => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have key : ∀ a : G, y * (h * a * h⁻¹) = h * a * h⁻¹ * y ↔ h⁻¹ * y * h * a = a * (h⁻¹ * y * h) := by
    intro a
    constructor
    · intro hc
      calc h⁻¹ * y * h * a = h⁻¹ * (y * (h * a * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * a * h⁻¹) * y) * h := by rw [hc]
        _ = a * (h⁻¹ * y * h) := by group
    · intro hc
      calc y * (h * a * h⁻¹) = h * ((h⁻¹ * y * h) * a) * h⁻¹ := by group
        _ = h * (a * (h⁻¹ * y * h)) * h⁻¹ := by rw [hc]
        _ = h * a * h⁻¹ * y := by group
  rw [key u, key f]

theorem orderOf_image_prime {H Q : Type*} [Group H] [Group Q] {K : Subgroup H} [K.Normal]
    (hK : IsPGroup 2 K) (e : H ⧸ K ≃* Q) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : H}
    (hx : orderOf x = p) : orderOf (e (QuotientGroup.mk x)) = p := by
  rw [MulEquiv.orderOf_eq]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · have hmem : x ∈ K := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨n, hn⟩ := hK ⟨x, hmem⟩
    have h2 : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
      (hp.out.dvd_of_dvd_pow h3))

theorem card_centralizer_dvd_two_mul {H Q : Type*} [Group H] [Group Q] [Finite H]
    (K : Subgroup H) [K.Normal] (hK : IsPGroup 2 K) (e : H ⧸ K ≃* Q) (x : H)
    (hKC : Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) ≤ 2) {m : ℕ}
    (hQ : Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q)) = m) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) ∣ 2 * m := by
  rw [card_centralizer_eq_mul K e x]
  refine Nat.mul_dvd_mul ?_ ?_
  · obtain ⟨a, ha⟩ := (hK.to_le (inf_le_left :
      K ⊓ Subgroup.centralizer ({x} : Set H) ≤ K)).exists_card_eq
    rw [ha] at hKC ⊢
    have ha1 : a ≤ 1 := by
      by_contra hc
      push_neg at hc
      have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases a <;> norm_num
  · rw [← hQ]
    exact Subgroup.card_dvd_of_le (range_centMap_le K e x)

theorem not_three_normalized_of {H Q : Type*} [Group H] [Group Q] [Finite H]
    (K : Subgroup H) [K.Normal] (hK : IsPGroup 2 K) (e : H ⧸ K ≃* Q) {x : H}
    (hN : NoEvenNormalizer (e (QuotientGroup.mk x)))
    (hKC : Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) ≤ 2)
    {Y : Subgroup H} (hYC : Y ≤ Subgroup.centralizer ({x} : Set H)) (hY3 : Nat.card Y = 3) {w : H}
    (hw : w ∈ Subgroup.centralizer ({x} : Set H)) (hwY : ∀ y ∈ Y, w * y * w⁻¹ ∈ Y)
    (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card Y by rw [hY3])
  have hy3 : orderOf (y : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hYz : Y = Subgroup.zpowers (y : H) := by
    have hle : Subgroup.zpowers (y : H) ≤ Y := (Subgroup.zpowers_le).2 y.2
    refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [hY3, Nat.card_zpowers, hy3]
  have hψy := orderOf_image_prime hK e (by norm_num : 3 ≠ 2) hy3
  have hcomm : ∀ a ∈ Subgroup.centralizer ({x} : Set H),
      e (QuotientGroup.mk a) ∈ Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ha]
  have hwy : w * (y : H) * w⁻¹ ∈ Subgroup.zpowers (y : H) := by
    rw [← hYz]; exact hwY _ y.2
  have himg : e (QuotientGroup.mk w) * e (QuotientGroup.mk (y : H)) *
      (e (QuotientGroup.mk w))⁻¹ ∈ Subgroup.zpowers (e (QuotientGroup.mk (y : H))) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwy
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, ← QuotientGroup.mk_zpow, hk, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
  have h39 := hN _ (hcomm w hw) _ (hcomm _ (hYC y.2)) hψy himg
  have hw39 : w ^ 39 ∈ K := by
    rw [← map_pow, ← QuotientGroup.mk_pow, MulEquiv.map_eq_one_iff] at h39
    exact (QuotientGroup.eq_one_iff _).1 h39
  have hwinv : w ^ 39 = w⁻¹ := by
    have h3 : w ^ 3 * w = 1 := by rw [← pow_succ]; exact hw4
    rw [show (39 : ℕ) = 4 * 9 + 3 by norm_num, pow_add, pow_mul, hw4, one_pow, one_mul]
    exact eq_inv_of_mul_eq_one_left h3
  rw [hwinv] at hw39
  have hwK : w ∈ K ⊓ Subgroup.centralizer ({x} : Set H) :=
    Subgroup.mem_inf.2 ⟨by simpa using K.inv_mem hw39, hw⟩
  have hdvd : orderOf w ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set H)) :=
    Subgroup.orderOf_dvd_natCard _ hwK
  have hpos : 0 < Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set H)) := Nat.card_pos
  have h2 : orderOf w ∣ 2 := by
    have hc : Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set H)) = 1 ∨
        Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set H)) = 2 := by omega
    rcases hc with hc | hc
    · rw [hc] at hdvd; exact hdvd.trans (by norm_num)
    · rw [hc] at hdvd; exact hdvd
  exact hw2 (orderOf_dvd_iff_pow_eq_one.1 h2)

theorem orderOf_image_co1
    (e : cent xGmat ⧸ pCore 2 (cent xGmat) ≃* CFSG.Blueprint.NativeSporadic.Co1)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : cent xGmat} (hx : orderOf x = p) :
    orderOf (e (QuotientGroup.mk x)) = p := by
  rw [MulEquiv.orderOf_eq]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · have hmem : x ∈ pCore 2 (cent xGmat) := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := cent xGmat)) ⟨x, hmem⟩
    have h2 : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
      (hp.out.dvd_of_dvd_pow h3))

theorem twoB_xGmat₁₃ : IsTwoBCentralizer xGmat := isTwoBCentralizer_Gmat xGmat (IsConj.refl _)

theorem finite_cent_xGmat : Finite (cent xGmat) :=
  Nat.finite_of_card_ne_zero (by rw [twoB_xGmat₁₃.2.2.2.2.1]; simp [twoBCentralizerOrder])

theorem factorization_cent_xGmat_thirteen : (Nat.card (cent xGmat)).factorization 13 = 1 := by
  rw [twoB_xGmat₁₃.2.2.2.2.1, twoBCentralizerOrder,
    show (2 ^ 46 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23 : ℕ) = 13 * 10731679932795102167040000 by
      norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]


theorem c_mem_cent : gw genD13W1 ∈ cent xGmat := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← rhoG_z_eq_xGmat]
  exact thirteen_b_facts.1.symm

@[expose] noncomputable def c13H : cent xGmat := ⟨gw genD13W1, c_mem_cent⟩


theorem orderOf_c13 : orderOf (gw genD13W1) = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime d13_gw_facts.2.2.1 d13_gw_facts.2.2.2.2.2.2.1

theorem orderOf_c13H : orderOf c13H = 13 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_c13


theorem card_pCore_inf_centralizer_c_le :
    Nat.card ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({c13H} : Set (cent xGmat))) ≤ 2 := by
  have h := Certificates.certificate16957
  refine le_trans (Nat.card_le_card_of_injective
    (fun y => (⟨(y : cent xGmat), Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩ :
      ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer ({gw genD13W1} : Set Gmat)))) ?_) h
  · exact Subgroup.mem_subgroupOf.2 ((mem_pCore_cent_xGmat_iff _).1 (Subgroup.mem_inf.1 y.2).1)
  · have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  · intro y y' hyy
    have := congrArg Subtype.val hyy
    simp only at this
    exact Subtype.ext (Subtype.ext this)

theorem card_pCore_inf_centralizer_le_two {x : cent xGmat} (hx : orderOf x = 13) :
    Nat.card ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x} : Set (cent xGmat))) ≤ 2 := by
  have : Finite (cent xGmat) := finite_cent_xGmat
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one factorization_cent_xGmat_thirteen
    orderOf_c13H hx
  have hk1 : c13H ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    norm_num at hx
  rw [hxk, card_inf_centralizer_conj, centralizer_pow_eq_of_prime orderOf_c13H hk1]
  exact card_pCore_inf_centralizer_c_le


theorem card_centralizer_cent_xGmat_dvd {x : cent xGmat} (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set (cent xGmat))) ∣ 312 := by
  have : Finite (cent xGmat) := finite_cent_xGmat
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨e⟩ := twoB_xGmat₁₃.2.2.2.1
  have h156 := (co1_thirteen_facts _ (orderOf_image_co1 e (by norm_num : 13 ≠ 2) hx)).1
  exact @card_centralizer_dvd_two_mul (cent xGmat) CFSG.Blueprint.NativeSporadic.Co1 _
    Units.instGroup _ (pCore 2 (cent xGmat)) _ pCore_isPGroup e x
    (card_pCore_inf_centralizer_le_two hx) 156 h156

theorem not_three_normalized {x : cent xGmat} (hx : orderOf x = 13)
    {Y : Subgroup (cent xGmat)} (hYC : Y ≤ Subgroup.centralizer ({x} : Set (cent xGmat)))
    (hY3 : Nat.card Y = 3) {w : cent xGmat}
    (hw : w ∈ Subgroup.centralizer ({x} : Set (cent xGmat)))
    (hwY : ∀ y ∈ Y, w * y * w⁻¹ ∈ Y) (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) : False := by
  have : Finite (cent xGmat) := finite_cent_xGmat
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨e⟩ := twoB_xGmat₁₃.2.2.2.1
  have hN := (co1_thirteen_facts _ (orderOf_image_co1 e (by norm_num : 13 ≠ 2) hx)).2
  exact @not_three_normalized_of (cent xGmat) CFSG.Blueprint.NativeSporadic.Co1 _ Units.instGroup _
    (pCore 2 (cent xGmat)) _ pCore_isPGroup e x hN (card_pCore_inf_centralizer_le_two hx) Y hYC
    hY3 w hw hwY hw4 hw2

theorem card_cent_inf_eq {f : Gmat} (hf : f ∈ cent xGmat) :
    Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓ Subgroup.centralizer ({f} : Set Gmat) :
      Subgroup Gmat) =
      Nat.card (Subgroup.centralizer ({(⟨f, hf⟩ : cent xGmat)} : Set (cent xGmat))) :=
  Nat.card_congr
    { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
      invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨y.1.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }

theorem card_inf_centralizer_dvd {u h f : Gmat} (hh : h * u * h⁻¹ = xGmat) (hfu : f * u = u * f)
    (hfo : orderOf f = 13) :
    Nat.card (Subgroup.centralizer ({u} : Set Gmat) ⊓ Subgroup.centralizer ({f} : Set Gmat) :
      Subgroup Gmat) ∣ 312 := by
  have hf' : h * f * h⁻¹ ∈ cent xGmat := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
    calc h * f * h⁻¹ * (h * u * h⁻¹) = h * (f * u) * h⁻¹ := by group
      _ = h * (u * f) * h⁻¹ := by rw [hfu]
      _ = h * u * h⁻¹ * (h * f * h⁻¹) := by group
  have ho : orderOf (⟨h * f * h⁻¹, hf'⟩ : cent xGmat) = 13 := by
    rw [Subgroup.orderOf_mk, show h * f * h⁻¹ = (MulAut.conj h) f by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq, hfo]
  rw [← card_inf_centralizer_conj₂ h u f, hh, card_cent_inf_eq hf']
  exact card_centralizer_cent_xGmat_dvd ho

theorem inf_centralizer_eq_bot_of_twoB {u h f w : Gmat} (hh : h * u * h⁻¹ = xGmat)
    (hfu : f * u = u * f) (hfo : orderOf f = 13) {N : Subgroup Gmat}
    (hNf : N ≤ Subgroup.centralizer ({f} : Set Gmat)) (hodd : Odd (Nat.card N))
    (h13 : ¬ 13 ∣ Nat.card N) (hwu : w * u = u * w) (hwf : w * f = f * w)
    (hwN : ∀ n ∈ N, w * n * w⁻¹ ∈ N) (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) :
    N ⊓ Subgroup.centralizer ({u} : Set Gmat) = ⊥ := by
  set Y := N ⊓ Subgroup.centralizer ({u} : Set Gmat) with hYdef
  have hYD : Y ≤ Subgroup.centralizer ({u} : Set Gmat) ⊓ Subgroup.centralizer ({f} : Set Gmat) :=
    fun y hy => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, hNf (Subgroup.mem_inf.1 hy).1⟩
  have hdvd : Nat.card Y ∣ 312 :=
    (Subgroup.card_dvd_of_le hYD).trans (card_inf_centralizer_dvd hh hfu hfo)
  have hYN : Nat.card Y ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
  have hY3 : Nat.card Y ∣ 3 := by
    have hcop2 : Nat.Coprime (Nat.card Y) (2 ^ 3) := by
      refine Nat.Coprime.pow_right 3 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
        Nat.prime_two).2 fun h2 => ?_))
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hYN))
    have hcop13 : Nat.Coprime (Nat.card Y) 13 :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h => h13 (h.trans hYN))
    rw [show (312 : ℕ) = 2 ^ 3 * (3 * 13) by norm_num] at hdvd
    exact hcop13.dvd_of_dvd_mul_right (hcop2.dvd_of_dvd_mul_left hdvd)
  rcases (Nat.dvd_prime (by norm_num)).1 hY3 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq Y h1
  exfalso
  have hf' : h * f * h⁻¹ ∈ cent xGmat := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
    calc h * f * h⁻¹ * (h * u * h⁻¹) = h * (f * u) * h⁻¹ := by group
      _ = h * (u * f) * h⁻¹ := by rw [hfu]
      _ = h * u * h⁻¹ * (h * f * h⁻¹) := by group
  have hconjC : ∀ a : Gmat, a * u = u * a → h * a * h⁻¹ ∈ cent xGmat := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
    calc h * a * h⁻¹ * (h * u * h⁻¹) = h * (a * u) * h⁻¹ := by group
      _ = h * (u * a) * h⁻¹ := by rw [ha]
      _ = h * u * h⁻¹ * (h * a * h⁻¹) := by group
  have hconjF : ∀ a : Gmat, a * f = f * a →
      (h * a * h⁻¹) * (h * f * h⁻¹) = (h * f * h⁻¹) * (h * a * h⁻¹) := by
    intro a ha
    calc (h * a * h⁻¹) * (h * f * h⁻¹) = h * (a * f) * h⁻¹ := by group
      _ = h * (f * a) * h⁻¹ := by rw [ha]
      _ = (h * f * h⁻¹) * (h * a * h⁻¹) := by group
  set x' : cent xGmat := ⟨h * f * h⁻¹, hf'⟩ with hx'
  have ho : orderOf x' = 13 := by
    rw [hx', Subgroup.orderOf_mk, show h * f * h⁻¹ = (MulAut.conj h) f by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq, hfo]
  let Y' : Subgroup (cent xGmat) :=
    (Y.map (MulAut.conj h).toMonoidHom).subgroupOf (cent xGmat)
  have hYmem : ∀ y : cent xGmat, y ∈ Y' ↔ ∃ a ∈ Y, h * a * h⁻¹ = (y : Gmat) := by
    intro y
    simp only [Y', Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  have hYle : Y.map (MulAut.conj h).toMonoidHom ≤ cent xGmat := by
    rintro _ ⟨a, ha, rfl⟩
    exact hconjC a (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2)
  have hY'3 : Nat.card Y' = 3 := by
    rw [show Nat.card Y' = Nat.card (Y.map (MulAut.conj h).toMonoidHom) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj h).injective, h3]
  refine not_three_normalized ho (Y := Y') (w := ⟨h * w * h⁻¹, hconjC w hwu⟩) ?_ hY'3 ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨a, ha, hay⟩ := (hYmem y).1 hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    rw [← hay]
    exact hconjF a (Subgroup.mem_centralizer_singleton_iff.1 (hNf (Subgroup.mem_inf.1 ha).1))
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hconjF w hwf)
  · intro y hy
    obtain ⟨a, ha, hay⟩ := (hYmem y).1 hy
    refine (hYmem _).2 ⟨w * a * w⁻¹, Subgroup.mem_inf.2 ⟨hwN a (Subgroup.mem_inf.1 ha).1, ?_⟩, ?_⟩
    · have hau : Commute a u := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
      have hwu' : Commute w u := hwu
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hwu'.mul_left hau).mul_left hwu'.inv_left).eq
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      rw [← hay]
      group
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk]
    rw [show (h * w * h⁻¹) ^ 4 = (MulAut.conj h) (w ^ 4) by simp [MulAut.conj_apply], hw4, map_one]
  · intro h2
    apply hw2
    have := congrArg Subtype.val h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk] at this
    rw [show (h * w * h⁻¹) ^ 2 = (MulAut.conj h) (w ^ 2) by simp [MulAut.conj_apply]] at this
    exact (MulEquiv.map_eq_one_iff _).1 this

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
