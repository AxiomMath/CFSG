module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Eleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenFusion
public import Certificates.Certificate16953
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem rhoG_z_eq_xGmat : rhoG (true, 0, 0) = xGmat := by
  apply Subtype.ext
  rw [coe_rhoG]
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  rw [h]
  rfl

@[expose] noncomputable def centVisEquiv : cent xGmat ≃* Gvis :=
  ((cent xGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_xGmat)

theorem coe_centVisEquiv (y : cent xGmat) :
    ((centVisEquiv y : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = ((y : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) := rfl


theorem mem_pCore_cent_xGmat_iff (y : cent xGmat) :
    y ∈ pCore 2 (cent xGmat) ↔ ((y : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ := by
  have hmap : (pCore 2 (cent xGmat)).map centVisEquiv.toMonoidHom = rhoQvis := by
    rw [pCore_map_iso 2 centVisEquiv, pCore_Gvis]
  constructor
  · intro hy
    have h1 : centVisEquiv y ∈ rhoQvis := hmap ▸ ⟨y, hy, rfl⟩
    rw [← coe_centVisEquiv]
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hy
    have h1 : centVisEquiv y ∈ rhoQvis := Subgroup.mem_subgroupOf.2 ((coe_centVisEquiv y) ▸ hy)
    rw [← hmap] at h1
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = y := centVisEquiv.injective hyy
    rw [← this]
    exact hy'


theorem x11_mem_cent : gw gen11W0 ∈ cent xGmat := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← rhoG_z_eq_xGmat]
  exact (eleven_gw_facts.2.2.2.2.2.2.2).symm

@[expose] noncomputable def x11H : cent xGmat := ⟨gw gen11W0, x11_mem_cent⟩

theorem orderOf_x11 : orderOf (gw gen11W0) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime eleven_gw_facts.1 eleven_gw_facts.2.2.2.1

theorem orderOf_x11H : orderOf x11H = 11 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_x11


theorem card_pCore_inf_centralizer_x11_le :
    Nat.card ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x11H} : Set (cent xGmat))) ≤ 32 := by
  have h := Certificates.certificate16953
  refine le_trans (Nat.card_le_card_of_injective
    (fun y => (⟨(y : cent xGmat), Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩ :
      ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer ({gw gen11W0} : Set Gmat)))) ?_) h
  · exact Subgroup.mem_subgroupOf.2 ((mem_pCore_cent_xGmat_iff _).1 (Subgroup.mem_inf.1 y.2).1)
  · have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  · intro y y' hyy
    have := congrArg Subtype.val hyy
    simp only at this
    exact Subtype.ext (Subtype.ext this)

theorem twoB_xGmat : IsTwoBCentralizer xGmat := isTwoBCentralizer_Gmat xGmat (IsConj.refl _)

theorem natCard_cent_xGmat : Nat.card (cent xGmat) = twoBCentralizerOrder := twoB_xGmat.2.2.2.2.1

instance : Finite (cent xGmat) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_cent_xGmat]; simp [twoBCentralizerOrder])

theorem factorization_cent_xGmat_eleven : (Nat.card (cent xGmat)).factorization 11 = 1 := by
  rw [twoB_xGmat.2.2.2.2.1, twoBCentralizerOrder,
    show (2 ^ 46 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23 : ℕ) = 11 * 12682894466030575288320000 by
      norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem dvd_sixty_six_of_le {n : ℕ} (hpos : 0 < n) (h3 : 3 ∣ n) (h11 : 11 ∣ n) (hle : n ≤ 66) :
    n ∣ 66 := by
  obtain ⟨m, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 11) h3 h11
  have hm : m ≤ 2 := by omega
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hpos; norm_num at hpos
    · exact h
  interval_cases m <;> norm_num

theorem orderOf_image_eleven (e : cent xGmat ⧸ pCore 2 (cent xGmat) ≃* CFSG.Blueprint.NativeSporadic.Co1)
    {x : cent xGmat} (hx : orderOf x = 11) : orderOf (e (QuotientGroup.mk x)) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [MulEquiv.orderOf_eq]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · have hmem : x ∈ pCore 2 (cent xGmat) := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := cent xGmat)) ⟨x, hmem⟩
    have h2 : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h3)
    norm_num at this


theorem card_centralizer_image_dvd (e : cent xGmat ⧸ pCore 2 (cent xGmat) ≃* CFSG.Blueprint.NativeSporadic.Co1)
    {x : cent xGmat} (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set CFSG.Blueprint.NativeSporadic.Co1)) ∣ 66 := by
  have hc := orderOf_image_eleven e hx
  obtain ⟨hle, h3⟩ := Co1Eleven.card_centralizer_Co1_eleven _ hc
  have h11 := Subgroup.orderOf_dvd_natCard
    (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set CFSG.Blueprint.NativeSporadic.Co1))
    (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  rw [hc] at h11
  exact dvd_sixty_six_of_le Nat.card_pos h3 h11 hle

theorem card_centralizer_cent_xGmat_le {x : cent xGmat} (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set (cent xGmat))) ≤ 32 * 66 := by
  obtain ⟨e⟩ := twoB_xGmat.2.2.2.1
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one factorization_cent_xGmat_eleven
    orderOf_x11H hx
  have hk1 : x11H ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    norm_num at hx
  rw [hxk, card_centralizer_conj_eq, centralizer_pow_eq_of_prime orderOf_x11H hk1]
  refine (@card_centralizer_le_mul (cent xGmat) CFSG.Blueprint.NativeSporadic.Co1 _ Units.instGroup _ _
    (pCore 2 (cent xGmat)) _ e x11H).trans (Nat.mul_le_mul card_pCore_inf_centralizer_x11_le ?_)
  exact Nat.le_of_dvd (by norm_num) (card_centralizer_image_dvd e orderOf_x11H)

theorem card_centralizer_xGmat_inf_lt {x : Gmat} (hx : orderOf x = 11) (hxt : x * xGmat = xGmat * x) :
    Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓ Subgroup.centralizer ({x} : Set Gmat) :
      Subgroup Gmat) < 11 * 2 ^ 10 := by
  have hxC : x ∈ cent xGmat := Subgroup.mem_centralizer_singleton_iff.2 hxt
  set x' : cent xGmat := ⟨x, hxC⟩
  have hx' : orderOf x' = 11 := by rw [← Subgroup.orderOf_coe]; exact hx
  have hcard : Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({x} : Set Gmat) : Subgroup Gmat) =
      Nat.card (Subgroup.centralizer ({x'} : Set (cent xGmat))) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
        invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨y.1.2, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  rw [hcard]
  have := card_centralizer_cent_xGmat_le hx'
  omega

theorem gLAPPrimeCoreOf_x11_inf_xGmat_eq_bot
    (hodd : Odd (Nat.card (CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat)))))
    {w₀ e₀ : Gmat} (hw₀t : w₀ ∈ cent xGmat) (hw₀x : w₀ * gw gen11W0 = gw gen11W0 * w₀)
    (hw₃ : orderOf w₀ = 3) (he₀t : e₀ ∈ cent xGmat) (he₀E : (e₀ : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ)
    (he₀x : e₀ * gw gen11W0 = gw gen11W0 * e₀) (hwe : w₀ * e₀ ≠ e₀ * w₀) :
    CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) ⊓
      Subgroup.centralizer ({xGmat} : Set Gmat) = ⊥ := by
  obtain ⟨e⟩ := twoB_xGmat.2.2.2.1
  set N := CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) with hN
  set Y := (N ⊓ Subgroup.centralizer ({xGmat} : Set Gmat)).subgroupOf (cent xGmat) with hY
  have hle : N ⊓ Subgroup.centralizer ({xGmat} : Set Gmat) ≤ cent xGmat := inf_le_right
  have hcardY : Nat.card Y = Nat.card (N ⊓ Subgroup.centralizer ({xGmat} : Set Gmat) :
      Subgroup Gmat) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hdvd : Nat.card Y ∣ Nat.card N := hcardY ▸ Subgroup.card_dvd_of_le inf_le_left
  have hoddY : Odd (Nat.card Y) := Odd.of_dvd_nat hodd hdvd
  have h11Y : ¬ 11 ∣ Nat.card Y := fun h =>
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 (coprime_card_GLAPPrimeCoreOf (by norm_num) _)
      (h.trans hdvd)
  have hYbot := @eq_bot_of_odd_normal_centralizer (cent xGmat) CFSG.Blueprint.NativeSporadic.Co1 _
    Units.instGroup _ _ (pCore 2 (cent xGmat)) _ pCore_isPGroup e x11H
    (card_centralizer_image_dvd e orderOf_x11H) ⟨w₀, hw₀t⟩ ⟨e₀, he₀t⟩
    (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hw₀x))
    (by rw [← Subgroup.orderOf_coe]; exact hw₃)
    (Subgroup.mem_inf.2 ⟨(mem_pCore_cent_xGmat_iff _).2 he₀E,
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext he₀x)⟩)
    (fun h => hwe (congrArg Subtype.val h)) Y
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.1
        (GLAPPrimeCoreOf_le _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1))))
    (fun g hg y hy => by
      rw [hY, Subgroup.mem_subgroupOf] at hy ⊢
      obtain ⟨hyN, hyt⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem (g : Gmat) ?_ _ hyN, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg))
      · exact ((g * y * g⁻¹ : cent xGmat)).2)
    hoddY h11Y
  rw [eq_bot_iff]
  intro n hn
  have hnY : (⟨n, hle hn⟩ : cent xGmat) ∈ Y := Subgroup.mem_subgroupOf.2 hn
  rw [hYbot, Subgroup.mem_bot] at hnY
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hnY)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
