module

public import CFSG.ClassicalInvolution.Q3.TL3Harris
public import CFSG.ClassicalInvolution.Q3.TL3Conv
public import CFSG.ClassicalInvolution.Q3.TL3SecOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

theorem oddCoreIn_top_quotient_eq_bot' (Y : Type*) [Group Y] [Finite Y] :
    oddCoreIn (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y)) = ⊥ := by
  have hS : (oddCoreIn (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
  have h2 := CFSG.ComponentClassification.OddCore.maximal (Y ⧸ classicalInvolutionOddCore Y)
    (oddCoreIn ⊤) hS (odd_card_oddCoreIn _)
  have hcf : componentClassificationOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  rw [hcf] at h2
  exact le_bot_iff.mp h2

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.good_of_hasLift (hd : TightDatum R S t) (h : TightHasLift R t) :
    GoodThreeElement R t := by
  classical
  obtain ⟨L, hKL, hL⟩ := h
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set N : Subgroup C := classicalInvolutionOddCore C with hN
  set π : C →* C ⧸ N := QuotientGroup.mk' N with hπ
  have hcentop : Subgroup.centralizer ({π ⟨t, htC⟩} : Set (C ⧸ N)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hL' := (hL.subgroupOf hLC).map_oddQuotient
  set Lb : Subgroup (C ⧸ N) := (L.subgroupOf C).map π with hLb
  have hLbsub : IsSubnormal Lb ⊤ := by
    have h1 := hL'.subnormal
    rw [show QuotientGroup.mk' (classicalInvolutionOddCore C) (⟨t, hLC hL.mem⟩ : C) =
      π ⟨t, htC⟩ from rfl, hcentop] at h1
    exact h1
  have hOtop : oddCoreIn (⊤ : Subgroup (C ⧸ N)) = ⊥ := oddCoreIn_top_quotient_eq_bot' C
  have hOLb : classicalInvolutionOddCore Lb = ⊥ := by
    have h1 : IsSubnormal (oddCoreIn Lb) ⊤ := isSubnormal_trans (isSubnormal_oddCoreIn Lb) hLbsub
    have h2 := le_oddCoreIn_of_isSubnormal h1 (odd_card_oddCoreIn Lb)
    rw [hOtop, le_bot_iff] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ Lb.subtype_injective).mp h2
  obtain ⟨e⟩ := hL'.nonempty_equiv_sl2 hOLb
  set S0 : Subgroup Y := (S : Subgroup R).map R.subtype with hS0
  have d : OddByQuat R S0 t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  have hS0C : S0 ≤ C := d.S_le.trans hd.cent
  have hS0L : S0 ≤ L := hd.sylow_core.1.trans hKL
  set Pb : Subgroup (C ⧸ N) := (S0.subgroupOf C).map π with hPb
  have hPbL : Pb ≤ Lb := Subgroup.map_mono fun x hx => hS0L hx
  have hRN : ∀ o : Y, o ∈ oddCoreImg R → ∀ ho : o ∈ C, (⟨o, ho⟩ : C) ∈ N := by
    intro o ho hoC
    set K : Subgroup C := (oddCoreImg R).subgroupOf C with hK
    have hKn : K.Normal := by
      refine ⟨fun k hk c => ?_⟩
      have hcN : (c : Y) ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer c.2
      exact conj_mem_oddCoreImg hcN hk
    have hKodd : Odd (Nat.card K) := by
      rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((oddCoreImg_le R).trans hd.cent)).toEquiv]
      exact odd_natCard_oddCoreImg R
    have hKle : K ≤ classicalInvolutionOddCore C := le_sSup ⟨hKn, hKodd⟩
    exact hKle ho
  have hπo : ∀ o : Y, o ∈ oddCoreImg R → ∀ ho : o ∈ C, π ⟨o, ho⟩ = 1 := by
    intro o ho hoC
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hRN o ho hoC
  have hS0N : S0.subgroupOf C ⊓ N = ⊥ :=
    OddQ.inf_eq_bot_of_two (d.S_two.comap_subtype) (CFSG.ComponentClassification.OddCore.odd_card C)
  have hPbcard : Nat.card Pb = Nat.card S0 := by
    have hbij : Function.Bijective (π.subgroupMap (S0.subgroupOf C)) :=
      ⟨TwistQ.subgroupMap_injective hS0N, MonoidHom.subgroupMap_surjective _ _⟩
    rw [hPb, ← Nat.card_congr (Equiv.ofBijective _ hbij),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0C).toEquiv]
  have hS8 : 8 ≤ Nat.card S0 := by
    obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
    rw [hS0, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr eS.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 2 ≤ 2 ^ (r - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hPb8 : Nat.card Pb = 8 := by
    have h2 : IsPGroup 2 Pb := (d.S_two.comap_subtype).map π
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hdvd : Nat.card Pb ∣ 24 := by
      have h1 := Subgroup.card_dvd_of_le hPbL
      rwa [Nat.card_congr e.toEquiv, Q3T6.Aut.sl2Three_natCard] at h1
    have hge : 8 ≤ 2 ^ k := hk ▸ (hPbcard ▸ hS8)
    rw [hk] at hdvd ⊢
    have hle : 2 ^ k ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hk4 : k ≤ 4 := by
      by_contra hk'
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp_all
  have hPbn : ∀ g ∈ (⊤ : Subgroup (C ⧸ N)), ∀ p ∈ Pb, g * p * g⁻¹ ∈ Pb := by
    intro g _ p hp
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨s, hs, rfl⟩ := hp
    have hcsR : (c : Y) * s * (c : Y)⁻¹ ∈ R := by
      have hcN : (c : Y) ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer c.2
      exact (Subgroup.mem_normalizer_iff.mp hcN s).mp (d.S_le hs)
    obtain ⟨s', hs', o, ho, hcs⟩ := d.exists_mul_S_O _ hcsR
    have hoC : o ∈ C := hd.cent ((oddCoreImg_le R) ho)
    have hcs' : c * s * c⁻¹ = (⟨s', hS0C hs'⟩ : C) * ⟨o, hoC⟩ := Subtype.ext hcs
    refine ⟨⟨s', hS0C hs'⟩, hs', ?_⟩
    show π _ = QuotientGroup.mk' N c * π s * (QuotientGroup.mk' N c)⁻¹
    rw [show QuotientGroup.mk' N c = π c from rfl, ← map_inv, ← map_mul, ← map_mul, hcs', map_mul,
      hπo o ho hoC, mul_one]
  obtain ⟨y0, hy03, hy01⟩ := sl2Three_exists_order_three
  obtain ⟨c0, hc0⟩ := QuotientGroup.mk'_surjective N ((e.symm y0 : Lb) : C ⧸ N)
  have hNpos : 0 < orderOf c0 := orderOf_pos c0
  obtain ⟨a, b, hb3, hNab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hNpos.ne' 3 (by norm_num)
  set xC : C := c0 ^ b with hxC
  have hxC3 : xC ^ 3 ^ a = 1 := by
    rw [hxC, ← pow_mul, mul_comm, ← hNab]
    exact pow_orderOf_eq_one c0
  have hπx : π xC = ((e.symm y0 ^ b : Lb) : C ⧸ N) := by
    rw [hxC, map_pow, show π c0 = QuotientGroup.mk' N c0 from rfl, hc0]
    rfl
  have hπxL : π xC ∈ Lb := by rw [hπx]; exact (e.symm y0 ^ b).2
  have hey : e ⟨π xC, hπxL⟩ = y0 ^ b := by
    have : (⟨π xC, hπxL⟩ : Lb) = e.symm y0 ^ b := Subtype.ext hπx
    rw [this, map_pow, MulEquiv.apply_symm_apply]
  have hy13 : (y0 ^ b) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy03, one_pow]
  have hy11 : y0 ^ b ≠ 1 := by
    intro h1
    have hord : orderOf y0 = 3 := orderOf_eq_prime hy03 hy01
    exact hb3 (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  have hcentP : ∀ y : C, (∀ r ∈ R, ⁅(y : Y), r⁆ ∈ oddCoreImg R) →
      ∀ p ∈ Pb, π y * p = p * π y := by
    intro y hy p hp
    obtain ⟨s, hs, rfl⟩ := hp
    have h1 := hy s (d.S_le hs)
    have hcC : ⁅(y : Y), (s : Y)⁆ ∈ C := hd.cent ((oddCoreImg_le R) h1)
    have h2 : π ⁅y, s⁆ = 1 := by
      have : ⁅y, s⁆ = (⟨⁅(y : Y), (s : Y)⁆, hcC⟩ : C) := rfl
      rw [this]
      exact hπo _ h1 hcC
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  refine ⟨xC, a, xC.2, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hxC3
    simpa using this
  ·
    by_contra hcon
    push Not at hcon
    have hc := hcentP xC hcon
    let f : Pb → {z : SL(2, ZMod 3) // z * y0 ^ b = y0 ^ b * z} := fun p =>
      ⟨e ⟨p, hPbL p.2⟩, by
        rw [← hey, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc p p.2).symm⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have h1 : e ⟨p, hPbL p.2⟩ = e ⟨q, hPbL q.2⟩ := congrArg Subtype.val hpq
      have h2 : (p : C ⧸ N) = q := congrArg (fun z : Lb => (z : C ⧸ N)) (e.injective h1)
      exact Subtype.ext h2
    have h1 := Nat.card_le_card_of_injective f hf
    rw [hPb8, Nat.card_eq_fintype_card] at h1
    have h2 := sl2Three_centralizer_card (y0 ^ b) hy13 hy11
    omega
  ·
    intro y hyC hy
    have hc := hcentP ⟨y, hyC⟩ hy
    have hcomm := Harris3.centralizes_of_isSubnormal_sl2 hLbsub e hPbL hPb8 hPbn hOtop
      (Subgroup.mem_top (π ⟨y, hyC⟩)) hc hπxL
    have h1 : π ⁅xC, (⟨y, hyC⟩ : C)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩

end CFSG.ClassicalInvolution.Q3
