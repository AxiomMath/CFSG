module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Irr
public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Diag
import CFSG.Quasithin.MS93.ML3Split
import CFSG.Quasithin.MS93.S36SpEType
public import CFSG.Quasithin.Background.FFC8A

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.Timmesfeld.Orders
  CFSG.Quasithin.H13.VolI CFSG.Quasithin.MS93
open CFSG.Open (quasithinG2 ordA ordBC ordG2)

theorem eq_one_of_mem_center_of_equiv_statedSL_zmod {d : ℕ} (hd : 1 ≤ d) {K : Type} [Group K]
    (e : ↥(StatedSL d (ZMod 2)) ≃* K) {z : K} (hz : z ∈ Subgroup.center K) : z = 1 := by
  let e' : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ≃* K :=
    (specialLinearGroupEquivStatedSL d (ZMod 2)).trans e
  have hy : e'.symm z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e'.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (e' g)
  obtain ⟨r, hr, hry⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hy
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    fin_cases r
    · exfalso
      have h0 : (0 : ZMod 2) ^ d = 0 := zero_pow (by omega)
      have : (0 : ZMod 2) = 1 := by
        have h' : ((0 : ZMod 2) : ZMod 2) ^ d = 1 := hr
        rw [h0] at h'
        exact h'
      exact absurd this (by decide)
    · rfl
  subst hr1
  have : e'.symm z = 1 := by
    apply Subtype.ext
    rw [← hry]
    simp
  simpa using congrArg e' this



theorem exists_ne_one_mem_center_statedSL_three {F : Type} [Field F] [Finite F] {e : ℕ}
    (hF : Nat.card F = 2 ^ e) (hev : Even e) :
    ∃ z ∈ Subgroup.center ↥(StatedSL 3 F), z ≠ 1 := by
  obtain ⟨k, hk⟩ := hev
  have h3 : 3 ∣ Nat.card Fˣ := by
    have : Nat.card Fˣ = 2 ^ e - 1 := by
      classical
      have := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
    rw [this, hk, ← two_mul, pow_mul]
    have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) k
    norm_num at this ⊢
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ((ω : F)) ^ Fintype.card (Fin 3) = 1 := by
    rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one]
    rfl
  let ζ := rootsOfUnity.mkOfPowEq (ω : F) hω3
  have hζ : ζ ≠ 1 := by
    intro h
    have : (ω : F) = 1 := by
      have := congrArg (fun x : rootsOfUnity (Fintype.card (Fin 3)) F => ((x : Fˣ) : F)) h
      simpa [ζ, rootsOfUnity.coe_mkOfPowEq] using this
    have h1 : ω = 1 := Units.ext this
    rw [h1, orderOf_one] at hω
    omega
  let e0 := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  let z0 := e0.symm ζ
  let eq := specialLinearGroupEquivStatedSL 3 F
  refine ⟨eq z0.1, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply eq.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    have := Subgroup.mem_center_iff.mp z0.2 (eq.symm g)
    exact this
  · intro h
    apply hζ
    have h1 : z0.1 = 1 := by simpa using eq.injective (h.trans (map_one eq).symm)
    have : z0 = 1 := Subtype.ext h1
    simpa [z0] using congrArg e0 this



section CoreA
variable {V : Type} [CommGroup V] [Finite V]

theorem core_eq_one (h51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1)
    {J K P : Subgroup (MulAut V)} (hB : B51Hyp J K)
    (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V)))
    {z : MulAut V} (hzP : z ∈ ⁅P, P⁆) (hzK : z ∈ K) {m : ℕ} (hm : Odd m) (hzm : z ^ m = 1) :
    z = 1 := by
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 V hV J K hB
  have hPP : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun a ha b hb =>
    P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have hzc : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hP (hPP hzP)) k k.2
  have hone : ∀ {d : ℕ}, 1 ≤ d → ↥(StatedSL d (ZMod 2)) ≃* ↥K → z = 1 := by
    intro d hd e
    have := eq_one_of_mem_center_of_equiv_statedSL_zmod hd e hzc
    simpa using congrArg Subtype.val this
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · exact eq_one_of_trivial_on_commV hV hzK hm hzm
      (fun u hu => commutator_trivial_of_isIrrPlus hi.1 hP z hzP u hu)
  · obtain ⟨-, n, F, iF, fF, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
    refine eq_one_of_trivial_on_commV hV hzK hm hzm (fun u hu => ?_)
    rw [commutator_trivial_of_case1ii ⟨n, F, iF, fF, hF, I, π, hind, hsup, hreal⟩ hP z hzP hzK m hm
      hzm u hu, mul_inv_cancel]
    exact one_mem _
  · obtain ⟨-, hn, π, U₁, U₂, -, h1, -⟩ := hiii
    exact hone (d := n) (by omega) (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)
  · obtain ⟨-, n, hn, k, hk1, hkn, I, π, -, -, -, hreal⟩ := hiv
    exact hone (d := n) (by omega) (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))

end CoreA

section CoreB

variable {V : Type} [CommGroup V] [Finite V]

private theorem false_of_sl3_of_center_bot {K : Type} [Group K] {F : Type} [Field F] [Finite F] {n e : ℕ}
    (he1 : 1 ≤ e) (hev : Even e) (hZ : Subgroup.center K = ⊥)
    (hcard : Nat.card (K ⧸ Subgroup.center K) = ordA 2 (2 ^ e))
    (hF : Nat.card F = 2 ^ n) (e' : ↥(StatedSL 3 F) ≃* K) : False := by
  obtain ⟨hn, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three hF e'
  have hne : n = e := by
    by_contra hne
    exact ne_of_two_part (two_part_ordA_two hn) (two_part_ordA_two he1) (N := n * 3) (N' := e * 3)
      (by omega) (hc.symm.trans hcard)
  subst hne
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_center_statedSL_three hF hev
  have hzc : e' z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e'.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact hz (e'.symm g)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hz1 (e'.injective (hzc.trans (map_one e').symm))

theorem core_classify
    (h51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {J K : Subgroup (MulAut V)} (hB : B51Hyp J K)
    {e : ℕ} (hPSL : IsPSL 3 2 e (↥K ⧸ Subgroup.center ↥K)) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (π : ↥(StatedSL 3 F) →* ↥K),
        Nat.card F = 2 ^ e ∧ Function.Bijective π ∧
        (FFModel.nat (StatedSL 3 F)).RealizesVia K (commV K) (fixV K ⊓ commV K) π) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (π : ↥(StatedSL 3 F) →* ↥K)
        (I : Fin 2 → Subgroup V), Nat.card F = 2 ^ e ∧ Function.Bijective π ∧
        iSupIndep I ∧ (⨆ i, I i) = commV K ∧
        ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π) := by
  have hq : CFSG.IsQuasisimple ↥K := hB.2.1
  have he1 : 1 ≤ e := hPSL.1.2.1
  have hR : IsRankTwoLie2Derived (↥K ⧸ Subgroup.center ↥K) := Or.inl ⟨e, hPSL⟩
  have hcard : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordA 2 (2 ^ e) :=
    (card_statedClassicalModel_two hPSL).1 rfl
  have hsl3 : ∀ {n : ℕ} {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ n →
      ↥(StatedSL 3 F) ≃* ↥K → n = e := by
    intro n F _ _ hF e'
    obtain ⟨hn, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three hF e'
    by_contra hne
    exact ne_of_two_part (two_part_ordA_two hn) (two_part_ordA_two he1) (N := n * 3) (N' := e * 3)
      (by omega) (hc.symm.trans hcard)
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 V hV J K hB
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hpair, -⟩ := hi
    rcases hpair with ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ |
      ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ | hG2d | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
      ⟨π, hπ⟩ | ⟨α, π, hπ⟩ | hHat | hSL4 | hSL5 | hE4 | hE5
    ·
      exact (false_of_equiv_statedSL_two hq hR hF
        (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
    ·
      have hne := hsl3 hF (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)
      subst hne
      exact Or.inl ⟨F, iF, fF, π, hF,
        ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩, hπ⟩
    ·
      let e' := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
        rw [show n = 1 by omega] at hF
        exact R3c2.not_isQuasisimple_statedSp_two (hF.trans (pow_one 2)) e'.symm hq
      exact (S36E.ordA_two_ne_ordBC_two (n := e) hn2
        (hcard.symm.trans (card_quot_of_equiv_statedSp hF hn2 e'))).elim
    ·
      have : CharP F 2 := FFC.charP_two_of_card_pow hF
      let e' := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
        rw [show n = 1 by omega] at hF
        exact R3c2.not_isQuasisimple_quasithinG2_two (hF.trans (pow_one 2)) e'.symm hq
      exact (ordA_two_ne_ordG2 he1 hn2
        (hcard.symm.trans (card_quot_of_equiv_quasithinG2 hF hn2 e'))).elim
    ·
      obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hG2d
      have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
      have : CharP F 2 := FFC.charP_two_of_card_pow hF
      let e' := FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ
      obtain ⟨-, hc⟩ := card_quot_of_equiv_g2Derived hF2 e'
      exact (S32.ordA_two_ne_6048 he1 (hcard.symm.trans hc)).elim
    ·
      exact (false_of_equiv_alt hR (Or.inl rfl)
        (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
    ·
      exact (ordA_two_ne_360 he1 (hcard.symm.trans (card_quot_of_equiv_alt6
        (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)))).elim
    ·
      exact (false_of_equiv_alt hR (Or.inr rfl)
        (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
    ·
      exact (false_of_equiv_alt hR (Or.inr rfl)
        (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ)).elim
    ·
      obtain ⟨Kf, iK, fK, Γ₀, -, -, hhat, -, π, hπ⟩ := id hHat
      have hH : IsHat ↥K ↥(alternatingGroup (Fin 6)) :=
        IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ) hhat
      exact (ordA_two_ne_360 he1 (hcard.symm.trans (card_quot_of_isHat hH))).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL4
      exact (false_of_equiv_statedSL_zmod hR (Or.inl rfl)
        (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL5
      exact (false_of_equiv_statedSL_zmod hR (Or.inr rfl)
        (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
    · obtain ⟨π, hπ⟩ := id hE4
      exact (false_of_equiv_statedSL_zmod hR (Or.inl rfl)
        (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim
    · obtain ⟨π, hπ⟩ := id hE5
      exact (false_of_equiv_statedSL_zmod hR (Or.inr rfl)
        (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim
  · obtain ⟨-, n, F, iF, fF, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
    have hne := hsl3 hF (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal 0))
    subst hne
    exact Or.inr ⟨F, iF, fF, π, I, hF,
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0), (hreal 0).1⟩, hind, hsup,
      hreal⟩
  · obtain ⟨-, hn, π, U₁, U₂, -, h1, -⟩ := hiii
    exact (false_of_equiv_statedSL_zmod hR hn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)).elim
  · obtain ⟨-, n, hn, k, hk1, hkn, I, π, -, -, -, hreal⟩ := hiv
    exact (false_of_equiv_statedSL_zmod hR hn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))).elim

theorem core_center_ne_bot
    (h51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {J K : Subgroup (MulAut V)} (hB : B51Hyp J K)
    {e : ℕ} (hev : Even e) (hPSL : IsPSL 3 2 e (↥K ⧸ Subgroup.center ↥K)) :
    Subgroup.center ↥K ≠ ⊥ := by
  intro hZ
  have he1 : 1 ≤ e := hPSL.1.2.1
  have hcard : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordA 2 (2 ^ e) :=
    (card_statedClassicalModel_two hPSL).1 rfl
  rcases core_classify h51 hV hB hPSL with ⟨F, iF, fF, π, hF, hbij, -⟩ | ⟨F, iF, fF, π, I, hF, hbij, -⟩
  · exact false_of_sl3_of_center_bot he1 hev hZ hcard hF (MulEquiv.ofBijective π hbij)
  · exact false_of_sl3_of_center_bot he1 hev hZ hcard hF (MulEquiv.ofBijective π hbij)

end CoreB

end CFSG.HardMathSupport.Curtis.Coordinator
