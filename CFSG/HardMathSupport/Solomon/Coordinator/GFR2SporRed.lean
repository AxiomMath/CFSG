module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.ComponentClassification.OuterAutomorphisms

theorem gfr2spor_card_ge (hOG : UniquenessMaximal.InputONGroup) {Y : Type} [Group Y] [Finite Y]
    {J : Subgroup Y} (hty : IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J)) : 1080 ≤ Nat.card J := by
  have hbar : Nat.card (barOf 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 J))
  have hpos : 0 < Nat.card J := Nat.card_pos
  have h1 := Nat.le_of_dvd hpos hbar
  rcases hty with h | h
  · have h2 := (UniquenessMaximal.isSimple_card_of_isHatON hOG h).2
    rw [h2, h.2.1] at hbc
    unfold orderON at hbc
    omega
  · have := gfr2_card_isHatSix h
    omega

theorem sporNoPumpup_of_card_bound (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo)
    {name : TauCeti.SporadicName} (N : ℕ) (hN : 3 * N < 1080)
    (hb : ∀ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 →
      Nat.card ↥(Subgroup.centralizer ({s} : Set _)) ≤ N) : SporNoPumpup name := by
  intro Y _ _ hq hKg hcore ⟨e⟩ x hxo J₁ hJ₁ hty
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hperf : commutator Y = ⊤ := hq.1
  have hzodd := odd_card_center_of_core_bot hcore
  have hzd := card_center_dvd_mult hSpM hq name e
  have hz13 := odd_dvd_twelve (hzd.trans (sporadicMultiplierOrder_dvd_twelve name)) hzodd
  have hz3 : Nat.card (Subgroup.center Y) ≤ 3 := by omega
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hs := hq.2
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := hOut _ hs hnab name ⟨e⟩
  have hβ3 : (autCenterQuot Y x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨s, hsβ, hs3⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout
    (autCenterQuot Y x) hβ3
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hsβ
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hperf (by rw [← hsβ, map_one])
    rw [h2, orderOf_one] at hxo
    omega
  have hso : orderOf (e s) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hs3 hs1
  have hbound := hb (e s) hso
  haveI : Finite (TauCeti.CFSGIndex.sporadic name).Group := Finite.of_equiv _ e.toEquiv
  let π : Y →* (TauCeti.CFSGIndex.sporadic name).Group :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  let φ : ↥J₁ →* (TauCeti.CFSGIndex.sporadic name).Group := π.comp J₁.subtype
  have hrange : φ.range ≤ Subgroup.centralizer ({e s} : Set _) := by
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : x j = j := hJ₁.1 hj
    have h1 : (autCenterQuot Y x) (j : Y ⧸ Subgroup.center Y) = (j : Y ⧸ Subgroup.center Y) := by
      rw [autCenterQuot_mk, hfix]
    rw [← hsβ, MulAut.conj_apply] at h1
    show e (QuotientGroup.mk j) * e s = e s * e (QuotientGroup.mk j)
    rw [← map_mul, ← map_mul]
    congr 1
    calc (QuotientGroup.mk j : Y ⧸ Subgroup.center Y) * s
        = s * (s⁻¹ * QuotientGroup.mk j * s) := by group
      _ = s * QuotientGroup.mk j := by
        congr 1
        have : s * (QuotientGroup.mk j : Y ⧸ Subgroup.center Y) * s⁻¹ = QuotientGroup.mk j := h1
        rw [mul_inv_eq_iff_eq_mul] at this
        calc s⁻¹ * QuotientGroup.mk j * s = s⁻¹ * (QuotientGroup.mk j * s) := by group
          _ = s⁻¹ * (s * QuotientGroup.mk j) := by rw [this]
          _ = QuotientGroup.mk j := by group
  have hker : Nat.card φ.ker ≤ Nat.card (Subgroup.center Y) := by
    refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥J₁) : Y), ?_⟩ : Subgroup.center Y)) ?_
    · have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have : QuotientGroup.mk' (Subgroup.center Y) (k : Y) = 1 := e.injective (by
        have := hk
        simpa [φ, π] using this)
      exact (QuotientGroup.eq_one_iff _).1 this
    · intro a b hab
      have h1 : ((a : ↥J₁) : Y) = ((b : ↥J₁) : Y) :=
        congrArg (fun w : Subgroup.center Y => (w : Y)) hab
      exact Subtype.ext (Subtype.ext h1)
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hrng : Nat.card φ.range ≤ N :=
    (Subgroup.card_le_of_le hrange).trans hbound
  have hJle : Nat.card J₁ ≤ 3 * N := by
    rw [← hcard]
    exact (Nat.mul_le_mul (hker.trans hz3) hrng)
  have := gfr2spor_card_ge hOG hty
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
