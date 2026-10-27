module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE4

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Assembly.LowTwoRank

theorem famF_of_odd (hPSL : FamF .PSL) (hPSU : FamF .PSU) (hPSp : FamF .PSp)
    (hOdd : FamF .POmegaOdd) (hPlus : FamF .POmegaPlus) (hMinus : FamF .POmegaMinus)
    (hG2 : FamF .G2) (hF4 : FamF .F4) (hE6 : FamF .E6) (hE7 : FamF .E7) (hE8 : FamF .E8)
    (hTE6 : FamF .twistedE6) (hD4 : FamF .trialityD4) (hTG2 : FamF .twistedG2) :
    ∀ τ : StatedLieTag, FamF τ := by
  intro τ
  cases τ with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact hOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | G2 => exact hG2
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTE6
  | trialityD4 => exact hD4
  | twistedG2 => exact hTG2
  | twistedB2 => exact famF_of_char_two char_two_of_lieModel_twistedB2
  | twistedF4 => exact famF_of_char_two char_two_of_lieModel_twistedF4
  | Tits => exact famF_of_char_two char_two_of_lieModel_Tits

theorem exists_sylow_klein {R : Type} [Group R] [Finite R]
    (hR : IsKleinFour (R ⧸ pPrimeCore 2 R)) :
    ∃ S : Subgroup R, Nat.card S = 4 ∧ ∀ s ∈ S, s * s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 R) := inferInstance
  set O := pPrimeCore 2 R with hOdef
  have hO : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hSO : (S : Subgroup R) ⊓ O = ⊥ := by
    refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  refine ⟨S, ?_, fun s hs => ?_⟩
  · have h1 := card_mul_index (S : Subgroup R)
    have h2 : ¬ 2 ∣ (S : Subgroup R).index := S.not_dvd_index
    have h3 := card_eq_card_quotient_mul_card_subgroup O
    rw [hR.card_four] at h3
    have hidx : Odd (S : Subgroup R).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have hmo : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
    have hdvd1 : 2 ^ k ∣ 4 := by
      refine hmo.dvd_of_dvd_mul_right ⟨(S : Subgroup R).index, ?_⟩
      rw [← hk, h1, h3]
    have hdvd2 : 4 ∣ 2 ^ k := by
      have hc : Nat.Coprime 4 (S : Subgroup R).index :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hidx)
      refine hc.dvd_of_dvd_mul_right ⟨Nat.card O, ?_⟩
      rw [← hk, h1, h3]
    rw [hk]
    exact Nat.dvd_antisymm hdvd1 hdvd2
  · have h1 : s * s ∈ (S : Subgroup R) ⊓ O := by
      refine mem_inf.mpr ⟨mul_mem hs hs, ?_⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact IsKleinFour.mul_self _
    rw [hSO, mem_bot] at h1
    exact h1

theorem harris82Lemma51E4_of_famF (hPSL : FamF .PSL) (hPSU : FamF .PSU) (hPSp : FamF .PSp)
    (hOdd : FamF .POmegaOdd) (hPlus : FamF .POmegaPlus) (hMinus : FamF .POmegaMinus)
    (hG2 : FamF .G2) (hF4 : FamF .F4) (hE6 : FamF .E6) (hE7 : FamF .E7) (hE8 : FamF .E8)
    (hTE6 : FamF .twistedE6) (hD4 : FamF .trialityD4) (hTG2 : FamF .twistedG2) :
    Harris82Lemma51E4 := by
  intro X _ _ _ τ n p f hp hp2 hX z hz R hRC hRsub hzR hR4
  by_contra hq
  have hfam := famF_of_odd hPSL hPSU hPSp hOdd hPlus hMinus hG2 hF4 hE6 hE7 hE8 hTE6 hD4 hTG2 τ
  obtain ⟨S, hS4, hSsq⟩ := exists_sylow_klein hR4
  set T := S.map R.subtype with hT
  have hTR : T ≤ R := map_subtype_le S
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hcomm : ∀ (t : T) (w : zpowers z), Commute (T.subtype t) ((zpowers z).subtype w) := by
    rintro ⟨t, ht⟩ ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    exact Commute.zpow_right (mem_centralizer_singleton_iff.mp (hRC (hTR ht))) i
  set φ := MonoidHom.noncommCoprod T.subtype (zpowers z).subtype hcomm with hφ
  have hzpow : ∀ w ∈ zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← zpow_mod_orderOf, hz]
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr ⟨subtype_injective _,
      subtype_injective _, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff, eq_bot_iff]
    intro w hw
    obtain ⟨hwT, hwz⟩ := mem_inf.mp hw
    rcases hzpow w hwz with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hTR hwT) hzR
  set P := φ.range with hP
  have hφapp : ∀ x : T × zpowers z, φ x = (x.1 : X) * (x.2 : X) := fun x => rfl
  have hPcard : Nat.card P = 8 := by
    rw [hP, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      card_map_of_injective (subtype_injective R), hS4, Nat.card_zpowers, hz]
  have hzP : z ∈ P := ⟨(1, ⟨z, mem_zpowers z⟩), by rw [hφapp]; simp⟩
  have hPC : P ≤ centralizer ({z} : Set X) := by
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    refine mul_mem (hRC (hTR x.1.2)) ?_
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp x.2.2
    rw [← hi]
    exact zpow_mem (mem_centralizer_singleton_iff.mpr rfl) i
  have hPsq : ∀ q ∈ P, q * q = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    have h1 : (x.1 : X) * (x.1 : X) = 1 := by
      obtain ⟨s, hs, hsx⟩ := mem_map.mp x.1.2
      rw [← hsx]
      exact congrArg Subtype.val (hSsq s hs)
    have h2 : (x.2 : X) * (x.2 : X) = 1 := by
      rcases hzpow _ x.2.2 with h | h <;> rw [h]
      · exact mul_one 1
      · exact hzz
    have hab : (x.1 : X) * x.2 = x.2 * x.1 := (hcomm x.1 x.2).eq
    calc (x.1 : X) * x.2 * (x.1 * x.2) = x.1 * (x.2 * x.1) * x.2 := by group
      _ = x.1 * (x.1 * x.2) * x.2 := by rw [← hab]
      _ = x.1 * x.1 * (x.2 * x.2) := by group
      _ = 1 := by rw [h1, h2, mul_one]
  have hsolv : Group.IsSolvable (↥R ⧸ pPrimeCore 2 ↥R) :=
    Group.isSolvable_of_comm (mul_comm_of_exponent_two hR4.exponent_two)
  have hPK : ∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, ∀ g ∈ P, (k : X) * g = g * k := by
    rintro K hK hKe k hk _ ⟨x, rfl⟩
    rw [hφapp]
    have h1 := commute_of_isComponent hRC hRsub hsolv hK hKe k hk x.1 (hTR x.1.2)
    have h2 : (k : X) * x.2 = x.2 * k := by
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp x.2.2
      rw [← hi]
      exact ((Commute.zpow_right (mem_centralizer_singleton_iff.mp k.2) i)).eq
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  exact (hfam X n p f hp hp2 hX hq z hz P hPC hzP hPcard hPK).2 hPsq

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
