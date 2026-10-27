module

public import CFSG.ClassicalInvolution.Asc77.AscT7TFieldPart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight

namespace T7T

variable {p f : ℕ} [Fact p.Prime]

theorem c25_16_of_odd (hfo : Odd f) : C25_16 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS hF
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hR'K' : R' ≤ K' := hyp.hR'.2.1
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hR'K'
  have hqR' : IsQuatSub R' := hΩ.isQuatSub_of_mem_RSet hp hyp.hR'.1
  have h8 := hqR'.eight_le
  have hzR' : IsUniqueInvolution R' z :=
    AscL62.isUniqueInvolution_of_le hz' hR'K'
      (mem_of_isUniqueInvolution_of_isPGroup hz' hR'K' hR'syl.2.1 (by omega))
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)
  have haR' : conjSub a R' = R' := mem_normalizer_iff_conjSub_eq.mp hF.1
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    by_contra hne
    have hK2 : conjSub a K' ∈ Ω := hΩ.conjInvariant a K' hK'
    have hRK2 : R' ≤ conjSub a K' := haR' ▸ conjSub_mono hR'K'
    have := hΩ.card_le_two_of_le_inf hK' hK2 (Ne.symm hne) hR'syl.2.1 hR'K' hRK2
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact absurd hfo (by decide)
  obtain ⟨z₀, hz₀⟩ := hΩ.classical K' hK'
  obtain ⟨e⟩ := hz₀.nonempty_equiv
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hF' : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.pos_of_ne_zero hf0, hFcard⟩
  have h3 : 3 < Nat.card (GaloisField p f) := by rw [hFcard]; omega
  have hne1 := fieldPart_ne_one_of_isFAut e hFcard hF' h3 hp hR'K' hqR' hzR' hF ha2 haK'
  apply hne1
  set σ := (normalizerToPGammaL2Mod e hFcard hF' h3 ⟨a, haK'⟩).right with hσ
  have h1 : σ ^ f = 1 := ringEquiv_pow_eq_one hf0 σ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp ha2) ⟨a, Subgroup.mem_zpowers a⟩
  have hao : a ^ (2 ^ m) = 1 := by
    have h1 : orderOf a = 2 ^ m := by
      rw [← hm]; exact (Subgroup.orderOf_mk a (Subgroup.mem_zpowers a)).symm
    rw [← h1]
    exact pow_orderOf_eq_one a
  have hn : (⟨a, haK'⟩ : Subgroup.normalizer (K' : Set G)) ^ (2 ^ m) = 1 :=
    Subtype.ext (by simpa using hao)
  have h2 : σ ^ (2 ^ m) = 1 := by
    have h3' : (normalizerToPGammaL2Mod e hFcard hF' h3 ⟨a, haK'⟩) ^ (2 ^ m) = 1 := by
      rw [← map_pow, hn, map_one]
    have := congrArg (fun γ => SemidirectProduct.rightHom γ) h3'
    simpa [map_pow, SemidirectProduct.rightHom_eq_right, hσ] using this
  have hcop : Nat.gcd (2 ^ m) f = 1 := by
    have : Nat.Coprime (2 ^ m) f := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hfo)
    exact this
  have := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rwa [hcop, pow_one] at this

end T7T

end CFSG.ClassicalInvolution.Asc77
