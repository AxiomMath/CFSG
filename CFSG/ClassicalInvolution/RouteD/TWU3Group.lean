module

public import CFSG.ClassicalInvolution.RouteD.TWU3Aux
public import CFSG.ClassicalInvolution.RouteD.TWU2Chain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.TWT9Typed

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.TWT9 (twinYModel_minus_four_of_mod)

set_option linter.unusedSectionVars false

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}



theorem leaf_twin_group (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u}) (h1 : p ^ f % 4 = 1)
    (hshape : LocalShapeT p f 0 (twinYModel (p ^ f) .POmegaMinus 4).1
      (twinYModel (p ^ f) .POmegaMinus 4).2 Ω u) {K T β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hT : T ∈ centralizingMembers Ω {u})
    (hβ : β ∈ centralizingMembers Ω {u}) (hz : IsClassicalMember p f K z)
    (hzT : IsClassicalMember p f T z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (hTK : T ≠ K)
    (hKT : Commutes K T) :
    ∃ (J₁ J₂ : Subgroup G) (w₁ AK AT AJ AJ' : G), J₁ ∈ centralizingMembers Ω {u} ∧
      J₂ ∈ centralizingMembers Ω {u} ∧ Commutes K J₁ ∧ Commutes K J₂ ∧ Commutes T J₁ ∧
      Commutes T J₂ ∧ Commutes J₁ J₂ ∧ J₁ ≠ J₂ ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W β J₁) ∧ z ∉ J₁ ∧ z ∉ J₂ ∧
      IsClassicalMember p f J₁ w₁ ∧ IsClassicalMember p f J₂ w₁ ∧ AK ∈ K ∧ AT ∈ T ∧ AJ ∈ J₁ ∧
      AJ' ∈ J₂ ∧ AK * AK = z ∧ AT * AT = z ∧ AJ * AJ = w₁ ∧ AJ' * AJ' = w₁ ∧
      s = AK * AT * (AJ * AJ') := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  obtain ⟨i, hi⟩ : ∃ i : GaloisField p f, i * i = -1 := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    have hsq : IsSquare (-1 : GaloisField p f) := by
      rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card,
        GaloisField.card p f (by omega), h1]
      norm_num
    obtain ⟨i, hi⟩ := hsq
    exact ⟨i, hi.symm⟩
  rw [twinYModel_minus_four_of_mod h1] at hshape
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf1, by norm_num⟩
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape
  have hY := yData_minus (by norm_num) hp2 hadm (by omega)
  have hF := orthFacts_minus (m := 5) hp2 (by norm_num) hq
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨RT, hRT, hTR⟩ := e.mem T hT
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaMinus 5 p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  have hTne : RT ≠ R₀ := fun h => hTK (locImg_injOn hΩ hP1 hT hK (by rw [hTR, hKR, h]))
  obtain ⟨r₀, hr₀, hφr₀⟩ := e.exists_involution hY hK hR₀ hKR hz
  obtain ⟨rT, hrT, hφrT⟩ := e.exists_involution hY hT hRT hTR hzT
  have hTinv : ∃ r r', InvOf R₀ r ∧ InvOf RT r' ∧
      r⁻¹ * r' ∈ Subgroup.center (modelUniv .POmegaMinus 5 p f Fact.out).K :=
    ⟨r₀, rT, hr₀, hrT, e.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφr₀, hφrT]
      exact inv_mul_cancel _)⟩
  have hchain : ChainTwin
      (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 5 p f Fact.out).D)
      (GaloisField p f) R₀ R₁ RT :=
    chain_twin_model hp2 hq ⟨i, hi⟩ hR₀ hR₁ hRT hadjR ⟨W', hW'⟩ hTne hTinv
  obtain ⟨RJ, RJ', hRJ, hRJ', cJ0, cJT, cJ'0, cJ'T, cJJ', hne, ⟨WJ, hWJ⟩, hsepJ, hsepJ', a, a', b,
    b', r₁, ν, ha, ha', hb, hb', hr₁, hsa, hsa', hsb, hsb', hsr, hνc, haa, hbb, hP⟩ := hchain
  obtain ⟨J₁, hJ₁, hJ₁R⟩ := e.comp RJ hRJ
  obtain ⟨J₂, hJ₂, hJ₂R⟩ := e.comp RJ' hRJ'
  have hKJ₁ : Commutes K J₁ :=
    commutes_symm ((e.commutes_iff hY hΩ hP1 hJ₁ hK hRJ hJ₁R hKR).mpr cJ0)
  have hKJ₂ : Commutes K J₂ :=
    commutes_symm ((e.commutes_iff hY hΩ hP1 hJ₂ hK hRJ' hJ₂R hKR).mpr cJ'0)
  have hTJ₁ : Commutes T J₁ :=
    commutes_symm ((e.commutes_iff hY hΩ hP1 hJ₁ hT hRJ hJ₁R hTR).mpr cJT)
  have hTJ₂ : Commutes T J₂ :=
    commutes_symm ((e.commutes_iff hY hΩ hP1 hJ₂ hT hRJ' hJ₂R hTR).mpr cJ'T)
  have hJJ : Commutes J₁ J₂ := (e.commutes_iff hY hΩ hP1 hJ₁ hJ₂ hRJ hJ₁R hJ₂R).mpr cJJ'
  have hJne : J₁ ≠ J₂ := fun h => by
    rw [← h] at hJJ
    exact not_commutes_self_of_mem hΩ hJ₁.1 hJJ
  obtain ⟨w₁, hw₁⟩ := hΩ.classical J₁ hJ₁.1
  obtain ⟨w₂, hw₂⟩ := hΩ.classical J₂ hJ₂.1
  obtain ⟨AK, hAKY, hAKK, hAKφ, hAKsq⟩ := exists_sqrt_member e hY hex hK hR₀ hKR hz ha hsa
  obtain ⟨AT, hATY, hATT, hATφ, hATsq⟩ := exists_sqrt_member e hY hex hT hRT hTR hzT ha' hsa'
  obtain ⟨AJ, hAJY, hAJJ, hAJφ, hAJsq⟩ := exists_sqrt_member e hY hex hJ₁ hRJ hJ₁R hw₁ hb hsb
  obtain ⟨AJ', hAJ'Y, hAJ'J, hAJ'φ, hAJ'sq⟩ :=
    exists_sqrt_member e hY hex hJ₂ hRJ' hJ₂R hw₂ hb' hsb'
  have hsqimg : ∀ {A w : G} (hA : A ∈ locLayer Ω u) (hw : w ∈ locLayer Ω u)
      {c : (modelUniv .POmegaMinus 5 p f Fact.out).K}, locElt Ω u A hA = e.φ c → A * A = w →
      locElt Ω u w hw = e.φ (c * c) := by
    intro A w hA hw c hAc hAw
    rw [map_mul, ← hAc, locElt_mul hA hA]
    exact locElt_congr _ _ hAw.symm
  have hzY : z ∈ locLayer Ω u := le_centralizingLayer hK hz.mem
  have hw₁Y : w₁ ∈ locLayer Ω u := le_centralizingLayer hJ₁ hw₁.mem
  have hw₂Y : w₂ ∈ locLayer Ω u := le_centralizingLayer hJ₂ hw₂.mem
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz.orderOf_eq_two
  have hw₁w₁ : w₁ * w₁ = 1 := mul_self_eq_one_of_orderOf_eq_two hw₁.orderOf_eq_two
  have hw₂w₂ : w₂ * w₂ = 1 := mul_self_eq_one_of_orderOf_eq_two hw₂.orderOf_eq_two
  have hφν : e.φ ν = 1 := by
    have h1 := hsqimg hAKY hzY hAKφ hAKsq
    have h2 := hsqimg hATY hzY hATφ hATsq
    rw [← haa, map_mul, ← h1, ← h2, locElt_mul hzY hzY]
    exact locElt_eq_one _ hzz
  have hww : w₂ = w₁ := by
    have h1 := hsqimg hAJY hw₁Y hAJφ hAJsq
    have h2 := hsqimg hAJ'Y hw₂Y hAJ'φ hAJ'sq
    have h3 : locElt Ω u w₁ hw₁Y * locElt Ω u w₂ hw₂Y = 1 := by
      rw [h1, h2, ← map_mul, hbb, hφν]
    have h4 : locElt Ω u w₁ hw₁Y * locElt Ω u w₁ hw₁Y = 1 := by
      rw [locElt_mul hw₁Y hw₁Y]
      exact locElt_eq_one _ hw₁w₁
    exact eq_of_locElt_eq_of_sq hP1 hw₂Y hw₁Y hw₂w₂ hw₁w₁ (mul_left_cancel (h3.trans h4.symm))
  have hPP : (AK * AT * (AJ * AJ')) * (AK * AT * (AJ * AJ')) = 1 := by
    have c1 : Commute AK AT := commute_of_commutes hKT hAKK hATT
    have c2 : Commute AJ AJ' := commute_of_commutes hJJ hAJJ hAJ'J
    have c3 : Commute (AK * AT) (AJ * AJ') :=
      ((commute_of_commutes hKJ₁ hAKK hAJJ).mul_right
        (commute_of_commutes hKJ₂ hAKK hAJ'J)).mul_left
        ((commute_of_commutes hTJ₁ hATT hAJJ).mul_right (commute_of_commutes hTJ₂ hATT hAJ'J))
    rw [← pow_two, c3.mul_pow, c1.mul_pow, c2.mul_pow, pow_two AK, pow_two AT, pow_two AJ,
      pow_two AJ', hAKsq, hATsq, hAJsq, hAJ'sq, hww, hzz, hw₁w₁, one_mul]
  have hPY : AK * AT * (AJ * AJ') ∈ locLayer Ω u :=
    (locLayer Ω u).mul_mem ((locLayer Ω u).mul_mem hAKY hATY)
      ((locLayer Ω u).mul_mem hAJY hAJ'Y)
  obtain ⟨rs, hrs, hφrs⟩ := e.exists_involution hY hβ hR₁ hβR hs
  have hsY : s ∈ locLayer Ω u := le_centralizingLayer hβ hs.mem
  have hss : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs.orderOf_eq_two
  have hPφ : e.φ (a * a' * (b * b')) = e.φ r₁ := by
    rcases hP with h | h
    · rw [h]
    · rw [h, map_mul, hφν, one_mul]
  have himg : locElt Ω u s hsY = locElt Ω u (AK * AT * (AJ * AJ')) hPY := by
    have h1 : locElt Ω u (AK * AT * (AJ * AJ')) hPY = e.φ (a * a' * (b * b')) := by
      rw [map_mul, map_mul, map_mul, ← hAKφ, ← hATφ, ← hAJφ, ← hAJ'φ, locElt_mul hAKY hATY,
        locElt_mul hAJY hAJ'Y, locElt_mul _ _]
    rw [h1, hPφ, ← hsr rs hrs.1 hrs.2]
    exact hφrs.symm
  have hsP : s = AK * AT * (AJ * AJ') := eq_of_locElt_eq_of_sq hP1 hsY hPY hss hPP himg
  have hzJ : ∀ {J : Subgroup G} {RJ : Subgroup (modelUniv .POmegaMinus 5 p f Fact.out).K},
      J ∈ centralizingMembers Ω {u} → locImg Ω u J = RJ.map e.φ →
      (∀ r ∈ R₀, orderOf r = 2 → ∀ r' ∈ RJ,
        r⁻¹ * r' ∉ Subgroup.center (modelUniv .POmegaMinus 5 p f Fact.out).K) → z ∉ J := by
    intro J RJ hJ hJR hsep hzJ
    have hmem : locElt Ω u z hzY ∈ locImg Ω u J :=
      locElt_mem_locImg (le_centralizingLayer hJ) hzJ
    rw [hJR] at hmem
    obtain ⟨r, hr, hφr⟩ := hmem
    refine hsep r₀ hr₀.1 hr₀.2 r hr (e.ker_le ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφr, hφr₀]
    exact inv_mul_cancel _
  exact ⟨J₁, J₂, w₁, AK, AT, AJ, AJ', hJ₁, hJ₂, hKJ₁, hKJ₂, hTJ₁, hTJ₂, hJJ, hJne,
    e.pair_of_model hq hΩ hP1 hβ hJ₁ hβR hJ₁R hWJ, hzJ hJ₁ hJ₁R hsepJ, hzJ hJ₂ hJ₂R hsepJ', hw₁,
    hww ▸ hw₂, hAKK, hATT, hAJJ, hAJ'J, hAKsq, hATsq, hAJsq, hAJ'sq.trans hww, hsP⟩

end Group

end CFSG.ClassicalInvolution.RouteD.TWU
