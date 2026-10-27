module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.CTIB.DistThreeProductCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster CFSG.Monster.B
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ThreeAInv


theorem orderOf_label_mul_le (p q : CVert) : orderOf (clabelS p * clabelS q) ≤ 4 := by
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hdiam := CTIB.dist_le_three_of_inputs hL (outerInput_of_ambient hamb)
    (pathInput_of_ambient hamb) (typeThreeBoundInput_of_ambient hamb)
  rcases CTIB.commute_or_three_or_four hdiam hL p q with h | ⟨-, h⟩ | ⟨-, h⟩
  · have hp2 : clabelS p * clabelS p = 1 := by
      have := pow_orderOf_eq_one (clabelS p)
      rwa [orderOf_clabelS, sq] at this
    have hq2 : clabelS q * clabelS q = 1 := by
      have := pow_orderOf_eq_one (clabelS q)
      rwa [orderOf_clabelS, sq] at this
    have h2 : (clabelS p * clabelS q) ^ 2 = 1 := by
      rw [sq]
      calc clabelS p * clabelS q * (clabelS p * clabelS q)
          = clabelS p * (clabelS q * clabelS p) * clabelS q := by simp only [mul_assoc]
        _ = clabelS p * (clabelS p * clabelS q) * clabelS q := by rw [h.eq]
        _ = 1 := by rw [← mul_assoc, hp2, one_mul, hq2]
    exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · rw [h]
    norm_num
  · rw [h]

theorem gLAPPrimeCoreOf_typeThree_eq_bot' {v w : CVert} (hw : w ∈ sphereThree v) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) = ⊥ := by
  have hfacts : cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      Subgroup.center (cnGroup v w) = ⊥ ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -, -, -, h14, -⟩ := hTT v w hw
    exact ⟨h1, h2, h10, h14⟩
  have hsimple : IsSimpleGroup (cnGroup v w) ∧ Nat.card (cnGroup v w) = 64561751654400 ∧
      commutator (cnGroup v w) = ⊤ := by
    obtain ⟨h1, -, h3, h4, -⟩ := native_three_transposition_group_simple v w hw
    exact ⟨h1, h3, h4⟩
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hinj : Function.Injective clabel := by
    have hamb := ambientRootOrbitsHyp
    exact CTIB.clabel_injective_of_inputs (labelsInput_of_ambient hamb)
      (outerInput_of_ambient hamb) (pathInput_of_ambient hamb)
      (typeThreeBoundInput_of_ambient hamb)
  obtain ⟨hHQ, hHnorm, hcenter, hCQH⟩ := hfacts
  obtain ⟨hsimp, hcardH, hcomm⟩ := hsimple
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hdi : (clabelS v)⁻¹ = clabelS v := inv_eq_of_mul_eq_one_right hd2
  have hei : (clabelS w)⁻¹ = clabelS w := inv_eq_of_mul_eq_one_right he2
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  have hinv : clabelS v * (clabelS v * clabelS w) * (clabelS v)⁻¹ =
      (clabelS v * clabelS w)⁻¹ := by
    rw [hdi, mul_inv_rev, hdi, hei, ← mul_assoc, hd2, one_mul]
  have hCQ : Subgroup.centralizer ({clabelS v} : Set Shat) ⊓
      Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat) = vStab v ⊓ vStab w := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have he : g * clabelS w = clabelS w * g := by
        have e1 : clabelS w = clabelS v * (clabelS v * clabelS w) := by
          rw [← mul_assoc, hd2, one_mul]
        rw [e1]
        calc g * (clabelS v * (clabelS v * clabelS w))
            = g * clabelS v * (clabelS v * clabelS w) := by rw [mul_assoc]
          _ = clabelS v * g * (clabelS v * clabelS w) := by rw [h1]
          _ = clabelS v * (g * (clabelS v * clabelS w)) := by rw [mul_assoc]
          _ = clabelS v * (clabelS v * clabelS w * g) := by rw [h2]
          _ = clabelS v * (clabelS v * clabelS w) * g := by simp only [mul_assoc]
      exact ⟨(CTIB.commute_clabelS_iff hinj v g).1 h1, (CTIB.commute_clabelS_iff hinj w g).1 he⟩
    · rintro ⟨h1, h2⟩
      have hd := commute_of_mem_vStab h1
      have he := commute_of_mem_vStab h2
      refine ⟨hd, ?_⟩
      calc g * (clabelS v * clabelS w) = g * clabelS v * clabelS w := by rw [mul_assoc]
        _ = clabelS v * g * clabelS w := by rw [hd]
        _ = clabelS v * (g * clabelS w) := by rw [mul_assoc]
        _ = clabelS v * (clabelS w * g) := by rw [he]
        _ = clabelS v * clabelS w * g := by rw [mul_assoc]
  have hHn : ∀ q ∈ vStab v ⊓ vStab w, ∀ h ∈ cnGroup v w, q * h * q⁻¹ ∈ cnGroup v w := by
    intro q hq h hh
    have := hHnorm.conj_mem ⟨h, hHQ hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hLQ : GLAPPrimeCoreOf 3 (vStab v ⊓ vStab w) = ⊥ := by
    refine gLAPPrimeCoreOf_eq_bot_of_isQuasisimple Nat.prime_three (L := cnGroup v w) hHQ hHn
      ⟨hcomm, MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        QuotientGroup.quotientBot)⟩ (by rw [hcardH]; norm_num) ?_
    have hbot : vStab v ⊓ vStab w ⊓ Subgroup.centralizer (cnGroup v w : Set Shat) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact hCQH g hg.1 fun h hh => (Subgroup.mem_centralizer_iff.1 hg.2 h hh).symm
    rw [hbot]
    exact IsPGroup.of_bot
  refine gLAPPrimeCoreOf_centralizer_eq_bot_of_inverting_involution Nat.prime_three (by norm_num)
    hd2 hso hinv (by rw [hCQ]; exact hLQ) ?_
  intro x y hx hy
  obtain ⟨p, rfl⟩ := CTIB.exists_clabelS_eq_of_isConj hx
  obtain ⟨q, rfl⟩ := CTIB.exists_clabelS_eq_of_isConj hy
  exact (orderOf_label_mul_le p q).trans (by norm_num)

theorem gLAPPrimeCoreOf_eq_bot_of_inverted_by_label {s : Shat} (hs : orderOf s = 3) {x : CVert}
    (hx : clabelS x * s * (clabelS x)⁻¹ = s⁻¹) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set Shat)) = ⊥ := by
  have hx2 : clabelS x * clabelS x = 1 := by
    have := pow_orderOf_eq_one (clabelS x)
    rwa [orderOf_clabelS, sq] at this
  have hodd : Odd (orderOf s) := by rw [hs]; decide
  obtain ⟨y, hy⟩ := CTIB.exists_clabelS_eq_of_isConj (isConj_mul_of_inverts_odd hx hodd)
  have hsxy : s = clabelS y * clabelS x := by rw [hy, mul_assoc, hx2, mul_one]
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hdiam := CTIB.dist_le_three_of_inputs hL (outerInput_of_ambient hamb)
    (pathInput_of_ambient hamb) (typeThreeBoundInput_of_ambient hamb)
  rcases CTIB.commute_or_three_or_four hdiam hL y x with hc | ⟨hw, -⟩ | ⟨-, h4⟩
  · exfalso
    have hy2 : clabelS y * clabelS y = 1 := by
      have := pow_orderOf_eq_one (clabelS y)
      rwa [orderOf_clabelS, sq] at this
    have h2 : s ^ 2 = 1 := by
      rw [sq, hsxy]
      calc clabelS y * clabelS x * (clabelS y * clabelS x)
          = clabelS y * (clabelS x * clabelS y) * clabelS x := by simp only [mul_assoc]
        _ = clabelS y * (clabelS y * clabelS x) * clabelS x := by rw [hc.eq]
        _ = 1 := by rw [← mul_assoc, hy2, one_mul, hx2]
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  · rw [hsxy]
    exact gLAPPrimeCoreOf_typeThree_eq_bot' hw
  · exfalso
    rw [← hsxy, hs] at h4
    exact absurd h4 (by norm_num)

theorem oPrimeCoreTrivialAt_Shat_three_of_census (hC : BThreeCensus) (hB : BThreeCentral) :
    OPrimeCoreTrivialAt 3 Shat := by
  intro s hs
  rcases hC s hs with ⟨v, w, hw, hc⟩ | h13
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    refine (gLAPPrimeCoreOf_centralizer_conj g s).1 ?_
    rw [hg]
    exact gLAPPrimeCoreOf_typeThree_eq_bot' hw
  · exact hB s hs h13

theorem oPrimeCoreTrivialAt_B_three_of_census
    (hC : BThreeCensus) (hB : BThreeCentral) :
    OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
  OPrimeCoreTrivialAt.of_mulEquiv (CTIB.iotaEquiv.trans CTIB.sEquiv)
    (oPrimeCoreTrivialAt_Shat_three_of_census hC hB)

@[expose] def BThreeUninverted : Prop :=
  ∀ s : Shat, orderOf s = 3 → (∀ x : CVert, clabelS x * s * (clabelS x)⁻¹ ≠ s⁻¹) →
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set Shat)) = ⊥

theorem oPrimeCoreTrivialAt_Shat_three_of_uninverted (h : BThreeUninverted) :
    OPrimeCoreTrivialAt 3 Shat := by
  intro s hs
  by_cases hinv : ∃ x : CVert, clabelS x * s * (clabelS x)⁻¹ = s⁻¹
  · obtain ⟨x, hx⟩ := hinv
    exact gLAPPrimeCoreOf_eq_bot_of_inverted_by_label hs hx
  · exact h s hs fun x hx => hinv ⟨x, hx⟩

theorem oPrimeCoreTrivialAt_B_three_of_uninverted
    (h : BThreeUninverted) :
    OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
  OPrimeCoreTrivialAt.of_mulEquiv (CTIB.iotaEquiv.trans CTIB.sEquiv)
    (oPrimeCoreTrivialAt_Shat_three_of_uninverted h)

end ThreeAInv

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
