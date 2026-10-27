module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeP
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2C
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol78Bridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Base

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SignalizerFivePumpLTwoInnerInput : Prop :=
  SignalizerFivePumpExactCaseInput fun X _ M a =>
    Blueprint.LieModel (M ⧸ pPrimeCore 2 M) .PSL 2 5 2 ∧
      ∃ (ha : a ∈ normalizer (M : Set X)) (m : M ⧸ pPrimeCore 2 M), m ≠ 1 ∧
        TBLit.oddQuotAction M ⟨a, ha⟩ = MulAut.conj m

theorem signalizerFivePumpLTwoInput_of_inner
    (hres : SignalizerFivePumpLTwoInnerInput) : SignalizerFivePumpLTwoInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, hp2, hf, h5, hL⟩ := hP
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    AutL2Facts.isOddPrimePower_of hp hp2 hf hF
  have hF4 : 4 ≤ Nat.card F := by omega
  have : IsSimpleGroup (GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  have : IsSimpleGroup (↥M ⧸ pPrimeCore 2 ↥M) := e.isSimpleGroup
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
  have hJcM' : Jc ≤ M := by
    have h1 := hJcM
    rwa [hfix, sup_idem] at h1
  have hJcMpc' : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
    have h1 := hJcMpc
    rwa [hfix, sup_idem] at h1
  have hJcY : Jc ≤ M ⊓ centralizer ({t} : Set X) :=
    le_inf hJcM' ((hJcJ.trans inf_le_left).trans hpair.1.2.1)
  have hD5 : Nat.card ((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  have : Nontrivial ((coreImage θ he₀).supportᶜ : Finset (Fin 9)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD5]
    norm_num
  have : IsSimpleGroup (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 9))) :=
    alternatingGroup.isSimpleGroup (by rw [hD5])
  have hA60 : Nat.card (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = 60 := by
    rw [nat_card_alternatingGroup, hD5]
    rfl
  set st := TBLit.oddQuotAction M ⟨t, htN⟩ with hstdef
  have hst : st * st = 1 := by
    rw [hstdef, ← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (M : Set X)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [h1, map_one]
  have hst1 : st ≠ 1 := fun h1 =>
    hcov (FiveFL2.sup_pPrimeCore_eq_of_oddQuotAction_eq_one htN ht2 h1 hJcY hJcMpc' χ)
  have hS := FiveFHe.hasOddA_fixedSubgroup_oddQuotAction htN ht2 hJcY hJcMpc' χ
  set αt := MulAut.congr e st with hαtdef
  have hαt2 : αt * αt = 1 := by rw [hαtdef, ← map_mul, hst, map_one]
  have hαt1 : αt ≠ 1 := fun h1 => hst1 ((MulAut.congr e).injective (by rw [← hαtdef, h1, map_one]))
  have hS' := hS.of_mulEquiv (((fixedSubgroup st).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (FiveFHe.map_fixedSubgroup_congr e st)))
  obtain ⟨h25, hrt⟩ := FiveFL2.card_eq_25_of_hasOddA hpp hαt2 hαt1 hA60 hS'
  have hp5 : p = 5 := by
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    rw [← hF, h25, show (25 : ℕ) = 5 * 5 by norm_num] at h2
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h <;>
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
  subst hp5
  have hf2 : f = 2 := by
    have h1 : 5 ^ f = 5 ^ 2 := by
      rw [← hF, h25]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1
  subst hf2
  by_contra hMX
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oc := (pPrimeCore 2 ↥Cc).map Cc.subtype with hOcdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hao
    omega
  have hS₀ : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hac
  obtain ⟨-, hbc, -⟩ := Sol78.balanceTwoComponentInput_holds X (zpowers a) (zpowers c) hS₀ hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact ha2))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hc2)) hST
  have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = Cc := centralizer_zpowers_eq' c
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = Ca := centralizer_zpowers_eq' a
  rw [hCc', hCa'] at hbc
  obtain ⟨hXN, hcc⟩ := hbc M ⟨hMC, hMpc⟩
  obtain ⟨haN', -, -⟩ := hcc hMX
  have haM : a ∈ normalizer (M : Set X) := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp haN'
    obtain ⟨hga, hgN⟩ := mem_inf.mp hg
    rcases eq_one_or_eq_of_mem_zpowers ha2 hga with h | h
    · exact absurd (Subtype.ext h) hg1
    · exact h ▸ hgN
  have hOMC : (pPrimeCore 2 ↥M).map M.subtype ≤ Oc := pPrimeCore_le_of_isPComponent hMC hMpc
  have hXNM : Oa ⊓ Cc ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN
  have hX : ¬ Oa ⊓ Cc ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hMX ((commutator_le_of_le_coreActionKernel h).trans hOMC)
  have hCaN : Ca ≤ normalizer (Oa : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca)
  have hXn : ∀ g ∈ Ca ⊓ Cc, ∀ x ∈ Oa ⊓ Cc, g * x * g⁻¹ ∈ Oa ⊓ Cc := by
    intro g hg x hx
    obtain ⟨hga, hgc⟩ := mem_inf.mp hg
    obtain ⟨hxa, hxc⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCaN hga) x).mp hxa,
      mul_mem (mul_mem hgc hxc) (inv_mem hgc)⟩
  have hXodd : Odd (Nat.card ↥(Oa ⊓ Cc)) := by
    have h1 : Odd (Nat.card Oa) := by
      rw [hOadef, card_map_of_injective Ca.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hXa : Oa ⊓ Cc ≤ Ca := inf_le_left.trans (map_subtype_le _)
  have hinner : ∀ φ : MulAut (↥M ⧸ pPrimeCore 2 ↥M), Odd (orderOf φ) → ∃ g, φ = MulAut.conj g :=
    fun φ hφ => FiveFL2.exists_eq_conj_of_odd_psl2_sq Nat.prime_five hF e φ hφ
  have hconj := FiveFL2.conj_injective_psl2 e
  set sa := TBLit.oddQuotAction M ⟨a, haM⟩ with hsadef
  have hsa : sa * sa = 1 := by
    rw [hsadef, ← map_mul]
    have h1 : (⟨a, haM⟩ : normalizer (M : Set X)) * ⟨a, haM⟩ = 1 := Subtype.ext ha2
    rw [h1, map_one]
  have hcomm : sa * st = st * sa := by
    rw [hsadef, hstdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hat
  have hstL : st ∉ FooteLit.Aut5L2.linL2 e := hrt
  by_cases hsaL : (AutL2Facts.autEquiv e sa).right = 1
  ·
    have hsaI : sa ∈ Foote5.innAut5 (↥M ⧸ pPrimeCore 2 ↥M) := by
      by_contra hI
      exact FooteLit.Aut5L2.not_commute_l2 e Nat.prime_five (by norm_num) hF sa st hsaL hI hstL
        hst hcomm
    obtain ⟨m, hm⟩ := hsaI
    by_cases hm1 : m = 1
    ·
      have hsa1 : sa = 1 := by rw [← hm, hm1, map_one]
      have hO : pPrimeCore 2 (fixedSubgroup (TBLit.oddQuotAction M ⟨a, haM⟩)) = ⊥ := by
        rw [← hsadef, hsa1]
        have htop : fixedSubgroup (1 : MulAut (↥M ⧸ pPrimeCore 2 ↥M)) = ⊤ :=
          eq_top_iff.2 fun g _ => rfl
        have h1 := pPrimeCore_map_iso 2 ((MulEquiv.subgroupCongr htop).trans topEquiv)
        rw [FiveFL2.pPrimeCore_eq_bot_psl2 hpp hF4 e,
          map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h1
        exact h1
      exact hX (FiveFL2.le_coreActionKernel_of_fixed_pPrimeCore hMC haM ha2 hinner hconj hO
        hXodd hXNM hXa hXn)
    ·
      exact hMX (hres X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc
        hinv hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
        ⟨hL, haM, m, hm1, hm.symm⟩)
  ·
    have hαa2 : MulAut.congr e sa * MulAut.congr e sa = 1 := by rw [← map_mul, hsa, map_one]
    have hO' := FiveFL2.pPrimeCore_fixedSubgroup_field hpp (MulAut.congr e sa) hαa2 hsaL
    have hO : pPrimeCore 2 (fixedSubgroup (TBLit.oddQuotAction M ⟨a, haM⟩)) = ⊥ := by
      rw [← hsadef]
      have h1 := pPrimeCore_map_iso 2 (((fixedSubgroup sa).equivMapOfInjective e.toMonoidHom
        e.injective).trans (MulEquiv.subgroupCongr (FiveFHe.map_fixedSubgroup_congr e sa)))
      rw [hO', map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h1
      exact h1
    exact hX (FiveFL2.le_coreActionKernel_of_fixed_pPrimeCore hMC haM ha2 hinner hconj hO
      hXodd hXNM hXa hXn)

end CFSG.ComponentClassification.SolMax
