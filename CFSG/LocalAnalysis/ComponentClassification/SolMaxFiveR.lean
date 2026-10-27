module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_compl_support_ne_three {σ : Perm (Fin 9)} (hσ : σ * σ = 1)
    (hA : σ ∈ alternatingGroup (Fin 9)) : σ.supportᶜ.card ≠ 3 := by
  classical
  intro h3
  have h6 : σ.support.card = 6 := by
    have h1 : σ.supportᶜ.card = 9 - σ.support.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h2 : σ.support.card ≤ 9 := by
      have := Finset.card_le_univ σ.support
      rwa [Fintype.card_fin] at this
    omega
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hσ)
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 := (Perm.dvd_of_mem_cycleType hn).trans hord
    have h2 := Perm.two_le_of_mem_cycleType hn
    have h3 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.cycleType.sum = 6 := by rw [Perm.sum_cycleType, h6]
  have hcard : Multiset.card σ.cycleType = 3 := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  have hsign := Perm.sign_of_cycleType σ
  rw [hsum, hcard, Odd.neg_one_pow (by decide : Odd (6 + 3))] at hsign
  have h1 : Perm.sign σ = 1 := Perm.mem_alternatingGroup.mp hA
  rw [h1] at hsign
  exact absurd hsign (by decide)

variable {X : Type} [Group X]

theorem inf_le_normalizer_of_balance (hbal : Sol78.BalanceTwoComponentInput) [Finite X]
    {a c : X} (hao : orderOf a = 2) (hc : orderOf c = 2) (hac : a * c = c * a)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) :
    (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype ⊓
      centralizer ({c} : Set X) ≤ normalizer (M : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hac
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers c) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact ha2))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hc2)) hST
  have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = centralizer ({c} : Set X) :=
    centralizer_zpowers_eq' c
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) :=
    centralizer_zpowers_eq' a
  rw [hCc', hCa'] at hbc
  obtain ⟨hXN, -⟩ := hbc M ⟨hMC, hMpc⟩
  exact le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN

theorem exists_seven_pump_of_beta
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) {c a β : X} (hc : orderOf c = 2) (hao : orderOf a = 2)
    (hac : a * c = c * a) {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hMX : ¬ ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype)
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)} (hρ : IsPermAction θM ρ) (haMm : a ∈ M)
    (haM : a ∈ normalizer (M : Set X)) (h3 : (ρ ⟨a, haM⟩).supportᶜ.card = 3)
    (hβo : orderOf β = 2) (hβc : β * c = c * β) (hβa : β * a = a * β)
    (hβM : β ∈ normalizer (M : Set X)) (hρβ : ρ ⟨β, hβM⟩ = 1) :
    ∃ M' : Subgroup X, M' ≤ centralizer ({β} : Set X) ∧
      IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))) ∧
      GSLit.fixedLayer M (zpowers β) ≤ M' ⊔ M'.map (MulAut.conj c).toMonoidHom ∧
      IsPComponent 2 ((GSLit.fixedLayer M (zpowers β)).subgroupOf
        ((M' ⊔ M'.map (MulAut.conj c).toMonoidHom) ⊓ centralizer ({c} : Set X))) ∧
      Nonempty (↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Cβ : Subgroup X := centralizer ({β} : Set X) with hCβdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have hβ2 : β * β = 1 := by rw [← sq, ← hβo, pow_orderOf_eq_one]
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβo
    omega
  have hρa1 : ρ ⟨a, haM⟩ ≠ 1 := by
    intro h
    rw [h, Perm.support_one, Finset.compl_empty, Finset.card_univ, Fintype.card_fin] at h3
    omega
  have hOaodd : Odd (Nat.card Oa) := by
    rw [hOadef, card_map_of_injective Ca.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOaC : Oa ≤ Ca := map_subtype_le _
  have hX₀N : Oa ⊓ Cc ≤ normalizer (M : Set X) :=
    inf_le_normalizer_of_balance hbal hao hc hac hMC hMpc
  have hX₀K : ¬ Oa ⊓ Cc ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hMX ((commutator_le_of_le_coreActionKernel h).trans (pPrimeCore_le_of_isPComponent hMC hMpc))
  obtain ⟨x, hxX₀, hxK⟩ : ∃ x ∈ Oa ⊓ Cc, x ∉ UnbalancedLayer.coreActionKernel M := by
    by_contra h
    push Not at h
    exact hX₀K h
  have hx1 : ρ ⟨x, hX₀N hxX₀⟩ ≠ 1 := fun h => hxK (hρ.mem_coreActionKernel _ h)
  have hX₀odd : Odd (Nat.card ↥(Oa ⊓ Cc)) := hOaodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hβCa : β ∈ Ca := mem_centralizer_singleton_iff.mpr hβa
  have hβCc : β ∈ Cc := mem_centralizer_singleton_iff.mpr hβc
  have hβX₀ : zpowers β ≤ normalizer ((Oa ⊓ Cc : Subgroup X) : Set X) :=
    zpowers_le.mpr (inf_mem_normalizer' (le_normalizer_pPrimeCore (le_normalizer hβCa))
      (le_normalizer hβCc))
  have hβN : zpowers β ≤ normalizer (M : Set X) := zpowers_le.mpr hβM
  have hA1 : ∀ (g : X) (hg : g ∈ zpowers β), ρ ⟨g, hβN hg⟩ = 1 := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have h1 : (⟨β ^ k, hβN hg⟩ : ↥(normalizer (M : Set X))) = ⟨β, hβM⟩ ^ k := rfl
    rw [h1, map_zpow, hρβ, one_zpow]
  obtain ⟨x', hx'X₀, hx'β, hx'1⟩ := exists_centralizing_of_ne_one hX₀N hX₀odd
    (isPGroup_zpowers_of_mul_self hβ2) hβX₀ hβN hA1 hxX₀ hx1
  have hx'β' : x' * β = β * x' := (mem_centralizer_iff.mp hx'β β (mem_zpowers β)).symm
  have hx'Oa : x' ∈ Oa := (mem_inf.mp hx'X₀).1
  have hx'Cc : x' ∈ Cc := (mem_inf.mp hx'X₀).2
  have hx'Cβ : x' ∈ Cβ := mem_centralizer_singleton_iff.mpr hx'β'
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M Cc hMC).mp hMpc).2.2
  have hMsub : (M.subgroupOf Cc).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers β ≤ UnbalancedLayer.coreActionKernel M :=
    zpowers_le.mpr (hρ.mem_coreActionKernel hβM hρβ)
  have hE2 : IsPGroup 2 (zpowers β) := isPGroup_zpowers_of_mul_self hβ2
  have hEX : zpowers β ≤ Cc := zpowers_le.mpr hβCc
  have hCE : centralizer ((zpowers β : Subgroup X) : Set X) = Cβ := centralizer_zpowers_eq' β
  set L := GSLit.fixedLayer M (zpowers β) with hLdef
  have hLpc := GSLit.fixedLayer_isPComponent hMC hMsub hEX hE hE2 hMq
  rw [hCE, inf_comm] at hLpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers β)
  rw [hCE] at hle
  have hLM : L ≤ M := hle.trans inf_le_left
  have hLY : L ≤ Cβ ⊓ Cc := fun z hz => mem_inf.2 ⟨(mem_inf.1 (hle hz)).2, hMC (hLM hz)⟩
  obtain ⟨hsup, hcoreL⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  obtain ⟨θL, -⟩ := exists_coreQuot_of_sup hLM hsup θM
  have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hLY hLpc
  have hLq : Nontrivial (↥L ⧸ pPrimeCore 2 ↥L) := by
    have : Nontrivial (alternatingGroup (Fin 7)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact θL.toEquiv.nontrivial
  have hcl := GSLit.fixedLayer_eq_closure hMq hE hE2
  have haβ : a ∈ centralizer ((zpowers β : Subgroup X) : Set X) := by
    rw [hCE]
    exact mem_centralizer_singleton_iff.mpr hβa.symm
  have haL : a ∈ L := by
    rw [hLdef, hcl]
    exact subset_closure ⟨mem_inf.2 ⟨haMm, haβ⟩, 1, by rw [pow_one]; exact hao⟩
  have hx'L : x' ∈ normalizer (L : Set X) :=
    mem_normalizer_fixedLayer hMq hE hE2 (hX₀N hx'X₀) hx'β'
  have hcore : (pPrimeCore 2 ↥L).map L.subtype ≤ (pPrimeCore 2 ↥M).map M.subtype := by
    rw [hcoreL]
    exact inf_le_right
  have hfin : ∀ M' : Subgroup X, L ≤ M' → x' ∈ UnbalancedLayer.coreActionKernel M' → False := by
    intro M' hLM' hK'
    have h1 := mem_coreActionKernel_of_le hLM' hK' hx'L
    have h2 := mem_coreActionKernel_of_fixedLayer hMC hMpc hLM hLperf hLq hsup hcore hx'Cc h1
    exact hx'1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) h2)
  have haK : ∀ M' : Subgroup X, L ≤ M' → a ∉ UnbalancedLayer.coreActionKernel M' := by
    intro M' hLM' hK'
    have h1 := mem_coreActionKernel_of_le hLM' hK' (le_normalizer haL)
    have h2 := mem_coreActionKernel_of_fixedLayer hMC hMpc hLM hLperf hLq hsup hcore
      (mem_centralizer_singleton_iff.mpr hac) h1
    exact hρa1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) h2)
  have hX'odd : Odd (Nat.card ↥(Oa ⊓ Cβ)) := hOaodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hX'a : Oa ⊓ Cβ ≤ centralizer ({a} : Set X) := inf_le_left.trans hOaC
  have hX'n : ∀ g ∈ centralizer ({a} : Set X) ⊓ Cβ, ∀ y ∈ Oa ⊓ Cβ, g * y * g⁻¹ ∈ Oa ⊓ Cβ := by
    intro g hg y hy
    have h1 : g ∈ normalizer ((Oa ⊓ Cβ : Subgroup X) : Set X) :=
      inf_mem_normalizer' (le_normalizer_pPrimeCore (le_normalizer (mem_inf.1 hg).1))
        (le_normalizer (mem_inf.1 hg).2)
    exact (mem_normalizer_iff.mp h1 y).mp hy
  have hK : SectionRank.IsKGroupCat ↥Cβ :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP (centralizer_ne_top_of_ne_one hnab hβ1)
  have hcβ : c ∈ Cβ := mem_centralizer_singleton_iff.mpr hβc.symm
  obtain ⟨M', hM'Y, hM'pc, hLM', hLM'pc, htype⟩ :=
    pump_type_in hPump hK hcβ hc hLY hLpc (by decide) le_rfl θL
  have hT : zpowers β ≠ ⊥ := fun h => hβ1 (zpowers_eq_bot.mp h)
  have hβc' : β * a = a * β := hβa
  rcases htype with ⟨hfix', ⟨m', hm', hm'7, eM'⟩ | ⟨-, ⟨ψ⟩⟩⟩ | ⟨-, eM'⟩
  · have hLM'' : L ≤ M' := by
      have h1 := hLM'
      rwa [hfix', sup_idem] at h1
    by_cases hm9 : 9 ≤ m'
    ·
      exfalso
      have hM'Y' : M' ≤ centralizer ((zpowers β : Subgroup X) : Set X) := by
        rw [hCE]
        exact hM'Y
      have hM'pc' : IsPComponent 2
          (M'.subgroupOf (centralizer ((zpowers β : Subgroup X) : Set X))) := by
        rw [hCE]
        exact hM'pc
      have hZ := hN1 X hnab hKP hunb hnU (zpowers β) m' M' hT hE2 hm' hm9 hM'Y' hM'pc' eM'
      obtain ⟨eM''⟩ := eM'
      have θ' : ↥M' ⧸ pPrimeCore 2 ↥M' ≃* alternatingGroup (Fin m') :=
        (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eM''
      have hle9 : m' ≤ 9 := hpair.2.2.2.1 β M' m' ⟨hβo, hM'Y, hM'pc, ⟨θ'⟩⟩ hm'
      have h9 : m' = 9 := le_antisymm hle9 hm9
      subst h9
      obtain ⟨ρ', hρ'⟩ := exists_isPermAction (M := M') (by norm_num) (by norm_num) θ'
      have haM'm : a ∈ M' := hLM'' haL
      have haM' : a ∈ normalizer (M' : Set X) := le_normalizer haM'm
      have hρ'a2 : ρ' ⟨a, haM'⟩ * ρ' ⟨a, haM'⟩ = 1 := by
        rw [← map_mul]
        convert map_one ρ'
        exact Subtype.ext ha2
      have hρ'aA : ρ' ⟨a, haM'⟩ ∈ alternatingGroup (Fin 9) := by
        rw [hρ'.apply_of_mem (by norm_num) ⟨a, haM'm⟩]
        exact (θ' _).2
      have hX'N := inf_le_normalizer_of_balance hbal hao hβo hβc'.symm hM'Y hM'pc
      have hX'K := le_coreActionKernel_of_alt_ne_three (by decide) hρ' haM' ha2
        (card_compl_support_ne_three hρ'a2 hρ'aA) hX'N inf_le_left
      exact hfin M' hLM'' (hX'K (mem_inf.2 ⟨hx'Oa, hx'Cβ⟩))
    ·
      have h7 : m' = 7 := by
        obtain ⟨j, hj⟩ := hm'
        omega
      subst h7
      exact ⟨M', hM'Y, hM'pc, hLM', hLM'pc, eM'⟩
  ·
    exfalso
    have hLM'' : L ≤ M' := by
      have h1 := hLM'
      rwa [hfix', sup_idem] at h1
    have hM'perf : ⁅M', M'⁆ = M' := UnbalancedCorr.commutator_eq_of_isPComponent hM'Y hM'pc
    have haM'm : a ∈ M' := hLM'' haL
    have hX'N := inf_le_normalizer_of_balance hbal hao hβo hβc'.symm hM'Y hM'pc
    have hX'K := le_coreActionKernel_of_held_pump hM'Y hM'perf ψ haM'm (le_normalizer haM'm) ha2
      (by rw [inv_mul_cancel]; exact one_mem _) (haK M' hLM'') hX'odd hX'N hX'a hX'n
    exact hfin M' hLM'' (hX'K (mem_inf.2 ⟨hx'Oa, hx'Cβ⟩))
  · exact ⟨M', hM'Y, hM'pc, hLM', hLM'pc, eM'⟩

end CFSG.ComponentClassification.SolMax
