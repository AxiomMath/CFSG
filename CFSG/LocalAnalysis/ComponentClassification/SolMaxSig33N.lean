module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33L

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem exists_balanced_pump (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) {c e₀ : X}
    (hcB : c ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X)) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hc : orderOf c = 2) (he₀ : e₀ ∈ J)
    (he₀2 : e₀ * e₀ = 1) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hk9' : 9 ≤ n - (coreImage θ he₀).support.card)
    (hτc : ∀ (e : X) (he : e ∈ E), coreImage θ (S.le he) * coreImage θ he₀ =
      coreImage θ he₀ * coreImage θ (S.le he))
    (hdich : (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).support) ∨
      (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).supportᶜ)) :
    ∃ Jc M : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) ∧
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) ∧
      M ≤ centralizer ({c} : Set X) ∧ IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) ∧
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M ∧
      (∀ (g : X) (hgN : g ∈ normalizer (J : Set X)), g * c = c * g →
        (∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ →
          (coreImage θ ((mem_normalizer_iff.mp hgN x).mp hx)).support ⊆
            (coreImage θ he₀).supportᶜ) →
        g ∈ normalizer (Jc : Set X)) ∧
      ∀ a ∈ E ⊔ zpowers y, a ≠ 1 →
        ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype ∧
        ⁅M.map (MulAut.conj t).toMonoidHom, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have htcC : t ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr htc
  obtain ⟨Jc, hJcJ, hJcpc, hinv, hsubP, χ, hχ⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 θ hcN hc2 he₀ hce (by omega)
  have hτ₀2 : coreImage θ he₀ * coreImage θ he₀ = 1 := by
    have h1 : (⟨e₀, he₀⟩ : ↥J) * ⟨e₀, he₀⟩ = 1 := Subtype.ext he₀2
    have h2 : θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  have hev : 2 ∣ (coreImage θ he₀).support.card :=
    Perm.two_dvd_card_support (by rw [sq]; exact hτ₀2)
  set k := n - (coreImage θ he₀).support.card with hkdef
  have hk9 : 9 ≤ k := by omega
  have hkodd : Odd k := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    obtain ⟨b, hb⟩ := hev
    exact ⟨a - b, by omega⟩
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin k) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans S.pair.1.2.1
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf hJcCt (hJcJ.trans inf_le_right)
  obtain ⟨M, r, hMC, hMpc, hJcM, hr, hkr, hrn, ⟨θM⟩, hcase⟩ :=
    exists_pump_data hPump hN1 S.nonab S.kProper S.unbal S.notU S.pair.2.2.2.1 hc S.pair.1.1
      htcC hJcC hJcpc hk9 hkodd eJc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  obtain ⟨hMtC, hMtpc, hJcMt, ⟨θMt⟩, hcaset⟩ :=
    pump_data_conj S.t_mul_self htcC hMC hMpc hJcM ⟨θM⟩ hcase
  have hJcK : ¬ Jc ≤ UnbalancedLayer.coreActionKernel M := by
    intro hK
    obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
    have hMtN : M.map (MulAut.conj t).toMonoidHom ≤ normalizer (M : Set X) := by
      by_cases hfix : M.map (MulAut.conj t).toMonoidHom = M
      · rw [hfix]
        exact le_normalizer
      · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hMC hMtC hMpc hMtpc
          (Ne.symm hfix) hz).1
    have hJcN : Jc ≤ normalizer (M : Set X) := hJcM.trans (sup_le le_normalizer hMtN)
    have hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc) := by
      have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have : Nontrivial (alternatingGroup (Fin k)) :=
        alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
      exact eJc.toEquiv.nontrivial
    obtain ⟨z, hz⟩ := exists_ne_one_of_pump hMC hMpc htcC hJcM hJcCt hJcperf hJcq (by omega) hρ
      hJcN
    exact hz (hρ.eq_one_of_mem_coreActionKernel (by omega) (hK z.2))
  refine ⟨Jc, M, hJcJ, hinv, hMC, hMpc, hJcM, hJcK, fun g hgN hgc hgs =>
    mem_normalizer_of_fixed_component θ (hJcJ.trans inf_le_right) hres hinv hsubP hgN hgc hgs,
    fun a ha ha1 => ⟨?_, ?_⟩⟩
  · have hj := S.exists_acts_like hcB he₀ hJcJ hinv hsubP hres hτc hdich χ hχ ha
    exact commutator_le_core_of_pump hbal hc2 hc1 (S.mul_self_of_mem ha) ha1
      (mem_centralizer_iff.mp hcB a ha) htcC hMC hMpc hJcM hJcCt hJcperf hres hk9 hβ χ hkr θM
      hcase S.t_mul_self hj
  · have hj := S.exists_acts_like hcB he₀ hJcJ hinv hsubP hres hτc hdich χ hχ ha
    exact commutator_le_core_of_pump hbal hc2 hc1 (S.mul_self_of_mem ha) ha1
      (mem_centralizer_iff.mp hcB a ha) htcC hMtC hMtpc hJcMt hJcCt hJcperf hres hk9 hβ χ hkr θMt
      hcaset S.t_mul_self hj

abbrev PumpOracle : Prop :=
  ∀ {c e₀ : X}, c ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X) → t * c = c * t →
    c ∈ normalizer (J : Set X) → orderOf c = 2 → ∀ (he₀ : e₀ ∈ J), e₀ * e₀ = 1 →
    c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J → (coreImage θ he₀).support.card ≤ 4 →
    (∀ (e : X) (he : e ∈ E), coreImage θ (S.le he) * coreImage θ he₀ =
      coreImage θ he₀ * coreImage θ (S.le he)) →
    ((∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).support) ∨
      (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).supportᶜ)) →
    ∃ Jc M : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) ∧
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) ∧
      M ≤ centralizer ({c} : Set X) ∧ IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) ∧
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M ∧
      (∀ (g : X) (hgN : g ∈ normalizer (J : Set X)), g * c = c * g →
        (∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ →
          (coreImage θ ((mem_normalizer_iff.mp hgN x).mp hx)).support ⊆
            (coreImage θ he₀).supportᶜ) →
        g ∈ normalizer (Jc : Set X)) ∧
      ∀ a ∈ E ⊔ zpowers y, a ≠ 1 →
        ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype ∧
        ⁅M.map (MulAut.conj t).toMonoidHom, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype

theorem pumpOracle_of_large (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n) :
    S.PumpOracle := by
  intro c e₀ hcB htc hcN hc he₀ he₀2 hce hs4 hτc hdich
  exact S.exists_balanced_pump hbal hPump hN1 hcB htc hcN hc he₀ he₀2 hce (by omega) hτc hdich

end Sol33

end CFSG.ComponentClassification.SolMax
