module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem commutator_le_core_of_pump (hbal : Sol78.BalanceTwoComponentInput) [Finite X]
    {c a t : X} (hc2 : c * c = 1) (hc1 : c ≠ 1) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hac : a * c = c * a) (htc : t ∈ centralizer ({c} : Set X)) {M Jc : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hJcM : Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hJcC : Jc ≤ centralizer ({t} : Set X)) (hJcperf : ⁅Jc, Jc⁆ = Jc)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤) {β : Type*} [Fintype β]
    [DecidableEq β] {k : ℕ} (hk : 9 ≤ k) (hβ : Fintype.card β = k)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup β) {r : ℕ} (hkr : k ≤ r)
    (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    (hcase : r = k ∨ (M.map (MulAut.conj t).toMonoidHom = M ∧
      IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X)))))
    (htt : t * t = 1)
    (hj : ∃ (j : X) (hjJ : j ∈ Jc), a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc ∧
      ((χ ((⟨j, hjJ⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup β) :
        Perm β).support.card ≤ 4) :
    ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype ⊓
        centralizer ({c} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  by_contra hMX
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hac
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers c) hS hT
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
  have hXNM : (pPrimeCore 2 ↥Ca).map Ca.subtype ⊓ Cc ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
  have hMtN : M.map (MulAut.conj t).toMonoidHom ≤ normalizer (M : Set X) := by
    by_cases hfix : M.map (MulAut.conj t).toMonoidHom = M
    · rw [hfix]
      exact le_normalizer
    · obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htc
      exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hMC hMtC hMpc hMtpc
        (Ne.symm hfix) hz).1
  have hJcN : Jc ≤ normalizer (M : Set X) := hJcM.trans (sup_le le_normalizer hMtN)
  have hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc) := by
    have : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have : Nontrivial (alternatingGroup β) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_eq_fintype_card]; omega)
    exact χ.toEquiv.nontrivial
  have hne := exists_ne_one_of_pump hMC hMpc htc hJcM hJcC hJcperf hJcq (by omega) hρ hJcN
  have hcase' : r = k ∨ ∃ s : X, s ∈ normalizer (M : Set X) ∧ s * s = 1 ∧ Jc ≤ M ∧
      Jc ≤ centralizer ({s} : Set X) ∧
      IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({s} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨t, mem_normalizer_iff_map_conj_eq.mpr hfix, htt, ?_, hJcC, hpc⟩
      rw [hfix, sup_idem] at hJcM
      exact hJcM
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (by omega) hkr (by omega) θM hρ hJcN hres hJcperf
    hβ χ hne hcase'
  obtain ⟨j, hjJ, haj, hjs⟩ := hj
  have hsupp := card_support_le_of_cak (by omega) hJcN hβ χ hτk ψ hψ haM hjJ haj
  have hXK := hρ.le_coreActionKernel_of_fix haM ha2 (by omega) hXNM inf_le_left
  exact hMX ((commutator_le_of_le_coreActionKernel hXK).trans
    (pPrimeCore_le_of_isPComponent hMC hMpc))

end CFSG.ComponentClassification.SolMax
