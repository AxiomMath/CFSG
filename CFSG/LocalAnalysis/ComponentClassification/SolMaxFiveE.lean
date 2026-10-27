module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33O

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

@[expose] def ThompsonBurgoyneTypes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → ∀ (x y : X) (L : Subgroup X),
    UnbalancedLayer.GSUnbalancingTriple x y L →
    (∃ n : ℕ, Odd n ∧ 9 ≤ n ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)

@[expose] def SignalizerFivePumpTBInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → ∀ (c a : X) (M : Subgroup X),
    orderOf c = 2 → orderOf a = 2 → a * c = c * a → M ≤ centralizer ({c} : Set X) →
    IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
    ¬ ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype →
    (∃ n : ℕ, Odd n ∧ 9 ≤ n ∧ Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (M ⧸ pPrimeCore 2 M) .PSL 2 p f) ∨
      (Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 3 2 2)

variable {X : Type} [Group X]

theorem commutator_eq_of_core_sup_eq [Finite X] {C M D : Subgroup X} (hMC : M ≤ C)
    (hMpc : IsPComponent 2 (M.subgroupOf C)) (hDN : D ≤ normalizer (M : Set X))
    (h : (pPrimeCore 2 ↥C).map C.subtype ⊔ M = (pPrimeCore 2 ↥C).map C.subtype ⊔ ⁅M, D⁆) :
    ⁅M, D⁆ = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := (pPrimeCore 2 ↥C).map C.subtype with hOdef
  set K := ⁅M, D⁆ with hKdef
  have hKM : K ≤ M := commutator_le_left_of_le_normalizer hDN
  have hKn : (K.subgroupOf M).Normal := by
    rw [normal_subgroupOf_iff hKM]
    intro k m hk hm
    have h1 : K ≤ K.comap (MulAut.conj m).toMonoidHom := by
      rw [hKdef, commutator_le]
      intro a ha b hb
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e1 : m * ⁅a, b⁆ * m⁻¹ = ⁅m * a, b⁆ * ⁅m, b⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (commutator_mem_commutator (mul_mem hm ha) hb)
        (inv_mem (commutator_mem_commutator hm hb))
    exact h1 hk
  have hON : C ≤ normalizer (O : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥C)
  have hMO : M ⊓ O ≤ (pPrimeCore 2 ↥M).map M.subtype := by
    refine le_pPrimeCore_map inf_le_left
      (fun m hm => inf_mem_normalizer' (le_normalizer hm) (hON (hMC hm))) ?_
    have h1 : Nat.Coprime 2 (Nat.card O) := by
      rw [hOdef, card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right) h1
  have hsupM : (pPrimeCore 2 ↥M).map M.subtype ⊔ K = M := by
    refine le_antisymm (sup_le (map_subtype_le _) hKM) ?_
    intro m hm
    have hm' : m ∈ O ⊔ K := h ▸ mem_sup_right hm
    have hKO : K ≤ normalizer (O : Set X) := hKM.trans (hMC.trans hON)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left O K hKO] at hm'
    obtain ⟨o, ho, k, hk, rfl⟩ := hm'
    have hoM : o ∈ M := by
      have h1 : o = (o * k) * k⁻¹ := by group
      rw [h1]
      exact mul_mem hm (inv_mem (hKM hk))
    exact mul_mem (mem_sup_left (hMO (mem_inf.mpr ⟨hoM, ho⟩))) (mem_sup_right hk)
  set K' : Subgroup ↥M := K.subgroupOf M with hK'def
  set OM : Subgroup ↥M := pPrimeCore 2 ↥M with hOMdef
  have hsup' : OM ⊔ K' = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, hK'def, map_subgroupOf_eq_of_le hKM, hsupM, ← MonoidHom.range_eq_map,
      range_subtype]
  have hidx : Odd K'.index := by
    have h1 : K'.index = K'.relIndex OM := by
      rw [← relIndex_top_right, ← hsup', relIndex_sup_right]
    rw [h1]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (index_dvd_card (K'.subgroupOf OM))
  have hres := primeResidual_eq_top_of_isPComponent hMC hMpc
  have htop : K' = ⊤ := by
    rw [eq_top_iff, ← hres]
    exact CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 K'
      (Nat.coprime_two_left.mpr hidx)
  apply le_antisymm hKM
  intro m hm
  have h1 : (⟨m, hm⟩ : ↥M) ∈ K' := htop ▸ mem_top _
  exact h1

theorem gsUnbalancingTriple_of_not_balanced [Finite X] (hbal : Sol78.BalanceTwoComponentInput)
    {c a : X} (hc : orderOf c = 2) (hao : orderOf a = 2) (hac : a * c = c * a) {M : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hMX : ¬ ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype) :
    UnbalancedLayer.GSUnbalancingTriple c a M := by
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
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
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
  obtain ⟨haN', hOX, hOM⟩ := hcc hMX
  have haM : a ∈ normalizer (M : Set X) := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp haN'
    obtain ⟨hga, hgN⟩ := mem_inf.mp hg
    rcases eq_one_or_eq_of_mem_zpowers ha2 hga with h | h
    · exact absurd (Subtype.ext h) hg1
    · exact h ▸ hgN
  have hXNM := le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN
  have hzN : zpowers a ⊓ normalizer (M : Set X) = zpowers a :=
    inf_eq_left.mpr (zpowers_le.mpr haM)
  rw [hzN] at hOM
  rw [UnbalancedLayer.gsUnbalancingTriple_iff]
  exact ⟨hc, hao, hac.symm, hMC, hMpc,
    commutator_eq_of_core_sup_eq hMC hMpc (zpowers_le.mpr haM) hOM,
    commutator_eq_of_core_sup_eq hMC hMpc hXNM hOX⟩

theorem signalizerFivePumpTBInput_of_types (hbal : Sol78.BalanceTwoComponentInput)
    (hTB : ThompsonBurgoyneTypes) : SignalizerFivePumpTBInput := by
  intro X _ _ _ hnab hKP hunb hnU c a M hc hao hac hMC hMpc hMX
  exact hTB X hnab hKP hunb hnU c a M
    (gsUnbalancingTriple_of_not_balanced hbal hc hao hac hMC hMpc hMX)

end CFSG.ComponentClassification.SolMax
