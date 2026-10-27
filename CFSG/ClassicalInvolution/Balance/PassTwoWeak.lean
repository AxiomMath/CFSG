module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceWeakFrame
public import CFSG.ClassicalInvolution.Balance.SL2
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.SmallCases.FrameRank

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

section Data

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

theorem weakPreFrame_isElemAbelian (Fr : WeakPreFrame F Ω E S) : IsElemAbelian 2 E :=
  ⟨weak_isMulCommutative Fr, fun x hx => by rw [pow_two]; exact Fr.elem x hx⟩

theorem WeakPreFrame.exists_weakMember (Fr : WeakPreFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) :
    ∃ z ∈ E, WeakMember F K z := by
  obtain ⟨z, hz, hzE⟩ := (Fr.weakInSigma hK).member
  exact ⟨z, hzE, hz⟩

variable [Finite G]

theorem exists_card_eight_of_weakFrame (Fr : WeakPreFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsCentralInvolution L₀ z₀)
    (ht : t ∈ axisSub E L₀) :
    ∃ E₀ : Subgroup G, E₀ ≤ axisSub E L₀ ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧ z₀ ∈ E₀ ∧
      t ∈ E₀ := by
  have := Fr.finite
  exact exists_card_eight_of_relIndex_two (weakPreFrame_isElemAbelian Fr) inf_le_left
    (Fr.weakInSigma hL₀).index_two h16 (Fr.mem_axisSub_of_central hL₀ hz₀) ht

end Data

section TheoremQ

variable {F : Type*} [Field F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem WeakMember.data {K : Subgroup G} {z : G} (h : WeakMember F K z) [Finite F]
    (h4 : 4 ≤ Nat.card F) :
    commutator K = ⊤ ∧ K ≠ ⊥ ∧ CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) := by
  have hm := IsInvolutionMember.of_weakMember h h4
  refine ⟨hm.perfect, ?_, hm.quasisimple⟩
  have hc := h.isCentralInvolution
  intro hbot
  have := hc.mem
  rw [hbot, Subgroup.mem_bot] at this
  exact hc.ne_one this

theorem isQuasisimple_of_weakFrame (Fr : WeakPreFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : WeakMember F L₀ z₀)
    (ht : t ∈ axisSub E L₀) {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hL₀K : L₀ ≤ K)
    (hB : ∀ f ∈ axisSub E L₀, f ≠ 1 →
      ∀ M : Subgroup ↥(imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})),
        TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
          ⁅M.map (imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})).subtype,
            imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  have := Fr.finite
  have hc := hz₀.isCentralInvolution
  have h4 : 4 ≤ Nat.card F := by have := Fr.five; omega
  obtain ⟨hperf, hne, hq⟩ := hz₀.data h4
  obtain ⟨E₀, hE₀L, hE₀, hcard, hz₀E, htE⟩ := exists_card_eight_of_weakFrame Fr h16 hL₀ hc ht
  have hE₀E : E₀ ≤ E := hE₀L.trans inf_le_left
  have hE₀C : E₀ ≤ Subgroup.centralizer ({t} : Set G) := fun e he =>
    mem_centralizer_singleton_of_isElemAbelian hE₀ htE he
  have hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((mem_axisSub_iff.mp (hE₀L he)).2 l hl).symm
  have hL₀t : L₀ ≤ Subgroup.centralizer ({t} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_axisSub_iff.mp ht).2 l hl
  exact isQuasisimple_of_isTwoComponent_of_layer_of_centralizes hKC hK hE₀C hE₀ hcard hL₀K hL₀E
    hperf hne (deltaCore_eq_bot_of_le hE₀E hΔ)
    (isSubnormal_inf_centralizer_of_isSubnormal hz₀E (le_inf hL₀t hL₀E) hz₀.subnormal) hq
    fun f hf hf1 => hB f (hE₀L hf) hf1

theorem isQuasisimple_of_weakFrame_central (Fr : WeakPreFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ : G} (hz₀ : WeakMember F L₀ z₀)
    (hB : ∀ f ∈ axisSub E L₀, f ≠ 1 →
      ∀ M : Subgroup ↥(imageModOddCore f (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer {f})),
        TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
          ⁅M.map (imageModOddCore f (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer {f})).subtype,
            imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple L₀ := by
  have := Fr.finite
  have hc := hz₀.isCentralInvolution
  have h4 : 4 ≤ Nat.card F := by have := Fr.five; omega
  obtain ⟨hperf, hne, hq⟩ := hz₀.data h4
  have hzaxis : z₀ ∈ axisSub E L₀ := Fr.mem_axisSub_of_central hL₀ hc
  obtain ⟨E₀, hE₀L, hE₀, hcard, hz₀E, -⟩ := exists_card_eight_of_weakFrame Fr h16 hL₀ hc hzaxis
  have hE₀E : E₀ ≤ E := hE₀L.trans inf_le_left
  have hE₀C : E₀ ≤ Subgroup.centralizer ({z₀} : Set G) := fun e he =>
    mem_centralizer_singleton_of_isElemAbelian hE₀ hz₀E he
  have hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((mem_axisSub_iff.mp (hE₀L he)).2 l hl).symm
  have hE₀N : E₀ ≤ Subgroup.normalizer (L₀ : Set G) := fun e he => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcomm := (mem_axisSub_iff.mp (hE₀L he)).2
    constructor
    · intro hx
      have : e * x * e⁻¹ = x := by rw [← hcomm x hx]; group
      rw [this]
      exact hx
    · intro hx
      have h1 : e * x * e⁻¹ ∈ L₀ := hx
      have : x * e = e * x := by
        have h2 := hcomm (e * x * e⁻¹) h1
        calc x * e = e⁻¹ * (e * x * e⁻¹ * e) * e := by group
          _ = e⁻¹ * (e * (e * x * e⁻¹)) * e := by rw [h2]
          _ = e * x := by group
      have h3 : e * x * e⁻¹ = x := by rw [← this]; group
      rw [h3] at h1
      exact h1
  have hL₀z : L₀ ≤ Subgroup.centralizer ({z₀} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc.central l hl).symm
  exact isQuasisimple_of_deltaTrivial_of_layer_of_normalizes hz₀.subnormal hperf hq hE₀N hE₀C hE₀
    hcard le_rfl hL₀E hperf hne (deltaCore_eq_bot_of_le hE₀E hΔ)
    (isSubnormal_inf_centralizer_of_isSubnormal hz₀E (le_inf hL₀z hL₀E) hz₀.subnormal) hq
    fun f hf hf1 => hB f (hE₀L hf) hf1

end TheoremQ

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem classicalInvolutionOddCore_conjSub_eq_bot {L : Subgroup G}
    (h : classicalInvolutionOddCore L = ⊥) (n : G) :
    classicalInvolutionOddCore (conjSub n L) = ⊥ := by
  let e : L ≃* conjSub n L :=
    L.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
      classicalInvolutionOddCore (conjSub n L) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [← hO, h, Subgroup.map_bot]

theorem exactMembers_of_isQuasisimple (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {L₀ : Subgroup G} (hL₀ : L₀ ∈ Ω)
    (hq : CFSG.Open.IsQuasisimple L₀) : ExactMembers Ω := by
  obtain ⟨z, hz⟩ := hΩ.classical L₀ hL₀
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hO₀ : classicalInvolutionOddCore L₀ = ⊥ :=
    (classicalInvolutionOddCore_eq_bot_of_isQuasisimple hq hp2 hf h9 e).1
  obtain ⟨K, -, hall⟩ := hsingle
  obtain ⟨g₀, hg₀⟩ := hall L₀ hL₀
  intro L hL
  obtain ⟨g, hg⟩ := hall L hL
  have hK : K = conjSub g₀⁻¹ L₀ := by rw [hg₀, conjSub_inv_conjSub]
  have hLeq : L = conjSub (g * g₀⁻¹) L₀ := by rw [conjSub_mul, ← hK, hg]
  rw [hLeq]
  exact classicalInvolutionOddCore_conjSub_eq_bot hO₀ _

theorem exactMembers_of_weakFrame {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G}
    {S : Set (Subgroup G)} (Fr : WeakPreFrame F Ω E S) (hp2 : p ≠ 2) (hf : 0 < f)
    (h9 : p ^ f ≠ 9) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {L₀ : Subgroup G} (hL₀ : L₀ ∈ S)
    (hq : CFSG.Open.IsQuasisimple L₀) : ExactMembers Ω :=
  exactMembers_of_isQuasisimple hp2 hf h9 hΩ hsingle (Fr.subset hL₀) hq

end Exact

end CFSG.ClassicalInvolution.Balance
