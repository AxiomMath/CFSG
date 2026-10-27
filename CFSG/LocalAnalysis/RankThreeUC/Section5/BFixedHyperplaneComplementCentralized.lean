module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.NormalizerFixedSpaceBTrivial
public import CFSG.LinearAlgebra.CoprimeActions.CoprimeTwoGroupFixedSpaceControl
public import CFSG.LinearAlgebra.CoprimeActions.OddFixedSpaceCentralizerCommutator
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator
public import CFSG.LinearAlgebra.CoprimeActions.PrimeOrderComplementFixedSpaceFaithfulness
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BFixedHyperplaneComplementCentralized

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem centralizes {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (E : Subgroup G) (hE : E ∈ Delta p P ρ)
    (hBN : B ≤ Subgroup.normalizer (E : Set G))
    (R : Subgroup G) (hRP : R ≤ P) (hRE : R ⊓ E = ⊥) (hRsup : R ⊔ E = P)
    (hRcard : Nat.card R = p)
    (hUR : twoCoreCommutator T B ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    B ≤ Subgroup.centralizer (R : Set G) := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  haveI : FiniteDimensional (ZMod 2) V :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional.finiteDimensional_of_irreducible
      ρ hc.faithfulBinaryIrreducibleAction.irreducible
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hN
  set U : Subgroup G := twoCoreCommutator T B ⊓ N with hU
  set W : Submodule (ZMod 2) V := CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ E with hW
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hEP : E ≤ P := hE.1
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRN : R ≤ N := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hrP : r ∈ P := hRP hr
    constructor
    · intro hx
      have h1 : r * x * r⁻¹ = x := by rw [hcomm r hrP x (hEP hx)]; simp
      rwa [h1]
    · intro hx
      have hxP : x ∈ P := by
        have := hP.conj_mem _ (hEP hx) r⁻¹
        simpa [mul_assoc] using this
      have h1 : r * x * r⁻¹ = x := by rw [hcomm r hrP x hxP]; simp
      rwa [h1] at hx
  have hmemW : ∀ w, w ∈ W ↔ ∀ x ∈ E, ρ x w = w := fun w =>
    CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ E w
  have hinv : ∀ n ∈ N, ∀ w ∈ W, ρ n w ∈ W := by
    intro n hn w hw
    rw [hmemW] at hw ⊢
    intro x hx
    have hx' : n⁻¹ * x * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hn) x).1 hx
      simpa using this
    have h1 := hw _ hx'
    calc ρ x (ρ n w) = ρ n (ρ (n⁻¹ * x * n) w) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2; group
      _ = ρ n w := by rw [h1]
  let σ : N →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun n => LinearEquiv.ofLinear
        ((ρ n.1).restrict (fun w hw => hinv n.1 n.2 w hw))
        ((ρ n.1⁻¹).restrict (fun w hw => hinv n.1⁻¹ (N.inv_mem n.2) w hw))
        (by
          ext w
          change ρ n.1 (ρ n.1⁻¹ w) = w
          rw [← Module.End.mul_apply, ← map_mul]; simp)
        (by
          ext w
          change ρ n.1⁻¹ (ρ n.1 w) = w
          rw [← Module.End.mul_apply, ← map_mul]; simp)
      map_one' := by ext w; simp
      map_mul' := fun a b => by ext w; simp }
  have hσ : ∀ (n : N) (w : W), ((σ n w : W) : V) = ρ n.1 w := fun n w => rfl
  let σR : Representation (ZMod 2) N W :=
    { toFun := fun n => (σ n).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun a b => by rw [map_mul]; rfl }
  have hσR : ∀ (n : N) (w : W), σR n w = σ n w := fun n w => rfl
  have hUN : U ≤ N := inf_le_right
  have hU2 : IsPGroup 2 U := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact (hK.to_le (CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful.Xs_le_pCoreOf T B
      le_sup_left)).to_le (inf_le_left : U ≤ twoCoreCommutator T B)
  have hBXs : B ≤ Subgroup.normalizer (twoCoreCommutator T B : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hBU_G : B ≤ Subgroup.normalizer (U : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hBXs hb) x
    have h2 : x ∈ N ↔ b * x * b⁻¹ ∈ N := by
      have hbN : b ∈ N := hBN hb
      refine ⟨fun hx => mul_mem (mul_mem hbN hx) (inv_mem hbN), fun hx => ?_⟩
      have := mul_mem (mul_mem (inv_mem hbN) hx) hbN
      simpa [mul_assoc] using this
    simp only [hU, Subgroup.mem_inf]
    rw [h1, h2]
  have hodd : Odd p := hS.odd
  have transfer : ∀ (X : Subgroup G), B ≤ Subgroup.normalizer (X : Set G) →
      X ≤ N → B.subgroupOf N ≤ Subgroup.normalizer ((X.subgroupOf N : Subgroup N) : Set N) := by
    intro X hBX hXN b hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have := Subgroup.mem_normalizer_iff.1 (hBX hb) n.1
    simpa [Subgroup.mem_subgroupOf] using this
  set U' : Subgroup N := U.subgroupOf N with hU'
  set B' : Subgroup N := B.subgroupOf N with hB'
  set R' : Subgroup N := R.subgroupOf N with hR'
  have hU'2 : IsPGroup 2 U' := hU2.comap_subtype
  have hB'odd : Odd (Nat.card B') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
    exact hS.oddOrder
  have hR'odd : Odd (Nat.card R') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv, hRcard]
    exact hodd
  have hB'U' : B' ≤ Subgroup.normalizer (U' : Set N) := transfer U hBU_G hUN
  have hB'R' : B' ≤ Subgroup.normalizer (R' : Set N) := transfer R hBR hRN
  have hfix1 : ∀ b ∈ B', ∀ v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σR U', σR b v = v := by
    intro b hb v hv
    rw [CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport.mem_fixedSubmodule_iff] at hv
    by_cases hv0 : v = 0
    · subst hv0; simp
    · have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
      have := CFSG.LocalAnalysis.RankThreeUC.Section5.NormalizerFixedSpaceBTrivial.fixes hc E hE hBN v.1 v.2 hv0'
        (fun s hs hsN => by
          have hsU : (⟨s, hsN⟩ : N) ∈ U' := by
            rw [hU', Subgroup.mem_subgroupOf]; exact ⟨hs, hsN⟩
          exact congrArg Subtype.val (hv ⟨s, hsN⟩ hsU)) b.1 hb
      exact Subtype.ext this
  have hctrl := CFSG.LinearAlgebra.CoprimeActions.CoprimeTwoGroupFixedSpaceControl.fixes σR U' B' hU'2 hB'odd
    hB'U' hfix1
  have hcomm_le : ⁅U', B'⁆ ≤ U' := Subgroup.le_normalizer_iff_commutator_le_left.1 hB'U'
  have hS2 : IsPGroup 2 ↥(⁅U', B'⁆ : Subgroup N) := hU'2.to_le hcomm_le
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI : IsCyclic R := isCyclic_of_prime_card hRcard
  have hcyc := CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer R U B
    (fun u hu => hUR hu) hBR
  have hmapc : Subgroup.map N.subtype ⁅U', B'⁆ = ⁅U, B⁆ := by
    rw [Subgroup.map_commutator, hU', hB', Subgroup.map_subgroupOf_eq_of_le hUN,
      Subgroup.map_subgroupOf_eq_of_le hBN]
  have hRS : R' ≤ Subgroup.centralizer ((⁅U', B'⁆ : Subgroup N) : Set N) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s.1 ∈ ⁅U, B⁆ := by rw [← hmapc]; exact ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hcyc hs') r.1 hr
    exact Subtype.ext (by simpa using this.symm)
  have hPne : P ≠ ⊥ := by
    intro h0
    have h1 : E.relIndex P = 1 := Subgroup.relIndex_eq_one.2 (by rw [h0]; exact bot_le)
    have := hE.2.1
    rw [h1] at this
    exact (hS.prime.one_lt).ne this
  haveI := hP
  have hfaith := CFSG.LinearAlgebra.CoprimeActions.PrimeOrderComplementFixedSpaceFaithfulness.faithful ρ
    hc.faithfulBinaryIrreducibleAction.faithful hc.faithfulBinaryIrreducibleAction.irreducible P hPne E R hEP hRP
    (by rw [sup_comm]; exact hRsup) hS.prime hRcard hE.2.2
  have hfaith' : ∀ r ∈ R', (∀ v, σ r v = v) → r = 1 := by
    intro r hr hv
    have : r.1 = 1 := hfaith r.1 hr (fun w hw => by
      have := hv ⟨w, hw⟩
      exact congrArg Subtype.val this)
    exact Subtype.ext this
  have hB'fix : ∀ b ∈ B', ∀ v : W, (∀ s ∈ (⁅U', B'⁆ : Subgroup N), σ s v = v) → σ b v = v := by
    intro b hb v hv
    exact hctrl b hb v (by
      rw [CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport.mem_fixedSubmodule_iff]
      exact hv)
  have hfin := CFSG.LinearAlgebra.CoprimeActions.OddFixedSpaceCentralizerCommutator.centralizes σ ⁅U', B'⁆ R' B'
    hS2 hR'odd hB'R' hRS hfaith' hB'fix
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hb' : (⟨b, hBN hb⟩ : N) ∈ B' := hb
  have := Subgroup.mem_centralizer_iff.1 (hfin hb') ⟨r, hRN hr⟩ hr
  have h2 := congrArg Subtype.val this
  exact h2

end CFSG.LocalAnalysis.RankThreeUC.Section5.BFixedHyperplaneComplementCentralized
end
