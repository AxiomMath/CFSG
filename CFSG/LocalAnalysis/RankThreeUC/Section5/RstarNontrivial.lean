module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
import all CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeActionFixedFree
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerEqCenterAndActorCyclicAndPrimeCoreCyclic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful.SstarQuotientFaithful

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.RstarNontrivial

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ne_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) : R P T B A ≠ ⊥ := by
  intro hR
  have hN : Subgroup.normalizer (P : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hc.faithfulBinaryIrreducibleAction.normal
  have hAbot : A ≠ ⊥ := by
    intro h
    subst h
    rw [Subgroup.card_bot] at hA
    exact hq.one_lt.ne hA
  have hcyc : IsCyclic ↥B := (centralizer_eq_center_and_actor_cyclic_and_primeCore_cyclic hc).2.1
  have hchar : ∀ φ : ↥B ≃* ↥B,
      Subgroup.map φ.toMonoidHom (A.subgroupOf B) = A.subgroupOf B := by
    intro φ
    haveI : Finite (A.subgroupOf B) := inferInstance
    rw [IsCyclic.subgroup_eq_iff_card_eq, Subgroup.card_map_of_injective φ.injective]
  have h57 := (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction A hAB hchar).2.2 hAbot
  apply h57
  set K2 := CFSG.Open.pCoreOf 2 (B ⊔ T) with hK2def
  have hXA : ⁅twoCoreCommutator T B, A⁆ ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := by rw [hN]; trivial
    have haN : a ∈ Subgroup.normalizer (P : Set G) := by rw [hN]; trivial
    have h1 : Subgroup.normalizerMonoidHom P ⟨x, hxN⟩ ∈ Sstar P T B :=
      ⟨⟨x, hxN⟩, (Subgroup.mem_subgroupOf).mpr hx, rfl⟩
    have h2 : Subgroup.normalizerMonoidHom P ⟨a, haN⟩ ∈ Bstar P A :=
      ⟨⟨a, haN⟩, (Subgroup.mem_subgroupOf).mpr ha, rfl⟩
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    change _ ∈ R P T B A at h3
    rw [hR, Subgroup.mem_bot] at h3
    have hker : ⁅(⟨x, hxN⟩ : Subgroup.normalizer (P : Set G)), ⟨a, haN⟩⁆ ∈
        (Subgroup.normalizerMonoidHom P).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]; exact h3
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  have hKle : ⁅K2, B⁆ ≤ K2 := SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left
  have hBK : B ≤ Subgroup.normalizer (K2 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hKle
  have hK2 : IsPGroup 2 K2 := (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hq2 : q ≠ 2 := PrimeActionFixedFree.q_ne_two hc hAB hA
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K2) := by
    rw [hn, hA]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr
      (hq.eq_two_or_odd'.resolve_left hq2))
  have hidem := CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime K2 A hcop (hAB.trans hBK)
  have hle1 : ⁅K2, A⁆ ≤ twoCoreCommutator T B := Subgroup.commutator_mono le_rfl hAB
  have hle2 : ⁅K2, A⁆ ≤ Subgroup.centralizer (P : Set G) := by
    calc ⁅K2, A⁆ = ⁅⁅K2, A⁆, A⁆ := hidem.symm
      _ ≤ ⁅twoCoreCommutator T B, A⁆ := Subgroup.commutator_mono hle1 le_rfl
      _ ≤ _ := hXA
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro y hy s hs
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  exact (Subgroup.mem_centralizer_iff.mp (hle2 hs) y hy)

end CFSG.LocalAnalysis.RankThreeUC.Section5.RstarNontrivial
