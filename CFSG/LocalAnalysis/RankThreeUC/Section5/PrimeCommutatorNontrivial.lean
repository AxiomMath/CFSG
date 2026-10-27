module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.SstarCoprimeStructure
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerEqCenterAndActorCyclicAndPrimeCoreCyclic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeCommutatorNontrivial

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_char_prime {B : Subgroup G} [IsCyclic B] {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card B) :
    ∃ A : Subgroup G, A ≤ B ∧ Nat.card A = r ∧
      ∀ φ : ↥B ≃* ↥B, Subgroup.map φ.toMonoidHom (A.subgroupOf B) = A.subgroupOf B := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) r hd
  refine ⟨(Subgroup.zpowers x).map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩; exact y.2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, Nat.card_zpowers, hx]
  · intro φ
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Subgroup.card_map_of_injective φ.injective]

theorem exists_prime_subgroup {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {r : ℕ} (hr : r ∈ piOf B) :
    ∃ A : Subgroup G, A ≤ B ∧ Nat.card A = r ∧
      (A.subgroupOf B).map (bToJoint h.oddPrimeClassTwoAction) ≤
        Subgroup.normalizer (((Sstar P T B).subgroupOf (joint P T B) : Subgroup (joint P T B)) :
          Set (joint P T B)) ∧
      ⁅(A.subgroupOf B).map (bToJoint h.oddPrimeClassTwoAction), (Sstar P T B).subgroupOf (joint P T B)⁆ ≠ ⊥ ∧
      IsPGroup 2
        (⁅(A.subgroupOf B).map (bToJoint h.oddPrimeClassTwoAction), (Sstar P T B).subgroupOf (joint P T B)⁆ :
          Subgroup (joint P T B)) := by
  classical
  haveI : IsCyclic B := (centralizer_eq_center_and_actor_cyclic_and_primeCore_cyclic h).2.1
  obtain ⟨hrp, hrd⟩ := hr
  obtain ⟨A, hAB, hcard, hchar⟩ := exists_char_prime hrp hrd
  have h51 := h.oddPrimeClassTwoAction
  have h53 := h.faithfulBinaryIrreducibleAction
  set K := CFSG.Open.pCoreOf 2 (B ⊔ T) with hK
  have hAbot : A ≠ ⊥ := by
    intro hA
    rw [hA, Subgroup.card_bot] at hcard
    exact hrp.one_lt.ne hcard
  have hne : ⁅P, ⁅K, A⁆⁆ ≠ ⊥ := (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants h51 h53 A hAB hchar).2.2 hAbot
  have hNtop : Subgroup.normalizer (P : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr h53.normal
  have hXK : twoCoreCommutator T B ≤ K := SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXK
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans hBK
  have hK2 : IsPGroup 2 K := (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    obtain ⟨n, hn⟩ := hK2.exists_card_eq
    rw [hn]
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_two_right]
    exact Odd.of_dvd_nat h51.setting.oddOrder (Subgroup.card_dvd_of_le hAB)
  have hidem : ⁅⁅K, A⁆, A⁆ = ⁅K, A⁆ :=
    CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime K A hcop hAK
  have hSA : ⁅K, A⁆ ≤ twoCoreCommutator T B := Subgroup.commutator_mono le_rfl hAB
  have hnormD : (A.subgroupOf B).map (bToJoint h51) ≤
      Subgroup.normalizer (((Sstar P T B).subgroupOf (joint P T B) : Subgroup (joint P T B)) :
        Set (joint P T B)) := by
    rintro _ ⟨b, hb, rfl⟩
    have hmem : ((bToJoint h51 b : joint P T B) : MulAut ↥P) ∈ Bstar P B := by
      rw [BstarFaithful.range_eq h51]; exact ⟨b, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp
      (SstarCoprimeStructure.normalizes h hmem))
    rw [Subgroup.mem_normalizer_iff]
    intro q
    simp only [Subgroup.mem_subgroupOf]
    exact this q
  refine ⟨A, hAB, hcard, hnormD, ?_, ?_⟩
  · intro hbot
    apply hne
    have hE : ∀ a ∈ A, ∀ x ∈ twoCoreCommutator T B, ∀ g ∈ P,
        (a : G) * x * g * x⁻¹ * a⁻¹ = x * a * g * a⁻¹ * x⁻¹ := by
      intro a ha x hx g hg
      have hNx : x ∈ Subgroup.normalizer (P : Set G) := by rw [hNtop]; trivial
      have hσ : Subgroup.normalizerMonoidHom P ⟨x, hNx⟩ ∈ Sstar P T B :=
        ⟨⟨x, hNx⟩, (Subgroup.mem_subgroupOf).mpr hx, rfl⟩
      set d : joint P T B := bToJoint h51 ⟨a, hAB ha⟩ with hd
      set q : joint P T B := ⟨_, Sstar_le_joint P T B hσ⟩ with hq
      have hdD : d ∈ (A.subgroupOf B).map (bToJoint h51) :=
        ⟨⟨a, hAB ha⟩, (Subgroup.mem_subgroupOf).2 ha, rfl⟩
      have hqQ : q ∈ (Sstar P T B).subgroupOf (joint P T B) := (Subgroup.mem_subgroupOf).2 hσ
      have h1 : ⁅d, q⁆ ∈ ⁅(A.subgroupOf B).map (bToJoint h51),
          (Sstar P T B).subgroupOf (joint P T B)⁆ := Subgroup.commutator_mem_commutator hdD hqQ
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      have h2 := congrArg (fun φ : joint P T B => (((φ : MulAut ↥P) ⟨g, hg⟩ : P) : G)) h1
      simpa [hd, hq, bToJoint_apply, BstarFaithful.bAction_apply, mul_assoc] using h2
    have hcen : ⁅A, twoCoreCommutator T B⁆ ≤ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : a⁻¹ * x⁻¹ * g * x * a ∈ P := by
        have := h53.normal.conj_mem g hg (a⁻¹ * x⁻¹)
        simpa [mul_assoc] using this
      have h3 := hE a ha x hx _ hg'
      have h4 : (⁅(a : G), x⁆) * g * (⁅(a : G), x⁆)⁻¹ = g := by
        have h5 : (⁅(a : G), x⁆) * g * (⁅(a : G), x⁆)⁻¹ =
            a * x * (a⁻¹ * x⁻¹ * g * x * a) * x⁻¹ * a⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [h5, h3]; group
      calc g * ⁅(a : G), x⁆ = ((⁅(a : G), x⁆) * g * (⁅(a : G), x⁆)⁻¹) * ⁅(a : G), x⁆ := by rw [h4]
        _ = ⁅(a : G), x⁆ * g := by group
    have hle : ⁅K, A⁆ ≤ Subgroup.centralizer (P : Set G) := by
      calc ⁅K, A⁆ = ⁅⁅K, A⁆, A⁆ := hidem.symm
        _ ≤ ⁅twoCoreCommutator T B, A⁆ := Subgroup.commutator_mono hSA le_rfl
        _ = ⁅A, twoCoreCommutator T B⁆ := Subgroup.commutator_comm _ _
        _ ≤ _ := hcen
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  · have hle : ⁅(A.subgroupOf B).map (bToJoint h51), (Sstar P T B).subgroupOf (joint P T B)⁆ ≤
        (Sstar P T B).subgroupOf (joint P T B) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hnormD
    exact ((SstarQuotientFaithful.isPGroup h).comap_subtype (K := joint P T B)).to_le hle

end CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeCommutatorNontrivial
