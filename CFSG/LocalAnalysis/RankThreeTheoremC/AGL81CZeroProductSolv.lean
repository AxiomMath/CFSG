module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)

namespace CZeroProduct

open CFSG.AGLEmbedding.SUPair (map_oUpperTwo isSubnormal_oUpperTwo)

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_oUpperTwo {T : Subgroup Y} (hb : IsSymThreeOrSUThreeTwo ↥T) :
    IsPGroup 3 (oUpperTwo T) := by
  have hc := IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb
  have hmap : oUpperTwo T = (oUpperTwo (⊤ : Subgroup ↥T)).map T.subtype := by
    rw [map_oUpperTwo, ← MonoidHom.range_eq_map, range_subtype]
  rintro ⟨x, hx⟩
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨1, Subtype.ext ?_⟩
  have h3 := congrArg Subtype.val (hc y hy)
  simpa using h3

theorem commutator_oUpperTwo_eq_bot (hSUC : SubnormalSUThreeTwoCommute) (hO : CFSG.pCore 2 Y = ⊥)
    {T₁ T₂ : Subgroup Y} (h₁ : IsSubnormal T₁ ⊤) (h₂ : IsSubnormal T₂ ⊤)
    (hb₁ : IsSymThreeOrSUThreeTwo ↥T₁) (hb₂ : IsSymThreeOrSUThreeTwo ↥T₂)
    (hne : oUpperTwo T₁ ≠ oUpperTwo T₂) : ⁅oUpperTwo T₁, oUpperTwo T₂⁆ = ⊥ := by
  rcases hb₁ with hs₁ | hu₁
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro b hb
    exact SubnormalCommute.commute_oUpperTwo_of_symThree h₁ hs₁ (isPGroup_oUpperTwo hb₂)
      (isSubnormal_oUpperTwo h₂) x hx b hb
  rcases hb₂ with hs₂ | hu₂
  · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro b hb
    exact SubnormalCommute.commute_oUpperTwo_of_symThree h₂ hs₂
      (isPGroup_oUpperTwo (Or.inr hu₁)) (isSubnormal_oUpperTwo h₁) x hx b hb
  exact hSUC Y hO T₁ T₂ h₁ h₂ hu₁ hu₂ hne

theorem pCore_quotient_pCore_eq_bot {X : Type} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] :
    CFSG.pCore p (X ⧸ CFSG.pCore p X) = ⊥ := by
  set N : Subgroup X := CFSG.pCore p X with hN
  set K : Subgroup X := (CFSG.pCore p (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := (CFSG.pCore_normal (p := p) (G := X ⧸ N)).comap _
  have hKp : IsPGroup p K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := p) (G := X ⧸ N) ⟨_, hx⟩
    have hxa : x ^ (p ^ a) ∈ N := by
      have h1 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := p) (G := X) ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_add, pow_mul, h2]
  have hle : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

theorem oUpperTwo_sup_eq {I N : Subgroup Y} (hN : N ≤ I) :
    oUpperTwo (oUpperTwo I ⊔ N) = oUpperTwo I := by
  apply le_antisymm
  · refine (closure_le _).mpr fun y hy => ?_
    exact subset_closure ⟨sup_le (oUpperTwo_le_self I) hN hy.1, hy.2⟩
  · refine (closure_le _).mpr fun x hx => ?_
    exact subset_closure ⟨mem_sup_left (subset_closure hx), hx.2⟩

end CZeroProduct

open CZeroProduct
open CFSG.AGLEmbedding.SUPair (map_oUpperTwo)

variable {G : Type} [Group G] [Finite G]

theorem commutator_oUpperTwo_le_pCoreOf (hSUC : SubnormalSUThreeTwoCommute)
    {X I₁ I₂ : Subgroup G} (h₁ : IsCZeroMember X I₁) (h₂ : IsCZeroMember X I₂)
    (hb₁ : pCoreOf 2 I₁ = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I₁ ⧸ CFSG.pCore 2 ↥I₁))
    (hb₂ : pCoreOf 2 I₂ = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I₂ ⧸ CFSG.pCore 2 ↥I₂))
    (hne : oUpperTwo I₁ ≠ oUpperTwo I₂) : ⁅oUpperTwo I₁, oUpperTwo I₂⁆ ≤ pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have data : ∀ {I : Subgroup G}, IsCZeroMember X I →
      pCoreOf 2 I = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I) →
      IsSubnormal ((I.subgroupOf X).map π) ⊤ ∧
        IsSymThreeOrSUThreeTwo ↥((I.subgroupOf X).map π) ∧ N ≤ I.subgroupOf X ∧
        (oUpperTwo (I.subgroupOf X)).map X.subtype = oUpperTwo I := by
    intro I hI hb
    have hsub : IsSubnormal ((I.subgroupOf X).map π) ⊤ := by
      have := (IsSubnormal.of_mathlib hI.subnormal.subgroupOf).map π
      rwa [map_top_of_surjective π hπs] at this
    have hNI : N ≤ I.subgroupOf X := by
      intro n hn
      rw [mem_subgroupOf]
      have : (n : G) ∈ pCoreOf 2 X := mem_map_of_mem X.subtype hn
      rw [← hb.1] at this
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 I this
    set φ : ↥I →* ↥X ⧸ N := π.comp (inclusion hI.le) with hφ
    have hrange : φ.range = (I.subgroupOf X).map π := by
      rw [hφ, MonoidHom.range_comp, inclusion_range]
    have hker : φ.ker = CFSG.pCore 2 ↥I := by
      ext i
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have h1 : inclusion hI.le i ∈ N ↔ (i : G) ∈ pCoreOf 2 X := by
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨y, hy, hyi⟩
          have : y = inclusion hI.le i := Subtype.ext hyi
          rwa [← this]
      rw [h1, ← hb.1]
      constructor
      · rintro ⟨y, hy, hyi⟩
        have : y = i := Subtype.ext hyi
        rwa [← this]
      · intro h
        exact ⟨_, h, rfl⟩
    have e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥((I.subgroupOf X).map π) :=
      ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
    refine ⟨hsub, IsSymThreeOrSUThreeTwo.of_mulEquiv e hb.2, hNI, ?_⟩
    rw [map_oUpperTwo, subgroupOf_map_subtype, inf_of_le_left hI.le]
  obtain ⟨hs₁, hb₁', hN₁, hm₁⟩ := data h₁ hb₁
  obtain ⟨hs₂, hb₂', hN₂, hm₂⟩ := data h₂ hb₂
  set S₁ := oUpperTwo (I₁.subgroupOf X)
  set S₂ := oUpperTwo (I₂.subgroupOf X)
  have hne' : oUpperTwo ((I₁.subgroupOf X).map π) ≠ oUpperTwo ((I₂.subgroupOf X).map π) := by
    rw [← map_oUpperTwo, ← map_oUpperTwo]
    intro heq
    have hc := congrArg (Subgroup.comap π) heq
    rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hc
    have e₁ : oUpperTwo (S₁ ⊔ N) = S₁ := oUpperTwo_sup_eq hN₁
    have e₂ : oUpperTwo (S₂ ⊔ N) = S₂ := oUpperTwo_sup_eq hN₂
    have hS : S₁ = S₂ := by
      rw [← e₁, ← e₂]
      exact congrArg oUpperTwo hc
    apply hne
    rw [← hm₁, ← hm₂, hS]
  have hO : CFSG.pCore 2 (↥X ⧸ N) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hcomm := commutator_oUpperTwo_eq_bot hSUC hO hs₁ hs₂ hb₁' hb₂' hne'
  rw [← map_oUpperTwo, ← map_oUpperTwo, ← map_commutator, Subgroup.map_eq_bot_iff, hπ,
    QuotientGroup.ker_mk'] at hcomm
  rw [← hm₁, ← hm₂, ← map_commutator]
  exact map_mono hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC
