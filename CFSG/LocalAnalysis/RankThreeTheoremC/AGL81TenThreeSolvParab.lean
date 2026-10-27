module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvParabBlocks
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphQuasi
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup SolvParab
open CFSG.ComponentClassification.AS76b (oUpperTwo)

private theorem false_of_perfect_of_symThree {G : Type} [Group G] {I : Subgroup G}
    (hp : ⁅I, I⁆ = I) (e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3)) : False := by
  set f : ↥I →* ℤˣ :=
    Equiv.Perm.sign.comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥I))) with hf
  have htop : commutator ↥I = ⊤ := by
    rw [commutator_def]
    apply map_injective I.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hp]
  have hker : commutator ↥I ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [htop] at hker
  obtain ⟨x, hx⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) (Equiv.swap 0 1)
  have h1 : f x = 1 := hker (mem_top x)
  have h2 : f x = Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) := by
    simp only [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg Equiv.Perm.sign hx
  rw [Equiv.Perm.sign_swap (by decide), h1] at h2
  exact absurd h2 (by decide)

theorem commutator_le_pCoreOf_of_symThreePairs {G : Type} [Group G] [Finite G]
    {X I₁ I₂ : Subgroup G} (hX : SymThreePairs (↥X ⧸ CFSG.pCore 2 ↥X))
    (h₁ : I₁ ∈ cZero X) (h₂ : I₂ ∈ cZero X)
    (hs₁ : Nonempty (↥I₁ ⧸ CFSG.pCore 2 ↥I₁ ≃* Equiv.Perm (Fin 3)))
    (hs₂ : Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)))
    (hne : oUpperTwo I₁ ≠ oUpperTwo I₂) : ⁅I₁, I₂⁆ ≤ pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have h₁' : IsCZeroMember X I₁ := h₁
  have h₂' : IsCZeroMember X I₂ := h₂
  have shape : ∀ {I : Subgroup G}, IsCZeroMember X I →
      Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 I = pCoreOf 2 X := by
    intro I hI ⟨e⟩
    rcases hI.shape with hc | hb
    · exact (false_of_perfect_of_symThree hc.perfect e).elim
    · exact hb.1
  have data : ∀ {I : Subgroup G}, IsCZeroMember X I → pCoreOf 2 I = pCoreOf 2 X →
      Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3)) →
      IsSubnormal ((I.subgroupOf X).map π) ⊤ ∧
        Nonempty (↥((I.subgroupOf X).map π) ≃* Equiv.Perm (Fin 3)) ∧ N ≤ I.subgroupOf X ∧
        (oUpperTwo (I.subgroupOf X)).map X.subtype = oUpperTwo I := by
    intro I hI hb ⟨eI⟩
    have hsub : IsSubnormal ((I.subgroupOf X).map π) ⊤ := by
      have := (IsSubnormal.of_mathlib hI.subnormal.subgroupOf).map π
      rwa [map_top_of_surjective π hπs] at this
    have hNI : N ≤ I.subgroupOf X := by
      intro n hn
      rw [mem_subgroupOf]
      have : (n : G) ∈ pCoreOf 2 X := mem_map_of_mem X.subtype hn
      rw [← hb] at this
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
      rw [h1, ← hb]
      constructor
      · rintro ⟨y, hy, hyi⟩
        have : y = i := Subtype.ext hyi
        rwa [← this]
      · intro h
        exact ⟨_, h, rfl⟩
    have e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥((I.subgroupOf X).map π) :=
      ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
    refine ⟨hsub, ⟨e.symm.trans eI⟩, hNI, ?_⟩
    rw [SUPair.map_oUpperTwo, subgroupOf_map_subtype, inf_of_le_left hI.le]
  obtain ⟨hsn₁, he₁, hN₁, hm₁⟩ := data h₁' (shape h₁' hs₁) hs₁
  obtain ⟨hsn₂, he₂, hN₂, hm₂⟩ := data h₂' (shape h₂' hs₂) hs₂
  have hne' : (I₁.subgroupOf X).map π ≠ (I₂.subgroupOf X).map π := by
    intro heq
    apply hne
    have hc := congrArg (Subgroup.comap π) heq
    rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hN₁,
      sup_eq_left.mpr hN₂] at hc
    rw [← hm₁, ← hm₂, hc]
  rcases hX _ _ hsn₁ hsn₂ he₁ he₂ with heq | hcomm
  · exact absurd heq hne'
  · have hle : ⁅I₁.subgroupOf X, I₂.subgroupOf X⁆ ≤ N := by
      have hmap : ⁅I₁.subgroupOf X, I₂.subgroupOf X⁆.map π = ⊥ := by
        rw [map_commutator, hcomm]
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    have hI : ∀ {I : Subgroup G}, I ≤ X → (I.subgroupOf X).map X.subtype = I := fun h => by
      rw [subgroupOf_map_subtype, inf_of_le_left h]
    calc ⁅I₁, I₂⁆ = ⁅I₁.subgroupOf X, I₂.subgroupOf X⁆.map X.subtype := by
          rw [map_commutator, hI h₁'.le, hI h₂'.le]
      _ ≤ N.map X.subtype := map_mono hle
      _ = pCoreOf 2 X := rfl

section Small

private theorem symThreePairs_small {X : Type} [Group X] [Finite X] {L J : Subgroup X}
    (hCP : CompParab L J) (h : IsSmallTwoOrG2 (↥L ⧸ center ↥L)) :
    SymThreePairs (↥J ⧸ CFSG.pCore 2 ↥J) := by
  classical
  rcases (CFSG.HardMathSupport.Curtis.Proving.isSmallTwoOrG2_iff _).mp h with h4 | hA8
  · have hord : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥L ⧸ center ↥L) :=
      CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo h4
    obtain ⟨hJL, T, hT, hTN⟩ := hCP.parab
    have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hLperf : commutator ↥L = ⊤ := hCP.comp.2.2.1
    set πL : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπL
    have hπLs : Function.Surjective πL := QuotientGroup.mk'_surjective _
    set Jb : Subgroup ↥L := J.subgroupOf L with hJb
    have hJbne : Jb.map πL ≠ ⊤ := by
      intro htop
      apply hCP.ne_top
      have hJbtop : Jb = ⊤ := by
        refine CFSG.HardMathSupport.Curtis.Proving.top_of_mul_central_of_perfect
          (Subgroup.center ↥L) Jb le_rfl hLperf ?_
        intro g
        have hg : πL g ∈ Jb.map πL := htop ▸ Subgroup.mem_top _
        obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 hg
        exact ⟨h', hh', h'⁻¹ * g, QuotientGroup.eq.1 he, (mul_inv_cancel_left h' g).symm⟩
      rw [hJb, Subgroup.subgroupOf_eq_top] at hJbtop
      exact le_antisymm hJL hJbtop
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf ((T.subgroupOf L).map πL) ⊤ :=
      CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
        (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) πL hπLs
    have hT₀J : (T.subgroupOf L).map πL ≤ Jb.map πL :=
      Subgroup.map_mono (fun x hx => hTJ hx)
    have h96 : Nat.card (Jb.map πL) ∣ 96 := hord _ _ hT₀ hT₀J hJbne
    have hZc : (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≤ center ↥J := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      refine Subgroup.inclusion_injective hJL ?_
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hx (Subgroup.inclusion hJL y)
    have hZo : Odd (Nat.card ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) := by
      refine Odd.of_dvd_nat hCP.odd ?_
      have hcard : Nat.card ↥(Subgroup.map (Subgroup.inclusion hJL)
          ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) =
          Nat.card ↥((Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJL)
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (by rintro - ⟨z, hz, rfl⟩; exact hz)
    have h96' : Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) ∣ 96 := by
      set g : ↥J →* ↥L ⧸ center ↥L := πL.comp (Subgroup.inclusion hJL) with hg
      have hgker : g.ker = (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) := by
        ext x
        rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.mem_comap, hπL,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hgrange : g.range = Jb.map πL := by
        rw [hg, MonoidHom.range_comp, Subgroup.inclusion_range]
      have e : ↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≃* ↥(Jb.map πL) :=
        (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
          ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hgrange))
      rw [show Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL))
          = Nat.card ↥(Jb.map πL) from Nat.card_congr e.toEquiv]
      exact h96
    exact symThreePairs_of_card_dvd hZc hZo h96'
  · obtain ⟨eA⟩ := hA8
    obtain ⟨e8⟩ := CFSG.AGLEmbedding.ToralCensus.nonempty_alt_eight_mulEquiv_projectiveSL
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.AGLEmbedding.ToralCensus.center_eq_bot_of_mulEquiv_alt_eight hCP.comp.2.2 hCP.odd eA
    obtain ⟨ρ, hρ⟩ :=
      CFSG.AGLEmbedding.ToralCensus.exists_compat_of_center_eq_bot hZ (eA.trans e8)
    obtain ⟨hρs, -⟩ := CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat
      hCP.comp.2.2.1 (eA.trans e8) ρ hρ
    obtain ⟨σ, e', I, hσs, hσ, -, hcomap, -, -⟩ :=
      CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hCP.odd (n := 4) (by norm_num)
        (eA.trans e8) hρs hρ hCP.parab
    obtain ⟨-, hσk⟩ := CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat
      hCP.comp.2.2.1 e' σ hσ
    exact symThreePairs_of_hasLeviCensus
      (ParabCensus.hasLeviCensus_of_comap_eq_flagStabilizer hCP.parab.1 (by norm_num) σ hσs hσk
        hcomap)

end Small

private theorem symThreePairs_of_compParab (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {L J : Subgroup X} (hCP : CompParab L J)
    (hB2 : ¬ IsLieOf ParabCensus.IdxBTwo (↥L ⧸ center ↥L)) :
    SymThreePairs (↥J ⧸ CFSG.pCore 2 ↥J) := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxA hGA hCP h)
  · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxTwistedA hCP h)
  · rcases ParabCensus.isLieOf_idxB_cases h with h | h
    · exact absurd h hB2
    · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxBBig hZ hCP h)
  · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxD hZ hCP h)
  · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxTwistedD hZ hCP h)
  · exact symThreePairs_of_hasLeviCensus (ParabCensus.hasLeviCensus_idxG2 hGA hCP h)
  · exact symThreePairs_small hCP h

theorem symThreePairs_of_parabolic (hGA : GriessAllModelsStatement) {A : Type} [Group A]
    [Finite A] {Y P : Subgroup A} (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hcl : IsClassicalTwoOrG2 (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) :
    SymThreePairs (↥P ⧸ CFSG.pCore 2 ↥P) := by
  classical
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  by_cases hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)
  · exact symThreePairs_of_isSpTwoLeviProduct
      (ParabCensus.isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hP)
  rcases ParabCensus.parabolic_cases hY hO hcl hP with hPY | ⟨T, hT, hPNeq⟩ | hCP
  ·
    subst P
    have hpc := ParabCensus.pCore_eq_bot_of_pCoreOf_eq_bot hO
    have hquot : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    exact SymThreePairs.of_mulEquiv hquot.symm (SymThreePairs.of_eq_top fun _ hT hb =>
      (TwelveNotLe.false_of_subnormal_symThree_of_isQuasisimple hY hb hT).elim)
  ·
    have hTP : T ≤ P := by
      rw [hPNeq]
      exact fun x hx => ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hPN : P ≤ Subgroup.normalizer (T : Set A) := by
      rw [hPNeq]
      exact inf_le_right
    obtain ⟨hoddO, -⟩ := ParabCensus.odd_relIndex_pCoreOf_of_le_normalizer hT hTP hP.1 hPN
    refine SymThreePairs.of_odd ?_
    rw [← Subgroup.index_eq_card, ParabCensus.index_pCore_eq_relIndex_pCoreOf]
    exact hoddO
  ·
    obtain ⟨eq⟩ :=
      ParabCensus.nonempty_quotient_pCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.1)
    exact (symThreePairs_of_compParab hGA hCP
      (ParabCensus.not_isLieOf_quotient_center_top (Q := ↥Y) hB2)).of_mulEquiv eq

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
