module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Cells
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.LinBar
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

theorem outPChain_a_tf {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsLieOfTorusFree IdxA p X) : OutPChain p X := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨d, hv⟩, hPd, ht, ⟨e⟩⟩ := hX
  cases d with
  | A r q =>
    have hq2 : q.p = 2 := hPd
    have hm := CFSG.AGLEmbedding.statedClassicalModel_of_typeA hv e
    rw [hq2] at hm
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    by_cases h1 : r = 1
    · subst h1
      exact (outPNice_PSL_two hp hm).toChain
    · refine (outPNice_PSL_ge_three hp hp2 (by omega) hm ?_).toChain
      intro hd
      have hd2 : p ∣ 2 ^ q.exponent - 1 := hd.trans (Nat.gcd_dvd_right _ _)
      rcases (show q.card = 2 ∨ ¬ p ∣ q.card - 1 from ht) with h2 | h2
      · rw [hc] at h2
        have : q.exponent = 1 := by
          have := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
          exact this
        rw [this] at hd2
        norm_num at hd2
        omega
      · exact h2 (hc ▸ hd2)
  | _ => exact hPd.elim

theorem centCycCell_of_core' {𝔉 : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParabE L J →
      𝔉 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
        ∀ v : ↥L ⧸ Subgroup.center ↥L, CentCycBar (jBar L J) p v →
          OutPChain p (↥L ⧸ Subgroup.center ↥L))
    (hcyc : ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParabE L J →
      𝔉 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
        ∀ v : ↥L ⧸ Subgroup.center ↥L, CentCycBar (jBar L J) p v →
          ∀ Dh : Subgroup (↥L ⧸ Subgroup.center ↥L), ⁅Dh, Dh⁆ = Dh → Dh ≤ jBar L J → v ∈ Dh →
          ∀ A : Subgroup (↥L ⧸ Subgroup.center ↥L), A ≤ jBar L J → IsPGroup p A →
            A ≤ Subgroup.centralizer (Dh : Set (↥L ⧸ Subgroup.center ↥L)) → IsCyclic A) :
    CentCycCell 𝔉 := by
  intro Y _ _ L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hCP.comp.2.2.1
  obtain ⟨ρ, hρker, hρJ, hv, hDhp, hDhJ, hvDh⟩ :=
    exists_centCycBar' hCP hp hDp hDJ hDcyc hDpart hxD hxp hxC hxW
  refine ⟨exists_cyclic_mod_of_outPChain (hOut Y L J hCP hX p hp hp5 _ hv) hEp hEN,
    fun hEJ hEC => ?_⟩
  refine exists_cover_mod_centralizer ρ hρker hEJ ?_
  refine hcyc Y L J hCP hX p hp hp5 _ hv _ hDhp hDhJ hvDh _ ?_ ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  · exact (hEp.comap_subtype (K := J ⊔ Subgroup.centralizer (L : Set Y))).map ρ
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have := Subgroup.mem_centralizer_iff.1 (hEC (Subgroup.mem_subgroupOf.1 he)) d
      (Subgroup.mem_subgroupOf.1 hd)
    simpa using this

theorem bar_facts {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} (h : CompParabE L J) :
    commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ ∧ IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) ∧
      Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  have : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)
  exact ⟨Group.isPerfect_def.mp this, h.comp.2.2.2, center_bar_eq_bot h⟩

theorem centCycCell_a (hFour : TorusFourCell) (hThree : TorusThreeCell) :
    CentCycCell (IsLieOf IdxA) := by
  refine centCycCell_of_core' (fun Y _ _ L J h hX p hp hp5 v hv => ?_)
    (fun Y _ _ L J h hX p hp hp5 v hv Dh hDp hDJ hvD A hAJ hAp hAD => ?_)
  · rcases isLieOf_split (p := p) hX with hTF | hT
    · exact outPChain_a_tf hp hp5 hTF
    · obtain ⟨hperf, hsimple, hZ⟩ := bar_facts h
      obtain ⟨f, ⟨e⟩, -⟩ := centCycBar_torus_three hFour hperf hsimple hZ hp hp5 hT hv
      refine OutPChain.of_mulEquiv e (outPNice_projectiveSL hp (by omega) le_rfl ?_).toChain
      intro hd
      have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 3 _))
      omega
  · rcases isLieOf_split (p := p) hX with hTF | hT
    · exact isCyclic_of_centCycBar_hub hv
        (perfectJoinHub_of_torusFree_classical (Or.inl rfl) hp hp5 hTF) hAJ hAp
    · obtain ⟨hperf, hsimple, hZ⟩ := bar_facts h
      exact isCyclic_of_centCycBar_torus_three hFour hThree hperf hsimple hZ hp hp5 hT hv hDp hDJ
        hvD hAJ hAp hAD

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
