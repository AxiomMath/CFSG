module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618Strong
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63
import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem mem_of_mem_sup_of_coprime {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {N M : Subgroup X} [N.Normal] (hM : Nat.Coprime p (Nat.card M)) {w : X} (hw : w ∈ N ⊔ M)
    (hwp : w ^ p = 1) : w ∈ N := by
  have h1 : QuotientGroup.mk' N w ∈ M.map (QuotientGroup.mk' N) := by
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hw
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at this
  have h2 : orderOf (QuotientGroup.mk' N w) ∣ Nat.card M :=
    (Subgroup.orderOf_dvd_natCard _ h1).trans (Subgroup.card_map_dvd M _)
  have h3 : orderOf (QuotientGroup.mk' N w) ∣ p := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow, hwp, map_one])
  have h4 : orderOf (QuotientGroup.mk' N w) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hM) h2
  exact (QuotientGroup.eq_one_iff w).mp (orderOf_eq_one_iff.mp h4)

theorem mem_pLayer_of_mem_layer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {w : X}
    (hw : (w : X ⧸ pPrimeCore p X) ∈ layer (X ⧸ pPrimeCore p X)) (hwp : w ^ p = 1) :
    w ∈ pLayer X p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (pLayer X p).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := p)
  have h1 : w ∈ (layer (X ⧸ pPrimeCore p X)).comap (QuotientGroup.mk' (pPrimeCore p X)) := hw
  rw [CFSG.ComponentClassification.LBalance.Quot.comap_layer_quotient_eq] at h1
  exact mem_of_mem_sup_of_coprime hp (pPrimeCore_coprime_card (p := p) (G := X)) h1 hwp

theorem map_centralizer_subtype {G : Type} [Group G] {M : Subgroup G} {y : G} (hyM : y ∈ M) :
    (centralizer ({(⟨y, hyM⟩ : ↥M)} : Set ↥M)).map M.subtype = M ⊓ centralizer ({y} : Set G) := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨w'.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hw'))⟩
  · rintro ⟨hwM, hwC⟩
    exact ⟨⟨w, hwM⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hwC)), rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem l613_of_facts (hI : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input10_20_3)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hβ : KFactBetaStructure) (h291 : KD291a3)
    (hr : KFact613rankP)
    (h313 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NormalElementaryRankFour) : L613 := by
  intro G _ _ p P M x z hS hx hz hpc H K hHM hsec hpS f hf hf2 hfp hfS
  by_cases hf3 : f = 3
  · subst hf3
    exact L630.l613f3_of_facts hI hSch hβ h291 h313 G p P M x z hS hx hz hpc H K hHM hsec hpS hfS
  have hp := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hf5 : 5 ≤ f := by
    by_contra hlt
    interval_cases f <;> simp_all <;> exact absurd hf (by norm_num)
  have hxM : x ∈ M := hx.mem_M hS
  have hzM : z ∈ M := hS.sylow_le hz.mem
  have hpl := plane63_of_situation hS hx hz
  obtain ⟨hβs, hdvd⟩ := l613_front hSch hβ h291 hS hx hz hpc hHM hsec hpS
  obtain ⟨C₀⟩ : Nonempty (CFSG.LocalCores.ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) p)) :=
    (Nat.card_pos_iff.mp (by rw [hβs.card_components]; exact hp.pos)).1
  have hfC : ∀ C : CFSG.LocalCores.ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) p),
      f ∣ Nat.card ↥C.1 := fun C => hfS.trans (hdvd C)
  have hrk := pRank_ge_of_beta hpl hβs hI C₀ hf hf2 (hfC C₀)
  have h4 : 4 ≤ Open.pRank f M := by
    have := pRank_top_subtype hf.one_lt M
    have h5 := hS.p_ge
    omega
  have hnsolv := not_isSolvable_of_section hxM hHM hsec
  refine stronglyEmbedded_of_rank hS hf hf2 hfp hnsolv h4 ?_
  intro hlt y hyM hyo
  have hKM : CFSG.Open.IsKGroup ↥M :=
    (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup).mp hpl.catalog
  have hnab : ¬ ∀ a ∈ ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M),
      ∀ b ∈ ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M), a * b = b * a := by
    intro hab
    have hxP' : (⟨x, hxM⟩ : ↥M) ∈ ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr hx.mem
    have hle : ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M) ≤
        centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := fun a ha =>
      mem_centralizer_singleton_iff.mpr (hab a ha _ hxP')
    have h1 := CFSG.SectionRank.pRank_mono hp.one_lt hle
    have h2 := hpl.four_le
    have h3 := hpl.rank_centralizer
    omega
  have hcent : ∀ w ∈ ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M),
      (∀ b ∈ ((P.subtype hS.sylow_le : Sylow p ↥M) : Subgroup ↥M), w * b = b * w) → w ^ p = 1 →
        w ∈ pLayer ↥M p := by
    intro w hwP hwc hwp
    have hwz : w ∈ zpowers (⟨z, hzM⟩ : ↥M) :=
      hpl.plane.center w hwP (mem_centralizer_iff.mpr fun b hb => (hwc b hb).symm) hwp
    have hzL := hβs.z_mem_layer
    have hzp : (⟨z, hzM⟩ : ↥M) ^ p = 1 := (plane_basic hpl).2.1
    exact (zpowers_le.mpr (mem_pLayer_of_mem_layer hp hzL hzp)) hwz
  have hyo' : orderOf (⟨y, hyM⟩ : ↥M) = f := by
    rw [← hyo]
    exact (Subgroup.orderOf_coe (⟨y, hyM⟩ : ↥M)).symm
  have h3 := hr ↥M p f hp hf hf5 hlt hKM
    (fun C => ⟨isSimpleGroup_of_component C.2 (hβs.centreless C), hfC C⟩)
    (le_of_eq hβs.card_components.symm)
    (fun C D => by
      obtain ⟨k, hk⟩ := hβs.transitive C D
      exact ⟨(⟨x, hxM⟩ : ↥M) ^ k, by rw [map_pow]; exact congrArg Subtype.val hk⟩)
    (P.subtype hS.sylow_le) hnab hcent ⟨y, hyM⟩ hyo'
  rw [← pRank_map_subtype hf.one_lt, map_centralizer_subtype hyM] at h3
  exact h3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

