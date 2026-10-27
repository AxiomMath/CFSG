module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Bridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Steps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaKD
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PThree
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Conv

variable {G : Type} [Group G] {H K : Subgroup G}

theorem isSimpleGroup_quotient_of_section [(K.subgroupOf H).Normal]
    (h : S622IsSimpleSection H K) : IsSimpleGroup (↥H ⧸ K.subgroupOf H) := by
  obtain ⟨hKH, -, hKne, hmin, -⟩ := h
  haveI : Nontrivial (↥H ⧸ K.subgroupOf H) := by
    obtain ⟨g, hgH, hgK⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hKH hKne)
    refine ⟨⟨(⟨g, hgH⟩ : ↥H), 1, fun h1 => hgK ?_⟩⟩
    have := (QuotientGroup.eq_one_iff (N := K.subgroupOf H) (⟨g, hgH⟩ : ↥H)).mp h1
    exact Subgroup.mem_subgroupOf.mp this
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top_of_normal := fun M hM => ?_ }
  set N' : Subgroup ↥H := M.comap (QuotientGroup.mk' (K.subgroupOf H)) with hN'
  have hKM : K ≤ N'.map H.subtype := fun k hk => by
    refine Subgroup.mem_map.mpr ⟨⟨k, hKH hk⟩, ?_, rfl⟩
    rw [hN', Subgroup.mem_comap]
    have : QuotientGroup.mk' (K.subgroupOf H) ⟨k, hKH hk⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
    rw [this]
    exact M.one_mem
  have hsub : (N'.map H.subtype).subgroupOf H = N' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N'
  have hnorm : ((N'.map H.subtype).subgroupOf H).Normal := by
    rw [hsub]
    exact hM.comap _
  rcases hmin (N'.map H.subtype) hKM (Subgroup.map_subtype_le _) hnorm with h1 | h1
  · left
    have hN'K : N' = K.subgroupOf H := by rw [← hsub, h1]
    refine (Subgroup.eq_bot_iff_forall M).mpr fun q hq => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have : g ∈ N' := hq
    rw [hN'K] at this
    exact (QuotientGroup.eq_one_iff g).mpr this
  · right
    have hN'top : N' = ⊤ := by rw [← hsub, h1, Subgroup.subgroupOf_self]
    refine (Subgroup.eq_top_iff' M).mpr fun q => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have : g ∈ N' := by rw [hN'top]; exact Subgroup.mem_top g
    exact this

theorem not_comm_quotient_of_section [(K.subgroupOf H).Normal] (h : S622IsSimpleSection H K) :
    ¬ ∀ a b : ↥H ⧸ K.subgroupOf H, a * b = b * a := by
  intro hcomm
  apply h.2.2.2.2
  intro a ha b hb
  have h1 : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥H) :
      ↥H ⧸ K.subgroupOf H) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)]
    group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem isSecOf_of_section {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hHM : H ≤ M ⊓ centralizer ({x} : Set G)) [(K.subgroupOf H).Normal] :
    IsSecOf (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) (↥H ⧸ K.subgroupOf H) := by
  have hHle : H ≤ M := fun h hh => (hHM hh).1
  refine ⟨H.subgroupOf M, fun h hh => ?_,
    (QuotientGroup.mk' (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hHle).toMonoidHom,
    (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hHle).surjective⟩
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (mem_centralizer_singleton_iff.mp
    (Subgroup.mem_inf.mp (hHM (Subgroup.mem_subgroupOf.mp hh))).2)

theorem not_isSolvable_of_section {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hHM : H ≤ M ⊓ centralizer ({x} : Set G)) (hsec : S622IsSimpleSection H K) :
    ¬ Group.IsSolvable ↥M := by
  haveI hKn : (K.subgroupOf H).Normal := hsec.2.1
  haveI hsimp : IsSimpleGroup (↥H ⧸ K.subgroupOf H) := isSimpleGroup_quotient_of_section hsec
  exact IsSecOf.not_isSolvable (not_comm_quotient_of_section hsec)
    ((isSecOf_of_section (K := K) hxM hHM).mono le_top)

end Conv

section Front

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem l613_front (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hβ : KFactBetaStructure)
    (h291 : KD291a3) (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    (hpc : ¬ CFSG.ABGLocalTools.IsPConstrained p ↥M) {H K : Subgroup G}
    (hHM : H ≤ M ⊓ centralizer ({x} : Set G)) (hsec : S622IsSimpleSection H K)
    (hpS : p ∣ K.relIndex H) :
    BetaStructure p ↥M (P.subtype hS.sylow_le) ⟨x, hx.mem_M hS⟩ ⟨z, hS.sylow_le hz.mem⟩ ∧
      ∀ C : CFSG.LocalCores.ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) p),
        K.relIndex H ∣ Nat.card ↥C.1 := by
  have hp := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hxM : x ∈ M := hx.mem_M hS
  have hpl := plane63_of_situation hS hx hz
  haveI hKn : (K.subgroupOf H).Normal := hsec.2.1
  haveI hsimp : IsSimpleGroup (↥H ⧸ K.subgroupOf H) := isSimpleGroup_quotient_of_section hsec
  have hnab := not_comm_quotient_of_section hsec
  have hpS' : p ∣ Nat.card (↥H ⧸ K.subgroupOf H) := hpS
  have hS1 := isSecOf_of_section (K := K) hxM hHM
  have hcomp2 : ∃ L K' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K' ⊤ ∧ L ≠ K' := by
    by_contra hno
    push Not at hno
    obtain ⟨L₀, hL₀, -⟩ := CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component
      hS.toGlobal.d1Global.kProper M hx.ne_top p hp
      (fun h => hpc (CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_of_hasPrimeConstraint h))
    have hnpc := h291 ↥M p _ _ _ hpl L₀ hL₀ (fun K' hK' => hno K' L₀ hK' hL₀)
    have hS2 := hS1.subgroupOf (le_refl _)
    rw [Subgroup.subgroupOf_self] at hS2
    exact false_of_hasNormalPComplement hp hnab hpS' hnpc hS2
  have hβs := hβ p ↥M _ _ _ hpl hcomp2
  exact ⟨hβs, fun C => section_dvd_component hpl hβs hSch hnab hpS' hS1 C⟩

end Front

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem l613f3_of_facts (hI : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input10_20_3)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hβ : KFactBetaStructure) (h291 : KD291a3)
    (h313 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NormalElementaryRankFour) : L613f3 := by
  intro G _ _ p P M x z hS hx hz hpc H K hHM hsec hpS h3S
  have hp := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hpl := plane63_of_situation hS hx hz
  obtain ⟨hβs, hdvd⟩ := l613_front hSch hβ h291 hS hx hz hpc hHM hsec hpS
  obtain ⟨C₀⟩ : Nonempty (CFSG.LocalCores.ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) p)) :=
    (Nat.card_pos_iff.mp (by rw [hβs.card_components]; exact hp.pos)).1
  have h3C : 3 ∣ Nat.card ↥C₀.1 := h3S.trans (hdvd C₀)
  have hrk := pRank_ge_of_beta hpl hβs hI C₀ Nat.prime_three (by norm_num) h3C
  have h4 : 4 ≤ Open.pRank 3 M := by
    have := pRank_top_subtype (by norm_num : 1 < 3) M
    have h5 := hS.p_ge
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Fh, hFh⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 M
  have hFhp : IsPGroup 3 Fh := hFh.isPGroup
  have h4' : 4 ≤ Open.pRank 3 Fh := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hFh]
    exact h4
  obtain ⟨F₀, hle⟩ := hFhp.exists_le_sylow
  obtain ⟨hD, -⟩ := p65_d1Local_of_le hS Nat.prime_three (by norm_num) h4 hFh.le hFhp
    (by omega) F₀ hle
  exact stronglyEmbedded_three_of_global hS.toGlobal h313 hD

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
