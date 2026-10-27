module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeLie
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_perfect_lift_aux {M S : Subgroup G} (hQS : pCoreOf 2 M ≤ S)
    {Lb Jb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hJb : Jb ≤ barM M (Subgroup.normalizer (S : Set G)))
    {P : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)}
    (hPle : P ≤ (Jb.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    (hP : ⁅P, P⁆ = P) (h3 : 3 ∣ Nat.card P) :
    ∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) ∧ ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
  set f₁ : ↥(Jb.subgroupOf Lb) →* ↥Lb ⧸ Subgroup.center ↥Lb :=
    (QuotientGroup.mk' (Subgroup.center ↥Lb)).comp (Jb.subgroupOf Lb).subtype with hf₁
  have hPf₁ : P ≤ f₁.range := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := hPle hy
    exact ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨R₁, hR₁, hR₁P⟩ := exists_perfect_of_perfect_image f₁ hP hPf₁
  have hd₁ : Nat.card P ∣ Nat.card R₁ := by
    rw [← hR₁P]
    exact Subgroup.card_dvd_of_surjective (f₁.subgroupMap_surjective R₁)
  set g₂ : ↥(Jb.subgroupOf Lb) →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    Lb.subtype.comp (Jb.subgroupOf Lb).subtype with hg₂
  have hg₂inj : Function.Injective g₂ :=
    Lb.subtype_injective.comp (Jb.subgroupOf Lb).subtype_injective
  set R₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := R₁.map g₂ with hR₂
  have hR₂perf : ⁅R₂, R₂⁆ = R₂ := by rw [hR₂, ← Subgroup.map_commutator, hR₁]
  have hR₂card : Nat.card R₂ = Nat.card R₁ := Subgroup.card_map_of_injective hg₂inj
  have hR₂Jb : R₂ ≤ Jb := by
    rintro _ ⟨r, -, rfl⟩
    exact Subgroup.mem_subgroupOf.1 r.2
  set f₃ : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hf₃
  obtain ⟨R₃, hR₃, hR₃R₂⟩ := exists_perfect_of_perfect_image f₃ hR₂perf
    (fun y _ => QuotientGroup.mk'_surjective _ y)
  have hd₃ : Nat.card R₂ ∣ Nat.card R₃ := by
    rw [← hR₃R₂]
    exact Subgroup.card_dvd_of_surjective (f₃.subgroupMap_surjective R₃)
  refine ⟨R₃.map M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨r.2, ?_⟩
    have h1 : f₃ r ∈ R₂ := hR₃R₂ ▸ Subgroup.mem_map_of_mem f₃ hr
    exact coe_mem_of_mk_mem_barM (hQS.trans Subgroup.le_normalizer) r (hJb (hR₂Jb h1))
  · rw [← Subgroup.map_commutator, hR₃]
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact h3.trans (hd₁.trans (hR₂card ▸ hd₃))

theorem exists_perfect_lift {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S)
    {P : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))}
    (hPle : P ≤ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L))))
    (hP : ⁅P, P⁆ = P) (h3 : 3 ∣ Nat.card P) :
    ∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) ∧ ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y :=
  exists_perfect_lift_aux hQS (barM_mono inf_le_left) hPle hP h3

end Lift

section Types

variable {G : Type} [Group G] [Finite G]

theorem nineThreeTwo_parabolic {M S L : Subgroup G} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
      ∃ T J : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)),
        IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set _) ≤ J ∧
          J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤ ∧
          J = ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map
            (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
    hS (isSylowTwoOf_inf_of_barM hL.le (twoCore_le_of_hyp hA) hA.twoRadical.isPGroup hsyl)
  obtain ⟨hcl, ⟨hJL, T, hT, hNT⟩, hO⟩ := h2
  set Lb := barM M L with hLb
  set Jb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hJb
  set q := QuotientGroup.mk' (Subgroup.center ↥Lb) with hqdef
  have hT₁ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hN : ∀ z : ↥Lb,
      q z ∈ Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) →
        (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ Subgroup.normalizer (T : Set _) := fun z hz =>
    coe_mem_normalizer_of_subgroupOf hT.1 (mem_normalizer_of_mk_center_mem_normalizer hT₁ hz)
  have hSyl : IsSylowTwoOf ((T.subgroupOf Lb).map q) ⊤ :=
    isSylowTwoOf_map_top_of_surjective hT₁ (QuotientGroup.mk'_surjective _)
  have hle : Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) ≤
      (Jb.subgroupOf Lb).map q := by
    intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr (hNT ⟨z.2, hN z hy⟩))
  have hne : (Jb.subgroupOf Lb).map q ≠
      Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) := by
    intro heq
    have hJN : Jb ≤ Subgroup.normalizer (T : Set _) := fun j hj => by
      refine hN ⟨j, hJL hj⟩ ?_
      rw [← heq]
      exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hj)
    have hTJ : T ≤ Jb := fun t ht => hNT ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
    have hTO : T ≤ barM M (S ⊓ L) := by
      rw [hO]
      exact normal_pGroup_le_pCoreOf 2 T Jb hTJ
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hJN) hT.2.1
    refine hns ⟨barM_mono inf_le_right, by rw [hO]; exact pCoreOf_isPGroup 2 Jb,
      fun hd => hT.2.2 ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hTO)
  have htop : (Jb.subgroupOf Lb).map q ≠ ⊤ := by
    intro htop
    have hZJ : Subgroup.center ↥Lb ≤ Jb.subgroupOf Lb := by
      intro z hz
      have hzc : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
          Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, hT.1 ht⟩)
      exact Subgroup.mem_subgroupOf.mpr
        (hNT ⟨z.2, Subgroup.centralizer_le_normalizer _ hzc⟩)
    refine not_barM_le_blockPL (twoCore_le_of_hyp hA) hL (fun x hx => ?_)
    have hx' : q ⟨x, hx⟩ ∈ (Jb.subgroupOf Lb).map q := htop ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjx⟩ := hx'
    have hjz : j⁻¹ * ⟨x, hx⟩ ∈ Subgroup.center ↥Lb := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥Lb), MonoidHom.mem_ker, map_mul, map_inv,
        hjx, inv_mul_cancel]
    have hmem : (⟨x, hx⟩ : ↥Lb) ∈ Jb.subgroupOf Lb := by
      have := (Jb.subgroupOf Lb).mul_mem hj (hZJ hjz)
      simpa using this
    exact Subgroup.mem_subgroupOf.mp hmem
  exact ⟨hcl, _, _, hSyl, hle, hne, htop, rfl⟩

theorem aut3Le_of_nineThreeTwo (hP : LieCyclicParabolicThree) {M S L : Subgroup G}
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (hno : ¬ HasE9 ↥(barM M L)) : Aut3Le ↥(barM M L) := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  obtain ⟨hcl, T, J, hT, hle, hne, htop, hJ⟩ := nineThreeTwo_parabolic hA hL hS h2
  rcases hP _ hcl T J hT hle hne htop with hE | hAut | ⟨P, hPJ, hPperf, hP3⟩
  · exact absurd (hasE9_of_surjective (QuotientGroup.mk'_surjective _) hE) hno
  · exact aut3Le_of_center_quotient hAut
  · exfalso
    obtain ⟨Y, hY, hYperf, hY3⟩ :=
      exists_perfect_lift (twoCore_le_of_hyp hA) (hJ ▸ hPJ) hPperf hP3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (hperf Y hY hYperf) hY3

theorem aut3Le_barM_of_nineThree (h93 : Asc81bNineThree) (hP : LieCyclicParabolicThree)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (hno : ¬ HasE9 ↥(barM M L)) : Aut3Le ↥(barM M L) := by
  have hO := lieCyclicOrthogonalThree
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact aut3Le_of_nineThreeTwo hP hA hL hS h2 hperf hno
  · rcases hO _ h3.2.1 with hE | hAut
    · exact absurd hE hno
    · exact hAut
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inl h4)) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6)))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inl h7))))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inr h8))))) hno

theorem blockCyclicThree_of_lie (h93 : Asc81bNineThree) (hP : LieCyclicParabolicThree)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (h3 : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
      Nat.card E ≤ 3)
    (U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hUN : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hU : IsPGroup 3 U) :
    (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 3 :=
  relIndex_le_three_of_aut3Le hUN hU
    (aut3Le_barM_of_nineThree h93 hP hK hA hL hX hS hperf (not_hasE9_barM h3))

end Types

end CFSG.AGLEmbedding.BlockCyc

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.BlockCyc

theorem kFactBlockCyclicThree_of_lie (h93 : Asc81bNineThree) (hP : LieCyclicParabolicThree)
    : KFactBlockCyclicThree := by
  intro G _ _ M S L hK hA hL hX hS hperf _ h3 U hUN hU
  exact blockCyclicThree_of_lie h93 hP hK hA hL hX hS hperf h3 U hUN hU

end CFSG.AGLEmbedding
