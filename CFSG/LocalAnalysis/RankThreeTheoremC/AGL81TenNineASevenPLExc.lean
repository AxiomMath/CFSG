module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineASevenPLStar
public import CFSG.GroupTheory.AltSevenModule.Normalizer
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Goldschmidt75.Closure
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeLS

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

attribute [local instance] Coordinator.blockVCommGroup

theorem relIndex_eq_315_of_card_eight {V : Type*} [Group V]
    {Sstar Lstar : Subgroup (MulAut V)} (hSs : Sstar ≤ Lstar)
    (e : ↥Lstar ≃* alternatingGroup (Fin 7)) (h8 : Nat.card Sstar = 8) :
    Sstar.relIndex Lstar = 315 := by
  have hcardL : Nat.card Lstar = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hmul := Subgroup.relIndex_mul_card Sstar Lstar
  rw [inf_eq_left.2 hSs, h8, hcardL] at hmul
  omega

theorem card_commV_range_eq_sixteen (h16 : Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4)
    (ε : ↥(autOn L (blockV S L)) ≃* alternatingGroup (Fin 7)) :
    Nat.card (commV ((autOn L (blockV S L)).subtype.comp ε.symm.toMonoidHom).range) = 16 := by
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥(blockV S L) :=
    (autOn L (blockV S L)).subtype.comp ε.symm.toMonoidHom
  have hrange : ρ.range = autOn L (blockV S L) := by
    show ((autOn L (blockV S L)).subtype.comp ε.symm.toMonoidHom).range =
      autOn L (blockV S L)
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ ε.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hcard : Nat.card (@commV ↥(blockV S L) (Coordinator.blockVCommGroup S L)
      (autOn L (blockV S L))) = Nat.card ↥⁅blockV S L, L⁆ := by
    rw [← Subgroup.card_map_of_injective (f := (blockV S L).subtype)
      (blockV S L).subtype_injective,
      Coordinator.map_commV_autOn_blockV
        (le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L))]
  rw [hrange]
  exact hcard.trans (by rw [h16]; norm_num)

theorem exists_offender_alt7 (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹)
    (ε : ↥(autOn L (blockV S L)) ≃* alternatingGroup (Fin 7)) :
    ∃ A₀ : Subgroup ↥(alternatingGroup (Fin 7)),
      A₀ ≤ ((autOn S (blockV S L)).subgroupOf (autOn L (blockV S L))).map ε.toMonoidHom ∧
      A₀ ≠ ⊥ ∧ (∀ a ∈ A₀, a ^ 2 = 1) ∧
      Nat.card ↥(blockV S L) ≤ Nat.card A₀ *
        Nat.card (fixV (A₀.map
          ((autOn L (blockV S L)).subtype.comp ε.symm.toMonoidHom))) := by
  let V := blockV S L
  let Lstar := autOn L (blockV S L)
  let Sstar := autOn S V
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥V := Lstar.subtype.comp ε.symm.toMonoidHom
  have hSs : Sstar ≤ Lstar := autOn_le_autOn_of_act hact
  obtain ⟨A, hAmax, hAQ⟩ := Coordinator.exists_isMaxElemAbelian_not_le hA hL hSL
  have hAcent : ¬ A ≤ Subgroup.centralizer (V : Set G) :=
    Coordinator.not_le_centralizer_blockV_of_not_le hA hL hSL hAmax.1 hAQ
  have hFF : IsFFModule Sstar :=
    isFFModule_autOn (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _)
      (Coordinator.blockV_le hA hL hSL)
      (le_sup_right.trans (Coordinator.sup_le_normalizer_blockV S L)) hAmax.1 hAmax hAcent
  obtain ⟨B, hBle, hBne, hB2, hBoff⟩ := hFF
  refine ⟨(B.subgroupOf Lstar).map ε.toMonoidHom, Subgroup.map_mono (Subgroup.subgroupOf_mono _
    hBle), ?_, ?_, ?_⟩
  · intro hbot
    have h1 : B.subgroupOf Lstar = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (B.subgroupOf Lstar) (f := ε.toMonoidHom)
        ε.injective).mp (show (B.subgroupOf Lstar).map ε.toMonoidHom = ⊥ from hbot)
    exact hBne ((Subgroup.subgroupOf_eq_bot.mp h1).eq_bot_of_le (hBle.trans hSs))
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hbB : (b : MulAut ↥V) ∈ B := hb
    have hb2 : b ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hB2.2 (b : MulAut ↥V) hbB
    rw [← map_pow, hb2, map_one]
  · have hcomp : ∀ x : ↥Lstar, ρ (ε x) = (x : MulAut ↥V) := by
      intro x
      show ((ε.symm (ε x) : ↥Lstar) : MulAut ↥V) = (x : MulAut ↥V)
      rw [MulEquiv.symm_apply_apply]
    have hmap : ((B.subgroupOf Lstar).map ε.toMonoidHom).map ρ = B := by
      have hcomp' : ρ.comp ε.toMonoidHom = Lstar.subtype := MonoidHom.ext hcomp
      rw [Subgroup.map_map, hcomp', Subgroup.map_subgroupOf_eq_of_le (hBle.trans hSs)]
    have hcardB : Nat.card ((B.subgroupOf Lstar).map ε.toMonoidHom) = Nat.card B := by
      rw [Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBle.trans hSs)).toEquiv]
    rw [hcardB, hmap]
    exact hBoff

theorem mem_barM_normalizer_inf_of_mem_normalizer_alt7
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    {θ : ↥(barM M L) ≃* ↥(autOn L (blockV S L))}
    (hθ : ∀ (l : G) (hl : l ∈ L) (hlV : l ∈ Subgroup.normalizer (blockV S L : Set G)),
      ((θ (Proving.barMHomSub hL.le ⟨l, hl⟩) : ↥(autOn L (blockV S L))) :
        MulAut ↥(blockV S L)) = conjAct (blockV S L) ⟨l, hlV⟩)
    {ε : ↥(autOn L (blockV S L)) ≃* alternatingGroup (Fin 7)}
    (hSs : autOn S (blockV S L) ≤ autOn L (blockV S L))
    {e : ↥(alternatingGroup (Fin 7))}
    (he : e ∈ Subgroup.normalizer
      (((autOn S (blockV S L)).subgroupOf (autOn L (blockV S L))).map ε.toMonoidHom :
        Subgroup ↥(alternatingGroup (Fin 7)))) :
    (((ε.symm.trans θ.symm) e : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
  have hmapN : (Subgroup.normalizer
      ((autOn S (blockV S L)).subgroupOf (autOn L (blockV S L)))).map ε.toMonoidHom =
      Subgroup.normalizer (((autOn S (blockV S L)).subgroupOf
        (autOn L (blockV S L))).map ε.toMonoidHom) :=
    Subgroup.map_equiv_normalizer_eq _ ε
  have heN : ε.symm e ∈ Subgroup.normalizer
      ((autOn S (blockV S L)).subgroupOf (autOn L (blockV S L))) :=
    (Subgroup.mem_map_equiv (f := ε) (K := Subgroup.normalizer
      ((autOn S (blockV S L)).subgroupOf (autOn L (blockV S L))))).mp (hmapN ▸ he)
  have hzN : (ε.symm e : MulAut ↥(blockV S L)) ∈
      Subgroup.normalizer (autOn S (blockV S L)) :=
    CFSG.Goldschmidt75.mem_normalizer_of_mem_normalizer_subgroupOf hSs heN
  obtain ⟨l, hl⟩ := Proving.barMHomSub_surjective hL.le ((ε.symm.trans θ.symm) e)
  have hlV : (l : G) ∈ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L) l.2
  have hconj : conjAct (blockV S L) ⟨l.1, hlV⟩ = (ε.symm e : MulAut ↥(blockV S L)) := by
    have h := hθ l.1 l.2 hlV
    rw [show Proving.barMHomSub hL.le (⟨l.1, l.2⟩ : ↥L) = (ε.symm.trans θ.symm) e from hl] at h
    have h2 : ((θ ((ε.symm.trans θ.symm) e) : ↥(autOn L (blockV S L))) :
        MulAut ↥(blockV S L)) = (ε.symm e : MulAut ↥(blockV S L)) := by
      rw [show (ε.symm.trans θ.symm) e = θ.symm (ε.symm e) from rfl,
        MulEquiv.apply_symm_apply]
    rw [h2] at h
    exact h.symm
  have hzN' : conjAct (blockV S L) ⟨l.1, hlV⟩ ∈
      Subgroup.normalizer (autOn S (blockV S L) : Set (MulAut ↥(blockV S L))) := by
    rw [hconj]
    exact hzN
  have hlN : (l : G) ∈ Subgroup.normalizer (S : Set G) :=
    mem_normalizer_of_conjAct_mem_normalizer hA hL hSL hZ l.2 hlV hzN'
  refine Subgroup.mem_map.mpr ⟨⟨l.1, hL.le l.2⟩, ⟨hlN, l.2⟩, ?_⟩
  rw [QuotientGroup.mk'_apply, ← hl, Proving.coe_barMHomSub]
  rfl

theorem exists_elemAbelian_three_of_a7Exceptional
    (hX : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hnX : ¬ InClassXBlock L)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin 7))
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹)
    (h16 : Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4) :
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  let V := blockV S L
  letI := Coordinator.blockVCommGroup S L
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v =>
    Subtype.ext ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf
      (pCoreOf 2 (L ⊔ S))).2 (v : G) v.2)
  have hZ := center_barM_sup_eq_bot hA hL hSL e
  obtain ⟨θ, hθ⟩ := exists_barMEquiv_autOn hA hL hSL hZ
  let ε : ↥(autOn L V) ≃* alternatingGroup (Fin 7) := θ.symm.trans e
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥V :=
    (autOn L V).subtype.comp ε.symm.toMonoidHom
  have hρ : Function.Injective ρ := by
    intro x y hxy
    exact ε.symm.injective (Subtype.ext hxy)
  have h16' : Nat.card (commV ρ.range) = 16 := card_commV_range_eq_sixteen h16 ε
  let Sstar := autOn S V
  let Lstar := autOn L V
  have hSs : Sstar ≤ Lstar := autOn_le_autOn_of_act hact
  let T : Subgroup ↥(alternatingGroup (Fin 7)) := (Sstar.subgroupOf Lstar).map ε.toMonoidHom
  have hSstar2 : IsPGroup 2 Sstar := by
    show IsPGroup 2 (autOn S (blockV S L))
    exact CFSG.Quasithin.AutOn.isPGroup_autOn hA.twoRadical.isPGroup
  have hT2 : IsPGroup 2 T := by
    have hsub : IsPGroup 2 (Sstar.subgroupOf Lstar) :=
      IsPGroup.of_equiv (hG := hSstar2) (Subgroup.subgroupOfEquivOfLe hSs).symm
    exact hsub.map ε.toMonoidHom
  have hT8 : Nat.card T ≠ 8 := by
    intro h8
    have hcardT : Nat.card T = Nat.card (Sstar.subgroupOf Lstar) :=
      Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective
    have hcardSsub : Nat.card (Sstar.subgroupOf Lstar) = Nat.card Sstar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSs).toEquiv
    have hcardS : Nat.card Sstar = 8 := by
      rw [← hcardSsub, ← hcardT]
      exact h8
    have hrel : Sstar.relIndex Lstar = 315 :=
      relIndex_eq_315_of_card_eight hSs ε hcardS
    have hodd : ¬ 2 ∣ Sstar.relIndex Lstar := by
      rw [hrel]
      norm_num
    have hsyl : IsSylowTwoOf (S ⊓ L) L :=
      isSylowTwoOf_inf_of_relIndex hA hL hSL hZ hSs hodd
    exact hnX (asc81bEightFive_of_factorization aschbacherLocalFactorization_proved G M S L
      hX hA hL.toIsTwoPrimeComponent hsyl)
  obtain ⟨A₀, hA₀T, hA₀1, hA₀2, hoff⟩ := exists_offender_alt7 hA hL hSL hact ε
  obtain ⟨E₀, hE₀N, hE₀ab, hE₀9⟩ :=
    CFSG.GroupTheory.AltSevenModule.exists_elemAbelian_three_le_normalizer_of_offender
      hV2 ρ hρ h16' hT2 hT8 hA₀T hA₀1 hA₀2 hoff
  refine ⟨(E₀.map (ε.symm.trans θ.symm).toMonoidHom).map (barM M L).subtype, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    exact mem_barM_normalizer_inf_of_mem_normalizer_alt7 hA hL hSL hZ hθ hSs (hE₀N he)
  · exact CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.map hE₀ab (ε.symm.trans θ.symm).toMonoidHom)
      (barM M L).subtype
  · rw [Subgroup.card_map_of_injective (f := (barM M L).subtype) (barM M L).subtype_injective,
      Subgroup.card_map_of_injective (f := (ε.symm.trans θ.symm).toMonoidHom)
        (ε.symm.trans θ.symm).injective, hE₀9]

end CFSG.LocalAnalysis.RankThreeTheoremC
