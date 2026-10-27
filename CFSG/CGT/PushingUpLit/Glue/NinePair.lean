module

public import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
public import CFSG.CGT.PushingUpLit.Glue.BlockJ
public import CFSG.CGT.PushingUpLit.BlocksCommuteCore
public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.CGT.PushingUpLit.NineChoiceSteps

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

structure NinePair {G : Type} [Group G] [Finite G] (M I Y L : Subgroup G) : Prop where
  inClassX : InClassX ↥Y
  not_le : ¬ Y ≤ M
  le_normalizer : I ≤ Subgroup.normalizer (Y : Set G)
  commutator_eq : ⁅Y, I⁆ = Y
  I_le : I ≤ L
  Y_le : Y ≤ L
  subnormal : (Y.subgroupOf L).IsSubnormal
  oTwo_ne_bot : oTwoIn L ≠ ⊥
  closed : Subgroup.normalizer (oTwoIn L : Set G) ≤ L

section Base

variable {G : Type} [Group G] [Finite G]

theorem characteristicCoreStar_subgroupOf_le {H S M : Subgroup G} (T' : Sylow 2 ↥H)
    (hT' : (T' : Subgroup ↥H) = S.subgroupOf H) (hSH : S ≤ H)
    (hC : Subgroup.centralizer (omegaOneCenterIn S : Set G) ⊓ H ≤ M)
    (hN : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS S →
      (B.subgroupOf (pushingUpS S)).Characteristic → Subgroup.normalizer (B : Set G) ⊓ H ≤ M) :
    characteristicCoreStar (T' : Subgroup ↥H) ≤ M.subgroupOf H := by
  rw [hT']
  refine sup_le ?_ (iSup_le fun B' => iSup_le fun hB' => ?_)
  · intro x hx
    have hx' := coe_mem_centralizer_map hx
    rw [map_omegaOneCenterIn_subgroupOf hSH] at hx'
    exact hC (Subgroup.mem_inf.2 ⟨hx', x.2⟩)
  · intro x hx
    obtain ⟨hB'0, hB'S, hB'c⟩ := hB'
    have hBS : B'.map H.subtype ≤ pushingUpS S := by
      rw [← map_pushingUpS_subgroupOf hSH]
      exact Subgroup.map_mono hB'S
    have hsub : (B'.map H.subtype).subgroupOf H = B' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective B'
    have hBc : ((B'.map H.subtype).subgroupOf (pushingUpS S)).Characteristic := by
      refine (characteristic_pushingUpS_subgroupOf_iff hSH hBS).mp ?_
      rw [hsub]
      exact hB'c
    have hB0 : B'.map H.subtype ≠ ⊥ := fun hb =>
      hB'0 ((Subgroup.map_eq_bot_iff_of_injective B' H.subtype_injective).mp hb)
    exact hN _ hB0 hBS hBc (Subgroup.mem_inf.2 ⟨coe_mem_normalizer_map hx, x.2⟩)

theorem exists_btBlock_not_le (h : BHSLocalCStar) {Γ : Type} [Group Γ] [Finite Γ]
    (hchar : IsCharacteristicP 2 Γ) (T : Sylow 2 Γ) {M' : Subgroup Γ}
    (hM' : characteristicCoreStar (T : Subgroup Γ) ≤ M') (hne : M' ≠ ⊤) :
    ∃ E : Subgroup Γ, E.IsSubnormal ∧ IsBTBlock ⊤ (T : Subgroup Γ) E ∧ InClassX ↥E ∧
      ¬ E ≤ M' := by
  have hC : characteristicCoreStar (T : Subgroup Γ) ≠ ⊤ := fun h1 =>
    hne (top_le_iff.1 (h1 ▸ hM'))
  have hC' : cStarIn (⊤ : Subgroup Γ) (T : Subgroup Γ) ≠ ⊤ := by
    rwa [← characteristicCoreStar_eq_cStarIn]
  have hch := charTwo_top_of_isCharacteristicP hchar
  obtain ⟨𝒢, hB, hinv, hcomm, hgen, -⟩ := h Γ ⊤ T hch (isSylowOf_top T) hC'
  have hinv' : ∀ F ∈ 𝒢, ∀ g : Γ, CFSG.Quasithin.A1b.conjSub g F ∈ 𝒢 := fun F hF g =>
    hinv F hF g (Subgroup.mem_top g)
  by_contra hall
  push Not at hall
  have hle : ∀ E ∈ 𝒢, E ≤ M' := by
    intro E hE
    have hsub : E.IsSubnormal := isSubnormal_of_mem_family hinv' hcomm hE
    exact hall E hsub (hB E hE) (inClassX_of_isBTBlock (hB E hE)
      (charTwo_of_isSubnormal_top hch hsub))
  apply hne
  refine top_le_iff.1 ?_
  rw [← characteristicCoreStar_eq_cStarIn] at hgen
  rw [← hgen]
  exact sup_le hM' (iSup₂_le fun E hE => hle E hE)

theorem jIn_eq_thompsonJ' {X : Type} [Group X] [Finite X] (P : Subgroup X) :
    jIn P = CFSG.Quasithin.thompsonJ P :=
  CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ P

theorem exists_base_pair (h : BHSLocalCStar) (hchar : CFSG.Assembly.IsCharTwoType G)
    (T : Sylow 2 G) {I H S : Subgroup G}
    (hc : NineChoice (characteristicCoreStar (T : Subgroup G)) I H S) :
    ∃ Y : Subgroup G, NinePair (characteristicCoreStar (T : Subgroup G)) I Y H := by
  have hHloc : IsPLocal 2 H := hc.maxLocal.1
  have hHchar : IsCharacteristicP 2 ↥H := isCharacteristicP_of_isPLocal hchar hHloc
  have hSH : S ≤ H := hc.sylow.1
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf hc.sylow
  have hcore := characteristicCoreStar_subgroupOf_le T' hT' hSH hc.centralizer_le
    hc.normalizer_char_le
  have hne : (characteristicCoreStar (T : Subgroup G)).subgroupOf H ≠ ⊤ := fun htop =>
    hc.not_le (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨E', hsub, hblock, hX, hEM⟩ := exists_btBlock_not_le h hHchar T' hcore hne
  have hWT : oTwoIn E' ≤ (T' : Subgroup ↥H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : (pCore 2 ↥H).Normal := pCore_normal
    exact (oTwoIn_le_pCore hsub).trans (IsPGroup.le_sylow_of_normal pCore_isPGroup T')
  obtain ⟨hJn, hJc⟩ := commutator_thompsonJ_eq hblock hX T'.isPGroup' hWT
  have hjS : jIn S = I :=
    (hc.sylow_jIn H S hHchar (hc.I_le_S.trans hSH) hc.not_le hc.sylow hc.I_le_S).1
  have hI : (CFSG.Quasithin.thompsonJ (T' : Subgroup ↥H)).map H.subtype = I := by
    rw [← jIn_eq_thompsonJ', hT', ← hjS]
    exact map_jIn_subgroupOf hSH
  have hYsub : (E'.map H.subtype).subgroupOf H = E' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective E'
  have hHne : oTwoIn H ≠ ⊥ := fun hb =>
    pCore_ne_bot_of_isPLocal hHloc
      ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 hb)
  refine ⟨E'.map H.subtype, ?_⟩
  exact
    { inClassX := InClassX.of_mulEquiv (E'.equivMapOfInjective H.subtype H.subtype_injective) hX
      not_le := fun hle => hEM fun x hx => hle (Subgroup.mem_map_of_mem H.subtype hx)
      le_normalizer := by
        intro i hi
        rw [← hI] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        exact coe_mem_normalizer_map (hJn hj)
      commutator_eq := by
        rw [← hI, ← Subgroup.map_commutator, hJc]
      I_le := hc.I_le_S.trans hSH
      Y_le := Subgroup.map_subtype_le E'
      subnormal := by
        rw [hYsub]
        exact hsub
      oTwo_ne_bot := hHne
      closed := by
        have hloc : IsPLocal 2 (Subgroup.normalizer (oTwoIn H : Set G)) :=
          isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn H) hHne
        have hle : H ≤ Subgroup.normalizer (oTwoIn H : Set G) :=
          Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn H)
        by_contra hnot
        exact hc.maxLocal.2 _ (lt_of_le_of_ne hle fun heq => hnot heq.symm.le) hloc }

end Base

end CFSG.CGT.PushingUpLit.Glue
