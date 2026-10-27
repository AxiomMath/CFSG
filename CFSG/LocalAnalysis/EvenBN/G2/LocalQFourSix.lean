module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourThree
public import CFSG.LocalAnalysis.EvenBN.Common.HeisComplement

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_sup_eq_of_subgroupOf {G : Type*} [Group G] [Finite G] {H V E : Subgroup G}
    (hVH : V ≤ H) (hEV : E ≤ V)
    (h : ∃ C : Subgroup H, C ≤ V.subgroupOf H ∧ E.subgroupOf H ⊓ C = ⊥ ∧
      Nat.card (E.subgroupOf H) * Nat.card C = Nat.card (V.subgroupOf H)) :
    ∃ C : Subgroup G, C ≤ V ∧ E ⊓ C = ⊥ ∧ E ⊔ C = V := by
  obtain ⟨C, hCV, hinf, hcard⟩ := h
  have hCV' : C.map H.subtype ≤ V := by
    have := map_mono (f := H.subtype) hCV
    rwa [subgroupOf_map_subtype, inf_eq_left.2 hVH] at this
  have hinf' : E ⊓ C.map H.subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hzE, c, hc, rfl⟩
    have h1 : c ∈ E.subgroupOf H ⊓ C := Subgroup.mem_inf.2 ⟨mem_subgroupOf.2 hzE, hc⟩
    rw [hinf, mem_bot] at h1
    rw [h1]
    exact one_mem _
  refine ⟨C.map H.subtype, hCV', hinf', Common.sup_eq_of_inf_eq_bot_of_card_le hEV hCV' hinf' ?_⟩
  rw [card_map_of_injective H.subtype_injective,
    ← Nat.card_congr (subgroupOfEquivOfLe (hEV.trans hVH)).toEquiv,
    ← Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv, hcard]

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourComplement

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_complement_of_isSylowOf_yamadaB (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) {V : Subgroup G}
    (hV : IsSylowOf 2 V (yamadaB d)) {E : Subgroup G} (hEV : E ≤ V) (hEe : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEcard : Nat.card E = Nat.card K ^ 4) :
    ∃ C : Subgroup G, C ≤ V ∧ E ⊓ C = ⊥ ∧ E ⊔ C = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kc, hKc, hKle, hcase⟩ := h.yamada_5_10_layer_of_cat d hK hK4 hcat
  have hZ : center Kc = ⊥ := by
    rcases hcase with ⟨-, -, -, -, hZ, -⟩ | ⟨-, -, hZ, -⟩ <;> exact hZ
  have hB := h.map_yamadaB_eq d hK4 hKc hZ hKle
  have hKH : d.leviA2 ≤ centralizer (d.J₁ : Set G) := d.leviA2_le_centralizer_J₁ hK4
  have hVH : V ≤ centralizer (d.J₁ : Set G) := hV.le.trans (yamadaB_le_centralizer_J₁ d)
  have hcase' : (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = Kc ∧
        LieModel Kc .PSL 3 2 (2 * 2)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom,
          x * y = y * x) ∧
        Kc ⊓ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = ⊥ ∧
        LieModel Kc .PSL 3 2 2 ∧
        LieModel (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom)
          .PSL 3 2 2) := by
    rcases hcase with ⟨heq, -, -, -, -, hlie⟩ | ⟨-, hcomm, -, ⟨e⟩⟩
    · exact Or.inl ⟨heq, hlie⟩
    · right
      set tb := QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
        ⟨t, h.t_mem_centralizer_J₁ d⟩ with htb
      have hKcc : ∀ x ∈ Kc, ∀ y ∈ Kc.map (MulAut.conj tb).toMonoidHom, x * y = y * x :=
        fun x hx y hy => by
          have := commutator_mem_commutator hx hy
          rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
      have hKcinf : Kc ⊓ Kc.map (MulAut.conj tb).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hyc : (⟨y, (Subgroup.mem_inf.1 hy).1⟩ : Kc) ∈ center Kc :=
          mem_center_iff.2 fun x => Subtype.ext (hKcc x x.2 y (Subgroup.mem_inf.1 hy).2)
        rw [hZ, mem_bot] at hyc
        exact mem_bot.2 (congrArg Subtype.val hyc)
      obtain ⟨hcompK, -, -⟩ := h.yamada_5_10_hr7 d hK4
      have hne' := SeitzReduction.ne_bot_of_isQuasisimple hcompK.2.2
      have hKbm := SeitzReduction.LinearPilot.lieModel_quotient_center_map_oddCore hKH
        (d.isQuasisimple_leviA2 hK4) (d.lieModel_leviA2 hK4) hne'
      have hZK : center ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G))))) = ⊥ := by
        rw [← map_center_eq e, hZ, Subgroup.map_bot]
      have hKbl := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot) hKbm
      have hKcl := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hKbl
      exact ⟨hKcc, hKcinf, hKcl, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (Kc.equivMapOfInjective (MulAut.conj tb).toMonoidHom (MulAut.conj tb).injective) hKcl⟩
  have hV' : IsSylowOf 2 (V.subgroupOf (centralizer (d.J₁ : Set G)))
      ((yamadaB d).subgroupOf (centralizer (d.J₁ : Set G))) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.2 hVH,
      inf_eq_left.2 (yamadaB_le_centralizer_J₁ d)]
    exact hV
  have hEH := hEV.trans hVH
  refine exists_sup_eq_of_subgroupOf hVH hEV
    (Common.exists_complement_of_isSylowOf_of_map_eq hB (g := 2) (by norm_num) hcase' hV'
      (fun x hx => hEV hx)
      (fun e he => Subtype.ext (hEe _ (mem_subgroupOf.1 he)))
      (fun e he e' he' => Subtype.ext (hEc _ (mem_subgroupOf.1 he) _ (mem_subgroupOf.1 he')))
      ?_)
  rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv, hEcard, hK4]
  norm_num

end QFourComplement

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
