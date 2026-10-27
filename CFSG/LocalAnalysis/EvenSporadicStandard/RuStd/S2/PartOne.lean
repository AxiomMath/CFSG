module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOneE
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Janko
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.ThreeLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOneD
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

@[expose] def FanoLemma : Prop :=
  ∀ {G : Type} [Group G] (E U U₁ : Subgroup G) (t u r r₁ : G),
    Nat.card E = 8 → (∀ x ∈ E, x * x = 1) → U ≤ E → Nat.card U = 4 → U₁ ≤ E →
    Nat.card U₁ = 4 → t ∈ E → t ∉ U → u ∈ U → u ∉ U₁ → r ∈ normalizer (E : Set G) →
    r ∈ normalizer (U : Set G) → r * t = t * r → orderOf r = 3 → (∃ x ∈ U, r * x * r⁻¹ ≠ x) →
    r₁ ∈ normalizer (E : Set G) → r₁ ∈ normalizer (U₁ : Set G) → r₁ * u = u * r₁ →
    orderOf r₁ = 3 → (∃ x ∈ U₁, r₁ * x * r₁⁻¹ ≠ x) →
    ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 → ∃ y ∈ closure ({r, r₁} : Set G), y * e * y⁻¹ = e'

@[expose] def JankoFiveLemma : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {f t r r₁ : G} {D E : Subgroup G},
    orderOf f = 5 → orderOf t = 2 → f * t = t * f → Nonempty (↥D ≃* A5) →
    D ≤ centralizer ({f} : Set G) → D ≤ centralizer ({t} : Set G) → Disjoint (zpowers f) D →
    t ∉ zpowers f ⊔ D →
    centralizer ({f} : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers f ⊔ D) →
    E ≤ centralizer ({f} : Set G) → Nat.card E = 8 → (∀ x ∈ E, x * x = 1) → t ∈ E →
    r ∈ centralizer ({f} : Set G) → r ∈ normalizer (E : Set G) →
    r₁ ∈ centralizer ({f} : Set G) → r₁ ∈ normalizer (E : Set G) → orderOf r = 3 →
    orderOf r₁ = 3 →
    (∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ y ∈ closure ({r, r₁} : Set G), y * e * y⁻¹ = e') →
    ∀ {r' : G}, r' ∈ centralizer ({f} : Set G) → orderOf r' = 3 →
      25 ∣ Nat.card ↥(centralizer ({f} : Set G) ⊓ centralizer ({r'} : Set G))

variable {G : Type} [Group G]

theorem cent_pair_eq {L D : Subgroup G} {t f : G} (hc : Config G L t) (hDL : D ≤ L)
    (hDeq : L ⊓ centralizer ({f} : Set G) = zpowers f ⊔ D) (hft : f * t = t * f) :
    centralizer ({f} : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers f ⊔ D) := by
  have htf : t ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.2 hft.symm
  have htt : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  apply le_antisymm
  · rintro x ⟨hxf, hxt⟩
    rcases hc.mem_cases hxt with h1 | ⟨l, hl, rfl⟩
    · have : x ∈ zpowers f ⊔ D := hDeq ▸ ⟨h1, hxf⟩
      exact mem_sup_right this
    · have hlf : l ∈ centralizer ({f} : Set G) := by
        have := mul_mem (inv_mem htf) hxf
        simpa using this
      have : l ∈ zpowers f ⊔ D := hDeq ▸ ⟨hl, hlf⟩
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right this)
  · have hDf : D ≤ centralizer ({f} : Set G) := fun d hd =>
      (hDeq ▸ (mem_sup_right hd : d ∈ zpowers f ⊔ D) : d ∈ L ⊓ centralizer ({f} : Set G)).2
    exact sup_le (zpowers_le.2 ⟨htf, htt⟩) (sup_le
      (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_singleton_iff.2 hft⟩)
      fun d hd => ⟨hDf hd, hc.le_centralizer (hDL hd)⟩)

variable [Finite G]

theorem partThreeData_of_stage2 (hA5 : A5Lemma) (hFano : FanoLemma)
    {L L₁ : Subgroup G} {t u : G}
    (hc : Config G L t) (hc₁ : Config G L₁ u) (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hcard : Nat.card (centralizer ({(⟨u, huL⟩ : L)} : Set L)) = 116480)
    (hK : kComponent L ⟨u, huL⟩ ≤ L₁)
    (h2B : RuTwoBFacts L) (h5L : RuFiveFacts L) (h5L₁ : RuFiveFacts L₁)
    (hJ1 : JankoFiveLemma) :
    Nonempty (PartThreeData G L t) := by
  classical
  set u₀ : L := ⟨u, huL⟩ with hu₀
  have hu₀2 : orderOf u₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact hu2
  obtain ⟨f₀, hf₀K, hf₀5⟩ := h2B.elt5 u₀ hu₀2 hcard
  obtain ⟨u₁, hu₁2, hu₁ne, hu₁c⟩ := h2B.centralInv u₀ hu₀2 hcard
  have hf₀C : f₀ ∈ centralizer ({u₀} : Set L) := mem_centralizer_of_mem_derivedCentralizer hf₀K
  set f : G := (f₀ : G) with hfdef
  set u' : G := (u₁ : G) with hu'def
  have hfL : f ∈ L := f₀.2
  have hu'L : u' ∈ L := u₁.2
  have hf5 : orderOf f = 5 := by rw [hfdef, Subgroup.orderOf_coe]; exact hf₀5
  have hu'2o : orderOf u' = 2 := by rw [hu'def, Subgroup.orderOf_coe]; exact hu₁2
  have hfL₁ : f ∈ L₁ := hK ⟨f₀, hf₀K, rfl⟩
  have hfu : f * u = u * f := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hf₀C)
  have hfu' : f * u' = u' * f := congrArg Subtype.val (hu₁c f₀ hf₀C)
  have huu' : u * u' = u' * u :=
    congrArg Subtype.val (hu₁c u₀ (mem_centralizer_singleton_iff.2 rfl))
  have hne : u ≠ u' := fun h => hu₁ne (Subtype.ext h.symm)
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hu'1 : u' ≠ 1 := fun h => by rw [h, orderOf_one] at hu'2o; omega
  have hu2s : u * u = 1 := sq_eq_one_of_orderOf_two hu2
  have hu'2s : u' * u' = 1 := sq_eq_one_of_orderOf_two hu'2o
  have hftE : f * t = t * f := hc.comm f hfL
  have ht2 : orderOf t = 2 := hc.orderOf_z
  obtain ⟨hU4, hU2⟩ := klein_facts hu2s hu'2s huu' hne hu1 hu'1
  obtain ⟨hE8, hE2, htU⟩ := eight_facts hc huL hu'L ⟨hU4, hU2⟩
  have hUL : kleinOf u u' ≤ L := klein_le huL hu'L
  have hUf : kleinOf u u' ≤ centralizer ({f} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hfu.symm))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hfu'.symm))
  have hEf : eightOf u u' t ≤ centralizer ({f} : Set G) :=
    sup_le hUf (zpowers_le.2 (mem_centralizer_singleton_iff.2 hftE.symm))
  have hEu : eightOf u u' t ≤ centralizer ({u} : Set G) :=
    sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 huu'.symm)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hc.comm u huL).symm))
  obtain ⟨hU₁4, huU₁, hEeq⟩ := U1_facts hc₁ hE8 (u_mem_eight u u' t) hEu
  obtain ⟨D, hDL, hDiso, hDf, hDeq, hDdisj, hUD, hDtypeA⟩ :=
    typeA_data h5L hfL hf5 hUL hU4 hU2 (fun x hx => mem_centralizer_singleton_iff.1 (hUf hx))
  obtain ⟨r, hrD, hr3, hrNU, x, hxU, hx⟩ := normalizing_data hA5 hDiso hUD hU4
  obtain ⟨D₁, hD₁L, hD₁iso, hD₁f, hD₁eq, hD₁disj, hU₁D, -⟩ :=
    typeA_data h5L₁ hfL₁ hf5 (inf_le_right : eightOf u u' t ⊓ L₁ ≤ L₁) hU₁4
      (fun y hy => hE2 y hy.1) (fun y hy => mem_centralizer_singleton_iff.1 (hEf hy.1))
  obtain ⟨r₁, hr₁D, hr₁3, hr₁NU, x₁, hx₁U, hx₁⟩ := normalizing_data hA5 hD₁iso hU₁D hU₁4
  have hrt : r * t = t * r := hc.comm r (hDL hrD)
  have htUc : zpowers t ≤ centralizer ((kleinOf u u' : Subgroup G) : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun y hy => hc.comm y (hUL hy))
  have hrE : r ∈ normalizer ((eightOf u u' t : Subgroup G) : Set G) :=
    mem_normalizer_sup_zpowers htUc hrNU hrt
  have hr₁u : r₁ * u = u * r₁ := hc₁.comm r₁ (hD₁L hr₁D)
  have hr₁E : r₁ ∈ normalizer ((eightOf u u' t : Subgroup G) : Set G) := by
    have hu₁c : zpowers u ≤ centralizer ((eightOf u u' t ⊓ L₁ : Subgroup G) : Set G) :=
      zpowers_le.2 (mem_centralizer_iff.2 fun y hy => hc₁.comm y hy.2)
    have := mem_normalizer_sup_zpowers hu₁c hr₁NU hr₁u
    rwa [← hEeq] at this
  have htrans := hFano (eightOf u u' t) (kleinOf u u') (eightOf u u' t ⊓ L₁) t u r r₁ hE8 hE2
    le_sup_left hU4 inf_le_left hU₁4 (t_mem_eight u u' t) htU (u_mem_klein u u') huU₁ hrE hrNU
    hrt hr3 ⟨x, hxU, hx⟩ hr₁E hr₁NU hr₁u hr₁3 ⟨x₁, hx₁U, hx₁⟩
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hc.comm d (hDL hd))
  have htD : t ∉ zpowers f ⊔ D := fun h => hc.z_not_mem (sup_le (zpowers_le.2 hfL) hDL h)
  have hCt := cent_pair_eq hc hDL hDeq hftE
  have hrC : r ∈ centralizer ({f} : Set G) := hDf hrD
  have hr₁C : r₁ ∈ centralizer ({f} : Set G) := hD₁f hr₁D
  have hcardΓ := janko_card hf5 ht2 hftE hDiso hDf hDt hDdisj htD hCt hEf hE8 hE2
    (t_mem_eight u u' t) hrC hrE hr₁C hr₁E hr3 hr₁3 htrans
  have hD60 : Nat.card D = 60 := by
    obtain ⟨e⟩ := hDiso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨aD, haD⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 5 (by rw [hD60]; norm_num)
  set a : G := (aD : G) with hadef
  have ha5 : orderOf a = 5 := by rw [hadef, Subgroup.orderOf_coe]; exact haD
  have haD' : a ∈ D := aD.2
  have haf : a * f = f * a := mem_centralizer_singleton_iff.1 (hDf haD')
  have hF₁le : zpowers a ≤ centralizer (zpowers f : Set G) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (haf : Commute a f) k).eq).symm
  have hF₁disj : Disjoint (zpowers f) (zpowers a) := hDdisj.mono_right (zpowers_le.2 haD')
  have hF₁card : Nat.card ↥(zpowers f ⊔ zpowers a : Subgroup G) = 25 := by
    rw [card_sup_of_commute hF₁le hF₁disj, Nat.card_zpowers, Nat.card_zpowers, hf5, ha5]
  have hclos : closure ({r, r₁} : Set G) ≤ centralizer ({f} : Set G) :=
    (closure_le _).2 (Set.insert_subset_iff.2 ⟨hrC, Set.singleton_subset_iff.2 hr₁C⟩)
  refine ⟨{
    config := hc
    f := f
    r := r
    f_mem := hfL
    r_mem := hDL hrD
    f_ord := hf5
    r_ord := hr3
    fr_comm := (mem_centralizer_singleton_iff.1 hrC).symm
    card_Γ := hcardΓ
    inv_conj := invConj_of_janko f t (eightOf u u' t) ht2 hcardΓ hEf hE8 (t_mem_eight u u' t)
      fun e he he1 e' he' he1' => by
        obtain ⟨y, hy, hye⟩ := htrans e he he1 e' he' he1'
        exact ⟨y, hclos hy, hye⟩
    five_dvd := hJ1 hf5 ht2 hftE hDiso hDf hDt hDdisj htD hCt hEf hE8 hE2
      (t_mem_eight u u' t) hrC hrE hr₁C hr₁E hr3 hr₁3 htrans hrC hr3
    f_typeA := hDtypeA
    F₁ := zpowers f ⊔ zpowers a
    F₁_le_L := sup_le (zpowers_le.2 hfL) (zpowers_le.2 (hDL haD'))
    F₁_le_C := sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (zpowers_le.2 (hDf haD'))
    F₁_card := hF₁card }⟩

end CFSG.EvenSporadicStandard.RuStd.S2
