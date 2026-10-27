module

public import CFSG.LocalAnalysis.GH72.Sec4FourFactor
import CFSG.LocalAnalysis.GH72.G3aOdd
import CFSG.LocalAnalysis.GH72.Sec2
public import CFSG.LocalAnalysis.GH72.Sec4Induction

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (twoResidualOf)
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm
  card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn isElemAbelian_two_iff)

section Assembly

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem conj_mem_normalizer_of_mem_normalizer_map {A : Subgroup Y} {g m : Y}
    (hm : m ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) :
    g⁻¹ * m * g ∈ normalizer (A : Set Y) := by
  have key : ∀ y, y ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ A := fun y => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      show g⁻¹ * (g * a * g⁻¹) * g ∈ A
      rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
    · intro h
      refine ⟨_, h, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  rw [mem_normalizer_iff] at hm ⊢
  intro a
  have h1 := key (g * a * g⁻¹)
  have h3 := key (m * (g * a * g⁻¹) * m⁻¹)
  rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group] at h1
  rw [show g⁻¹ * (m * (g * a * g⁻¹) * m⁻¹) * g = g⁻¹ * m * g * a * (g⁻¹ * m * g)⁻¹ by group]
    at h3
  exact h1.symm.trans ((hm (g * a * g⁻¹)).trans h3)

theorem mem_normalizer_of_odd_of_le_sup {T₁ T₂ A : Subgroup Y} (hT₁₂ : T₁ ⊓ T₂ = ⊥)
    (hTc : T₂ ≤ centralizer (T₁ : Set Y)) (hD₁ : IsDih T₁) (hD₂ : IsDih T₂) (hA : IsE16 A)
    (hAT : A ≤ T₁ ⊔ T₂) {u : Y} (hu : Odd (orderOf u))
    (huN : u ∈ normalizer ((T₁ ⊔ T₂ : Subgroup Y) : Set Y)) :
    u ∈ normalizer (A : Set Y) := by
  rcases hD₂.isKleinFour_or_isDihNonab with hV₂ | hN₂
  · rcases hD₁.isKleinFour_or_isDihNonab with hV₁ | hN₁
    · have := hV₁
      have := hV₂
      have hcard : Nat.card (T₁ ⊔ T₂ : Subgroup Y) = 16 := by
        rw [card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy =>
            mem_centralizer_iff.1 (hTc hy) x hx) hT₁₂, IsKleinFour.card_four (G := ↥T₁),
          IsKleinFour.card_four (G := ↥T₂)]
      have heq : A = T₁ ⊔ T₂ := eq_of_le_of_card_ge hAT (by rw [hcard, hA.2])
      rw [heq]
      exact huN
    · have hd : DDDecomp (T₂ ⊔ T₁) T₂ T₁ :=
        ⟨rfl, by rwa [inf_comm], le_centralizer_iff.1 hTc, hD₂, hN₁⟩
      rw [sup_comm] at huN hAT
      exact odd_normalizes_e16_of_dd hd hu huN hAT hA
  · exact odd_normalizes_e16_of_dd ⟨rfl, hT₁₂, hTc, hD₁, hN₂⟩ hu huN hAT hA

theorem exists_normal_factors_of
    (hO : CFSG.oddCore Y = ⊥) {J T₁ T₂ F₁ F₂ A : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hT : IsSylowOf 2 (T₁ ⊔ T₂) J)
    (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y)) (hD₁ : IsDih T₁)
    (hD₂ : IsDih T₂)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFK₂ : F₂ ≤ twoResidualOf ⊤)
    (hFn₁ : (F₁.subgroupOf (twoResidualOf ⊤)).Normal)
    (hFn₂ : (F₂.subgroupOf (twoResidualOf ⊤)).Normal) (hF₁₂ : F₁ ⊓ F₂ = ⊥)
    (hFodd : Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)))
    (hA₁ : IsAStarFactor F₁) (hA₂ : IsAStarFactor F₂)
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) (hW₂ : IsSylowOf 2 (T₂ ⊓ F₂) F₂)
    (hNI : ∀ x ∈ twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y),
      x * x = 1 → x = 1)
    (hAJ : A ≤ J) (hA : IsE16 A) :
    ∃ L₁ L₂ : Subgroup Y, T₁ ≤ L₁ ∧ T₂ ≤ L₂ ∧ L₁ ≤ J ∧ L₂ ≤ J ∧
      J ≤ normalizer (L₁ : Set Y) ∧ J ≤ normalizer (L₂ : Set Y) ∧ L₁ ⊓ L₂ = ⊥ ∧
      L₂ ≤ centralizer (L₁ : Set Y) ∧ J ≤ (L₁ ⊔ L₂) ⊔ (J ⊓ normalizer (A : Set Y)) ∧
      IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧ IsSylowOf 2 T₁ L₁ ∧ IsSylowOf 2 T₂ L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₁, hTL₁, hL₁J, hJL₁, hL₁syl, hL₁t⟩ := exists_factor_of hO hKJ hT hT₁₂ hTc hD₁ hfus
    hFK₁ hFK₂ hFn₁ hFn₂ hF₁₂ hFodd hA₁ hA₂ hW₁ hW₂ hNI
  have hfus' : ∀ x ∈ T₂ ⊔ T₁, ∀ y ∈ T₂ ⊔ T₁, orderOf x = 2 → IsConj x y →
      (x ∈ T₂ ↔ y ∈ T₂) ∧ (x ∈ T₁ ↔ y ∈ T₁) := by
    intro x hx y hy hx2 hxy
    rw [sup_comm] at hx hy
    exact (hfus x hx y hy hx2 hxy).symm
  obtain ⟨L₂, hTL₂, hL₂J, hJL₂, hL₂syl, hL₂t⟩ := exists_factor_of hO hKJ (by rwa [sup_comm])
    (by rwa [inf_comm]) (le_centralizer_iff.1 hTc) hD₂ hfus' hFK₂ hFK₁ hFn₂ hFn₁
    (by rwa [inf_comm]) (by rwa [sup_comm]) hA₂ hA₁ hW₂ hW₁ hNI
  have hTp : IsPGroup 2 (T₁ ⊔ T₂ : Subgroup Y) := hT.isPGroup
  have hTL₂' : (T₁ ⊔ T₂) ⊓ L₂ = T₂ :=
    hL₂syl.eq_of_le (le_inf le_sup_right hTL₂) inf_le_right (hTp.to_le inf_le_left)
  have hJ12 : J ≤ normalizer ((L₁ ⊓ L₂ : Subgroup Y) : Set Y) := fun g hg =>
    mem_normalizer_inf_of_mem (hJL₁ hg) (hJL₂ hg)
  have hsyl12 := hT.inf_of_le_normalizer (inf_le_left.trans hL₁J) hJ12
  have hbot12 : (T₁ ⊔ T₂) ⊓ (L₁ ⊓ L₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxT₂ : x ∈ T₂ := by
      rw [← hTL₂']
      exact mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (mem_inf.1 hx).2).2⟩
    have hxT₁ : x ∈ T₁ := by
      have h : (T₁ ⊔ T₂) ⊓ L₁ = T₁ :=
        hL₁syl.eq_of_le (le_inf le_sup_left hTL₁) inf_le_right (hTp.to_le inf_le_left)
      rw [← h]
      exact mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (mem_inf.1 hx).2).1⟩
    have h : x ∈ T₁ ⊓ T₂ := mem_inf.2 ⟨hxT₁, hxT₂⟩
    rwa [hT₁₂] at h
  rw [hbot12] at hsyl12
  have hinf : L₁ ⊓ L₂ = ⊥ :=
    eq_bot_of_odd_of_le_normalizer hO hKJ hJ12 (odd_card_of_isSylowOf_bot hsyl12)
  have hcomm : L₂ ≤ centralizer (L₁ : Set Y) :=
    le_centralizer_of_le_normalizer_of_inf_eq_bot hL₂J hL₁J hJL₂ hJL₁ (by rwa [inf_comm])
  have hJL : J ≤ normalizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := le_normalizer_sup hJL₁ hJL₂
  have hTL : T₁ ⊔ T₂ ≤ L₁ ⊔ L₂ := sup_le_sup hTL₁ hTL₂
  have hFr := le_sup_inf_normalizer_of_isSylowOf (sup_le hL₁J hL₂J) hJL
    (hT.of_le hTL (sup_le hL₁J hL₂J))
  obtain ⟨g, hgJ, hgA⟩ := exists_mem_map_conj_le_of_isSylowOf hT hAJ
    (IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num))
  have hA' : IsE16 (A.map (MulAut.conj g).toMonoidHom) := hA.map _ (MulAut.conj g).injective
  have hNT : J ⊓ normalizer ((T₁ ⊔ T₂ : Subgroup Y) : Set Y) ≤
      (T₁ ⊔ T₂) ⊔ (J ⊓ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) := by
    have hTsyl : IsSylowOf 2 (T₁ ⊔ T₂) (J ⊓ normalizer ((T₁ ⊔ T₂ : Subgroup Y) : Set Y)) :=
      hT.of_le (le_inf hT.le le_normalizer) inf_le_left
    obtain ⟨k, hk⟩ :=
      exists_relIndex_twoResidualOf (J ⊓ normalizer ((T₁ ⊔ T₂ : Subgroup Y) : Set Y))
    refine (le_sup_of_isSylowOf_of_relIndex hTsyl hk).trans (sup_le_sup_left ?_ _)
    refine twoResidualOf_le_of_forall fun x hx hxo => mem_inf.2 ⟨(mem_inf.1 hx).1, ?_⟩
    exact mem_normalizer_of_odd_of_le_sup hT₁₂ hTc hD₁ hD₂ hA' hgA hxo (mem_inf.1 hx).2
  have hJA' : J ≤ (L₁ ⊔ L₂) ⊔
      (J ⊓ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) :=
    hFr.trans (sup_le le_sup_left (hNT.trans (sup_le (hTL.trans le_sup_left) le_sup_right)))
  have hJA : J ≤ (L₁ ⊔ L₂) ⊔ (J ⊓ normalizer (A : Set Y)) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ J := mul_mem (mul_mem hgJ hx) (inv_mem hgJ)
    obtain ⟨l, hl, m, hm, hlm⟩ :=
      (mem_sup_iff_of_le_normalizer (inf_le_left.trans hJL)).1 (hJA' hx')
    have hl' : g⁻¹ * l * g ∈ L₁ ⊔ L₂ := by
      have h := (mem_normalizer_iff.1 (hJL (inv_mem hgJ)) l).1 hl
      rwa [inv_inv] at h
    have hm' : g⁻¹ * m * g ∈ J ⊓ normalizer (A : Set Y) :=
      mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hgJ) (mem_inf.1 hm).1) hgJ,
        conj_mem_normalizer_of_mem_normalizer_map (mem_inf.1 hm).2⟩
    have e : x = g⁻¹ * l * g * (g⁻¹ * m * g) := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (l * m) * g := by rw [hlm]
        _ = g⁻¹ * l * g * (g⁻¹ * m * g) := by group
    rw [e]
    exact mul_mem (mem_sup_left hl') (mem_sup_right hm')
  exact ⟨L₁, L₂, hTL₁, hTL₂, hL₁J, hL₂J, hJL₁, hJL₂, hinf, hcomm, hJA, hL₁t, hL₂t, hL₁syl,
    hL₂syl⟩

end Assembly

section Bar

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_inf_centralizer {H : Subgroup G} (hiso : ∀ t, ¬ IsIsolatedIn H t)
    {x : Bar H}
    (hx : x ∈ twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup (Bar H)) : Set (Bar H)))
    (hx2 : x * x = 1) : x = 1 := by
  by_contra hx1
  have : (twoResidualOf (⊤ : Subgroup (Bar H))).Normal := twoResidualOf_top_normal
  set K := twoResidualOf (⊤ : Subgroup (Bar H)) with hK
  let Ω : Subgroup (Bar H) :=
    { carrier := {x | x ∈ K ⊓ centralizer (K : Set (Bar H)) ∧ x * x = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have hab : a * b = b * a :=
          mem_centralizer_iff.1 (mem_inf.1 hb.1).2 a (mem_inf.1 ha.1).1
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hΩn : Ω.Normal := by
    constructor
    rintro n ⟨hnKC, hn2⟩ g
    have : (centralizer (K : Set (Bar H))).Normal := inferInstance
    refine ⟨mem_inf.2 ⟨(inferInstance : K.Normal).conj_mem n (mem_inf.1 hnKC).1 g,
      (inferInstance : (centralizer (K : Set (Bar H))).Normal).conj_mem n
        (mem_inf.1 hnKC).2 g⟩, ?_⟩
    calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn2]; group
  have hΩ2 : IsPGroup 2 Ω := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]
    exact y.2.2)⟩
  have hΩC : Ω ≤ centralizer (K : Set (Bar H)) := fun y hy => (mem_inf.1 hy.1).2
  have hΩne : Ω ≠ ⊥ := by
    intro h
    have hmem : x ∈ Ω := ⟨hx, hx2⟩
    rw [h, mem_bot] at hmem
    exact hx1 hmem
  obtain ⟨t, ht⟩ := exists_isIsolatedIn_of_normal_le_centralizer hΩn hΩ2 hΩC hΩne
  exact hiso t ht

theorem bar_inf_le_bar_inf {H P J : Subgroup G} (hOJ : O H ≤ J) :
    bar H P ⊓ bar H J ≤ bar H (P ⊓ J) := by
  rintro _ ⟨⟨⟨p, hpH⟩, hp, rfl⟩, ⟨⟨j, hjH⟩, hj, hjp⟩⟩
  have hp' : p ∈ P := hp
  have hj' : j ∈ J := hj
  have hjp' : (QuotientGroup.mk ⟨j, hjH⟩ : Bar H) = QuotientGroup.mk ⟨p, hpH⟩ := hjp
  rw [QuotientGroup.eq] at hjp'
  have hO : j⁻¹ * p ∈ O H := ⟨_, hjp', rfl⟩
  have hpJ : p ∈ J := by
    have h := mul_mem hj' (hOJ hO)
    rwa [mul_inv_cancel_left] at h
  exact mk_mem_bar hpH ⟨hp', hpJ⟩

theorem O_le_twoResidualOf (H : Subgroup G) : O H ≤ twoResidualOf H := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_twoResidualOf_of_odd x.2 ?_
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : CFSG.oddCore H)
  rw [Subgroup.orderOf_mk] at h
  show Odd (orderOf (x : G))
  rw [Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat odd_card_oddCore h

end Bar

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem prop_4_4_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (hWalter : ∀ {X : Type} [Group X] [Finite X], CFSG.oddCore X = ⊥ →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) → ∀ (T T₁ T₂ : Subgroup X),
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → IsE16 T → IsKleinFour T₁ → IsKleinFour T₂ →
      T₁ ⊔ T₂ = T → T₁ ⊓ T₂ = ⊥ →
      (∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) →
      ∃ F₁ F₂ : Subgroup X, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
        (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂)
    (H : Subgroup G) (hH : H ≠ ⊤) (hiso : ∀ t, ¬ IsIsolatedIn H t)
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsE16 A) (J : Subgroup G) (hJ₁ : O2 H ⊔ A ≤ J)
    (hJ₂ : J ≤ H) (hsylJ : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J) :
    ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
      L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
      bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
      IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
      bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
      (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := 𝔖.decomp
  have hLJ : O2 H ≤ J := le_sup_left.trans hJ₁
  have hAJ : A ≤ J := le_sup_right.trans hJ₁
  have h₁T : 𝔖.S₁ ⊓ J ≤ (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) := le_sup_left
  have h₂T : 𝔖.S₂ ⊓ J ≤ (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) := le_sup_right
  have hTS : (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) ≤ 𝔖.S :=
    sup_le (inf_le_left.trans hd.le_left) (inf_le_left.trans hd.le_right)
  have hTH : (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) ≤ H := hsylJ.le.trans hJ₂
  have hTp : IsPGroup 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) : Subgroup G) := 𝔖.S.isPGroup'.to_le hTS
  have h₁H : 𝔖.S₁ ⊓ J ≤ H := inf_le_right.trans hJ₂
  have h₂H : 𝔖.S₂ ⊓ J ≤ H := inf_le_right.trans hJ₂
  have hT₀ : IsSylowOf 2 (((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) ⊓ twoResidualOf H) (twoResidualOf H) :=
    hsylJ.inf_of_le_normalizer hLJ (hJ₂.trans (le_normalizer_twoResidualOf H))
  obtain ⟨⟨V₁, hV₁, hV₁T⟩, ⟨V₂, hV₂, hV₂T⟩, -, F₁, F₂, hF₁K, hF₂K, hn₁, hn₂, hi, ho, hA₁, hA₂,
    hs₁, hs₂⟩ := 𝔖.prop_4_3_core_of h315 h317 hWalter hH hAH hA hiso hT₀ (inf_le_left.trans hTS)
  have hdih₁ : IsDih (𝔖.S₁ ⊓ J) :=
    hd.dih₁.of_le inf_le_left hV₁ (le_inf hV₁.1 (hV₁T.trans (inf_le_right.trans hLJ)))
  have hdih₂ : IsDih (𝔖.S₂ ⊓ J) :=
    hd.isDih₂.of_le inf_le_left hV₂ (le_inf hV₂.1 (hV₂T.trans (inf_le_right.trans hLJ)))
  have hKJ : twoResidualOf (⊤ : Subgroup (Bar H)) ≤ bar H J := by
    rw [← bar_twoResidualOf]
    exact bar_mono hLJ
  have hTbar : IsSylowOf 2 (bar H (𝔖.S₁ ⊓ J) ⊔ bar H (𝔖.S₂ ⊓ J)) (bar H J) := by
    rw [← bar_sup h₁H h₂H]
    exact isSylowOf_bar hJ₂ hsylJ
  have hinfb : bar H (𝔖.S₁ ⊓ J) ⊓ bar H (𝔖.S₂ ⊓ J) = ⊥ := by
    rw [← bar_inf_of_isPGroup h₁T h₂T hTp hTH]
    have h : (𝔖.S₁ ⊓ J) ⊓ (𝔖.S₂ ⊓ J) = ⊥ := eq_bot_iff.2 fun x hx => by
      have h' : x ∈ 𝔖.S₁ ⊓ 𝔖.S₂ :=
        mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 (mem_inf.1 hx).2).1⟩
      rwa [hd.inf_eq] at h'
    rw [h, bar_bot]
  have hcommb : bar H (𝔖.S₂ ⊓ J) ≤ centralizer (bar H (𝔖.S₁ ⊓ J) : Set (Bar H)) :=
    bar_le_centralizer fun x hx => mem_centralizer_iff.2 fun y hy =>
      hd.comm (mem_inf.1 hy).1 (mem_inf.1 hx).1
  have hfus : ∀ x ∈ bar H (𝔖.S₁ ⊓ J) ⊔ bar H (𝔖.S₂ ⊓ J),
      ∀ y ∈ bar H (𝔖.S₁ ⊓ J) ⊔ bar H (𝔖.S₂ ⊓ J), orderOf x = 2 → IsConj x y →
      (x ∈ bar H (𝔖.S₁ ⊓ J) ↔ y ∈ bar H (𝔖.S₁ ⊓ J)) ∧
        (x ∈ bar H (𝔖.S₂ ⊓ J) ↔ y ∈ bar H (𝔖.S₂ ⊓ J)) := by
    rw [← bar_sup h₁H h₂H]
    rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩ _ ⟨⟨y, hyH⟩, hy, rfl⟩ hx2 hxy
    have hx' : x ∈ (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) := hx
    have hy' : y ∈ (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) := hy
    have hx2' : orderOf x = 2 := by
      rw [← orderOf_mk_eq hTH hTp hx']
      exact hx2
    have hsep := 𝔖.separate_of_mk_isConj hTH hTS hx' hy' hx2' hxy
    have hxJ : x ∈ J := hsylJ.le hx'
    have hyJ : y ∈ J := hsylJ.le hy'
    have key : ∀ P : Subgroup G, P ⊓ J ≤ (𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J) → (x ∈ P ↔ y ∈ P) →
        ((QuotientGroup.mk ⟨x, hxH⟩ : Bar H) ∈ bar H (P ⊓ J) ↔
          (QuotientGroup.mk ⟨y, hyH⟩ : Bar H) ∈ bar H (P ⊓ J)) := by
      intro P hP hxy'
      rw [mk_mem_bar_iff hP hTp hxH hx', mk_mem_bar_iff hP hTp hyH hy', mem_inf, mem_inf]
      exact ⟨fun h => ⟨hxy'.1 h.1, hyJ⟩, fun h => ⟨hxy'.2 h.1, hxJ⟩⟩
    exact ⟨key _ h₁T hsep.1, key _ h₂T hsep.2⟩
  have hW : ∀ P : Subgroup G, IsPGroup 2 P → ∀ F : Subgroup (Bar H),
      IsSylowOf 2 (bar H (((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) ⊓ twoResidualOf H ⊓ P)) F →
      IsSylowOf 2 (bar H (P ⊓ J) ⊓ F) F := by
    intro P hP F hF
    have heq : bar H (P ⊓ J) ⊓ F = bar H (((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) ⊓ twoResidualOf H ⊓ P) :=
      hF.eq_of_le (le_inf (bar_mono (le_inf inf_le_right
        (inf_le_left.trans (inf_le_right.trans hLJ)))) hF.le) inf_le_right
        (isPGroup_bar (hP.to_le inf_le_left)).to_inf_left
    rw [heq]
    exact hF
  have hS₁p : IsPGroup 2 𝔖.S₁ := 𝔖.S.isPGroup'.to_le hd.le_left
  have hS₂p : IsPGroup 2 𝔖.S₂ := 𝔖.S.isPGroup'.to_le hd.le_right
  obtain ⟨L₁, L₂, hTL₁, hTL₂, hL₁J, hL₂J, hJL₁, hJL₂, hinf, hcomm, hJA, hL₁t, hL₂t, hL₁syl,
    hL₂syl⟩ := exists_normal_factors_of (oddCore_quotient_oddCore_eq_bot H) hKJ hTbar hinfb hcommb
      (hdih₁.bar h₁H) (hdih₂.bar h₂H) hfus hF₁K hF₂K hn₁ hn₂ hi ho hA₁ hA₂
      (hW _ hS₁p _ hs₁) (hW _ hS₂p _ hs₂)
      (fun x hx hx2 => eq_one_of_mem_inf_centralizer hiso hx hx2)
      (bar_mono hAJ) (hA.bar hAH)
  have hOJ : O H ≤ J := (O_le_twoResidualOf H).trans hLJ
  have hsyl' : ∀ (P : Subgroup G) (L : Subgroup (Bar H)), IsPGroup 2 P → bar H (P ⊓ J) ≤ L →
      IsSylowOf 2 (bar H (P ⊓ J)) L → IsSylowOf 2 (bar H P ⊓ L) L := by
    intro P L hP hPL hsyl
    have heq : bar H P ⊓ L = bar H (P ⊓ J) :=
      hsyl.eq_of_le (le_inf (bar_mono inf_le_left) hPL) inf_le_right (isPGroup_bar hP).to_inf_left
    rw [heq]
    exact hsyl
  refine ⟨L₁, L₂, hL₁J, hL₂J, hinf, hcomm,
    (normal_subgroupOf_iff_le_normalizer (sup_le hL₁J hL₂J)).2 (le_normalizer_sup hJL₁ hJL₂),
    le_antisymm hJA (sup_le (sup_le hL₁J hL₂J) inf_le_left), hL₁t, hL₂t,
    hsyl' _ _ hS₁p hTL₁ hL₁syl, hsyl' _ _ hS₂p hTL₂ hL₂syl,
    (bar_inf_le_bar_inf hOJ).trans hTL₁, (bar_inf_le_bar_inf hOJ).trans hTL₂,
    (normal_subgroupOf_iff_le_normalizer hL₁J).2 hJL₁,
    (normal_subgroupOf_iff_le_normalizer hL₂J).2 hJL₂⟩

theorem prop_4_4_J_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (hWalter : ∀ {X : Type} [Group X] [Finite X], CFSG.oddCore X = ⊥ →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) → ∀ (T T₁ T₂ : Subgroup X),
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → IsE16 T → IsKleinFour T₁ → IsKleinFour T₂ →
      T₁ ⊔ T₂ = T → T₁ ⊓ T₂ = ⊥ →
      (∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) →
      ∃ F₁ F₂ : Subgroup X, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
        (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂)
    (H : Subgroup G) (hH : H ≠ ⊤) (hiso : ∀ t, ¬ IsIsolatedIn H t)
    (A : Subgroup G) (hAH : A ≤ H) (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A))) (O2 H ⊔ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := 𝔖.decomp
  have hLH : twoResidualOf H ≤ H := twoResidualOf_le_self H
  have hT₀ : IsSylowOf 2 (((𝔖.S : Subgroup G) ⊓ H) ⊓ twoResidualOf H) (twoResidualOf H) :=
    hsyl.inf_of_le_normalizer hLH (le_normalizer_twoResidualOf H)
  obtain ⟨-, -, hsplit, -⟩ :=
    𝔖.prop_4_3_core_of h315 h317 hWalter hH hAH hA hiso hT₀ (inf_le_left.trans inf_le_left)
  set T₀ := ((𝔖.S : Subgroup G) ⊓ H) ⊓ twoResidualOf H with hT₀def
  have hT₀S : T₀ ≤ 𝔖.S := inf_le_left.trans inf_le_left
  have hT₀L : T₀ ≤ twoResidualOf H := inf_le_right
  have hAN : T₀ ⊔ A ≤ normalizer (twoResidualOf H : Set G) :=
    (sup_le (hT₀L.trans hLH) hAH).trans (le_normalizer_twoResidualOf H)
  have hT₀Ap : IsPGroup 2 (T₀ ⊔ A : Subgroup G) := 𝔖.S.isPGroup'.to_le (sup_le hT₀S hAS)
  have hinf : (T₀ ⊔ A) ⊓ twoResidualOf H = T₀ :=
    hT₀.eq_of_le (le_inf le_sup_left hT₀L) inf_le_right (hT₀Ap.to_le inf_le_left)
  have hsylX : IsSylowOf 2 (T₀ ⊔ A) (twoResidualOf H ⊔ (T₀ ⊔ A)) :=
    isSylowOf_sup_of_le_normalizer hAN hT₀Ap (by rw [hinf]; exact hT₀)
  rw [← sup_assoc, sup_eq_left.2 hT₀L] at hsylX
  have hQX : (𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)) ≤ O2 H ⊔ A :=
    sup_le inf_le_right inf_le_right
  have hQp : IsPGroup 2 ((𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)) : Subgroup G) :=
    𝔖.S.isPGroup'.to_le (sup_le (inf_le_left.trans hd.le_left) (inf_le_left.trans hd.le_right))
  have hle : T₀ ⊔ A ≤ (𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)) := by
    obtain ⟨hAsplit, -, -⟩ := hd.e16_split hAS hA
    refine sup_le (hsplit.le.trans (sup_le_sup ?_ ?_)) (hAsplit.le.trans (sup_le_sup ?_ ?_))
    · exact le_inf inf_le_right (inf_le_left.trans (hT₀L.trans le_sup_left))
    · exact le_inf inf_le_right (inf_le_left.trans (hT₀L.trans le_sup_left))
    · exact le_inf inf_le_right (inf_le_left.trans le_sup_right)
    · exact le_inf inf_le_right (inf_le_left.trans le_sup_right)
  rw [hsylX.eq_of_le hle hQX hQp]
  exact hsylX

end Sec4Setting

end CFSG.GH72
