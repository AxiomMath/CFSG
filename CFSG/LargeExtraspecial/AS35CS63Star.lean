module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.CorollaryBBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld

namespace S63

variable {X : Type} [Group X]

structure StarHyp (ζ : X) : Prop where
  mul_self : ζ * ζ = 1
  comm : ∀ a ∈ CorB.conjCent ζ, ∀ b ∈ CorB.conjCent ζ,
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = ζ
  fusion : ∀ τ ∈ CorB.conjCent ζ, τ ≠ ζ →
    ∃ f : X, f * ζ * f⁻¹ = ζ ∧ f * τ * f⁻¹ = ζ * τ

@[expose] def ZU (ζ : X) : Subgroup X :=
  (center ↥(normalClosure ({ζ} : Set X))).map (normalClosure ({ζ} : Set X)).subtype

theorem mem_ZU_iff {ζ w : X} : w ∈ ZU ζ ↔ ∃ hw : w ∈ normalClosure ({ζ} : Set X),
    (⟨w, hw⟩ : ↥(normalClosure ({ζ} : Set X))) ∈ center ↥(normalClosure ({ζ} : Set X)) := by
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨w'.2, hw'⟩
  · rintro ⟨hw, hc⟩
    exact ⟨⟨w, hw⟩, hc, rfl⟩

theorem comm_of_mem_ZU {ζ w u : X} (hw : w ∈ ZU ζ) (hu : u ∈ normalClosure ({ζ} : Set X)) :
    w * u = u * w := by
  obtain ⟨hw', hc⟩ := mem_ZU_iff.mp hw
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨u, hu⟩).symm

theorem mem_normalClosure_of_isConj {ζ u : X} (h : IsConj ζ u) :
    u ∈ normalClosure ({ζ} : Set X) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact normalClosure_normal.conj_mem _ (subset_normalClosure (Set.mem_singleton ζ)) c

theorem conj_mem_ZU {ζ w : X} (hw : w ∈ ZU ζ) (k : X) : k * w * k⁻¹ ∈ ZU ζ := by
  obtain ⟨hw', hc⟩ := mem_ZU_iff.mp hw
  have hU : (normalClosure ({ζ} : Set X)).Normal := normalClosure_normal
  refine mem_ZU_iff.mpr ⟨hU.conj_mem w hw' k, mem_center_iff.mpr fun u => Subtype.ext ?_⟩
  have h1 : (k⁻¹ * u * k) * w = w * (k⁻¹ * u * k) :=
    congrArg Subtype.val (mem_center_iff.mp hc ⟨k⁻¹ * u * k, by
      simpa using hU.conj_mem _ u.2 k⁻¹⟩)
  change (u : X) * (k * w * k⁻¹) = (k * w * k⁻¹) * u
  calc (u : X) * (k * w * k⁻¹) = k * ((k⁻¹ * u * k) * w) * k⁻¹ := by group
    _ = k * (w * (k⁻¹ * u * k)) * k⁻¹ := by rw [h1]
    _ = (k * w * k⁻¹) * u := by group

namespace StarHyp

variable {ζ : X} (H : StarHyp ζ)
include H

theorem comm_at {u a b : X} (hu : IsConj ζ u) (ha : IsConj ζ a) (hb : IsConj ζ b)
    (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = u := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hu
  have hmem : ∀ c, IsConj ζ c → c * (k * ζ * k⁻¹) = (k * ζ * k⁻¹) * c →
      k⁻¹ * c * k ∈ CorB.conjCent ζ := by
    intro c hc hcu
    refine ⟨?_, ?_⟩
    · calc k⁻¹ * c * k * ζ = k⁻¹ * (c * (k * ζ * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * ζ * k⁻¹) * c) * k := by rw [hcu]
        _ = ζ * (k⁻¹ * c * k) := by group
    · exact hc.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)
  have h := H.comm _ (hmem a ha hau) _ (hmem b hb hbu)
  have e : k⁻¹ * a * k * (k⁻¹ * b * k) * (k⁻¹ * a * k)⁻¹ * (k⁻¹ * b * k)⁻¹ =
      k⁻¹ * (a * b * a⁻¹ * b⁻¹) * k := by group
  rw [e] at h
  rcases h with h | h
  · left
    calc a * b * a⁻¹ * b⁻¹ = k * (k⁻¹ * (a * b * a⁻¹ * b⁻¹) * k) * k⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc a * b * a⁻¹ * b⁻¹ = k * (k⁻¹ * (a * b * a⁻¹ * b⁻¹) * k) * k⁻¹ := by group
      _ = k * ζ * k⁻¹ := by rw [h]

theorem eq_one_of_mul_mem_center (hζ : ζ ∉ ZU ζ) {y w : X} (hy : IsConj ζ y)
    (hw : w ∈ ZU ζ) (hyw : y = w * ζ) : w = 1 := by
  have hζU : ζ ∈ normalClosure ({ζ} : Set X) := subset_normalClosure (Set.mem_singleton ζ)
  have hwζ : w * ζ = ζ * w := comm_of_mem_ZU hw hζU
  by_contra hw1
  have hyc : y ∈ CorB.conjCent ζ := ⟨by rw [hyw, ← mul_assoc ζ w ζ, ← hwζ], hy⟩
  have hyne : y ≠ ζ := fun h => hw1 (by
    rw [hyw] at h
    exact mul_eq_right.mp h)
  obtain ⟨f, hfz, hfy⟩ := H.fusion y hyc hyne
  rw [hyw] at hfy
  have h1 : (f * w * f⁻¹) * ζ = w := by
    calc (f * w * f⁻¹) * ζ = (f * w * f⁻¹) * (f * ζ * f⁻¹) := by rw [hfz]
      _ = f * (w * ζ) * f⁻¹ := by group
      _ = ζ * (w * ζ) := hfy
      _ = (ζ * w) * ζ := by group
      _ = w * (ζ * ζ) := by rw [← hwζ]; group
      _ = w := by rw [H.mul_self, mul_one]
  have h2 : ζ = (f * w * f⁻¹)⁻¹ * w := by
    calc ζ = (f * w * f⁻¹)⁻¹ * ((f * w * f⁻¹) * ζ) := by group
      _ = (f * w * f⁻¹)⁻¹ * w := by rw [h1]
  have h3 : (f * w * f⁻¹)⁻¹ * w ∈ ZU ζ := mul_mem (inv_mem (conj_mem_ZU hw f)) hw
  rw [← h2] at h3
  exact hζ h3

theorem commute_of_commutator_mem_center (hζ : ζ ∉ ZU ζ) {u v : X} (hu : IsConj ζ u)
    (hv : IsConj ζ v) (huv : u * v * u⁻¹ * v⁻¹ ∈ ZU ζ) : u * v = v * u := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hv
  set u' := k⁻¹ * u * k with hu'
  have hu'c : IsConj ζ u' := hu.trans (isConj_iff.mpr ⟨k⁻¹, by rw [hu']; group⟩)
  set w := u' * ζ * u'⁻¹ * ζ⁻¹ with hw
  have hwZ : w ∈ ZU ζ := by
    have := conj_mem_ZU huv k⁻¹
    have e : k⁻¹ * (u * (k * ζ * k⁻¹) * u⁻¹ * (k * ζ * k⁻¹)⁻¹) * k⁻¹⁻¹ = w := by
      rw [hw, hu']; group
    rwa [e] at this
  have hyc : IsConj ζ (u' * ζ * u'⁻¹) := isConj_iff.mpr ⟨u', rfl⟩
  have h1 := H.eq_one_of_mul_mem_center hζ hyc hwZ (by rw [hw]; group)
  have h2 : u' * ζ * u'⁻¹ = ζ := by
    calc u' * ζ * u'⁻¹ = w * ζ := by rw [hw]; group
      _ = ζ := by rw [h1, one_mul]
  calc u * (k * ζ * k⁻¹) = k * (u' * ζ * u'⁻¹) * k⁻¹ * u := by rw [hu']; group
    _ = (k * ζ * k⁻¹) * u := by rw [h2]

theorem commute_of_mk_commute (hζ : ζ ∉ ZU ζ) {a c : ↥(normalClosure ({ζ} : Set X))}
    (ha : IsConj ζ (a : X)) (hc : IsConj ζ (c : X))
    (h : QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) a *
        QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) c =
      QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) c *
        QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) a) :
    (a : X) * c = c * a := by
  have h1 : a * c * a⁻¹ * c⁻¹ ∈ center ↥(normalClosure ({ζ} : Set X)) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
      map_inv, map_inv, h]
    group
  refine H.commute_of_commutator_mem_center hζ ha hc ?_
  exact ⟨a * c * a⁻¹ * c⁻¹, h1, by simp⟩

theorem false_of_rootSet [Finite X] (hζ : ζ ∉ ZU ζ)
    {D : Set (↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X)))}
    (hDdef : D = QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) '' CorB.clsIn ζ)
    (hH : Timmesfeld.Hyp (↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X))) D)
    {d e : ↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X))}
    (hd : d ∈ D) (he : e ∈ rootSet D d) (hne : e ≠ d) : False := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hH.nondeg
  have hc₀ : (a₀ * b₀) ^ 2 ∈ D := hH.root.2.2 a₀ ha₀ b₀ hb₀ hab
  have ha2 : a₀ * a₀ = 1 := by
    rw [← pow_two, ← hH.root.1 a₀ ha₀]; exact pow_orderOf_eq_one a₀
  have hb2 : b₀ * b₀ = 1 := by
    rw [← pow_two, ← hH.root.1 b₀ hb₀]; exact pow_orderOf_eq_one b₀
  have hab4 : (a₀ * b₀) ^ 4 = 1 := by rw [← hab]; exact pow_orderOf_eq_one _
  have hai : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha2
  have hbi : b₀⁻¹ = b₀ := inv_eq_of_mul_eq_one_right hb2
  have e2 : ((a₀ * b₀) ^ 2)⁻¹ = (a₀ * b₀) ^ 2 := by
    rw [← mul_eq_one_iff_inv_eq, ← pow_add]; exact hab4
  have hca : Commute a₀ ((a₀ * b₀) ^ 2) := by
    have e1 : a₀ * (a₀ * b₀) ^ 2 * a₀⁻¹ = ((a₀ * b₀) ^ 2)⁻¹ := by
      rw [hai, pow_two]
      calc a₀ * (a₀ * b₀ * (a₀ * b₀)) * a₀ = (a₀ * a₀) * b₀ * a₀ * b₀ * a₀ := by group
        _ = (b₀ * a₀) * (b₀ * a₀) := by rw [ha2]; group
        _ = (a₀ * b₀ * (a₀ * b₀))⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hai, hbi]
    rw [Commute, SemiconjBy]
    calc a₀ * (a₀ * b₀) ^ 2 = (a₀ * (a₀ * b₀) ^ 2 * a₀⁻¹) * a₀ := by group
      _ = (a₀ * b₀) ^ 2 * a₀ := by rw [e1, e2]
  have hcb : Commute b₀ ((a₀ * b₀) ^ 2) := by
    have e1 : b₀ * (a₀ * b₀) ^ 2 * b₀⁻¹ = ((a₀ * b₀) ^ 2)⁻¹ := by
      rw [hbi, pow_two]
      calc b₀ * (a₀ * b₀ * (a₀ * b₀)) * b₀ = b₀ * a₀ * b₀ * a₀ * (b₀ * b₀) := by group
        _ = (b₀ * a₀) * (b₀ * a₀) := by rw [hb2]; group
        _ = (a₀ * b₀ * (a₀ * b₀))⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hai, hbi]
    rw [Commute, SemiconjBy]
    calc b₀ * (a₀ * b₀) ^ 2 = (b₀ * (a₀ * b₀) ^ 2 * b₀⁻¹) * b₀ := by group
      _ = (a₀ * b₀) ^ 2 * b₀ := by rw [e1, e2]
  have hcomm₀ : a₀ * b₀ * a₀⁻¹ * b₀⁻¹ = (a₀ * b₀) ^ 2 := by rw [hai, hbi, pow_two]; group
  obtain ⟨g, hg⟩ := isConj_iff.mp (hH.isConj hd hc₀)
  have he₀ : g * e * g⁻¹ ∈ rootSet D ((a₀ * b₀) ^ 2) := by
    rw [← hg, hH.rootSet_conj g d]
    exact ⟨e, he, rfl⟩
  have hne₀ : g * e * g⁻¹ ≠ (a₀ * b₀) ^ 2 := fun h => hne (by
    rw [← hg] at h
    simpa using h)
  obtain ⟨heD, -, he₀f⟩ := (hH.mem_rootSet_iff hc₀).mp he₀
  have hea : Commute (g * e * g⁻¹) a₀ := he₀f a₀ ha₀ hca.symm
  have heb : Commute (g * e * g⁻¹) b₀ := he₀f b₀ hb₀ hcb.symm
  rw [hDdef] at ha₀ hb₀ hc₀ heD
  obtain ⟨a, ha, rfl⟩ := ha₀
  obtain ⟨b, hb, rfl⟩ := hb₀
  obtain ⟨c, hc, hcπ⟩ := hc₀
  obtain ⟨e', he', he'π⟩ := heD
  have ha' : IsConj ζ (a : X) := CorB.mem_clsIn.mp ha
  have hb' : IsConj ζ (b : X) := CorB.mem_clsIn.mp hb
  have hc' : IsConj ζ (c : X) := CorB.mem_clsIn.mp hc
  have he'' : IsConj ζ (e' : X) := CorB.mem_clsIn.mp he'
  have hac : (a : X) * c = c * a := H.commute_of_mk_commute hζ ha' hc' (by
    rw [hcπ]; exact hca.eq)
  have hbc : (b : X) * c = c * b := H.commute_of_mk_commute hζ hb' hc' (by
    rw [hcπ]; exact hcb.eq)
  have hae : (a : X) * e' = e' * a := H.commute_of_mk_commute hζ ha' he'' (by
    rw [he'π]; exact hea.eq.symm)
  have hbe : (b : X) * e' = e' * b := H.commute_of_mk_commute hζ hb' he'' (by
    rw [he'π]; exact heb.eq.symm)
  have hζ1 : ζ ≠ 1 := fun h => hζ (h ▸ one_mem _)
  have hcU : ¬ (c : X) ∈ ZU ζ := by
    intro hcZ
    obtain ⟨k, hk⟩ := isConj_iff.mp hc'
    apply hζ
    have := conj_mem_ZU hcZ k⁻¹
    rwa [← hk, show k⁻¹ * (k * ζ * k⁻¹) * k⁻¹⁻¹ = ζ by group] at this
  have habc : (a : X) * b * (a : X)⁻¹ * (b : X)⁻¹ = c := by
    rcases H.comm_at hc' ha' hb' hac hbc with h | h
    · exfalso
      apply hcU
      have h1 : QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) (a * b * a⁻¹ * b⁻¹) =
          QuotientGroup.mk' (center ↥(normalClosure ({ζ} : Set X))) c := by
        rw [hcπ, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm₀]
      have h2 : a * b * a⁻¹ * b⁻¹ = 1 := Subtype.ext (by simpa using h)
      rw [h2, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨c, h1, rfl⟩
    · exact h
  rcases H.comm_at he'' ha' hb' hae hbe with h | h
  · rw [habc] at h
    obtain ⟨k, hk⟩ := isConj_iff.mp hc'
    apply hζ1
    calc ζ = k⁻¹ * (k * ζ * k⁻¹) * k := by group
      _ = 1 := by rw [hk, h]; group
  · rw [habc] at h
    apply hne₀
    rw [← hcπ, ← he'π]
    exact congrArg _ (Subtype.ext h.symm)

end StarHyp

end S63

end CFSG.LargeExtraspecial
