module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem map_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨x, hx, hxa⟩ y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← hxa, ← map_mul, ← map_mul, hx y']
  · intro h
    refine ⟨a, fun g => ?_, rfl⟩
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)

noncomputable def quotientCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (map_center_equiv e)

theorem card_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) :=
  Nat.card_congr ((Subgroup.equivMapOfInjective (center A) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_center_equiv e))).toEquiv

variable {Y : Type} [Group Y]

theorem le_of_perfect_of_solvable_outer {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) [Group.IsSolvable (Outer ↥N)] {A : Subgroup Y}
    [Group.IsPerfect ↥A] : A ≤ N := by
  intro a ha
  obtain ⟨n, hn⟩ := perfect_action_inner
    ((MulAut.conjNormal : Y →* MulAut ↥N).comp A.subtype) ⟨a, ha⟩
  have hc : (n : Y)⁻¹ * a ∈ centralizer (N : Set Y) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : Y)) hn
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.conj_apply] at h
    have h' : a * x * a⁻¹ = n * x * (n : Y)⁻¹ := h
    calc x * ((n : Y)⁻¹ * a) = (n : Y)⁻¹ * (n * x * (n : Y)⁻¹) * a := by group
      _ = (n : Y)⁻¹ * (a * x * a⁻¹) * a := by rw [h']
      _ = (n : Y)⁻¹ * a * x := by group
  have h1 : (n : Y)⁻¹ * a ∈ N := hC hc
  have h2 : a = (n : Y) * ((n : Y)⁻¹ * a) := by group
  rw [h2]
  exact N.mul_mem n.2 h1

theorem center_eq_bot_of_fStarSimple {N : Subgroup Y} (hF : FStarSimple N) : center ↥N = ⊥ := by
  have := hF.isSimpleGroup
  rcases (inferInstance : (center ↥N).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hF.nonabelian
    have ha : a ∈ center ↥N := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem conjNormal_ne_one [Finite Y] {N : Subgroup Y} (hF : FStarSimple N) {t : Y} (ht1 : t ≠ 1) :
    (@MulAut.conjNormal Y _ N hF.normal t : MulAut ↥N) ≠ 1 := by
  have := hF.normal
  intro h1
  have hc : t ∈ centralizer (N : Set Y) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h := congrArg (fun σ : MulAut ↥N => ((σ ⟨n, hn⟩ : ↥N) : Y)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc n * t = (t * n * t⁻¹) * t := by rw [h]
      _ = t * n := by group
  have htN : t ∈ N := hF.centralizer_le hc
  have hz : (⟨t, htN⟩ : ↥N) ∈ center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.1 hc) g g.2)
  rw [center_eq_bot_of_fStarSimple hF, Subgroup.mem_bot] at hz
  exact ht1 (congrArg Subtype.val hz)

theorem exists_fixedComponent [Finite Y] {N : Subgroup Y} (hF : FStarSimple N) {t : Y}
    (ht : orderOf t = 2) {A : Subgroup Y} (hA : IsCompIn A (centralizer ({t} : Set Y)))
    (hAN : A ≤ N) :
    ∃ (σ : MulAut ↥N) (D : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 ∧ CFSG.IsComponent D ∧
      (t ∈ N → σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range) ∧ Nonempty (↥D ≃* ↥A) := by
  have := hF.normal
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  set σ : MulAut ↥N := MulAut.conjNormal t with hσdef
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, ht2, map_one]
  have hσ1 : σ ≠ 1 := conjNormal_ne_one hF ht1
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  have hfix : ∀ x : ↥N, x ∈ fixedSubgroup σ ↔ t * (x : Y) = x * t := by
    intro x
    change σ x = x ↔ _
    rw [← Subtype.coe_inj, hσdef, MulAut.conjNormal_apply]
    constructor
    · intro h
      calc t * (x : Y) = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h]
    · intro h
      rw [h]
      group
  have hA'le : A.subgroupOf N ≤ fixedSubgroup σ := by
    intro x hx
    rw [hfix]
    exact (mem_centralizer_singleton_iff.1 (hA.1 (Subgroup.mem_subgroupOf.1 hx))).symm
  let e : ↥((A.subgroupOf N).subgroupOf (fixedSubgroup σ)) ≃* ↥A :=
    (Subgroup.subgroupOfEquivOfLe hA'le).trans (Subgroup.subgroupOfEquivOfLe hAN)
  refine ⟨σ, (A.subgroupOf N).subgroupOf (fixedSubgroup σ), hσo, ?_, ?_, ⟨e⟩⟩
  · let f : ↥(fixedSubgroup σ) →* ↥(centralizer ({t} : Set Y)) :=
      (N.subtype.comp (fixedSubgroup σ).subtype).codRestrict _ (fun x =>
        mem_centralizer_singleton_iff.2 ((hfix x.1).1 x.2).symm)
    have hcomap : (A.subgroupOf N).subgroupOf (fixedSubgroup σ) =
        (A.subgroupOf (centralizer ({t} : Set Y))).comap f := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hA.isQuasisimple, ?_⟩
    rw [hcomap]
    exact Subgroup.IsSubnormal.comap f hA.2.2
  · intro htN
    exact ⟨⟨t, htN⟩, MulEquiv.ext fun x => Subtype.ext (by simp [hσdef, MulAut.conjNormal_apply])⟩

end CFSG.ComponentClassification.CatFC
