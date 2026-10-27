module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint

theorem eqLocus_conj {D : Type*} [Group D] (t : D) :
    (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) = centralizer {t} := by
  ext y
  rw [mem_centralizer_singleton_iff]
  change t * y * t⁻¹ = y ↔ y * t = t * y
  constructor
  · intro h
    calc y * t = t * y * t⁻¹ * t := by rw [h]
      _ = t * y := by group
  · intro h
    calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [h]
      _ = y := by group

theorem two_le_pRank_of_commute {G : Type*} [Group G] [Finite G] {H : Subgroup G} {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : 2 ≤ CFSG.Open.pRank 2 H := by
  classical
  let E : Subgroup G :=
    { carrier := {1, x, y, x * y}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have hyx : y * x = x * y := hxy.symm
        have h1 : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
        have h2 : y * (x * y) = x := by rw [← mul_assoc, hyx, mul_assoc, hyy, mul_one]
        have h3 : x * y * x = y := by rw [mul_assoc, hyx, ← mul_assoc, hxx, one_mul]
        have h4 : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
        have h5 : x * y * (x * y) = 1 := by
          rw [show x * y * (x * y) = x * (y * x) * y by group, hyx,
            show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hxx, hyy, h1, h2, h3, h4, h5, hyx]
      inv_mem' := by
        intro a ha
        have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, hxx]
        have hyi : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, hyy]
        have hxyi : (x * y)⁻¹ = x * y := by
          rw [mul_inv_rev, hxi, hyi, hxy]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> simp [hxi, hyi, hxyi] }
  have hmem : ∀ g, g ∈ E ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := fun g => Iff.rfl
  have hEH : E ≤ H := by
    intro g hg
    rcases (hmem g).1 hg with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hx
    · exact hy
    · exact H.mul_mem hx hy
  have hxy1 : x * y ≠ 1 := fun h => hne (by
    have := congrArg (· * y) h
    simpa [mul_assoc, hyy] using this)
  have hxyx : x * y ≠ x := fun h => hy1 (by simpa using h)
  have hxyy : x * y ≠ y := fun h => hx1 (by
    have := congrArg (· * y) h
    simpa [mul_assoc, hyy] using this)
  have hcard : Nat.card E = 2 ^ 2 := by
    have hfin : (E : Set G) = {1, x, y, x * y} := rfl
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hfin]
    rw [Set.ncard_insert_of_notMem (by simp [hx1.symm, hy1.symm, hxy1.symm]),
      Set.ncard_insert_of_notMem (by simp [hne, hxyx.symm]),
      Set.ncard_insert_of_notMem (by simp [hxyy.symm]), Set.ncard_singleton]
    norm_num
  have hE : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      change a * b = b * a
      have hc : Commute x y := hxy
      have hc1 : Commute x (x * y) := (Commute.refl x).mul_right hc
      have hc2 : Commute y (x * y) := hc.symm.mul_right (Commute.refl y)
      rcases (hmem a).1 ha with rfl | rfl | rfl | rfl <;>
        rcases (hmem b).1 hb with rfl | rfl | rfl | rfl <;>
        first
        | exact (Commute.one_left _).eq
        | exact (Commute.one_right _).eq
        | exact (Commute.refl _).eq
        | exact hc.eq
        | exact hc.symm.eq
        | exact hc1.eq
        | exact hc1.symm.eq
        | exact hc2.eq
        | exact hc2.symm.eq
    · rw [sq]
      rcases (hmem g).1 hg with rfl | rfl | rfl | rfl
      · simp
      · exact hxx
      · exact hyy
      · rw [show x * y * (x * y) = x * (y * x) * y by group, ← hxy,
          show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]
  exact CFSG.SectionRank.le_pRank one_lt_two hEH hE hcard

theorem noFour_of_pRank_le_one {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : CFSG.Open.pRank 2 H ≤ 1) : NoFour H := by
  intro x hx y hy hxx hyy hxy
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hy1, hne⟩ := hcon
  have := two_le_pRank_of_commute hx hy hxx hyy hxy hx1 hy1 hne
  omega

theorem stdKernelTwo_of_selector (hsel : InnerKernelSelector fun D _ => Catalog D) :
    CFSG.CGT.PushingUpLit.CGT6K1.StdKernelTwo := by
  intro D _ _ hD hKD n A hA hrank S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, hstd, -, K, _, _, hK, ⟨φ⟩⟩ := hA
  have hCeven : Even (Nat.card (centralizer (A : Set D))) := hstd.2.1
  have hSne : (S : Subgroup (centralizer (A : Set D))) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S (even_iff_two_dvd.mp hCeven)
  have hSnt : Nontrivial (S : Subgroup (centralizer (A : Set D))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  have hZnt : Nontrivial (center (S : Subgroup (centralizer (A : Set D)))) :=
    S.isPGroup'.center_nontrivial
  have hZp : IsPGroup 2 (center (S : Subgroup (centralizer (A : Set D)))) :=
    S.isPGroup'.to_subgroup _
  have h2Z : 2 ∣ Nat.card (center (S : Subgroup (centralizer (A : Set D)))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hk
      exact absurd (Finite.one_lt_card_iff_nontrivial.mpr hZnt) (by rw [hk]; omega)
    · rw [hk]
      exact dvd_pow_self 2 hk0.ne'
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := center (S : Subgroup (centralizer (A : Set D)))) 2 h2Z
  set t : D := (((z : (S : Subgroup (centralizer (A : Set D)))) : (centralizer (A : Set D))) : D)
    with htdef
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have htC : t ∈ (centralizer (A : Set D)) :=
    ((z : (S : Subgroup (centralizer (A : Set D)))) : (centralizer (A : Set D))).2
  obtain ⟨-, hAt, hAn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup A) htC ht2
  have hnab : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨a, -, b, -, hab⟩ :=
      CFSG.ComponentClassification.AS76b.Lemma34.exists_not_commute hstd.1
    exact ⟨a, b, hab⟩
  have hZD : center D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ center D := by rw [h]; exact mem_top b
      exact absurd (Subgroup.mem_center_iff.mp hb a) hab
  have hconj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center D := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun β : MulAut D => β h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc h * g = g * h * g⁻¹ * g := by rw [this]
        _ = g * h := by group
    rw [hZD, Subgroup.mem_bot] at hgZ
    exact hgZ
  have hα2 : orderOf (MulAut.conj t) = 2 := by
    rw [orderOf_injective _ hconj t, ht2]
  have hfour : NoFour ((MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer (A : Set D)) :=
    (noFour_of_pRank_le_one hrank).mono inf_le_right
  have hsurj : Function.Surjective (⊤ : Subgroup D).subtype := fun d => ⟨⟨d, mem_top d⟩, rfl⟩
  have hcat : Catalog D :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKD ⊤ (⊤ : Subgroup D).subtype hsurj
  have hbound := hsel D hD hcat n hn K hK (MulAut.conj t) hα2 ⟨t, rfl⟩ A
    (by rw [eqLocus_conj]; exact hAt) (by rw [eqLocus_conj]; exact hAn) ⟨φ⟩ hfour
  set Q : Subgroup D := (S : Subgroup (centralizer (A : Set D))).map
    (centralizer (A : Set D)).subtype with hQdef
  have hQle : Q ≤ (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer (A : Set D) := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_inf.2 ⟨?_, s.2⟩
    rw [eqLocus_conj, mem_centralizer_singleton_iff]
    have hzc := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    have := congrArg (fun w : (S : Subgroup (centralizer (A : Set D))) =>
      ((w : (centralizer (A : Set D))) : D)) hzc
    simpa using this
  have hQp : IsPGroup 2 Q := S.isPGroup'.map (centralizer (A : Set D)).subtype
  have hQcard : Nat.card Q = Nat.card (S : Subgroup (centralizer (A : Set D))) :=
    Subgroup.card_map_of_injective (centralizer (A : Set D)).subtype_injective
  have hle := hbound Q hQle hQp
  rw [hQcard] at hle
  have hge : 2 ≤ Nat.card (S : Subgroup (centralizer (A : Set D))) := by
    have h1 := orderOf_dvd_natCard ((z : (S : Subgroup (centralizer (A : Set D)))))
    rw [Subgroup.orderOf_coe, hz] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  exact le_antisymm hle hge

end CFSG.CGT.PushingUpLit.K1R
