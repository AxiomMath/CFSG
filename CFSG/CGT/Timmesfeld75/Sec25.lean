module

public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def ReachD {G : Type*} [Group G] (D : Set G) : G → G → Prop :=
  Relation.ReflTransGen fun a b : G => a ∈ D ∧ b ∈ D ∧ a * b = b * a

@[expose] def AschbacherNoPolarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    (∃ d₀ : G, D = {g | IsConj d₀ g}) → (∀ d ∈ D, orderOf d = 2) →
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∣ 2 ∨ Odd (orderOf (d * e))) →
    Subgroup.closure D = ⊤ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∃ x ∈ D, ∃ y ∈ D, ¬ ReachD D x y) →
    (∀ x ∈ D, ∀ y ∈ D, x * y = y * x → x ≠ y → x * y ∈ D) →
    CFSG.BenderSuzuki.IsBenderGroup G

section Glue

variable {G : Type*} [Group G] {T : Subgroup G}

theorem mul_mem_classD_of_commute (h : StrongWC T) {x y : G} (hx : x ∈ classD T)
    (hy : y ∈ classD T) (hc : x * y = y * x) (hne : x ≠ y) : x * y ∈ classD T := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  have hy' : g * y * g⁻¹ ∈ classD T := by
    simpa using classD_conj hy g⁻¹
  have hcomm : (g * y * g⁻¹) * t = t * (g * y * g⁻¹) := by
    have e1 : (g * y * g⁻¹) * t = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by group
    have e2 : t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by group
    rw [e1, e2, ← hc]
  have hyT : g * y * g⁻¹ ∈ T := commute_classD_le h ht ht1 hy' hcomm
  have hne' : t * (g * y * g⁻¹) ≠ 1 := by
    intro h1
    apply hne
    have hti : t = (g * y * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hinv : (g * y * g⁻¹)⁻¹ = g * y * g⁻¹ := by
      have := classD_mul_self h hy'
      exact inv_eq_of_mul_eq_one_right this
    rw [hinv] at hti
    rw [hti]; group
  have hmem : t * (g * y * g⁻¹) ∈ classD T :=
    mem_classD_of_mem (T.mul_mem ht hyT) hne'
  have := classD_conj hmem g
  have e : g⁻¹ * (t * (g * y * g⁻¹)) * g = g⁻¹ * t * g * y := by group
  rwa [e] at this

theorem closure_classD_eq_normalClosure :
    Subgroup.closure (classD T) = Subgroup.normalClosure (T : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨g, t, ht, ht1, rfl⟩
    have := (Subgroup.normalClosure_normal (s := (T : Set G))).conj_mem t
      (Subgroup.subset_normalClosure ht) g⁻¹
    simpa using this
  · have hN : (Subgroup.closure (classD T)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      refine Subgroup.closure_induction
        (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure (classD T)) ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact Subgroup.subset_closure (by simpa using classD_conj hy g⁻¹)
      · simp
      · intro a b _ _ ha hb
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]; exact Subgroup.mul_mem _ ha hb
      · intro a _ ha
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]; exact Subgroup.inv_mem _ ha
    apply Subgroup.normalClosure_le_normal
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (mem_classD_of_mem ht ht1)

end Glue

section Bender

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem isBenderGroup_quotient_center
    (hAsc : AschbacherNoPolarInput) (hT : StrongWC T)
    (hK : Subgroup.normalClosure (T : Set G) = ⊤) (hnT : ¬ ∀ g : G, conjSubgroup g T = T)
    (hTbot : T ≠ ⊥) (hcent : ∀ t ∈ T, t ≠ 1 → ∃ k : G, t * k ≠ k * t)
    (hcomm : ∀ x ∈ classD T, ∀ y ∈ classD T,
      (∀ k : G, ⁅x, y⁆ * k = k * ⁅x, y⁆) → x * y = y * x)
    (hS : ∀ R : Subgroup (G ⧸ Subgroup.center G), R.Normal → Group.IsSolvable R → R = ⊥) :
    CFSG.BenderSuzuki.IsBenderGroup (G ⧸ Subgroup.center G) := by
  set π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk_surjective
  have hπker : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.center G := fun g => QuotientGroup.eq_one_iff g
  have hcommπ : ∀ x y : G, π x * π y = π y * π x → ∀ k : G, ⁅x, y⁆ * k = k * ⁅x, y⁆ := by
    intro x y hxy k
    have h1 : π ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]; exact hxy
    have h2 := (hπker _).1 h1
    exact (Subgroup.mem_center_iff.1 h2 k).symm
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : G, classD T = {g | IsConj d₀ g} := by
    rcases single_class_or_normal hT hTbot with h | h
    · exact h
    · exact absurd h hnT
  have hDne : ∀ x ∈ classD T, x ≠ 1 := fun x hx h1 => by
    have := classD_orderOf hT hx
    rw [h1] at this; simp at this
  have hnotcentral : ∀ x ∈ classD T, π x ≠ 1 := by
    intro x hx hx1
    obtain ⟨g, t, ht, ht1, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hcent t ht ht1
    have hz := Subgroup.mem_center_iff.1 ((hπker _).1 hx1)
    apply hk
    have e : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    have hc : (g⁻¹ * t * g) * (g⁻¹ * k * g) = (g⁻¹ * k * g) * (g⁻¹ * t * g) :=
      (hz (g⁻¹ * k * g)).symm
    have : t * k = k * t := by
      have h2 : g * ((g⁻¹ * t * g) * (g⁻¹ * k * g)) * g⁻¹ =
          g * ((g⁻¹ * k * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      simpa [mul_assoc] using h2
    exact this
  apply hAsc (G ⧸ Subgroup.center G) (π '' classD T)
  · refine ⟨π d₀, ?_⟩
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [hd₀] at hg
      obtain ⟨c, hc⟩ := isConj_iff.1 hg
      exact isConj_iff.2 ⟨π c, by rw [← hc]; simp [map_mul, map_inv]⟩
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      obtain ⟨c, rfl⟩ := hπsurj c
      refine ⟨c * d₀ * c⁻¹, ?_, by rw [← hc]; simp [map_mul, map_inv]⟩
      rw [hd₀]; exact isConj_iff.2 ⟨c, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsq := classD_mul_self hT hx
    refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hsq, map_one]) (hnotcentral x hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    rcases orderOf_mul_classD hT hx hy with h | h
    · exact Or.inl ((orderOf_map_dvd π _).trans h)
    · exact Or.inr (Odd.of_dvd_nat h (orderOf_map_dvd π _))
  · rw [← MonoidHom.map_closure, closure_classD_eq_normalClosure, hK]
    exact MonoidHom.range_eq_top_of_surjective π hπsurj ▸ (MonoidHom.range_eq_map π).symm
  · exact hS
  ·
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTbot
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have htD : t ∈ classD T := mem_classD_of_mem ht ht1'
    obtain ⟨y₀, hy₀D, hy₀T⟩ : ∃ y₀ ∈ classD T, y₀ ∉ T := by
      by_contra hcon
      push Not at hcon
      apply hnT
      intro g
      apply conjSubgroup_eq_of_le
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact T.one_mem
      · have hx' : g⁻¹ * x * g ∈ T := mem_conjSubgroup.1 hx
        have hxD : x ∈ classD T := by
          refine ⟨g⁻¹, g⁻¹ * x * g, hx', ?_, by group⟩
          intro h1
          apply hx1
          have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          rw [e, h1]; group
        exact hcon x hxD
    refine ⟨π t, ⟨t, htD, rfl⟩, π y₀, ⟨y₀, hy₀D, rfl⟩, ?_⟩
    intro hreach
    let R : Set (G ⧸ Subgroup.center G) := {z | ∃ u ∈ T, u ≠ 1 ∧ z = π u}
    have hstep : ∀ b ∈ R, ∀ c ∈ π '' classD T, b * c = c * b → c ∈ R := by
      rintro _ ⟨u, hu, hu1, rfl⟩ _ ⟨v, hv, rfl⟩ hbc
      have huv : u * v = v * u :=
        hcomm u (mem_classD_of_mem hu hu1) v hv (hcommπ u v hbc)
      have hvT : v ∈ T := commute_classD_le hT hu hu1 hv huv.symm
      exact ⟨v, hvT, hDne v hv, rfl⟩
    have hreachR : ∀ w, ReachD (π '' classD T) (π t) w → w ∈ R := by
      intro w hw
      induction hw with
      | refl => exact ⟨t, ht, ht1', rfl⟩
      | tail _ hstp ih => exact hstep _ ih _ hstp.2.1 hstp.2.2
    obtain ⟨u, hu, hu1, hyu⟩ := hreachR _ hreach
    have hc : π y₀ * π u = π u * π y₀ := by rw [← hyu]
    have hyu' : y₀ * u = u * y₀ :=
      hcomm y₀ hy₀D u (mem_classD_of_mem hu hu1) (hcommπ y₀ u hc)
    exact hy₀T (commute_classD_le hT hu hu1 hy₀D hyu')
  ·
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hc hne
    have hc' : x * y = y * x := hcomm x hx y hy (hcommπ x y hc)
    have hne' : x ≠ y := fun h => hne (by rw [h])
    exact ⟨x * y, mul_mem_classD_of_commute hT hx hy hc' hne', by rw [map_mul]⟩

end Bender

end CFSG.CGT.Timmesfeld75
