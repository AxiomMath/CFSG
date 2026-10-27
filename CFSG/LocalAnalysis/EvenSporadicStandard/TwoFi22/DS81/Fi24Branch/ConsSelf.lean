module

public import CFSG.RankThree.Literature.FSmithForm

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G]

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.IsExtraspecialPGroup p A) : CFSG.IsExtraspecialPGroup p B := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini A).map e.toMonoidHom = frattini B :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm]
    exact Subgroup.map_center_eq e
  · rw [← hf, hfrat]
    exact Subgroup.map_center_eq e
  · rw [← Subgroup.map_center_eq e]
    rw [Subgroup.card_map_of_injective (f := (e : A →* B)) e.injective, hcard]

theorem mem_of_commutators_mem_center {R : Subgroup G} (hR : CFSG.IsExtraspecialPGroup 2 ↥R)
    (hC : centralizer (R : Set G) ≤ R) {g : G}
    (hg : ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ (center ↥R).map R.subtype) : g ∈ R := by
  have hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro r hr
    obtain ⟨c, _, hcv⟩ := hg r hr
    have : g * r * g⁻¹ = (c : G) * r := by
      rw [show (c : G) = g * r * g⁻¹ * r⁻¹ from hcv]; group
    rw [this]
    exact R.mul_mem c.2 hr
  have hgN : g ∈ normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj h hh, fun hh => ?_⟩
    have hfin : Function.Surjective
        (fun r : R => (⟨g * (r : G) * g⁻¹, hconj r r.2⟩ : R)) := by
      apply Finite.surjective_of_injective
      intro r s hrs
      have h1 : g * (r : G) * g⁻¹ = g * (s : G) * g⁻¹ := congrArg (fun x : R => (x : G)) hrs
      exact Subtype.ext (by
        have := congrArg (fun x : G => g⁻¹ * x * g) h1
        simpa [mul_assoc] using this)
    obtain ⟨r, hr⟩ := hfin ⟨g * h * g⁻¹, hh⟩
    have h1 : g * (r : G) * g⁻¹ = g * h * g⁻¹ := congrArg (fun x : R => (x : G)) hr
    have h2 : (r : G) = h := by
      have := congrArg (fun x : G => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    rw [← h2]
    exact r.2
  let N : Subgroup G := normalizer (R : Set G)
  let Q : Subgroup N := R.subgroupOf N
  have hQn : Q.Normal := inferInstance
  have hRN : R ≤ N := Subgroup.le_normalizer
  let e : Q ≃* R := Subgroup.subgroupOfEquivOfLe hRN
  have hQ : CFSG.IsExtraspecialPGroup 2 ↥Q := isExtraspecialPGroup_of_mulEquiv e.symm hR
  have hCQ : centralizer (Q : Set N) ≤ Q := by
    intro x hx
    change (x : G) ∈ R
    apply hC
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro r hr
    have hxq := hx ⟨r, Subgroup.le_normalizer hr⟩ hr
    have := congrArg (fun y : N => (y : G)) hxq
    simpa using this
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    AddCommGroup.zmodModule (n := 2) fun v => by
      obtain ⟨x, rfl⟩ := exists_ofMul_of v
      rw [← ofMul_pow, ← map_pow]
      exact (ofMul_of_eq_zero_iff hQ (x ^ 2)).2 (sq_mem_center hQ x)
  let g' : N := ⟨g, hgN⟩
  have hρ : extraspecialConjOrth hQ hQn g' = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [extraspecialConjOrth_apply]
    simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id]
    have hcent_of_map : ∀ y : Q, e y ∈ center ↥R → y ∈ center Q := by
      intro y hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro z
      apply e.injective
      rw [map_mul, map_mul]
      exact hy (e z)
    have key : conjAut hQn g' x * x⁻¹ ∈ center Q := by
      apply hcent_of_map
      obtain ⟨c, hc, hcv⟩ := hg (e x : R) (e x).2
      have hec : e (conjAut hQn g' x * x⁻¹) = c := by
        apply Subtype.ext
        change ((conjAut hQn g' x * x⁻¹ : Q) : G) = (c : G)
        rw [show (c : G) = g * (e x : G) * g⁻¹ * (e x : G)⁻¹ from hcv]
        have hcx : ((conjAut hQn g' x : Q) : G) = g * (x : G) * g⁻¹ := by
          have h := congrArg (fun y : N => (y : G)) (conjAut_apply hQn g' x)
          simpa using h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcx]
        rfl
      rw [hec]
      exact hc
    have hz : Additive.ofMul (Abelianization.of (conjAut hQn g' x)) =
        Additive.ofMul (Abelianization.of x) := by
      have h0 : Additive.ofMul (Abelianization.of (conjAut hQn g' x * x⁻¹)) = 0 :=
        (ofMul_of_eq_zero_iff hQ _).2 key
      rw [ofMul_of_mul] at h0
      rw [map_inv, ofMul_inv] at h0
      rwa [add_eq_zero_iff_eq_neg, neg_neg] at h0
    exact hz
  have hgQ : g' ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ hρ
  exact show g ∈ R from hgQ

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
