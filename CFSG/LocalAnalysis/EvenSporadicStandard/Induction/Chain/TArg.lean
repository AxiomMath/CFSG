module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Second
import CFSG.GroupTheory.OddOverlap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

@[expose] def FourAConcl (K L N₀ : Subgroup H) : Prop :=
  ¬ IsSectionOf ↥((N₀.subgroupOf K).map (QuotientGroup.mk' (center ↥K))) ↥(lam L N₀) ∧
    ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      Nonempty ((K₂ ⧸ center K₂) ≃* (↥K ⧸ center ↥K)) → NoFixedEmbeds K₂ ↥(lam L N₀)

omit [Finite H] in
theorem isSectionOf_of_le_range {X : Type} [Group X] {E Λ : Subgroup H} (hEΛ : E ≤ Λ)
    (g : ↥E →* X) (S : Subgroup X) (hS : S ≤ g.range) : IsSectionOf ↥S ↥Λ := by
  set B : Subgroup ↥E := S.comap g with hB
  let e : ↥B ≃* ↥(B.map (Subgroup.inclusion hEΛ)) :=
    Subgroup.equivMapOfInjective B (Subgroup.inclusion hEΛ) (Subgroup.inclusion_injective hEΛ)
  let f : ↥B →* ↥S := (g.comp B.subtype).codRestrict S (fun x => x.2)
  refine ⟨B.map (Subgroup.inclusion hEΛ), f.comp e.symm.toMonoidHom, ?_⟩
  intro s
  obtain ⟨x, hx⟩ := hS s.2
  have hxB : x ∈ B := by
    show g x ∈ S
    rw [hx]
    exact s.2
  refine ⟨e ⟨x, hxB⟩, ?_⟩
  show f (e.symm (e ⟨x, hxB⟩)) = s
  rw [MulEquiv.symm_apply_apply]
  exact Subtype.ext hx

omit [Finite H] in
theorem isSection_of_perfect {K N₀ Λ E : Subgroup H} (hEΛ : E ≤ Λ)
    (e : Nonempty ((↥E ⧸ center ↥E) ≃* (↥K ⧸ center ↥K))) :
    IsSectionOf ↥((N₀.subgroupOf K).map (QuotientGroup.mk' (center ↥K))) ↥Λ := by
  obtain ⟨e⟩ := e
  exact isSectionOf_of_le_range hEΛ ((e : (↥E ⧸ center ↥E) →* (↥K ⧸ center ↥K)).comp
    (QuotientGroup.mk' (center ↥E))) _ fun y _ =>
    ⟨(QuotientGroup.mk_surjective (e.symm y)).choose, by
      simp [(QuotientGroup.mk_surjective (e.symm y)).choose_spec]⟩

section Involution

variable {K L N₀ : Subgroup H} {t : H}

omit [Finite H] in
theorem mem_lam_of_commute (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H)) {y : H}
    (hyN : y ∈ centralizer (N₀ : Set H)) (hyt : y * t = t * y) : y ∈ lam L N₀ :=
  ⟨hCt (mem_centralizer_singleton_iff.2 hyt), hyN⟩

omit [Finite H] in
theorem false_of_diag_swap (h4 : FourAConcl K L N₀)
    (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H)) (ht2 : t * t = 1)
    (htN : t ∈ centralizer (N₀ : Set H)) {D : Subgroup H} [Group.IsPerfect ↥D]
    (hDN : D ≤ centralizer (N₀ : Set H))
    (hiso : Nonempty ((↥D ⧸ center ↥D) ≃* (↥K ⧸ center ↥K)))
    (hcomm : ∀ a ∈ D, ∀ b ∈ D.map (MulAut.conj t).toMonoidHom, a * b = b * a) : False := by
  have hmem : ∀ d : ↥D, t * (d : H) * t⁻¹ ∈ D.map (MulAut.conj t).toMonoidHom := fun d =>
    ⟨d, d.2, rfl⟩
  let φ : ↥D →* H :=
    { toFun := fun d => (d : H) * (t * (d : H) * t⁻¹)
      map_one' := by simp
      map_mul' := by
        intro n m
        have hc := hcomm (m : H) m.2 _ (hmem n)
        show ((n * m : ↥D) : H) * (t * ((n * m : ↥D) : H) * t⁻¹) =
          ((n : H) * (t * (n : H) * t⁻¹)) * ((m : H) * (t * (m : H) * t⁻¹))
        calc ((n * m : ↥D) : H) * (t * ((n * m : ↥D) : H) * t⁻¹)
            = (n : H) * (m * (t * (n : H) * t⁻¹)) * (t * (m : H) * t⁻¹) := by
              simp only [Subgroup.coe_mul]; group
          _ = (n : H) * ((t * (n : H) * t⁻¹) * m) * (t * (m : H) * t⁻¹) := by rw [hc]
          _ = _ := by group }
  have hφ : ∀ d : ↥D, φ d = (d : H) * (t * (d : H) * t⁻¹) := fun d => rfl
  have hEΛ : φ.range ≤ lam L N₀ := by
    rintro _ ⟨d, rfl⟩
    rw [hφ]
    have hdN : (d : H) ∈ centralizer (N₀ : Set H) := hDN d.2
    have h2 : t * (d : H) * t⁻¹ ∈ centralizer (N₀ : Set H) :=
      (centralizer (N₀ : Set H)).mul_mem ((centralizer (N₀ : Set H)).mul_mem htN hdN)
        ((centralizer (N₀ : Set H)).inv_mem htN)
    refine mem_lam_of_commute hCt ((centralizer (N₀ : Set H)).mul_mem hdN h2) ?_
    have hc := hcomm (d : H) d.2 _ (hmem d)
    calc (d : H) * (t * (d : H) * t⁻¹) * t
        = ((t * (d : H) * t⁻¹) * (d : H)) * t := by rw [hc]
      _ = t * ((d : H) * (t * (d : H) * t⁻¹)) := by
          have : t * ((d : H) * (t * (d : H) * t⁻¹)) =
              (t * (d : H) * t⁻¹) * ((t * t) * (d : H) * (t * t)⁻¹) * t := by group
          rw [this, ht2]; group
  have hker : φ.rangeRestrict.ker ≤ center ↥D := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hd1 : φ d = 1 := congrArg Subtype.val hd
    rw [hφ] at hd1
    have hdinv : (d : H) = (t * (d : H) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hd1
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : H) * d = d * (g : H)
    rw [hdinv]
    exact hcomm (g : H) g.2 _ ((D.map (MulAut.conj t).toMonoidHom).inv_mem (hmem d))
  have hE : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  obtain ⟨e₁⟩ := cqEquiv_of_central_cover φ.rangeRestrict φ.rangeRestrict_surjective hker
  obtain ⟨e₂⟩ := hiso
  exact h4.1 (isSection_of_perfect hEΛ ⟨e₁.symm.trans e₂⟩)

theorem false_of_diag_stable (h4 : FourAConcl K L N₀)
    (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H)) (ht2 : t * t = 1)
    (htN : t ∈ centralizer (N₀ : Set H)) {D : Subgroup H} [Group.IsPerfect ↥D]
    (hDN : D ≤ centralizer (N₀ : Set H))
    (hiso : Nonempty ((↥D ⧸ center ↥D) ≃* (↥K ⧸ center ↥K)))
    (hDt : D.map (MulAut.conj t).toMonoidHom = D) : False := by
  have htD : t ∈ normalizer (D : Set H) :=
    CFSG.EvenSporadicStandard.Solomon78.mem_normalizer_iff_map_conj_eq.2 hDt
  set α : MulAut ↥D := Subgroup.normalizerMonoidHom D ⟨t, htD⟩ with hα
  have hαapp : ∀ d : ↥D, ((α d : ↥D) : H) = t * d * t⁻¹ := fun d =>
    Subgroup.normalizerMonoidHom_apply_apply_coe D ⟨t, htD⟩ d
  by_cases hα1 : α = 1
  · have hDΛ : D ≤ lam L N₀ := by
      intro d hd
      refine mem_lam_of_commute hCt (hDN hd) ?_
      have h1 := hαapp ⟨d, hd⟩
      rw [hα1, MulAut.one_apply] at h1
      have h2 : t * (d : H) * t⁻¹ = d := h1.symm
      calc (d : H) * t = (t * (d : H) * t⁻¹) * t := by rw [h2]
        _ = t * d := by group
    exact h4.1 (isSection_of_perfect hDΛ hiso)
  · have hαα : α * α = 1 := by
      have : (⟨t, htD⟩ : ↥(normalizer (D : Set H))) * ⟨t, htD⟩ = 1 := Subtype.ext ht2
      rw [hα, ← map_mul, this, map_one]
    have hfix : ∀ k : ↥(fixSubgroup α), t * ((k : ↥D) : H) * t⁻¹ = ((k : ↥D) : H) := by
      intro k
      rw [← hαapp]
      exact congrArg Subtype.val k.2
    have hkΛ : ∀ k : ↥(fixSubgroup α), ((k : ↥D) : H) ∈ lam L N₀ := fun k =>
      mem_lam_of_commute hCt (hDN (k : ↥D).2) (by
        have h2 := hfix k
        calc ((k : ↥D) : H) * t = (t * ((k : ↥D) : H) * t⁻¹) * t := by rw [h2]
          _ = t * ((k : ↥D) : H) := by group)
    let f : ↥(fixSubgroup α) →* ↥(lam L N₀) :=
      { toFun := fun k => ⟨((k : ↥D) : H), hkΛ k⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp }
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : ((a : ↥D) : H) = ((b : ↥D) : H) :=
        congrArg (fun z : ↥(lam L N₀) => (z : H)) hab
      exact Subtype.ext (Subtype.ext h1)
    have hD4 := h4.2 ↥D inferInstance hiso α hα1 hαα
    by_cases htDm : t ∈ D
    ·
      have hinner : ∃ k : ↥D, α = MulAut.conj k := by
        refine ⟨⟨t, htDm⟩, ?_⟩
        ext n
        rw [hαapp]
        simp [MulAut.conj_apply]
      exact (hD4.2 hinner) ⟨f, hf⟩
    ·
      have htΛ : t ∈ lam L N₀ := ⟨hCt (mem_centralizer_singleton_iff.2 rfl), htN⟩
      obtain ⟨g, hg⟩ := exists_hom_of_sq_eq_one (⟨t, htΛ⟩ : ↥(lam L N₀)) (Subtype.ext ht2)
      have hb2 : ∀ b : Multiplicative (ZMod 2), b = 1 ∨ b = Multiplicative.ofAdd 1 := by
        intro b
        have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        rcases this (Multiplicative.toAdd b) with h0 | h1
        · exact Or.inl (by simpa using congrArg Multiplicative.ofAdd h0)
        · exact Or.inr (by simpa using congrArg Multiplicative.ofAdd h1)
      have hg1 : g 1 = 1 := map_one g
      have hcomm : ∀ (a : ↥(fixSubgroup α)) (b : Multiplicative (ZMod 2)), Commute (f a) (g b) := by
        intro a b
        rcases hb2 b with rfl | rfl
        · rw [hg1]
          exact Commute.one_right _
        · rw [hg]
          refine Subtype.ext ?_
          show ((a : ↥D) : H) * t = t * ((a : ↥D) : H)
          have := hfix a
          calc ((a : ↥D) : H) * t = (t * ((a : ↥D) : H) * t⁻¹) * t := by rw [this]
            _ = t * ((a : ↥D) : H) := by group
      have hne : ∀ x y : ↥(fixSubgroup α), f x * ⟨t, htΛ⟩ ≠ f y := by
        intro x y hxy
        apply htDm
        have h1 := congrArg (fun z : ↥(lam L N₀) => (z : H)) hxy
        simp only [Subgroup.coe_mul] at h1
        have h2 : t = (((x : ↥D) : H))⁻¹ * ((y : ↥D) : H) := by
          calc t = (((x : ↥D) : H))⁻¹ * (((x : ↥D) : H) * t) := by group
            _ = _ := by
              have h1' : ((x : ↥D) : H) * t = ((y : ↥D) : H) := h1
              rw [h1']
        rw [h2]
        exact D.mul_mem (D.inv_mem (x : ↥D).2) (y : ↥D).2
      refine (hD4.1) ⟨f.noncommCoprod g hcomm, ?_⟩
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have hab' : f a * g b = f a' * g b' := by
        simpa [MonoidHom.noncommCoprod_apply] using hab
      rcases hb2 b with rfl | rfl <;> rcases hb2 b' with rfl | rfl
      · rw [hg1, mul_one, mul_one] at hab'
        exact Prod.ext (hf hab') rfl
      · rw [hg1, hg, mul_one] at hab'
        exact (hne a' a hab'.symm).elim
      · rw [hg1, hg, mul_one] at hab'
        exact (hne a a' hab').elim
      · rw [hg, mul_left_inj] at hab'
        exact Prod.ext (hf hab') rfl

omit [Finite H] in
theorem centralizer_le_normalizer_of_order_two {L : Subgroup H} (hL : StdBare L) {t : H}
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set H) ≤ normalizer (L : Set H) := fun _ hy =>
  CFSG.StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hL.2 ht ht2
    (mem_centralizer_singleton_iff.1 hy)

theorem false_of_diag (h4 : FourAConcl K L N₀)
    (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H)) (ht2 : t * t = 1)
    (htN : t ∈ centralizer (N₀ : Set H)) {D : Subgroup H} [Group.IsPerfect ↥D]
    (hDN : D ≤ centralizer (N₀ : Set H))
    (hiso : Nonempty ((↥D ⧸ center ↥D) ≃* (↥K ⧸ center ↥K)))
    (hdich : D.map (MulAut.conj t).toMonoidHom = D ∨
      ∀ a ∈ D, ∀ b ∈ D.map (MulAut.conj t).toMonoidHom, a * b = b * a) : False := by
  rcases hdich with h | h
  · exact false_of_diag_stable h4 hCt ht2 htN hDN hiso h
  · exact false_of_diag_swap h4 hCt ht2 htN hDN hiso h

end Involution

end CFSG.EvenSporadicStandard.Induction
