module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.EvenSporadicStandard.Solomon78 CFSG.RankThree.PerfectCover

theorem hom_eq_of_perfect_of_central_diff {B C : Type*} [Group B] [Group C]
    (hB : Group.IsPerfect B) (f g : B →* C) (h : ∀ b, (f b)⁻¹ * g b ∈ Subgroup.center C) :
    f = g := by
  let δ : B →* C := MonoidHom.mk' (fun b => (f b)⁻¹ * g b) (fun b c => by
    have hb := Subgroup.mem_center_iff.1 (h b) (f c)⁻¹
    show (f (b * c))⁻¹ * g (b * c) = ((f b)⁻¹ * g b) * ((f c)⁻¹ * g c)
    rw [map_mul, map_mul, mul_inv_rev]
    calc (f c)⁻¹ * (f b)⁻¹ * (g b * g c) = ((f c)⁻¹ * ((f b)⁻¹ * g b)) * g c := by group
      _ = (((f b)⁻¹ * g b) * (f c)⁻¹) * g c := by rw [hb]
      _ = ((f b)⁻¹ * g b) * ((f c)⁻¹ * g c) := by group)
  have hδ : ∀ b, δ b = (f b)⁻¹ * g b := fun b => rfl
  have hker : commutator B ≤ δ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro x ⟨p, q, rfl⟩
    have hc : δ q * δ p = δ p * δ q := by
      rw [hδ p]
      exact Subgroup.mem_center_iff.1 (h p) (δ q)
    rw [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, ← hc]
    group
  have hperf : commutator B = ⊤ := Group.isPerfect_def.1 hB
  ext b
  have hb : b ∈ δ.ker := hker (by rw [hperf]; exact Subgroup.mem_top b)
  rw [MonoidHom.mem_ker, hδ] at hb
  exact inv_mul_eq_one.1 hb

theorem u62Cov_center_char {K : Type*} [Group K] (α : MulAut K) {x : K}
    (hx : x ∈ Subgroup.center K) : α x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := Subgroup.mem_center_iff.1 hx (α.symm g)
  calc g * α x = α (α.symm g * x) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = α (x * α.symm g) := by rw [h1]
    _ = α x * g := by rw [map_mul, MulEquiv.apply_symm_apply]

theorem involutionFixesElem_of_cover {B K Y : Type} [Group B] [Group K] [Group Y]
    [Finite B] [Finite K]
    (hB : Group.IsPerfect B) (hK : Group.IsPerfect K) (hY : Subgroup.center Y = ⊥)
    (p₀ : B →* Y) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ Subgroup.center B)
    (p : K →* Y) (hp : Function.Surjective p) (hpk : p.ker ≤ Subgroup.center K)
    (hp2 : IsPGroup 2 p.ker) (m : ℕ) (hm : Odd m)
    (hcard : Nat.card (hopfMultiplier Y) = Nat.card p₀.ker * m)
    (hk4 : Nat.card p₀.ker = 4) {n : ℕ} (hfix : InvolutionFixesElem B (4 * n)) :
    InvolutionFixesElem K n := by
  classical
  obtain ⟨α₀, hα₀s, hα₀⟩ := CFSG.GH74.Generic.exists_lift_of_odd_index hB hK p₀ hp₀ hk₀ p hp hpk
    hp2 m hm hcard
  have hα₀p : ∀ b, p (α₀ b) = p₀ b := fun b => DFunLike.congr_fun hα₀ b
  have hkerc : ∀ z ∈ Subgroup.center K, p z = 1 := by
    intro z hz
    have h1 : p z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := hp y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
    rw [hY, Subgroup.mem_bot] at h1
    exact h1
  intro σ hσ1 hσσ
  have hσσ' : ∀ x, σ (σ x) = x := fun x => by
    have h := congrArg (fun f : MulAut K => f x) hσσ
    simpa using h
  have hσker : ∀ x, p x = 1 → p (σ x) = 1 := fun x hx =>
    hkerc (σ x) (u62Cov_center_char σ (hpk (MonoidHom.mem_ker.2 hx)))
  have hle : p.ker ≤ (p.comp σ.toMonoidHom).ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hσker x hx
  let σb : Y →* Y := p.liftOfSurjective hp ⟨p.comp σ.toMonoidHom, hle⟩
  have hσb : ∀ x, σb (p x) = p (σ x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨p.comp σ.toMonoidHom, hle⟩ x
  have hσbσb : ∀ y, σb (σb y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    rw [hσb, hσb, hσσ']
  let p₀' : B →* Y := σb.comp p₀
  have hp₀'s : Function.Surjective p₀' := fun y => by
    obtain ⟨x, hx⟩ := hp₀ (σb y)
    exact ⟨x, by show σb (p₀ x) = y; rw [hx, hσbσb]⟩
  have hker' : p₀'.ker = p₀.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    show σb (p₀ x) = 1 ↔ p₀ x = 1
    constructor
    · intro h
      have := congrArg σb h
      rwa [hσbσb, map_one] at this
    · intro h
      rw [h, map_one]
  have hp₀2 : IsPGroup 2 p₀.ker := IsPGroup.of_card (n := 2) (by rw [hk4]; norm_num)
  obtain ⟨β, hβs, hβ⟩ := CFSG.GH74.Generic.exists_lift_of_odd_index hB hB p₀' hp₀'s
    (by rw [hker']; exact hk₀) p₀ hp₀ hk₀ hp₀2 m hm (by rw [hker']; exact hcard)
  have hβ' : ∀ b, p₀ (β b) = σb (p₀ b) := fun b => DFunLike.congr_fun hβ b
  have hdiff : ∀ b, (σ (α₀ b))⁻¹ * α₀ (β b) ∈ Subgroup.center K := by
    intro b
    apply hpk
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα₀p, ← hσb, hα₀p, hβ' b, inv_mul_cancel]
  have hcomm : ∀ b, α₀ (β b) = σ (α₀ b) := by
    have h := hom_eq_of_perfect_of_central_diff hB (σ.toMonoidHom.comp α₀) (α₀.comp β) hdiff
    intro b
    exact (DFunLike.congr_fun h b).symm
  have hβ2 : ∀ b, β (β b) = b := by
    have hdiff2 : ∀ b, ((β.comp β) b)⁻¹ * (MonoidHom.id B) b ∈ Subgroup.center B := by
      intro b
      apply hk₀
      rw [MonoidHom.mem_ker]
      show p₀ ((β (β b))⁻¹ * b) = 1
      rw [map_mul, map_inv, hβ', hβ', hσbσb, inv_mul_cancel]
    have h := hom_eq_of_perfect_of_central_diff hB (β.comp β) (MonoidHom.id B) hdiff2
    intro b
    exact DFunLike.congr_fun h b
  let β' : MulAut B :=
    { toFun := β
      invFun := β
      left_inv := hβ2
      right_inv := hβ2
      map_mul' := map_mul β }
  have hββ : β' * β' = 1 := by
    ext b
    exact hβ2 b
  have hβ1 : β' ≠ 1 := by
    intro h1
    apply hσ1
    ext x
    obtain ⟨b, rfl⟩ := hα₀s x
    have hb : β b = b := congrArg (fun f : MulAut B => f b) h1
    rw [← hcomm b, hb]
    rfl
  obtain ⟨E, hEfix, hE2, hEc, hEcard⟩ := hfix β' hβ1 hββ
  refine ⟨E.map α₀, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hcomm x]
    have hx' : β x = x := hEfix x hx
    rw [hx']
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hEc x hx y hy]
  ·
    set f : E →* ↥(E.map α₀) := α₀.subgroupMap E with hf
    have hfs : Function.Surjective f := MonoidHom.subgroupMap_surjective α₀ E
    have hmul := Subgroup.card_ker_mul_card_of_surjective hfs
    have hkerle : Nat.card f.ker ≤ 4 := by
      rw [← hk4]
      refine Nat.card_le_card_of_injective
        (fun x : f.ker => (⟨((x : E) : B), ?_⟩ : p₀.ker)) ?_
      · have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        have h1 : α₀ ((x : E) : B) = 1 := by
          have := congrArg Subtype.val hx
          simpa [hf] using this
        rw [← hα₀p, h1, map_one]
      · intro x y hxy
        have h' := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h')
    have h4 : 4 * n ≤ 4 * Nat.card ↥(E.map α₀) := by
      calc 4 * n ≤ Nat.card ↥E := hEcard
        _ = Nat.card f.ker * Nat.card ↥(E.map α₀) := hmul.symm
        _ ≤ 4 * Nat.card ↥(E.map α₀) := Nat.mul_le_mul_right _ hkerle
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)

end CFSG.EvenSporadicStandard.Induction.Fi
