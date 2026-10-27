module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmcRoot
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmrBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section General

variable {G : Type*} [Group G] [Finite G]

theorem gmr_card_le_two_mul_inf {X N : Subgroup G}
    (h : ∀ y ∈ X, ∀ y₀ ∈ X, y ∉ N → y₀ ∉ N → y * y₀⁻¹ ∈ N) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ N : Subgroup G) := by
  classical
  by_cases hX : ∃ y₀ ∈ X, y₀ ∉ N
  · obtain ⟨y₀, hy₀X, hy₀N⟩ := hX
    let F : X → (X ⊓ N : Subgroup G) × Bool := fun y =>
      if hy : (y : G) ∈ N then (⟨y, mem_inf.mpr ⟨y.2, hy⟩⟩, true)
      else (⟨y * y₀⁻¹, mem_inf.mpr ⟨mul_mem y.2 (inv_mem hy₀X), h y y.2 y₀ hy₀X hy hy₀N⟩⟩, false)
    have hF : Function.Injective F := by
      intro y y' hyy'
      by_cases hy : (y : G) ∈ N <;> by_cases hy' : (y' : G) ∈ N
      · have h1 : F y = (⟨y, mem_inf.mpr ⟨y.2, hy⟩⟩, true) := dite_eq_left hy
        have h2 : F y' = (⟨y', mem_inf.mpr ⟨y'.2, hy'⟩⟩, true) := dite_eq_left hy'
        rw [h1, h2] at hyy'
        exact Subtype.ext (congrArg (fun p : (X ⊓ N : Subgroup G) × Bool => (p.1 : G)) hyy')
      · have h1 : (F y).2 = true := by simp only [F, dite_eq_left hy]
        have h2 : (F y').2 = false := by simp only [F, dite_eq_right hy']
        rw [hyy', h2] at h1
        exact absurd h1 (by decide)
      · have h1 : (F y).2 = false := by simp only [F, dite_eq_right hy]
        have h2 : (F y').2 = true := by simp only [F, dite_eq_left hy']
        rw [hyy', h2] at h1
        exact absurd h1 (by decide)
      · have h1 : F y = (⟨y * y₀⁻¹, mem_inf.mpr ⟨mul_mem y.2 (inv_mem hy₀X),
            h y y.2 y₀ hy₀X hy hy₀N⟩⟩, false) := dite_eq_right hy
        have h2 : F y' = (⟨y' * y₀⁻¹, mem_inf.mpr ⟨mul_mem y'.2 (inv_mem hy₀X),
            h y' y'.2 y₀ hy₀X hy' hy₀N⟩⟩, false) := dite_eq_right hy'
        rw [h1, h2] at hyy'
        have h3 := congrArg (fun p : (X ⊓ N : Subgroup G) × Bool => (p.1 : G)) hyy'
        exact Subtype.ext (mul_right_cancel h3)
    have h1 := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
    linarith
  · push Not at hX
    have h1 := card_le_of_le (le_inf le_rfl hX : X ≤ X ⊓ N)
    omega

theorem gmr_card_le_card_sup_inf {X₁ T₁ : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htT₁ : ∀ y ∈ T₁, y * t = t * y) (htX : t ∉ X₁) (hX : X₁ ≤ T₁ ⊔ zpowers t) :
    Nat.card X₁ ≤ Nat.card ((X₁ ⊔ zpowers t) ⊓ T₁ : Subgroup G) := by
  classical
  have htC : t ∈ centralizer (T₁ : Set G) := mem_centralizer_iff.mpr htT₁
  have hsq : t ^ 2 = 1 := by rw [sq]; exact ht2
  have hmulT : ∀ y ∈ X₁, y ∉ T₁ → y * t ∈ T₁ := by
    intro y hy hyT
    obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htC (hX hy)
    rcases mem_zpowers_involution_eq_one_or_eq hsq hz with rfl | rfl
    · exact absurd (by rw [mul_one]; exact ha) hyT
    · rw [mul_assoc, ht2, mul_one]
      exact ha
  have hsupt : ∀ y ∈ X₁, y * t ∈ X₁ ⊔ zpowers t := fun y hy =>
    mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers t))
  let F : X₁ → ((X₁ ⊔ zpowers t) ⊓ T₁ : Subgroup G) := fun y =>
    if hy : (y : G) ∈ T₁ then ⟨y, mem_inf.mpr ⟨mem_sup_left y.2, hy⟩⟩
    else ⟨y * t, mem_inf.mpr ⟨hsupt y y.2, hmulT y y.2 hy⟩⟩
  refine Nat.card_le_card_of_injective F fun y y' hyy' => ?_
  have hval := congrArg (Subtype.val : ((X₁ ⊔ zpowers t) ⊓ T₁ : Subgroup G) → G) hyy'
  apply Subtype.ext
  by_cases hy : (y : G) ∈ T₁ <;> by_cases hy' : (y' : G) ∈ T₁
  · simpa [F, hy, hy'] using hval
  · simp only [F, hy, hy', dite_true, dite_false] at hval
    exfalso
    apply htX
    rw [show t = (y' : G)⁻¹ * y by rw [hval]; group]
    exact mul_mem (inv_mem y'.2) y.2
  · simp only [F, hy, hy', dite_true, dite_false] at hval
    exfalso
    apply htX
    rw [show t = (y : G)⁻¹ * y' by rw [← hval]; group]
    exact mul_mem (inv_mem y.2) y'.2
  · simp only [F, hy, hy', dite_false] at hval
    exact mul_right_cancel hval

theorem gmr_sq_comm_mem_of_mem_sup {X₁ Z : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htX : ∀ y ∈ X₁, y * t = t * y) (hsq : ∀ y ∈ X₁, y * y ∈ Z)
    (hcomm : ∀ y ∈ X₁, ∀ y' ∈ X₁, y * y' * y⁻¹ * y'⁻¹ ∈ Z) :
    (∀ y ∈ X₁ ⊔ zpowers t, y * y ∈ Z) ∧
      ∀ y ∈ X₁ ⊔ zpowers t, ∀ y' ∈ X₁ ⊔ zpowers t, y * y' * y⁻¹ * y'⁻¹ ∈ Z := by
  have htC : t ∈ centralizer (X₁ : Set G) := mem_centralizer_iff.mpr htX
  have hsq2 : t ^ 2 = 1 := by rw [sq]; exact ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hdec : ∀ y ∈ X₁ ⊔ zpowers t, ∃ c ∈ X₁, y = c ∨ y = c * t := by
    intro y hy
    obtain ⟨c, hc, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htC hy
    rcases mem_zpowers_involution_eq_one_or_eq hsq2 hz with rfl | rfl
    · exact ⟨c, hc, Or.inl (mul_one c)⟩
    · exact ⟨c, hc, Or.inr rfl⟩
  have hconj : ∀ c w : G, w * t = t * w → c * t * w * (c * t)⁻¹ = c * w * c⁻¹ := by
    intro c w hw
    calc c * t * w * (c * t)⁻¹ = c * (t * w) * t⁻¹ * c⁻¹ := by group
      _ = c * (w * t) * t⁻¹ * c⁻¹ := by rw [hw]
      _ = c * w * c⁻¹ := by group
  have htsup : ∀ y ∈ X₁ ⊔ zpowers t, y * t = t * y := by
    intro y hy
    obtain ⟨c, hc, hyc | hyc⟩ := hdec y hy
    · rw [hyc]
      exact htX c hc
    · rw [hyc]
      calc c * t * t = c := by rw [mul_assoc, ht2, mul_one]
        _ = t * t * c := by rw [ht2, one_mul]
        _ = t * (t * c) := by group
        _ = t * (c * t) := by rw [htX c hc]
  refine ⟨fun y hy => ?_, fun y hy y' hy' => ?_⟩
  · obtain ⟨c, hc, hyc | hyc⟩ := hdec y hy
    · rw [hyc]
      exact hsq c hc
    · rw [hyc, show c * t * (c * t) = c * (t * c) * t by group, ← htX c hc,
        show c * (c * t) * t = c * c * (t * t) by group, ht2, mul_one]
      exact hsq c hc
  · obtain ⟨c, hc, hyc | hyc⟩ := hdec y hy <;> obtain ⟨c', hc', hyc' | hyc'⟩ := hdec y' hy' <;>
      rw [hyc, hyc']
    · exact hcomm c hc c' hc'
    · rw [show c * (c' * t) * c⁻¹ * (c' * t)⁻¹ = c * c' * (t * c⁻¹) * t⁻¹ * c'⁻¹ by group,
        show t * c⁻¹ = c⁻¹ * t from (htX _ (inv_mem hc)).symm,
        show c * c' * (c⁻¹ * t) * t⁻¹ * c'⁻¹ = c * c' * c⁻¹ * c'⁻¹ by group]
      exact hcomm c hc c' hc'
    · rw [show c * t * c' * (c * t)⁻¹ * c'⁻¹ = (c * t * c' * (c * t)⁻¹) * c'⁻¹ by group,
        hconj c c' (htX c' hc')]
      exact hcomm c hc c' hc'
    · rw [show c * t * (c' * t) * (c * t)⁻¹ * (c' * t)⁻¹ =
          (c * t * (c' * t) * (c * t)⁻¹) * (c' * t)⁻¹ by group,
        hconj c (c' * t) (htsup _ (mul_mem (mem_sup_left hc') (mem_sup_right (mem_zpowers t)))),
        show c * (c' * t) * c⁻¹ * (c' * t)⁻¹ = c * c' * (t * c⁻¹) * t⁻¹ * c'⁻¹ by group,
        show t * c⁻¹ = c⁻¹ * t from (htX _ (inv_mem hc)).symm,
        show c * c' * (c⁻¹ * t) * t⁻¹ * c'⁻¹ = c * c' * c⁻¹ * c'⁻¹ by group]
      exact hcomm c hc c' hc'

end General

theorem gmr_two_mul_le_two_pow (f : ℕ) : 2 * f ≤ 2 ^ f := by
  rcases f with _ | k
  · simp
  · have hk : k < 2 ^ k := Nat.lt_two_pow_self
    rw [pow_succ]
    omega

theorem gmr_num_step3 {Q M c a : ℕ} (hQ : Q = M * M) (hQ2 : 2 ≤ Q) (ha : a ≤ M)
    (hc : c ≤ Q * Q) (h1 : Q ^ 5 * Q ≤ (c * a) ^ 2) : False := by
  have h2 : c * a ≤ Q * Q * M := Nat.mul_le_mul hc ha
  have h3 : (c * a) ^ 2 ≤ (Q * Q * M) ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : (Q * Q * M) ^ 2 = Q ^ 5 := by rw [hQ]; ring
  have h5 : Q ^ 5 * Q ≤ Q ^ 5 * 1 := by
    rw [mul_one]
    calc Q ^ 5 * Q ≤ (c * a) ^ 2 := h1
      _ ≤ (Q * Q * M) ^ 2 := h3
      _ = Q ^ 5 := h4
  have h6 : 0 < Q ^ 5 := pow_pos (by omega) 5
  have h7 := Nat.le_of_mul_le_mul_left h5 h6
  omega

theorem gmr_num_general {Q M c a R : ℕ} (hQ : Q = M * M) (hM : 4 ≤ M) (ha : a ≤ M)
    (hR : R ≤ a ^ 2) (hc : c ≤ 2 * (Q * R)) (h1 : Q ^ 5 * Q ≤ (c * a) ^ 2) : False := by
  have hR' : R ≤ M * M := hR.trans (by rw [sq]; exact Nat.mul_le_mul ha ha)
  have hc' : c ≤ 2 * (M * M * (M * M)) :=
    hc.trans (by rw [hQ]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR'))
  have h2 : c * a ≤ 2 * (M * M * (M * M)) * M := Nat.mul_le_mul hc' ha
  have h3 : (c * a) ^ 2 ≤ (2 * (M * M * (M * M)) * M) ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : M ^ 12 ≤ 4 * M ^ 10 := by
    have e1 : Q ^ 5 * Q = M ^ 12 := by rw [hQ]; ring
    have e2 : (2 * (M * M * (M * M)) * M) ^ 2 = 4 * M ^ 10 := by ring
    rw [← e1, ← e2]
    exact h1.trans h3
  have h5 : 16 * M ^ 10 ≤ M ^ 12 := by
    have e : M ^ 12 = M ^ 2 * M ^ 10 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by nlinarith)
  have h6 : 0 < M ^ 10 := pow_pos (by omega) 10
  omega

theorem gmr_num_four {c a R : ℕ} (ha : a ≤ 2) (hR : R ≤ 2) (hc : c ≤ 2 * (4 * R))
    (h1 : 4 ^ 5 * 4 ≤ (c * a) ^ 2) : False := by
  have hc' : c ≤ 16 := by omega
  have h2 : c * a ≤ 16 * 2 := Nat.mul_le_mul hc' ha
  have h3 : (c * a) ^ 2 ≤ (16 * 2) ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 := h1.trans h3
  norm_num at h4

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] [CharP E 2] {T₁ : Subgroup G}
  {σ : E →+* E} {u v : G → E}

theorem gmr_v_comm (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    v (y * y' * y⁻¹ * y'⁻¹) = u y * σ (u y') + σ (u y) * u y' := by
  have h0 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hz : y * y' * y⁻¹ * y'⁻¹ ∈ T₁ :=
    mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  have hu : u (y * y' * y⁻¹ * y'⁻¹) = 0 := by
    rw [hc.mul_u _ (mul_mem (mul_mem hy hy') (inv_mem hy)) _ (inv_mem hy'),
      hc.mul_u _ (mul_mem hy hy') _ (inv_mem hy), hc.mul_u _ hy _ hy', hc.u_inv hy, hc.u_inv hy']
    ring
  have e : (y * y' * y⁻¹ * y'⁻¹) * (y' * y) = y * y' := by group
  have h1 := congrArg v e
  rw [hc.mul_v _ hz _ (mul_mem hy' hy), hu, zero_mul, sub_zero, hc.mul_v _ hy' _ hy,
    hc.mul_v _ hy _ hy'] at h1
  linear_combination h1 + (-(u y * σ (u y'))) * h0

end U3RootCoords

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmr_card_le {x : G} (hxS₂ : x ∈ swapS₂ P U T) (hx2 : x * x = 1) :
    Nat.card U₁ * Nat.card (szA₁ (szT₁ L T)) ≤
      (Nat.card (U₁ ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G)) ^ 2 := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨K, _, _, _, κ, μ, hK, hκ, hμ⟩ := hS.exists_coords
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  refine gmr_card_mul_le (fun a ha => hW.T₁_le_U₁ (szA₁_le _ ha)) hx2
    (fun u hu => hW.conj_U₁ hxS₂ hu) (fun a ha => hW.conj_szA₁_of_mem hxS₂ ha) ?_ ?_
    (hL.muOne_comm_mem_szA₁ hS hκ hW.mu hK hμ) ?_
  · intro a ha u hu
    have h1 := hL.conj_szA₁ u (hL.U₁_le hu) a ha
    calc a * u = u * a * u⁻¹ * u := by rw [h1]
      _ = u * a := by group
  · intro a ha
    rw [← sq]
    exact hA₁2 a ha
  · intro u hu
    rw [← sq]
    exact hL.muOne_sq_mem_szA₁ hS hκ hW.mu hK hμ hu

theorem gmr_exists_conj (g : G) : ∃ g' : G, g' * t * g'⁻¹ = g * t * g⁻¹ ∧
    ∀ u ∈ U₁ ⊓ centralizer ({g * t * g⁻¹} : Set G), g'⁻¹ * u * g' ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hW.step.start
  have hU₁2 : IsPGroup 2 U₁ :=
    hW.isPGroup.to_le ((hW.level.U₁_le.trans le_sup_left).trans hW.le)
  set B : Subgroup G := (U₁ ⊓ centralizer ({g * t * g⁻¹} : Set G)).map
    (MulAut.conj g⁻¹).toMonoidHom with hBdef
  have hBt : B ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hux := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * u * g * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [hux]
      _ = t * (g⁻¹ * u * g) := by group
  have hBp : IsPGroup 2 B := (hU₁2.to_le inf_le_left).map _
  obtain ⟨a, haC, ha⟩ := exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer hBt hBp
  have hat : a * t = t * a := mem_centralizer_singleton_iff.mp haC
  refine ⟨g * a, ?_, fun u hu => ?_⟩
  · rw [show g * a * t * (g * a)⁻¹ = g * (a * t) * a⁻¹ * g⁻¹ by group, hat]
    group
  · have hb : g⁻¹ * u * g ∈ B := ⟨u, hu, by simp⟩
    have h1 := ha _ hb
    rwa [show a⁻¹ * (g⁻¹ * u * g) * a = (g * a)⁻¹ * u * (g * a) by group] at h1

theorem gmr_false {g : G} (hxS₂ : g * t * g⁻¹ ∈ swapS₂ P U T) (hxU : g * t * g⁻¹ ∉ U₁)
    {m : ℕ} (hm : f = 2 * m)
    (hcard : Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) ≤
      2 ^ m) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨hT₁card, hA₁card, -, -, -, hA₁2, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htT : t ∈ T := hW.t_mem
  have hTt : ∀ y ∈ T, y * t = t * y := fun y hy => mem_centralizer_singleton_iff.mp (h.le hy)
  have hQ : 2 ^ f = 2 ^ m * 2 ^ m := by rw [hm, two_mul, pow_add]
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  obtain ⟨g', hg', hg'T⟩ := hW.gmr_exists_conj g
  rw [← hg'] at hxS₂ hxU hcard hg'T
  set x := g' * t * g'⁻¹ with hxdef
  have hxx : x * x = 1 := by
    rw [hxdef, show g' * t * g'⁻¹ * (g' * t * g'⁻¹) = g' * (t * t) * g'⁻¹ by group, htt,
      mul_one, mul_inv_cancel]
  set CU := U₁ ⊓ centralizer ({x} : Set G) with hCUdef
  set CA := szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) with hCAdef
  have hA₁U₁ : szA₁ (szT₁ L T) ≤ U₁ := fun a ha => hW.T₁_le_U₁ (szA₁_le _ ha)
  have hCAU : CA ≤ CU := inf_le_inf_right _ hA₁U₁
  have hA₁c : ∀ a ∈ szA₁ (szT₁ L T), ∀ u ∈ U₁, a * u = u * a := by
    intro a ha u hu
    have h1 := hL.conj_szA₁ u (hL.U₁_le hu) a ha
    calc a * u = u * a * u⁻¹ * u := by rw [h1]
      _ = u * a := by group
  obtain ⟨K, _, _, _, κ, μ, hK, hκ, hμ⟩ := hS.exists_coords
  have hU₁sq : ∀ u ∈ U₁, u * u ∈ szA₁ (szT₁ L T) := fun u hu => by
    rw [← sq]
    exact hL.muOne_sq_mem_szA₁ hS hκ hW.mu hK hμ hu
  have hU₁comm := hL.muOne_comm_mem_szA₁ hS hκ hW.mu hK hμ
  have h1 := hW.gmr_card_le hxS₂ hxx
  rw [hL.muOne_card_U₁ hS, hA₁card] at h1
  set φ : G →* G := (MulAut.conj g'⁻¹).toMonoidHom with hφ
  have hφapp : ∀ y, φ y = g'⁻¹ * y * g' := fun y => by
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  set X : Subgroup G := CU.map φ with hXdef
  set Z₀ : Subgroup G := CA.map φ with hZ₀def
  have hXcard : Nat.card X = Nat.card CU := card_map_of_injective (MulAut.conj g'⁻¹).injective
  have hZ₀card : Nat.card Z₀ = Nat.card CA := card_map_of_injective (MulAut.conj g'⁻¹).injective
  have hXT : X ≤ T := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hφapp]
    exact hg'T u hu
  have htX : t ∉ X := by
    rintro ⟨u, hu, hut⟩
    rw [hφapp] at hut
    apply hxU
    have e : u = x := by rw [hxdef, ← hut]; group
    rw [← e]
    exact (mem_inf.mp hu).1
  have hXt : ∀ y ∈ X, y * t = t * y := fun y hy => hTt y (hXT hy)
  have hZ₀X : Z₀ ≤ X := map_mono hCAU
  have hZ₀2 : ∀ z ∈ Z₀, z * z = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha2 : a * a = 1 := by rw [← sq]; exact hA₁2 a (mem_inf.mp ha).1
    rw [hφapp, show g'⁻¹ * a * g' * (g'⁻¹ * a * g') = g'⁻¹ * (a * a) * g' by group, ha2]
    group
  have hZ₀c : ∀ z ∈ Z₀, ∀ y ∈ X, z * y = y * z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [hφapp, hφapp]
    have e := hA₁c a (mem_inf.mp ha).1 u (mem_inf.mp hu).1
    calc g'⁻¹ * a * g' * (g'⁻¹ * u * g') = g'⁻¹ * (a * u) * g' := by group
      _ = g'⁻¹ * (u * a) * g' := by rw [e]
      _ = g'⁻¹ * u * g' * (g'⁻¹ * a * g') := by group
  have hXsq : ∀ y ∈ X, y * y ∈ Z₀ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨huU, hux⟩ := mem_inf.mp hu
    refine ⟨u * u, mem_inf.mpr ⟨hU₁sq u huU, mul_mem hux hux⟩, ?_⟩
    rw [hφapp, hφapp]
    group
  have hXcomm : ∀ y ∈ X, ∀ y' ∈ X, y * y' * y⁻¹ * y'⁻¹ ∈ Z₀ := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    obtain ⟨huU, hux⟩ := mem_inf.mp hu
    obtain ⟨hu'U, hu'x⟩ := mem_inf.mp hu'
    refine ⟨u * u' * u⁻¹ * u'⁻¹, mem_inf.mpr ⟨hU₁comm u huU u' hu'U,
      mul_mem (mul_mem (mul_mem hux hu'x) (inv_mem hux)) (inv_mem hu'x)⟩, ?_⟩
    rw [hφapp, hφapp, hφapp]
    group
  have hZ₀T : ∀ z ∈ Z₀, z ∈ szT₁ L T ⊔ zpowers t := by
    intro z hz
    by_contra hzS
    have hzT : z ∈ T := hXT (hZ₀X hz)
    obtain ⟨-, -, hCz, -⟩ :=
      h.outer_facts_of_card_sylow hS2 hzT (by rw [sq]; exact hZ₀2 z hz) hzS
    have htN : t ∈ normalizer (X : Set G) :=
      mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
        rw [mul_assoc, hXt y hy, inv_mul_cancel_left]
        exact hy
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two htX htN htt
    have h3 := relIndex_mul_card (H := X) (K := X ⊔ zpowers t)
    rw [h2, inf_of_le_left le_sup_left] at h3
    have hHT : X ⊔ zpowers t ≤ T := sup_le hXT (zpowers_le.mpr htT)
    have hHz : X ⊔ zpowers t ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hZ₀c z hz y hy).symm) ?_
      exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hTt z hzT).symm)
    have hHT₁ : szT₁ L T ⊓ (X ⊔ zpowers t) ≤ szA₁ (szT₁ L T) := by
      intro y hy
      obtain ⟨hyT₁, hyH⟩ := mem_inf.mp hy
      exact hCz y hyT₁ (mem_centralizer_singleton_iff.mp (hHz hyH)).symm
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := szT₁ L T) (B := X ⊔ zpowers t) (hHT.trans hTN₁)
    have hsup : Nat.card (szT₁ L T ⊔ (X ⊔ zpowers t) : Subgroup G) ≤ Nat.card T :=
      card_le_of_le (sup_le (szT₁_le_left L T) hHT)
    have hinf : Nat.card (szT₁ L T ⊓ (X ⊔ zpowers t) : Subgroup G) ≤ 2 ^ f :=
      (card_le_of_le hHT₁).trans hA₁card.le
    rw [hT₁card, ← h3, hXcard] at hprod
    have h4 : (2 ^ f) ^ 3 * (2 * Nat.card CU) ≤ (2 ^ f) ^ 3 * (4 * f * 2 ^ f) := by
      calc (2 ^ f) ^ 3 * (2 * Nat.card CU) = Nat.card (szT₁ L T ⊔ (X ⊔ zpowers t) : Subgroup G) *
            Nat.card (szT₁ L T ⊓ (X ⊔ zpowers t) : Subgroup G) := hprod.symm
        _ ≤ (4 * f * (2 ^ f) ^ 3) * 2 ^ f := Nat.mul_le_mul (hsup.trans hW.card_T_le) hinf
        _ = (2 ^ f) ^ 3 * (4 * f * 2 ^ f) := by ring
    have h5 := Nat.le_of_mul_le_mul_left h4 (pow_pos (by norm_num) 3)
    have h6 : Nat.card CU ≤ 2 ^ f * 2 ^ f := by
      have h7 := gmr_two_mul_le_two_pow f
      have h8 : 2 * Nat.card CU ≤ 2 * (2 ^ f * 2 ^ f) :=
        calc 2 * Nat.card CU ≤ 4 * f * 2 ^ f := h5
          _ = 2 * ((2 * f) * 2 ^ f) := by ring
          _ ≤ 2 * (2 ^ f * 2 ^ f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h7)
      exact Nat.le_of_mul_le_mul_left h8 (by norm_num)
    exact gmr_num_step3 hQ hQ2 hcard h6 h1
  have hXsqN : ∀ y ∈ X, y ^ 2 ∈ szT₁ L T ⊔ zpowers t := fun y hy => by
    rw [sq]
    exact hZ₀T _ (hXsq y hy)
  have h4 : Nat.card X ≤ 2 * Nat.card (X ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) :=
    gmr_card_le_two_mul_inf fun y hy y₀ hy₀ hyN hy₀N =>
      h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (hXT hy) (hXT hy₀) (hXsqN y hy) (hXsqN y₀ hy₀)
        hyN hy₀N
  set X₁ := X ⊓ (szT₁ L T ⊔ zpowers t) with hX₁def
  have htX₁ : t ∉ X₁ := fun ht => htX (mem_inf.mp ht).1
  have htT₁ : ∀ y ∈ szT₁ L T, y * t = t * y := fun y hy =>
    mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
  set Y := (X₁ ⊔ zpowers t) ⊓ szT₁ L T with hYdef
  have h5 : Nat.card X₁ ≤ Nat.card Y := gmr_card_le_card_sup_inf htt htT₁ htX₁ inf_le_right
  have hYT₁ : Y ≤ szT₁ L T := inf_le_right
  obtain ⟨hYsq, hYcomm⟩ := gmr_sq_comm_mem_of_mem_sup (X₁ := X₁) (Z := Z₀) htt
    (fun y hy => hXt y (mem_inf.mp hy).1) (fun y hy => hXsq y (mem_inf.mp hy).1)
    (fun y hy y' hy' => hXcomm y (mem_inf.mp hy).1 y' (mem_inf.mp hy').1)
  obtain ⟨E, _, _, _, σ, -, hσ, -, u, v, hc, hA⟩ := h.exists_rootCoords_of_card_sylow hS2
  obtain ⟨ψ, hψ⟩ := hc.exists_hom hYT₁
  have hYcard := U3RootCoords.card_eq_mul_card_range hA hYT₁ hψ
  have hYA : Nat.card (Y ⊓ szA₁ (szT₁ L T) : Subgroup G) ≤ 2 ^ f :=
    (card_le_of_le inf_le_right).trans hA₁card.le
  set Zv : Set E := v '' (Z₀ : Set G) with hZvdef
  have hZvcard : Nat.card Zv ≤ Nat.card CA := by
    rw [← hZ₀card]
    exact Finite.card_image_le (s := (Z₀ : Set G)) v
  have hN : ∀ b : Y, Multiplicative.toAdd (ψ b) * σ (Multiplicative.toAdd (ψ b)) ∈ Zv := by
    intro b
    rw [hψ, toAdd_ofAdd, ← (hc.sq (hYT₁ b.2)).2]
    exact Set.mem_image_of_mem v (by rw [sq]; exact hYsq b (mem_inf.mp b.2).1)
  have hTr : ∀ b b' : Y, Multiplicative.toAdd (ψ b) * σ (Multiplicative.toAdd (ψ b')) +
      σ (Multiplicative.toAdd (ψ b)) * Multiplicative.toAdd (ψ b') ∈ Zv := by
    intro b b'
    rw [hψ, hψ, toAdd_ofAdd, toAdd_ofAdd, ← hc.gmr_v_comm (hYT₁ b.2) (hYT₁ b'.2)]
    exact Set.mem_image_of_mem v (hYcomm b (mem_inf.mp b.2).1 b' (mem_inf.mp b'.2).1)
  have hcU : Nat.card CU ≤ 2 * (2 ^ f * Nat.card ψ.range) := by
    calc Nat.card CU = Nat.card X := hXcard.symm
      _ ≤ 2 * Nat.card X₁ := h4
      _ ≤ 2 * Nat.card Y := Nat.mul_le_mul_left _ h5
      _ = 2 * (Nat.card (Y ⊓ szA₁ (szT₁ L T) : Subgroup G) * Nat.card ψ.range) := by
          rw [hYcard]
      _ ≤ 2 * (2 ^ f * Nat.card ψ.range) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hYA)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm1 : m = 1 := by have := h.two_le; omega
    subst hm1
    have hf : f = 2 := by omega
    subst hf
    have hσ4 : ∀ z, σ z = z ^ 4 := fun z => by rw [hσ]; norm_num
    have hcard' : Nat.card CA ≤ 2 := by simpa using hcard
    have hR := gmr_card_range_le_two σ hσ4 ψ Zv (hZvcard.trans hcard') hN
    have h1' : 4 ^ 5 * 4 ≤ (Nat.card CU * Nat.card CA) ^ 2 := by
      rw [show (4 : ℕ) ^ 5 * 4 = (2 ^ 2) ^ 5 * 2 ^ 2 by norm_num]
      exact h1
    have hcU' : Nat.card CU ≤ 2 * (4 * Nat.card ψ.range) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact hcU
    exact gmr_num_four hcard' hR hcU' h1'
  ·
    have hR := (gmr_card_range_le σ ψ Zv hN hTr).trans (Nat.pow_le_pow_left hZvcard 2)
    have hM : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    exact gmr_num_general hQ hM hcard hR hcU h1

end U3C1OuterSwapHigh

theorem u3C1GmcRootInput_holds : U3C1GmcRootInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW _ _ g hg hgS _ _ m hm hcard
  exact hW.gmr_false hg (fun h => hgS (mem_sup_left (hW.level.U₁_le h))) hm hcard

theorem u3C1GmsFusionInput_holds : U3C1GmsFusionInput :=
  u3C1GmsFusionInput_of_root u3C1GmcRootInput_holds

end CFSG.SeitzReduction.RankOne
