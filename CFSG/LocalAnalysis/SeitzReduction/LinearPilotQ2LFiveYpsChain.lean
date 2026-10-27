module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsHeight
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsRow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiChain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem ypsMat_apply01_mul (u v : unitriangular 5 F) :
    ypsMat (u * v) 0 1 = ypsMat u 0 1 + ypsMat v 0 1 :=
  ypsMat_mul_apply_succ u v 0

theorem ypsMat_apply01_inv (u : unitriangular 5 F) : ypsMat u⁻¹ 0 1 = -ypsMat u 0 1 :=
  ypsMat_inv_apply_succ u 0

theorem ypsMat_uFiveRoot_map (σ : F ≃+* F) (i j : Fin 5) (hij : i < j) (a : F) :
    (ypsMat (uFiveRoot i j hij a)).map σ = ypsMat (uFiveRoot i j hij (σ a)) := by
  rw [ypsMat_uFiveRoot, ypsMat_uFiveRoot]
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

section Chain

variable [Finite F] {H : Type*} [Group H] {N : Subgroup H} (Θ : N ≃* unitriangular 5 F)

omit [Finite F] in
theorem uFiveChain_theta_commutator {x y : H} (hx : x ∈ N) (hy : y ∈ N) (hxy : ⁅x, y⁆ ∈ N) :
    Θ ⟨⁅x, y⁆, hxy⟩ = Θ ⟨x, hx⟩ * Θ ⟨y, hy⟩ * (Θ ⟨y, hy⟩ * Θ ⟨x, hx⟩)⁻¹ := by
  have h : (⟨⁅x, y⁆, hxy⟩ : N) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨y, hy⟩ * ⟨x, hx⟩)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [h, map_mul, map_mul, map_inv, map_mul]

theorem seitzChain_four_eq_of_model [hN : N.Normal] (σ : F ≃+* F) {ω : F} (hω : σ ω ≠ ω)
    {t d : H} (hcos : ∀ h : H, h ∈ N ∨ ∃ s ∈ N, h = s * t ∨ h = s * d ∨ h = s * (d * t))
    (hcomm : commutator H ≤ N)
    (ht : ∀ x y : N, (y : H) = t * x * t⁻¹ → ypsMat (Θ y) = (ypsMat (Θ x)).map σ)
    (hd : ∀ x y : N, (y : H) = d * x * d⁻¹ → Θ x ∈ uFiveRow → Θ y ∈ uFiveCol) :
    seitzChain H 4 = N := by
  have hc0 : σ ω - ω ≠ 0 := sub_ne_zero.2 hω
  have hconj : ∀ (g : H) {x : H}, x ∈ N → g * x * g⁻¹ ∈ N := fun g x hx => hN.conj_mem x hx g
  have hcm : ∀ a b : H, ⁅a, b⁆ ∈ commutator H := fun a b =>
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  let e : N → F := fun n => ypsMat (Θ n) 0 1
  have e_mul : ∀ a b : N, e (a * b) = e a + e b := fun a b => by
    simp only [e, map_mul]
    exact ypsMat_apply01_mul _ _
  have e_inv : ∀ a : N, e a⁻¹ = -e a := fun a => by
    simp only [e, map_inv]
    exact ypsMat_apply01_inv _
  have e_t : ∀ x y : N, (y : H) = t * x * t⁻¹ → e y = σ (e x) := fun x y h => by
    simp only [e]
    rw [ht x y h, Matrix.map_apply]
  have e_d : ∀ x y : N, (y : H) = d * x * d⁻¹ → Θ x ∈ uFiveRow → e y = 0 :=
    fun x y h hx => (hd x y h hx).1
  have hroot_t : ∀ (i j : Fin 5) (hij : i < j) (a : F) (y : N),
      (y : H) = t * (Θ.symm (uFiveRoot i j hij a) : H) * t⁻¹ → Θ y = uFiveRoot i j hij (σ a) :=
    fun i j hij a y hy => ypsMat_injective (by
      rw [ht _ y hy, MulEquiv.apply_symm_apply, ypsMat_uFiveRoot_map])
  have hyk : ∀ k : Fin 4, ∃ hy : ⁅((Θ.symm (uFiveRoot k.castSucc k.succ
      (Fin.castSucc_lt_succ (i := k)) ω) : N) : H)⁻¹, t⁆ ∈ N,
      Θ ⟨_, hy⟩ = uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) (σ ω - ω) := by
    intro k
    set a : N := Θ.symm (uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) ω)
    have hta := hconj t a.2
    have heq : (⟨⁅(a : H)⁻¹, t⁆, hcomm (hcm _ _)⟩ : N) = a⁻¹ * ⟨_, hta⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
      group
    refine ⟨hcomm (hcm _ _), ?_⟩
    rw [heq, map_mul, map_inv, hroot_t _ _ _ ω ⟨_, hta⟩ rfl, MulEquiv.apply_symm_apply,
      uFiveRoot_inv, uFiveRoot_mul, neg_add_eq_sub]
  have hy' : ∃ hy : ⁅((Θ.symm (uFiveRoot 0 1 (by decide) ω) : N) : H), d⁆ ∈ N,
      e ⟨_, hy⟩ = ω := by
    set b : N := Θ.symm (uFiveRoot 0 1 (by decide) ω)
    have hdb := hconj d (b⁻¹).2
    have heq : (⟨⁅(b : H), d⁆, hcomm (hcm _ _)⟩ : N) = b * ⟨_, hdb⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    refine ⟨hcomm (hcm _ _), ?_⟩
    rw [heq, e_mul, e_d b⁻¹ ⟨_, hdb⟩ rfl (by
      rw [map_inv, MulEquiv.apply_symm_apply]
      exact uFiveRow.inv_mem (uFiveRoot_mem_uFiveRow (by decide) ω)), add_zero]
    simp only [e, b, MulEquiv.apply_symm_apply, ypsMat_uFiveRoot]
    simp
  have claim : ∀ k : ℕ, k ≤ 4 → ∀ h : H,
      h ∈ seitzChain H k ↔ ∃ hh : h ∈ N, Θ ⟨h, hh⟩ ∈ uFiveHeight (5 - k) := by
    intro k
    induction k with
    | zero =>
      intro _ h
      rw [seitzChain_zero, Subgroup.mem_bot, Nat.sub_zero, uFiveHeight_five]
      constructor
      · rintro rfl
        exact ⟨one_mem _, by rw [Subgroup.mem_bot]; exact (map_eq_one_iff Θ Θ.injective).2 rfl⟩
      · rintro ⟨hh, h1⟩
        rw [Subgroup.mem_bot, map_eq_one_iff Θ Θ.injective] at h1
        exact congrArg Subtype.val h1
    | succ k ih =>
      intro hk h
      have ih' := ih (by omega)
      have hz01 : ∀ z : H, z ∈ seitzChain H k → ∃ hz : z ∈ N, e ⟨z, hz⟩ = 0 := by
        intro z hz
        obtain ⟨hzN, hθ⟩ := (ih' z).1 hz
        exact ⟨hzN, hθ 0 1 (by decide) (by
          change 1 < 0 + (5 - k)
          omega)⟩
      rw [mem_seitzChain_succ]
      constructor
      · intro hall
        have hhN : h ∈ N := by
          rcases hcos h with hN' | ⟨s, hs, hst | hsd | hsdt⟩
          · exact hN'
          · exfalso
            obtain ⟨hyN, hye⟩ := hy'
            set y := ⁅((Θ.symm (uFiveRoot 0 1 (by decide) ω) : N) : H), d⁆
            obtain ⟨hz, hze⟩ := hz01 _ (hall y (hcm _ _))
            have hty := hconj t hyN
            have heq : (⟨⁅h, y⁆, hz⟩ : N) = ⟨s, hs⟩ * ⟨_, hty⟩ * ⟨s, hs⟩⁻¹ * ⟨y, hyN⟩⁻¹ := by
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, hst]
              group
            rw [heq, e_mul, e_mul, e_mul, e_inv, e_inv, e_t ⟨y, hyN⟩ ⟨_, hty⟩ rfl, hye] at hze
            exact hc0 (by linear_combination hze)
          · exfalso
            obtain ⟨hyN, hye⟩ := hyk 0
            obtain ⟨hz, hze⟩ := hz01 _ (hall ⁅((Θ.symm (uFiveRoot (Fin.castSucc (0 : Fin 4))
              (Fin.succ 0) (Fin.castSucc_lt_succ (i := 0)) ω) : N) : H)⁻¹, t⁆ (hcm _ _))
            have hdy := hconj d hyN
            have heq : (⟨_, hz⟩ : N) = ⟨s, hs⟩ * ⟨_, hdy⟩ * ⟨s, hs⟩⁻¹ * ⟨_, hyN⟩⁻¹ := by
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, hsd]
              group
            rw [heq, e_mul, e_mul, e_mul, e_inv, e_inv, e_d _ ⟨_, hdy⟩ rfl (by
              rw [hye]
              exact uFiveRoot_mem_uFiveRow (by decide) _)] at hze
            have h1 : e ⟨_, hyN⟩ = σ ω - ω := by
              simp only [e, hye, ypsMat_uFiveRoot]
              simp
            rw [h1] at hze
            exact hc0 (by linear_combination -hze)
          · exfalso
            obtain ⟨hyN, hye⟩ := hyk 0
            obtain ⟨hz, hze⟩ := hz01 _ (hall ⁅((Θ.symm (uFiveRoot (Fin.castSucc (0 : Fin 4))
              (Fin.succ 0) (Fin.castSucc_lt_succ (i := 0)) ω) : N) : H)⁻¹, t⁆ (hcm _ _))
            have hty := hconj t hyN
            have hdty := hconj d hty
            have heq : (⟨_, hz⟩ : N) = ⟨s, hs⟩ * ⟨_, hdty⟩ * ⟨s, hs⟩⁻¹ * ⟨_, hyN⟩⁻¹ := by
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, hsdt]
              group
            have hty' : Θ ⟨_, hty⟩ ∈ uFiveRow := by
              have h2 : Θ ⟨_, hty⟩ = uFiveRoot 0 1 (by decide) (σ (σ ω - ω)) :=
                ypsMat_injective (by rw [ht ⟨_, hyN⟩ ⟨_, hty⟩ rfl, hye, ypsMat_uFiveRoot_map]; rfl)
              rw [h2]
              exact uFiveRoot_mem_uFiveRow (by decide) _
            rw [heq, e_mul, e_mul, e_mul, e_inv, e_inv, e_d _ ⟨_, hdty⟩ rfl hty'] at hze
            have h1 : e ⟨_, hyN⟩ = σ ω - ω := by
              simp only [e, hye, ypsMat_uFiveRoot]
              simp
            rw [h1] at hze
            exact hc0 (by linear_combination -hze)
        refine ⟨hhN, ?_⟩
        have hstep := mem_uFiveHeight_of_agreeBelowFive (m := 5 - k) (by omega) hc0
          (u := Θ ⟨h, hhN⟩) (fun j => by
            obtain ⟨hyN, hye⟩ := hyk j
            obtain ⟨hz, hθ⟩ := (ih' _).1 (hall _ (hcm _ _))
            rw [uFiveChain_theta_commutator Θ hhN hyN hz, mul_inv_mem_uFiveHeight_iff, hye] at hθ
            exact hθ)
        rwa [Nat.sub_sub] at hstep
      · rintro ⟨hh, hθ⟩ y hy
        have hyN := hcomm hy
        have hz : ⁅h, y⁆ ∈ N := by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hh hyN) (inv_mem hh)) (inv_mem hyN)
        refine (ih' _).2 ⟨hz, ?_⟩
        rw [uFiveChain_theta_commutator Θ hh hyN hz, mul_inv_mem_uFiveHeight_iff]
        exact agreeBelowFive_mul_of_mem (by rwa [Nat.sub_sub]) _
  ext h
  rw [claim 4 le_rfl h]
  constructor
  · rintro ⟨hh, -⟩
    exact hh
  · intro hh
    refine ⟨hh, ?_⟩
    rw [show 5 - 4 = 1 from rfl, uFiveHeight_one]
    exact Subgroup.mem_top _

end Chain

end CFSG.SeitzReduction.LinearPilot
