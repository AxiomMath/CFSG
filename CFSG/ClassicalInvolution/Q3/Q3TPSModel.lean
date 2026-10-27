module

public import CFSG.ClassicalInvolution.Q3.Q3TPSMatCore
public import CFSG.ClassicalInvolution.Q3.Q3ZLiftCover
public import CFSG.ClassicalInvolution.Q3.Q3ZModel
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.LocalPair
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ClassicalInvolution.RouteD (le_of_perfect_of_le_sup_center ker_proj_eq_center)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ClassicalInvolution.Q3.Q3Z (isPerfect_sp4_three orderOf_not_dvd_three_of_center_sp)

local notation "F₃" => GaloisField 3 1

theorem ringChar_galoisField_three_ne_two : ringChar (GaloisField 3 1) ≠ 2 := by
  rw [ringChar.eq (GaloisField 3 1) 3]
  norm_num

theorem exists_semilinear_lift3 {X : Type} [Group X]
    (ψ : StatedSp 2 (GaloisField 3 1) →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1)))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (hstab : ∀ x, τ (ψ x) ∈ ψ.range) :
    ∃ (A : gsp 2 (GaloisField 3 1)) (σ : GaloisField 3 1 ≃+* GaloisField 3 1),
      ∀ x : StatedSp 2 (GaloisField 3 1),
        τ (ψ x) = ψ (conjSp 2 (GaloisField 3 1) A (fieldSp 2 (GaloisField 3 1) σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 2 (GaloisField 3 1)) := isPerfect_sp4_three
  have hmem : ∀ y : X, y ∈ ψ.range → τ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  let τC : ψ.range ≃* ψ.range :=
    { toFun := fun y => ⟨τ y, hmem y y.2⟩
      invFun := fun y => ⟨τ y, hmem y y.2⟩
      left_inv := fun y => Subtype.ext (hτ y)
      right_inv := fun y => Subtype.ext (hτ y)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : X) (b : X)) }
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 2 (GaloisField 3 1))
    (proj_surjective) (ker_proj_eq_center 2) (θ := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) τC
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 2)
    ringChar_galoisField_three_ne_two le_rfl
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 2 (GaloisField 3 1) →* StatedSp 2 (GaloisField 3 1) :=
    (conjSp 2 (GaloisField 3 1) A).toMonoidHom.comp (fieldSp 2 (GaloisField 3 1) σ).toMonoidHom
  have hα : ∀ x, proj 2 (GaloisField 3 1) (α x) = β (proj 2 (GaloisField 3 1) x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have := congrArg Subtype.val (hβ α hα x)
  exact this.symm

theorem three_eq_zero_galoisField_three : (3 : F₃) = 0 := by
  have := CharP.cast_eq_zero F₃ 3
  simpa using this

theorem sl2Upper_pow_three (c : F₃) : (sl2Upper c) ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  have key : c + c + c = 0 := by
    rw [show c + c + c = 3 * c by ring, three_eq_zero_galoisField_three, zero_mul]
  have key' : c + (c + c) = 0 := by rw [← add_assoc]; exact key
  fin_cases i <;> fin_cases j
  all_goals simp [pow_succ, CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.mul_apply,
    Fin.sum_univ_two, mul_comm]
  all_goals first | exact key | exact key'

theorem sl2Lower_pow_three (c : F₃) : (sl2Lower c) ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  have key : c + c + c = 0 := by
    rw [show c + c + c = 3 * c by ring, three_eq_zero_galoisField_three, zero_mul]
  fin_cases i <;> fin_cases j
  all_goals simp [pow_succ, CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two, mul_comm]
  all_goals exact key

theorem eq_top_of_normal_of_not_le_center3 {N : Subgroup (StatedSp 2 F₃)} [N.Normal]
    (hN : ¬ N ≤ Subgroup.center (StatedSp 2 F₃)) : N = ⊤ := by
  classical
  have hF : Nat.card F₃ = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F₃ (by norm_num)
    (Or.inr (Or.inl ⟨hF, le_rfl⟩))
  have hperf : Group.IsPerfect (StatedSp 2 F₃) := hq.1
  have hsimple : IsSimpleGroup (StatedSp 2 F₃ ⧸ Subgroup.center (StatedSp 2 F₃)) := hq.2.1
  set Z : Subgroup (StatedSp 2 F₃) := Subgroup.center (StatedSp 2 F₃) with hZ
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hN
    intro n hn
    have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · have hsup : (⊤ : Subgroup (StatedSp 2 F₃)) ≤ N ⊔ Z := by
      intro g _
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hmem : n⁻¹ * g ∈ Z := QuotientGroup.eq.mp hng
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hmem)
    have htop : (⊤ : Subgroup (StatedSp 2 F₃)) ≤ ⁅(⊤ : Subgroup (StatedSp 2 F₃)), ⊤⁆ :=
      (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (StatedSp 2 F₃)))).ge
    exact eq_top_iff.2 (le_of_perfect_of_le_sup_center le_rfl htop hsup)

theorem exists_fixed_shortRoot3 {X : Type} [Group X]
    (ψ : StatedSp 2 F₃ →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F₃))
    (hnorm : ψ.range.Normal) (τ : X ≃* X)
    (hτ : ∀ x, τ (τ x) = x) (θ : SL(2, F₃) →* X)
    (hθ : θ.range = (longBlock F₃ 2 1).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (h01 : (0 : Fin 2) ≠ 1) :
    ∃ g : StatedSp 2 F₃, (longBlock F₃ 2 1).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F₃ 2 1).range ∧
      ∀ x ∈ (shortBlock F₃ h01).range.map (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x := by
  classical
  have h2 : (2 : F₃) ≠ 0 := Ring.two_ne_zero ringChar_galoisField_three_ne_two
  have hPsp : Group.IsPerfect (StatedSp 2 F₃) := isPerfect_sp4_three
  set θ₂ : SL(2, F₃) →* X := ψ.comp (longBlock F₃ 2 1) with hθ₂
  have hθ₂inj : Function.Injective θ₂ := by
    intro s t hst
    apply longBlock_injective (1 : Fin 2)
    have h1 : ψ ((longBlock F₃ 2 1 t)⁻¹ * longBlock F₃ 2 1 s) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hst.symm
    have h2' : (longBlock F₃ 2 1 t)⁻¹ * longBlock F₃ 2 1 s ∈ suppGroup (coords (1 : Fin 2)) := by
      rw [← range_longBlock]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨t, rfl⟩) ⟨s, rfl⟩
    have h3 := injOn_suppGroup_of_ker_le_center ψ hker (S := coords (1 : Fin 2))
      (t := Sum.inl (0 : Fin 2)) (by simp [mem_coords]) _ h2' h1
    exact (inv_mul_eq_one.1 h3).symm
  have hθ₂range : θ₂.range = θ.range := by
    rw [hθ, hθ₂, MonoidHom.range_comp]
  have hstab : ∀ x, τ (ψ x) ∈ ψ.range := by
    set N : Subgroup (StatedSp 2 F₃) := ψ.range.comap (τ.toMonoidHom.comp ψ) with hNdef
    have hNn : N.Normal := ⟨fun n hn g => by
      have hn' : τ (ψ n) ∈ ψ.range := hn
      show τ (ψ (g * n * g⁻¹)) ∈ ψ.range
      simp only [map_mul, map_inv]
      exact hnorm.conj_mem _ hn' _⟩
    have hy₀ : longBlock F₃ 2 1 (sl2Upper 1) ∈ N := by
      show τ (ψ (longBlock F₃ 2 1 (sl2Upper 1))) ∈ ψ.range
      have : θ₂ (sl2Upper 1) ∈ θ.range := hθ₂range ▸ ⟨_, rfl⟩
      obtain ⟨s₁, hs₁⟩ := this
      show τ (θ₂ (sl2Upper 1)) ∈ ψ.range
      rw [← hs₁, hθτ]
      have : θ (diagConj2 (-1) 1 s₁) ∈ (longBlock F₃ 2 1).range.map ψ := hθ ▸ ⟨_, rfl⟩
      obtain ⟨y, -, hy⟩ := this
      exact ⟨y, hy⟩
    have hN : ¬ N ≤ Subgroup.center (StatedSp 2 F₃) := fun hle => by
      have hc := hle hy₀
      have hs : longBlock F₃ 2 1 (sl2Upper 1) ∈ suppGroup (coords (1 : Fin 2)) := by
        rw [← range_longBlock]
        exact ⟨_, rfl⟩
      have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl (0 : Fin 2))
        (by simp [mem_coords])
      have h2' := longBlock_injective (K := F₃) (n := 2) (1 : Fin 2) (h1.trans (map_one _).symm)
      have := congrArg (fun s : SL(2, F₃) => (s : Matrix (Fin 2) (Fin 2) F₃) 0 1) h2'
      simp [CFSG.LieType.Steinberg.coe_sl2Upper] at this
    have hNtop := eq_top_of_normal_of_not_le_center3 hN
    intro x
    have : x ∈ N := by rw [hNtop]; trivial
    exact this
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift3 ψ hker τ hτ hstab
  set ρ : StatedSp 2 F₃ ≃* StatedSp 2 F₃ := (fieldSp 2 F₃ σ).trans (conjSp 2 F₃ A) with hρdef
  have hρψ : ∀ x, ψ (ρ x) = τ (ψ x) := fun x => (hAσ x).symm
  have hex : ∀ s : SL(2, F₃), ∃ s' : SL(2, F₃), θ₂ s' = θ s := fun s => by
    have : θ s ∈ θ₂.range := hθ₂range ▸ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  choose γf hγf using hex
  let γ0 : SL(2, F₃) →* SL(2, F₃) :=
    { toFun := γf
      map_one' := hθ₂inj (by rw [hγf, map_one, map_one])
      map_mul' := fun s t => hθ₂inj (by rw [hγf, map_mul, map_mul, hγf, hγf]) }
  have hγsurj : Function.Surjective γ0 := fun t => by
    have : θ₂ t ∈ θ.range := hθ₂range ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hθ₂inj (by show θ₂ (γf s) = θ₂ t; rw [hγf]; exact hs)⟩
  let γ : SL(2, F₃) ≃* SL(2, F₃) :=
    MulEquiv.ofBijective γ0 ⟨Finite.injective_iff_surjective.2 hγsurj, hγsurj⟩
  have hγθ : ∀ s, θ₂ (γ s) = θ s := fun s => hγf s
  have hρL : ∀ s : SL(2, F₃), ρ (longBlock F₃ 2 1 s) ∈ (longBlock F₃ 2 1).range := by
    have hsup : (ρ.toMonoidHom.comp (longBlock F₃ 2 1)).range ≤
        (longBlock F₃ 2 1).range ⊔ ψ.ker := by
      rintro _ ⟨s, rfl⟩
      have h1 : τ (θ₂ s) ∈ θ₂.range := by
        have : θ₂ s ∈ θ.range := hθ₂range ▸ ⟨s, rfl⟩
        obtain ⟨s₁, hs₁⟩ := this
        rw [← hs₁, hθτ]
        exact hθ₂range ▸ ⟨_, rfl⟩
      obtain ⟨s', hs'⟩ := h1
      have hz : (longBlock F₃ 2 1 s')⁻¹ * ρ (longBlock F₃ 2 1 s) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρψ]
        show (θ₂ s')⁻¹ * τ (θ₂ s) = 1
        rw [hs', inv_mul_cancel]
      have : ρ (longBlock F₃ 2 1 s) =
          longBlock F₃ 2 1 s' * ((longBlock F₃ 2 1 s')⁻¹ * ρ (longBlock F₃ 2 1 s)) := by group
      show ρ (longBlock F₃ 2 1 s) ∈ _
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s', rfl⟩) (Subgroup.mem_sup_right hz)
    have hord : ∀ s : SL(2, F₃), s ^ 3 = 1 → ρ (longBlock F₃ 2 1 s) ∈ (longBlock F₃ 2 1).range := by
      intro s hs3
      have hmem : ρ (longBlock F₃ 2 1 s) ∈ (longBlock F₃ 2 1).range ⊔ ψ.ker := hsup ⟨s, rfl⟩
      obtain ⟨b, hb, w, hw, hbw⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hwc : w ∈ Subgroup.center (StatedSp 2 F₃) := hker hw
      have h3 : ρ (longBlock F₃ 2 1 s) ^ 3 = 1 := by
        rw [← map_pow, ← map_pow, hs3, map_one, map_one]
      have hcomm : Commute b w := Subgroup.mem_center_iff.mp hwc b
      have hpow : b ^ 3 * w ^ 3 = 1 := by
        rw [← hcomm.mul_pow, hbw]
        exact h3
      have hw3 : w ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hpow
      have hw3B : w ^ 3 ∈ (longBlock F₃ 2 1).range := by
        rw [hw3]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 3)
      have hw3c : w ^ 3 ∈ Subgroup.center (StatedSp 2 F₃) := Subgroup.pow_mem _ hwc 3
      have hw3one : w ^ 3 = 1 := by
        refine eq_one_of_mem_center_of_mem_suppGroup hw3c ?_ (S := coords (1 : Fin 2))
          (t := Sum.inl (0 : Fin 2)) (by simp [mem_coords])
        rw [← range_longBlock]
        exact hw3B
      have hw1 : w = 1 := by
        have hdvd : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3one
        have hnd := orderOf_not_dvd_three_of_center_sp (by norm_num : 1 ≤ 2) hwc
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact orderOf_eq_one_iff.mp h
        · exact absurd ⟨1, by omega⟩ hnd
      rw [← hbw, hw1, mul_one]
      exact hb
    intro s
    have hs : s ∈ Subgroup.closure (Set.range (sl2Upper (k := F₃)) ∪ Set.range sl2Lower) :=
      CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s
    refine Subgroup.closure_induction (p := fun s _ => ρ (longBlock F₃ 2 1 s) ∈
      (longBlock F₃ 2 1).range) ?_ ?_ ?_ ?_ hs
    · rintro s (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hord _ (sl2Upper_pow_three c)
      · exact hord _ (sl2Lower_pow_three c)
    · rw [map_one, map_one]
      exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      rw [map_mul, map_mul]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv, map_inv]
      exact Subgroup.inv_mem _ ha
  have hγ' : ∀ s : SL(2, F₃),
      ρ (longBlock F₃ 2 1 (γ s)) = longBlock F₃ 2 1 (γ (diagConj2 (-1) 1 s)) := by
    intro s
    obtain ⟨s'', hs''⟩ := hρL (γ s)
    have hs : s'' = γ (diagConj2 (-1) 1 s) := by
      apply hθ₂inj
      calc θ₂ s'' = ψ (longBlock F₃ 2 1 s'') := rfl
        _ = ψ (ρ (longBlock F₃ 2 1 (γ s))) := by rw [hs'']
        _ = τ (ψ (longBlock F₃ 2 1 (γ s))) := hρψ _
        _ = τ (θ s) := by rw [← hγθ]; rfl
        _ = θ (diagConj2 (-1) 1 s) := hθτ s
        _ = θ₂ (γ (diagConj2 (-1) 1 s)) := (hγθ _).symm
    rw [← hs'', hs]
  have hρρ : ∀ x : StatedSp 2 F₃, ρ (ρ x) = x := by
    let ρ2 : StatedSp 2 F₃ →* StatedSp 2 F₃ := ρ.toMonoidHom.comp ρ.toMonoidHom
    have key := RouteD.Gaps.fixed_of_perfect_of_central ρ2 (N := ⊤) inferInstance (Z := ψ.ker) hker
      (fun n _ => by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        show (ψ n)⁻¹ * ψ (ρ (ρ n)) = 1
        rw [hρψ, hρψ, hτ, inv_mul_cancel])
    exact fun x => key x trivial
  set Am : Mat4 F₃ := ((A : GL (Fin 2 ⊕ Fin 2) F₃) : Mat4 F₃) with hAm
  set Bm : Mat4 F₃ := (((A : GL (Fin 2 ⊕ Fin 2) F₃)⁻¹ : GL (Fin 2 ⊕ Fin 2) F₃) : Mat4 F₃) with hBm
  have hAB : Am * Bm = 1 := by
    rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hm : ((multiplier 2 F₃ A : F₃ˣ) : F₃) ≠ 0 := Units.ne_zero _
  have hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = ((multiplier 2 F₃ A : F₃ˣ) : F₃) * form u v :=
    form_mulVec_of_sim (multiplier_spec A)
  have hγm : ∀ s : SL(2, F₃), Am * blockMat (Sum.inl 1) (Sum.inr 1)
      (((γ s : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃).map σ) * Bm =
      blockMat (Sum.inl 1) (Sum.inr 1)
        ((γ (diagConj2 (-1) 1 s) : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃) := by
    intro s
    have h := congrArg (mat 2 F₃) (hγ' s)
    have e : mat 2 F₃ (ρ (longBlock F₃ 2 1 (γ s))) =
        Am * (mat 2 F₃ (longBlock F₃ 2 1 (γ s))).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, mat_longBlock, mat_longBlock, map_blockMat] at h
    exact h
  have hρm : ∀ x : StatedSp 2 F₃, Am * (Am * (mat 2 F₃ x).map σ * Bm).map σ * Bm = mat 2 F₃ x := by
    intro x
    have h := congrArg (mat 2 F₃) (hρρ x)
    have e1 : mat 2 F₃ (ρ (ρ x)) = Am * (mat 2 F₃ (ρ x)).map σ * Bm := mat_conjSp_fieldSp A σ (ρ x)
    have e2 : mat 2 F₃ (ρ x) = Am * (mat 2 F₃ x).map σ * Bm := mat_conjSp_fieldSp A σ x
    rw [e1, e2] at h
    exact h
  obtain ⟨hσ, g, hg1, hg2⟩ := core_mat h2 hAB hBA σ hm hsim γ hγm hρm h01
  refine ⟨g, hg1, ?_⟩
  rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
  have hmapid : ∀ M : Mat4 F₃, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hfix : ρ (g * shortBlock F₃ h01 s * g⁻¹) = g * shortBlock F₃ h01 s * g⁻¹ := by
    apply mat_injective
    have e : mat 2 F₃ (ρ (g * shortBlock F₃ h01 s * g⁻¹)) =
        Am * (mat 2 F₃ (g * shortBlock F₃ h01 s * g⁻¹)).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, hmapid, hg2 s, Matrix.mul_assoc, hAB, Matrix.mul_one]
  show τ (ψ (g * shortBlock F₃ h01 s * g⁻¹)) = ψ (g * shortBlock F₃ h01 s * g⁻¹)
  rw [← hρψ, hfix]

end CFSG.ClassicalInvolution.Q3.Q3TPS
