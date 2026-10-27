module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SDefs
public import CFSG.ClassicalInvolution.Q3.Q3TPSModel
public import CFSG.ClassicalInvolution.Q3.Q3VLiftCover
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternModel
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

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
open CFSG.ClassicalInvolution.RouteD.SpAdapt
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ClassicalInvolution.Q3.Q3Z (orderOf_not_dvd_three_of_center_sp)
open CFSG.ClassicalInvolution.Q3.Q3TPS (ringChar_galoisField_three_ne_two sl2Upper_pow_three
  sl2Lower_pow_three)

local notation "F₃" => GaloisField 3 1

theorem exists_semilinear_lift_sp6 {X : Type} [Group X] (ψ : StatedSp 3 F₃ →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F₃)) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    (hstab : ∀ x, τ (ψ x) ∈ ψ.range) :
    ∃ (A : gsp 3 F₃) (σ : F₃ ≃+* F₃), ∀ x : StatedSp 3 F₃,
      τ (ψ x) = ψ (conjSp 3 F₃ A (fieldSp 3 F₃ σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 3 F₃) := Q3V.Lift.isPerfect_sp_three (by norm_num)
  have hmem : ∀ y : X, y ∈ ψ.range → τ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  let τC : ψ.range ≃* ψ.range :=
    { toFun := fun y => ⟨τ y, hmem y y.2⟩
      invFun := fun y => ⟨τ y, hmem y y.2⟩
      left_inv := fun y => Subtype.ext (hτ y)
      right_inv := fun y => Subtype.ext (hτ y)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : X) (b : X)) }
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 3 F₃) (proj_surjective)
    (ker_proj_eq_center 3) (θ := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) τC
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 3)
    ringChar_galoisField_three_ne_two (by norm_num)
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 3 F₃ →* StatedSp 3 F₃ :=
    (conjSp 3 F₃ A).toMonoidHom.comp (fieldSp 3 F₃ σ).toMonoidHom
  have hα : ∀ x, proj 3 F₃ (α x) = β (proj 3 F₃ x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have := congrArg Subtype.val (hβ α hα x)
  exact this.symm

theorem eq_top_of_normal_of_not_le_center_sp6 {N : Subgroup (StatedSp 3 F₃)} [N.Normal]
    (hN : ¬ N ≤ Subgroup.center (StatedSp 3 F₃)) : N = ⊤ := by
  classical
  have hF : Nat.card F₃ = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 3 F₃ (by norm_num)
    (Or.inr (Or.inl ⟨hF, by norm_num⟩))
  have hperf : Group.IsPerfect (StatedSp 3 F₃) := hq.1
  have hsimple : IsSimpleGroup (StatedSp 3 F₃ ⧸ Subgroup.center (StatedSp 3 F₃)) := hq.2.1
  set Z : Subgroup (StatedSp 3 F₃) := Subgroup.center (StatedSp 3 F₃) with hZ
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hN
    intro n hn
    have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · have hsup : (⊤ : Subgroup (StatedSp 3 F₃)) ≤ N ⊔ Z := by
      intro g _
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hmem : n⁻¹ * g ∈ Z := QuotientGroup.eq.mp hng
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hmem)
    have htop : (⊤ : Subgroup (StatedSp 3 F₃)) ≤ ⁅(⊤ : Subgroup (StatedSp 3 F₃)), ⊤⁆ :=
      (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (StatedSp 3 F₃)))).ge
    exact eq_top_iff.2 (le_of_perfect_of_le_sup_center le_rfl htop hsup)

theorem stab_of_normal_sp6 {X : Type} [Group X] (ψ : StatedSp 3 F₃ →* X) (hnorm : ψ.range.Normal)
    (τ : X ≃* X) (θ : SL(2, F₃) →* X) (hθ : θ.range = (longBlock F₃ 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) : ∀ x, τ (ψ x) ∈ ψ.range := by
  classical
  have hθ₂range : (ψ.comp (longBlock F₃ 3 2)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp]
  set N : Subgroup (StatedSp 3 F₃) := ψ.range.comap (τ.toMonoidHom.comp ψ) with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : τ (ψ n) ∈ ψ.range := hn
    show τ (ψ (g * n * g⁻¹)) ∈ ψ.range
    simp only [map_mul, map_inv]
    exact hnorm.conj_mem _ hn' _⟩
  have hy₀ : longBlock F₃ 3 2 (sl2Upper 1) ∈ N := by
    show τ (ψ (longBlock F₃ 3 2 (sl2Upper 1))) ∈ ψ.range
    have : (ψ.comp (longBlock F₃ 3 2)) (sl2Upper 1) ∈ θ.range := hθ₂range ▸ ⟨_, rfl⟩
    obtain ⟨s₁, hs₁⟩ := this
    show τ ((ψ.comp (longBlock F₃ 3 2)) (sl2Upper 1)) ∈ ψ.range
    rw [← hs₁, hθτ]
    have : θ (diagConj2 (-1) 1 s₁) ∈ (longBlock F₃ 3 2).range.map ψ := hθ ▸ ⟨_, rfl⟩
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  have hN : ¬ N ≤ Subgroup.center (StatedSp 3 F₃) := fun hle => by
    have hc := hle hy₀
    have hs : longBlock F₃ 3 2 (sl2Upper 1) ∈ suppGroup (coords (2 : Fin 3)) := by
      rw [← range_longBlock]
      exact ⟨_, rfl⟩
    have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl (0 : Fin 3))
      (by simp [mem_coords])
    have h2' := longBlock_injective (K := F₃) (n := 3) (2 : Fin 3) (h1.trans (map_one _).symm)
    have := congrArg (fun s : SL(2, F₃) => (s : Matrix (Fin 2) (Fin 2) F₃) 0 1) h2'
    simp [CFSG.LieType.Steinberg.coe_sl2Upper] at this
  have hNtop := eq_top_of_normal_of_not_le_center_sp6 hN
  intro x
  have : x ∈ N := by rw [hNtop]; trivial
  exact this

theorem rho_mem_longBlock_sp6 {X : Type} [Group X] (ψ : StatedSp 3 F₃ →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F₃)) (τ : X ≃* X) (θ : SL(2, F₃) →* X)
    (hθ : θ.range = (longBlock F₃ 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (ρ : StatedSp 3 F₃ ≃* StatedSp 3 F₃)
    (hρψ : ∀ x, ψ (ρ x) = τ (ψ x)) :
    ∀ s : SL(2, F₃), ρ (longBlock F₃ 3 2 s) ∈ (longBlock F₃ 3 2).range := by
  classical
  have hθ₂range : (ψ.comp (longBlock F₃ 3 2)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp]
  have hsup : (ρ.toMonoidHom.comp (longBlock F₃ 3 2)).range ≤
      (longBlock F₃ 3 2).range ⊔ ψ.ker := by
    rintro _ ⟨s, rfl⟩
    have h1 : τ ((ψ.comp (longBlock F₃ 3 2)) s) ∈ (ψ.comp (longBlock F₃ 3 2)).range := by
      have : (ψ.comp (longBlock F₃ 3 2)) s ∈ θ.range := hθ₂range ▸ ⟨s, rfl⟩
      obtain ⟨s₁, hs₁⟩ := this
      rw [← hs₁, hθτ]
      exact hθ₂range ▸ ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ := h1
    have hz : (longBlock F₃ 3 2 s')⁻¹ * ρ (longBlock F₃ 3 2 s) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρψ]
      show (ψ (longBlock F₃ 3 2 s'))⁻¹ * τ (ψ (longBlock F₃ 3 2 s)) = 1
      have hs'' : ψ (longBlock F₃ 3 2 s') = τ (ψ (longBlock F₃ 3 2 s)) := hs'
      rw [hs'', inv_mul_cancel]
    have : ρ (longBlock F₃ 3 2 s) =
        longBlock F₃ 3 2 s' * ((longBlock F₃ 3 2 s')⁻¹ * ρ (longBlock F₃ 3 2 s)) := by group
    show ρ (longBlock F₃ 3 2 s) ∈ _
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s', rfl⟩) (Subgroup.mem_sup_right hz)
  have hord : ∀ s : SL(2, F₃), s ^ 3 = 1 →
      ρ (longBlock F₃ 3 2 s) ∈ (longBlock F₃ 3 2).range := by
    intro s hs3
    have hmem : ρ (longBlock F₃ 3 2 s) ∈ (longBlock F₃ 3 2).range ⊔ ψ.ker := hsup ⟨s, rfl⟩
    obtain ⟨b, hb, w, hw, hbw⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hwc : w ∈ Subgroup.center (StatedSp 3 F₃) := hker hw
    have h3 : ρ (longBlock F₃ 3 2 s) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hs3, map_one, map_one]
    have hcomm : Commute b w := Subgroup.mem_center_iff.mp hwc b
    have hpow : b ^ 3 * w ^ 3 = 1 := by
      rw [← hcomm.mul_pow, hbw]
      exact h3
    have hw3 : w ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    have hw3B : w ^ 3 ∈ (longBlock F₃ 3 2).range := by
      rw [hw3]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 3)
    have hw3c : w ^ 3 ∈ Subgroup.center (StatedSp 3 F₃) := Subgroup.pow_mem _ hwc 3
    have hw3one : w ^ 3 = 1 := by
      refine eq_one_of_mem_center_of_mem_suppGroup hw3c ?_ (S := coords (2 : Fin 3))
        (t := Sum.inl (0 : Fin 3)) (by simp [mem_coords])
      rw [← range_longBlock]
      exact hw3B
    have hw1 : w = 1 := by
      have hdvd : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3one
      have hnd := orderOf_not_dvd_three_of_center_sp (by norm_num : 1 ≤ 3) hwc
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd ⟨1, by omega⟩ hnd
    rw [← hbw, hw1, mul_one]
    exact hb
  intro s
  have hs : s ∈ Subgroup.closure (Set.range (sl2Upper (k := F₃)) ∪ Set.range sl2Lower) :=
    CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s
  refine Subgroup.closure_induction (p := fun s _ => ρ (longBlock F₃ 3 2 s) ∈
    (longBlock F₃ 3 2).range) ?_ ?_ ?_ ?_ hs
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

theorem rho_chart_sp6 {X : Type} [Group X] (ψ : StatedSp 3 F₃ →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F₃)) (τ : X ≃* X) (θ : SL(2, F₃) →* X)
    (hθ : θ.range = (longBlock F₃ 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (ρ : StatedSp 3 F₃ ≃* StatedSp 3 F₃)
    (hρψ : ∀ x, ψ (ρ x) = τ (ψ x)) (γ : SL(2, F₃) ≃* SL(2, F₃))
    (hγθ : ∀ s, ψ (longBlock F₃ 3 2 (γ s)) = θ s) (s : SL(2, F₃)) :
    ρ (longBlock F₃ 3 2 (γ s)) = longBlock F₃ 3 2 (γ (diagConj2 (-1) 1 s)) := by
  have hθ₂inj := comp_longBlock_injective ψ hker
  obtain ⟨s'', hs''⟩ := rho_mem_longBlock_sp6 ψ hker τ θ hθ hθτ ρ hρψ (γ s)
  have hs : s'' = γ (diagConj2 (-1) 1 s) := by
    apply hθ₂inj
    calc (ψ.comp (longBlock F₃ 3 2)) s'' = ψ (longBlock F₃ 3 2 s'') := rfl
      _ = ψ (ρ (longBlock F₃ 3 2 (γ s))) := by rw [hs'']
      _ = τ (ψ (longBlock F₃ 3 2 (γ s))) := hρψ _
      _ = τ (θ s) := by rw [hγθ]
      _ = θ (diagConj2 (-1) 1 s) := hθτ s
      _ = ψ (longBlock F₃ 3 2 (γ (diagConj2 (-1) 1 s))) := (hγθ _).symm
  rw [← hs'', hs]

theorem f4AdaptFact3 :
    ∀ {X : Type} [Group X] (ψ : StatedSp 3 (GaloisField 3 1) →* X),
      ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) → ψ.range.Normal →
      ∀ τ : X ≃* X, (∀ x, τ (τ x) = x) → ∀ θ : SL(2, GaloisField 3 1) →* X,
        θ.range = (longBlock (GaloisField 3 1) 3 2).range.map ψ →
        (∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) →
        ∃ g : StatedSp 3 (GaloisField 3 1),
          (longBlock (GaloisField 3 1) 3 2).range.map (MulAut.conj g).toMonoidHom =
              (longBlock (GaloisField 3 1) 3 2).range ∧
            (∀ x ∈ (shortBlock (GaloisField 3 1) (by decide : (1 : Fin 3) ≠ 2)).range.map
                (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x) ∧
            ∀ x ∈ (shortBlock (GaloisField 3 1) (by decide : (0 : Fin 3) ≠ 1)).range.map
                (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x := by
  intro X _ ψ hker hnorm τ hτ θ hθ hθτ
  classical
  have h2 : (2 : F₃) ≠ 0 := Ring.two_ne_zero ringChar_galoisField_three_ne_two
  have hPsp : Group.IsPerfect (StatedSp 3 F₃) := Q3V.Lift.isPerfect_sp_three (by norm_num)
  have hstab := stab_of_normal_sp6 ψ hnorm τ θ hθ hθτ
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift_sp6 ψ hker τ hτ hstab
  let ρ : StatedSp 3 F₃ ≃* StatedSp 3 F₃ := (fieldSp 3 F₃ σ).trans (conjSp 3 F₃ A)
  have hρψ : ∀ x, ψ (ρ x) = τ (ψ x) := fun x => (hAσ x).symm
  obtain ⟨γ, hγθ⟩ := exists_gamma ψ hker θ hθ
  have hρL := rho_mem_longBlock_sp6 ψ hker τ θ hθ hθτ ρ hρψ
  have hρρ : ∀ x : StatedSp 3 F₃,
      conjSp 3 F₃ A (fieldSp 3 F₃ σ (conjSp 3 F₃ A (fieldSp 3 F₃ σ x))) = x :=
    rho_rho ψ hker τ hτ hPsp ρ hρψ
  have hD := comm_longInv_of_rho A σ (rho_longInv h2 ρ hρL)
  have hsq := sq_scalar_of_rho A σ hρρ
  set Am : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃ :=
    ((A : GL (Fin 3 ⊕ Fin 3) F₃) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃) with hAm
  set Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃ :=
    (((A : GL (Fin 3 ⊕ Fin 3) F₃)⁻¹ : GL (Fin 3 ⊕ Fin 3) F₃) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃) with hBm
  have hAB : Am * Bm = 1 := by
    rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = ((multiplier 3 F₃ A : F₃ˣ) : F₃) * form u v :=
    form_mulVec_of_sim (multiplier_spec A)
  have hγm : ∀ s : SL(2, F₃), Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
      (((γ s : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃).map σ) * Bm =
      blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
        ((γ (diagConj2 (-1) 1 s) : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃) := by
    intro s
    have h := congrArg (mat 3 F₃)
      (rho_chart_sp6 ψ hker τ θ hθ hθτ ρ hρψ γ hγθ s)
    have e : mat 3 F₃ (ρ (longBlock F₃ 3 2 (γ s))) =
        Am * (mat 3 F₃ (longBlock F₃ 3 2 (γ s))).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, mat_longBlock, mat_longBlock, map_blockMat] at h
    exact h
  obtain ⟨hσ, κ, h, hAV, u₂, w₂, hu₂, hw₂, hAu, hAw, huw⟩ :=
    core_three h2 hAB hBA σ hsim hD hsq γ hγm
  obtain ⟨u, w, hfr, hAu', hAw', hu2, hw2⟩ := exists_frame_three h hAV hu₂ hw₂ hAu hAw huw
  obtain ⟨g, hg1, hg2⟩ := exists_g_of_frame hBA h hfr hAu' hAw' (hu2 ▸ hu₂) (hw2 ▸ hw₂)
  have hmapid : ∀ M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hfix : ∀ (i j : Fin 3) (hij : i ≠ j) (s : SL(2, F₃)),
      τ (ψ (g * shortBlock F₃ hij s * g⁻¹)) = ψ (g * shortBlock F₃ hij s * g⁻¹) := by
    intro i j hij s
    have hρx : ρ (g * shortBlock F₃ hij s * g⁻¹) = g * shortBlock F₃ hij s * g⁻¹ := by
      apply mat_injective
      have e : mat 3 F₃ (ρ (g * shortBlock F₃ hij s * g⁻¹)) =
          Am * (mat 3 F₃ (g * shortBlock F₃ hij s * g⁻¹)).map σ * Bm :=
        mat_conjSp_fieldSp A σ _
      rw [e, hmapid]
      exact hg2 i j hij s
    rw [← hρψ, hρx]
  refine ⟨g, hg1, ?_, ?_⟩
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
