module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.ClassicalInvolution.RouteD.GapsAut
import CFSG.ClassicalInvolution.Q3.Q3TPSMatCore
public import CFSG.ClassicalInvolution.WeakCT.AutExtend

public section

namespace CFSG.ClassicalInvolution.RouteD.SpToral

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open CFSG.ClassicalInvolution.RouteD (exists_semilinear_lift le_of_perfect_of_le_sup_center)

variable {F : Type} [Field F]

open CFSG.ClassicalInvolution.Q3.Q3TPS
  (Mat4 core_mat mat_conjSp_fieldSp form_mulVec_of_sim map_blockMat)

private theorem sl2Upper_one_coe :
    ((sl2Upper (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl


section Group

variable [Finite F]

private theorem range_le_commutator_aux {L H : Type*} [Group L] [Group H] [Group.IsPerfect L]
    (f : L →* H) : f.range ≤ ⁅f.range, f.range⁆ := by
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top
  have h : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  exact h.ge

omit [Finite F] in
private theorem eq_top_of_normal_of_not_le_center (h4 : 4 ≤ Nat.card F)
    {N : Subgroup (StatedSp 2 F)} [N.Normal] (hN : ¬ N ≤ Subgroup.center (StatedSp 2 F)) :
    N = ⊤ := by
  classical
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
    (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedSp 2 F) := hq.1
  have hsimple : IsSimpleGroup (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F)) := hq.2.1
  set Z : Subgroup (StatedSp 2 F) := Subgroup.center (StatedSp 2 F) with hZ
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hN
    intro n hn
    have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · have hsup : (⊤ : Subgroup (StatedSp 2 F)) ≤ N ⊔ Z := by
      intro g _
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hmem : n⁻¹ * g ∈ Z := QuotientGroup.eq.mp hng
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hmem)
    have htop : (⊤ : Subgroup (StatedSp 2 F)) ≤ ⁅(⊤ : Subgroup (StatedSp 2 F)), ⊤⁆ :=
      (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (StatedSp 2 F)))).ge
    exact eq_top_iff.2 (le_of_perfect_of_le_sup_center le_rfl htop hsup)

theorem exists_fixed_shortRoot (hodd : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hnorm : ψ.range.Normal) (τ : X ≃* X)
    (hτ : ∀ x, τ (τ x) = x) (θ : SL(2, F) →* X)
    (hθ : θ.range = (longBlock F 2 1).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (h01 : (0 : Fin 2) ≠ 1) :
    ∃ g : StatedSp 2 F, (longBlock F 2 1).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F 2 1).range ∧
      ∀ x ∈ (shortBlock F h01).range.map (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hPsp : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  set θ₂ : SL(2, F) →* X := ψ.comp (longBlock F 2 1) with hθ₂
  have hθ₂inj : Function.Injective θ₂ := by
    intro s t hst
    apply longBlock_injective (1 : Fin 2)
    have h1 : ψ ((longBlock F 2 1 t)⁻¹ * longBlock F 2 1 s) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hst.symm
    have h2' : (longBlock F 2 1 t)⁻¹ * longBlock F 2 1 s ∈ suppGroup (coords (1 : Fin 2)) := by
      rw [← range_longBlock]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨t, rfl⟩) ⟨s, rfl⟩
    have h3 := injOn_suppGroup_of_ker_le_center ψ hker (S := coords (1 : Fin 2))
      (t := Sum.inl (0 : Fin 2)) (by simp [mem_coords]) _ h2' h1
    exact (inv_mul_eq_one.1 h3).symm
  have hθ₂range : θ₂.range = θ.range := by
    rw [hθ, hθ₂, MonoidHom.range_comp]
  have hstab : ∀ x, τ (ψ x) ∈ ψ.range := by
    set N : Subgroup (StatedSp 2 F) := ψ.range.comap (τ.toMonoidHom.comp ψ) with hNdef
    have hNn : N.Normal := ⟨fun n hn g => by
      have hn' : τ (ψ n) ∈ ψ.range := hn
      show τ (ψ (g * n * g⁻¹)) ∈ ψ.range
      simp only [map_mul, map_inv]
      exact hnorm.conj_mem _ hn' _⟩
    have hy₀ : longBlock F 2 1 (sl2Upper 1) ∈ N := by
      show τ (ψ (longBlock F 2 1 (sl2Upper 1))) ∈ ψ.range
      have : θ₂ (sl2Upper 1) ∈ θ.range := hθ₂range ▸ ⟨_, rfl⟩
      obtain ⟨s₁, hs₁⟩ := this
      show τ (θ₂ (sl2Upper 1)) ∈ ψ.range
      rw [← hs₁, hθτ]
      have : θ (diagConj2 (-1) 1 s₁) ∈ (longBlock F 2 1).range.map ψ := hθ ▸ ⟨_, rfl⟩
      obtain ⟨y, -, hy⟩ := this
      exact ⟨y, hy⟩
    have hN : ¬ N ≤ Subgroup.center (StatedSp 2 F) := fun hle => by
      have hc := hle hy₀
      have hs : longBlock F 2 1 (sl2Upper 1) ∈ suppGroup (coords (1 : Fin 2)) := by
        rw [← range_longBlock]
        exact ⟨_, rfl⟩
      have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl (0 : Fin 2))
        (by simp [mem_coords])
      have h2' := longBlock_injective (K := F) (n := 2) (1 : Fin 2) (h1.trans (map_one _).symm)
      have := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F) 0 1) h2'
      simp [sl2Upper_one_coe] at this
    have hNtop := eq_top_of_normal_of_not_le_center h4 hN
    intro x
    have : x ∈ N := by rw [hNtop]; trivial
    exact this
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift hodd h4 ψ hker τ hτ hstab
  set ρ : StatedSp 2 F ≃* StatedSp 2 F := (fieldSp 2 F σ).trans (conjSp 2 F A) with hρdef
  have hρψ : ∀ x, ψ (ρ x) = τ (ψ x) := fun x => (hAσ x).symm
  have hex : ∀ s : SL(2, F), ∃ s' : SL(2, F), θ₂ s' = θ s := fun s => by
    have : θ s ∈ θ₂.range := hθ₂range ▸ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  choose γf hγf using hex
  let γ0 : SL(2, F) →* SL(2, F) :=
    { toFun := γf
      map_one' := hθ₂inj (by rw [hγf, map_one, map_one])
      map_mul' := fun s t => hθ₂inj (by rw [hγf, map_mul, map_mul, hγf, hγf]) }
  have hγsurj : Function.Surjective γ0 := fun t => by
    have : θ₂ t ∈ θ.range := hθ₂range ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hθ₂inj (by show θ₂ (γf s) = θ₂ t; rw [hγf]; exact hs)⟩
  let γ : SL(2, F) ≃* SL(2, F) :=
    MulEquiv.ofBijective γ0 ⟨Finite.injective_iff_surjective.2 hγsurj, hγsurj⟩
  have hγθ : ∀ s, θ₂ (γ s) = θ s := fun s => hγf s
  have hρL : ∀ s : SL(2, F), ρ (longBlock F 2 1 s) ∈ (longBlock F 2 1).range := by
    have hAperf : (ρ.toMonoidHom.comp (longBlock F 2 1)).range ≤
        ⁅(ρ.toMonoidHom.comp (longBlock F 2 1)).range,
          (ρ.toMonoidHom.comp (longBlock F 2 1)).range⁆ :=
      range_le_commutator_aux _
    have hsup : (ρ.toMonoidHom.comp (longBlock F 2 1)).range ≤
        (longBlock F 2 1).range ⊔ ψ.ker := by
      rintro _ ⟨s, rfl⟩
      have h1 : τ (θ₂ s) ∈ θ₂.range := by
        have : θ₂ s ∈ θ.range := hθ₂range ▸ ⟨s, rfl⟩
        obtain ⟨s₁, hs₁⟩ := this
        rw [← hs₁, hθτ]
        exact hθ₂range ▸ ⟨_, rfl⟩
      obtain ⟨s', hs'⟩ := h1
      have hz : (longBlock F 2 1 s')⁻¹ * ρ (longBlock F 2 1 s) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρψ]
        show (θ₂ s')⁻¹ * τ (θ₂ s) = 1
        rw [hs', inv_mul_cancel]
      have : ρ (longBlock F 2 1 s) =
          longBlock F 2 1 s' * ((longBlock F 2 1 s')⁻¹ * ρ (longBlock F 2 1 s)) := by group
      show ρ (longBlock F 2 1 s) ∈ _
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s', rfl⟩) (Subgroup.mem_sup_right hz)
    exact fun s => le_of_perfect_of_le_sup_center hker hAperf hsup ⟨s, rfl⟩
  have hγ' : ∀ s : SL(2, F),
      ρ (longBlock F 2 1 (γ s)) = longBlock F 2 1 (γ (diagConj2 (-1) 1 s)) := by
    intro s
    obtain ⟨s'', hs''⟩ := hρL (γ s)
    have hs : s'' = γ (diagConj2 (-1) 1 s) := by
      apply hθ₂inj
      calc θ₂ s'' = ψ (longBlock F 2 1 s'') := rfl
        _ = ψ (ρ (longBlock F 2 1 (γ s))) := by rw [hs'']
        _ = τ (ψ (longBlock F 2 1 (γ s))) := hρψ _
        _ = τ (θ s) := by rw [← hγθ]; rfl
        _ = θ (diagConj2 (-1) 1 s) := hθτ s
        _ = θ₂ (γ (diagConj2 (-1) 1 s)) := (hγθ _).symm
    rw [← hs'', hs]
  have hρρ : ∀ x : StatedSp 2 F, ρ (ρ x) = x := by
    let ρ2 : StatedSp 2 F →* StatedSp 2 F := ρ.toMonoidHom.comp ρ.toMonoidHom
    have key := Gaps.fixed_of_perfect_of_central ρ2 (N := ⊤) inferInstance (Z := ψ.ker) hker
      (fun n _ => by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        show (ψ n)⁻¹ * ψ (ρ (ρ n)) = 1
        rw [hρψ, hρψ, hτ, inv_mul_cancel])
    exact fun x => key x trivial
  set Am : Mat4 F := ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with hAm
  set Bm : Mat4 F := (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with hBm
  have hAB : Am * Bm = 1 := by
    rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hm : ((multiplier 2 F A : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = ((multiplier 2 F A : Fˣ) : F) * form u v :=
    form_mulVec_of_sim (multiplier_spec A)
  have hγm : ∀ s : SL(2, F), Am * blockMat (Sum.inl 1) (Sum.inr 1)
      (((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
      blockMat (Sum.inl 1) (Sum.inr 1)
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro s
    have h := congrArg (mat 2 F) (hγ' s)
    have e : mat 2 F (ρ (longBlock F 2 1 (γ s))) =
        Am * (mat 2 F (longBlock F 2 1 (γ s))).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, mat_longBlock, mat_longBlock, map_blockMat] at h
    exact h
  have hρm : ∀ x : StatedSp 2 F, Am * (Am * (mat 2 F x).map σ * Bm).map σ * Bm = mat 2 F x := by
    intro x
    have h := congrArg (mat 2 F) (hρρ x)
    have e1 : mat 2 F (ρ (ρ x)) = Am * (mat 2 F (ρ x)).map σ * Bm := mat_conjSp_fieldSp A σ (ρ x)
    have e2 : mat 2 F (ρ x) = Am * (mat 2 F x).map σ * Bm := mat_conjSp_fieldSp A σ x
    rw [e1, e2] at h
    exact h
  obtain ⟨hσ, g, hg1, hg2⟩ := core_mat h2 hAB hBA σ hm hsim γ hγm hρm h01
  refine ⟨g, hg1, ?_⟩
  rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
  have hmapid : ∀ M : Mat4 F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hfix : ρ (g * shortBlock F h01 s * g⁻¹) = g * shortBlock F h01 s * g⁻¹ := by
    apply mat_injective
    have e : mat 2 F (ρ (g * shortBlock F h01 s * g⁻¹)) =
        Am * (mat 2 F (g * shortBlock F h01 s * g⁻¹)).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, hmapid, hg2 s, Matrix.mul_assoc, hAB, Matrix.mul_one]
  show τ (ψ (g * shortBlock F h01 s * g⁻¹)) = ψ (g * shortBlock F h01 s * g⁻¹)
  rw [← hρψ, hfix]

end Group


end CFSG.ClassicalInvolution.RouteD.SpToral
