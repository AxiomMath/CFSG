module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM28
public import CFSG.ClassicalInvolution.Asc77.AscC5OM8GStmt
public import CFSG.GH74.GLS.IVK.L2.SLAut
public import CFSG.ClassicalInvolution.Asc77.AscC5OM10
public import CFSG.ClassicalInvolution.Asc77.AscC5OM26
public import CFSG.ClassicalInvolution.Asc77.AscC5OM27

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]
  {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}

theorem Frame.mem_L_sup_of {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' : Y} (fr : Frame F Y Φ A A' z') (k : Fin 2) {x : StatedSp 2 F}
    (hx : fr.ψ x ∈ (longRootSp2 F 2 k).map fr.ψ) : x ∈ longRootSp2 F 2 k ⊔ spScalars 2 F := by
  obtain ⟨l, hl, hle⟩ := hx
  rcases fr.lift_eq_iff.mp hle.symm with h | h
  · rw [h]
    exact Subgroup.mem_sup_left hl
  · rw [h]
    exact Subgroup.mul_mem_sup hl negOne_mem_spScalars

theorem rho_eq [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂)
    {M : Type} [Group M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) {L L' : Subgroup M}
    (hmap₁ : L.map π₁ = A₁ ∧ L'.map π₁ = A₁') (hmap₂ : L.map π₂ = A₂ ∧ L'.map π₂ = A₂')
    (θ₀ θ₁ : MulAut SL(2, F))
    (hrel₀ : ∀ (m : M) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 0 b) →
      π₂ m = fr₂.ψ (longBlock F 2 0 (θ₀ b)))
    (hrel₁ : ∀ (m : M) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 1 b) →
      π₂ m = fr₂.ψ (longBlock F 2 1 (θ₁ b)))
    (d₀ d₁ : GL (Fin 2) F) (ρ₀ ρ₁ : F ≃+* F)
    (hθ₀ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ₀ b) =
      d₀ * glm ρ₀ (Matrix.SpecialLinearGroup.toGL b) * d₀⁻¹)
    (hθ₁ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ₁ b) =
      d₁ * glm ρ₁ (Matrix.SpecialLinearGroup.toGL b) * d₁⁻¹)
    (τ : M → M) (τ₁ : Y₁ ≃* Y₁) (τ₂ : Y₂ ≃* Y₂) (hτL : ∀ m ∈ L, τ m ∈ L')
    (hτ₁ : ∀ m, π₁ (τ m) = τ₁ (π₁ m)) (hτ₂ : ∀ m, π₂ (τ m) = τ₂ (π₂ m))
    (hinner : ∃ y : Y₂, ∀ x : Y₂, τ₂ x = y * x * y⁻¹) (hinv : ∀ x : Y₁, τ₁ (τ₁ x) = x)
    (hfix : ∀ J ∈ Φ₁, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → τ₁ x ≠ x) : ρ₀ = ρ₁ := by
  obtain ⟨N₁, hN₁, -, -⟩ := fr₁.exc_shape hp h2 h4 τ₁ hinv hfix
  obtain ⟨y, hy⟩ := hinner
  obtain ⟨Y₀, rfl⟩ := fr₂.surj y
  set N₂ : gsp 2 F := ⟨Y₀, statedSp_le_gsp Y₀.2⟩ with hN₂def
  have hN₂ : ∀ x, τ₂ (fr₂.ψ x) = fr₂.ψ (conjSp 2 F N₂ x) := fun x => by
    rw [hy, conjSp_of_sp, map_mul, map_mul, map_inv]
  have hswap : ∀ {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
      (fr : Frame F Y Φ A A' z') (π : M →* Y) (hm : L.map π = A ∧ L'.map π = A')
      (t : Y ≃* Y) (ht : ∀ m, π (τ m) = t (π m)) (N : gsp 2 F)
      (hN : ∀ x, t (fr.ψ x) = fr.ψ (conjSp 2 F N x)),
      conjSp 2 F N (longInv F 2 0) = longInv F 2 1 := by
    intro Y _ Φ A A' z' fr π hm t ht N hN
    refine longInv_of_map_le h2 h4 (conjSp 2 F N) 1 fun r hr => fr.mem_L_sup_of 1 ?_
    rw [← hN, ← fr.hA']
    have hrA : fr.ψ r ∈ L.map π := by rw [hm.1]; exact fr.mem_A hr
    obtain ⟨m, hm', hmr⟩ := hrA
    rw [← hmr, ← ht, ← hm.2]
    exact ⟨τ m, hτL m hm', rfl⟩
  obtain ⟨β, hβ⟩ := exists_swap_block h2 N₁ (hswap fr₁ π₁ hmap₁ τ₁ hτ₁ N₁ hN₁)
  obtain ⟨γ, hγ⟩ := exists_swap_block h2 N₂ (hswap fr₂ π₂ hmap₂ τ₂ hτ₂ N₂ hN₂)
  have key : ∀ b : SL(2, F), θ₁ (slConj β b) = slConj γ (θ₀ b) := by
    intro b
    have hbA : fr₁.ψ (longBlock F 2 0 b) ∈ L.map π₁ := by
      rw [hmap₁.1]
      exact fr₁.mem_A ⟨b, rfl⟩
    obtain ⟨m, -, hm⟩ := hbA
    have e1 : π₁ (τ m) = fr₁.ψ (longBlock F 2 1 (slConj β b)) := by
      rw [hτ₁, hm, hN₁, hβ]
    have e2 : π₂ (τ m) = fr₂.ψ (longBlock F 2 1 (slConj γ (θ₀ b))) := by
      rw [hτ₂, hrel₀ m b hm, hN₂, hγ]
    rw [hrel₁ _ _ e1] at e2
    exact longBlock_injective 1 (fr₂.injOn_L h2 1 ⟨_, rfl⟩ ⟨_, rfl⟩ e2)
  refine (semilinear_unique (d₁ * glm ρ₁ β) (γ * d₀) ρ₁ ρ₀ fun b => ?_).1.symm
  have e := congrArg Matrix.SpecialLinearGroup.toGL (key b)
  rw [hθ₁, slg_slConj, slg_slConj, hθ₀] at e
  simp only [map_mul, map_inv] at e
  convert e using 1 <;> group

theorem glm_symm_glm (ρ : F ≃+* F) (g : GL (Fin 2) F) : glm ρ.symm (glm ρ g) = g := by
  ext i j
  simp

theorem slg_slMap_symm (ρ : F ≃+* F) (b : SL(2, F)) :
    Matrix.SpecialLinearGroup.toGL ((slMap ρ).symm b) =
      glm ρ.symm (Matrix.SpecialLinearGroup.toGL b) :=
  Units.ext rfl

theorem injective_ψ_longBlock {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' : Y} (fr : Frame F Y Φ A A' z') (h2 : (2 : F) ≠ 0) (k : Fin 2) :
    Function.Injective (fr.ψ.comp (longBlock F 2 k)) := fun _ _ h =>
  longBlock_injective k (fr.injOn_L h2 k ⟨_, rfl⟩ ⟨_, rfl⟩ h)

theorem range_ψ_longBlock {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' : Y} (fr : Frame F Y Φ A A' z') (k : Fin 2) :
    (fr.ψ.comp (longBlock F 2 k)).range = (longRootSp2 F 2 k).map fr.ψ := by
  rw [MonoidHom.range_comp]
  rfl

section Setup

variable {p f : ℕ} [Fact p.Prime]


theorem exists_setup {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ a₁ b₁ : Y₁}
    {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ a₂ b₂ : Y₂}
    {M : Type} [Group M] [Finite M] {π₁ : M →* Y₁} {π₂ : M →* Y₂} {L L' : Subgroup M}
    (hT : TwinShare p f Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L') :
    ∃ (fr₁ : Frame (GaloisField p f) Y₁ Φ₁ A₁ A₁' z₁) (Φ₂' : Set (Subgroup Y₂))
      (fr₂ : Frame (GaloisField p f) Y₂ Φ₂' A₂ A₂' z₂)
      (θ : Fin 2 → MulAut SL(2, GaloisField p f)) (d : Fin 2 → GL (Fin 2) (GaloisField p f)),
      π₁.ker = π₂.ker ∧
      (∀ k b, Matrix.SpecialLinearGroup.toGL (θ k b) =
        d k * Matrix.SpecialLinearGroup.toGL b * (d k)⁻¹) ∧
      (∀ (k : Fin 2) (m : M) (b : SL(2, GaloisField p f)),
        π₁ m = fr₁.ψ (longBlock (GaloisField p f) 2 k b) →
          π₂ m = fr₂.ψ (longBlock (GaloisField p f) 2 k (θ k b))) := by
  obtain ⟨fr₁⟩ := exists_frame hT.data₁
  obtain ⟨fr₂⟩ := exists_frame hT.data₂
  have hp := hT.data₁.odd
  have h2 := two_ne_zero_gf (p := p) f hp
  have h5 := five_le_card_gf (p := p) (f := f) hT.data₁.five
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  have h3 : 3 < Nat.card (GaloisField p f) := by omega
  have hodd := odd_card_gf hp hT.data₁.five
  have hker : π₁.ker = π₂.ker := le_antisymm
    (fr₂.ker_le_ker h2 h4 π₁ π₂ hT.range₂ hT.odd₁) (fr₁.ker_le_ker h2 h4 π₂ π₁ hT.range₁ hT.odd₂)
  have hr : ∀ {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
      (fr : Frame (GaloisField p f) Y Φ A A' z') (π : M →* Y)
      (hm : L.map π = A ∧ L'.map π = A'),
      L.map π = (fr.ψ.comp (longBlock (GaloisField p f) 2 0)).range ∧
        L'.map π = (fr.ψ.comp (longBlock (GaloisField p f) 2 1)).range := by
    intro Y _ Φ A A' z' fr π hm
    rw [range_ψ_longBlock, range_ψ_longBlock, hm.1, hm.2]
    exact ⟨fr.hA, fr.hA'⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_twin_iso π₁ π₂ hker L _ _ (injective_ψ_longBlock fr₁ h2 0)
    (injective_ψ_longBlock fr₂ h2 0) (hr fr₁ π₁ hT.map₁).1 (hr fr₂ π₂ hT.map₂).1
  obtain ⟨θ₁, hθ₁⟩ := exists_twin_iso π₁ π₂ hker L' _ _ (injective_ψ_longBlock fr₁ h2 1)
    (injective_ψ_longBlock fr₂ h2 1) (hr fr₁ π₁ hT.map₁).2 (hr fr₂ π₂ hT.map₂).2
  obtain ⟨d₀, ρ₀, hd₀⟩ := CFSG.GH74.GLS.IVK.exists_semilinear_of_mulAut hodd h3 θ₀
  obtain ⟨d₁, ρ₁, hd₁⟩ := CFSG.GH74.GLS.IVK.exists_semilinear_of_mulAut hodd h3 θ₁
  obtain ⟨τ, τ₁, τ₂, hτL, -, hτ₁, hτ₂, hinner, hinv, hfix, -⟩ := hT.swap
  have hρ : ρ₀ = ρ₁ := rho_eq hp h2 h4 fr₁ fr₂ π₁ π₂ hT.map₁ hT.map₂ θ₀ θ₁
    (fun m b h => hθ₀ m b h) (fun m b h => hθ₁ m b h) d₀ d₁ ρ₀ ρ₁ hd₀ hd₁ τ τ₁ τ₂ hτL hτ₁
    hτ₂ hinner hinv hfix
  subst hρ
  refine ⟨fr₁, _, fr₂.twist ρ₀, fun k => if k = 0 then (slMap ρ₀)⁻¹ * θ₀ else (slMap ρ₀)⁻¹ * θ₁,
    fun k => glm ρ₀.symm (if k = 0 then d₀ else d₁), hker, ?_, ?_⟩
  · intro k b
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · simp only [↓reduceIte]
      change Matrix.SpecialLinearGroup.toGL ((slMap ρ₀).symm (θ₀ b)) = _
      rw [slg_slMap_symm, hd₀, map_mul, map_mul, map_inv, glm_symm_glm]
    · simp only [one_ne_zero, ↓reduceIte]
      change Matrix.SpecialLinearGroup.toGL ((slMap ρ₀).symm (θ₁ b)) = _
      rw [slg_slMap_symm, hd₁, map_mul, map_mul, map_inv, glm_symm_glm]
  · intro k m b hm
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · simp only [↓reduceIte]
      rw [hθ₀ m b hm, MonoidHom.comp_apply, fr₂.twist_ψ_longBlock ρ₀]
      rfl
    · simp only [one_ne_zero, ↓reduceIte]
      rw [hθ₁ m b hm, MonoidHom.comp_apply, fr₂.twist_ψ_longBlock ρ₀]
      rfl

end Setup

end CFSG.ClassicalInvolution.Asc77.C5O.M
