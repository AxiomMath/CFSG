module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.GH74.GLS.Stage4.T2P71L72G2Group

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

theorem g2_sign_ne_zero {F : Type*} [Field F] {a : F} (h : a = 1 ∨ a = -1) : a ≠ 0 := by
  rcases h with rfl | rfl <;> simp

end CFSG.GH74.GLS.Stage4.Rest.L72

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement

variable {F : Type} [Field F]

theorem exists_conj_formula (h3 : (3 : F) = 0) :
    ∃ e₁ e₂ e₃ e₄ δ γ : F, (e₁ = 1 ∨ e₁ = -1) ∧ (e₃ = 1 ∨ e₃ = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      (γ = 1 ∨ γ = -1) ∧ ⁅Xa (1 : F), Xr (1 : F)⁆ = Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄ ∧
      ∀ s t : F, Xa s * Xr t * (Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄) * (Xa s * Xr t)⁻¹ =
        Xu e₁ * Xv (e₂ + δ * (t * e₁)) * Xb e₃ * Xc (e₄ + γ * (s * e₃)) := by
  obtain ⟨e₁, e₂, e₃, e₄, he₁, -, he₃, -, har⟩ := rel_ar (K := F)
  obtain ⟨δ, hδ, hru⟩ := rel_ru (K := F) h3
  obtain ⟨γ, hγ, hab⟩ := rel_ab (K := F)
  have h1 := har 1 1
  simp only [mul_one, one_pow] at h1
  refine ⟨e₁, e₂, e₃, e₄, δ, γ, he₁, he₃, hδ, hγ, h1, fun s t => ?_⟩
  have e4 : ∀ g a b c d : ModGL .G2 F, g * (a * b * c * d) * g⁻¹ =
      (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) * (g * d * g⁻¹) := fun _ _ _ _ _ => by group
  have cj : ∀ g h : ModGL .G2 F, g * h * g⁻¹ = ⁅g, h⁆ * h := fun g h => by
    simp only [commutatorElement_def]
    group
  have hP : Xr t * (Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄) * (Xr t)⁻¹ =
      Xu e₁ * Xv (e₂ + δ * (t * e₁)) * Xb e₃ * Xc e₄ := by
    rw [e4, cj (Xr t) (Xu e₁), hru, (comm_rv h3 t e₂).mul_inv_cancel,
      (comm_rb t e₃).mul_inv_cancel, (comm_rc t e₄).mul_inv_cancel,
      ← (comm_uv h3 e₁ (δ * (t * e₁))).eq, mul_assoc (Xu e₁), ← Xv_add, add_comm]
  have hQ : ∀ w : F, Xa s * (Xu e₁ * Xv w * Xb e₃ * Xc e₄) * (Xa s)⁻¹ =
      Xu e₁ * Xv w * Xb e₃ * Xc (e₄ + γ * (s * e₃)) := by
    intro w
    rw [e4, (comm_au s e₁).mul_inv_cancel, (comm_av s w).mul_inv_cancel, cj (Xa s) (Xb e₃), hab,
      (comm_ac s e₄).mul_inv_cancel, ← (comm_bc e₃ (γ * (s * e₃))).eq]
    simp only [mul_assoc]
    rw [← Xc_add, add_comm]
  calc Xa s * Xr t * (Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄) * (Xa s * Xr t)⁻¹
      = Xa s * (Xr t * (Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄) * (Xr t)⁻¹) * (Xa s)⁻¹ := by group
    _ = _ := by rw [hP, hQ]

theorem exists_card_centralizer_mul_le [Finite F] (h3 : (3 : F) = 0) :
    ∃ x y : ↥(posUnipotent .G2 F), Nat.card ↥(Subgroup.centralizer {⁅x, y⁆}) * Nat.card F ^ 2 ≤
      Nat.card ↥(posUnipotent .G2 F) := by
  have : Finite (ModGL .G2 F) := finite_modGL
  obtain ⟨e₁, e₂, e₃, e₄, δ, γ, he₁, he₃, hδ, hγ, hξ, hconj⟩ := exists_conj_formula (F := F) h3
  let x : ↥(posUnipotent .G2 F) := ⟨Xa 1, Xa_mem 1⟩
  let y : ↥(posUnipotent .G2 F) := ⟨Xr 1, Xr_mem 1⟩
  refine ⟨x, y, ?_⟩
  set ξ : ↥(posUnipotent .G2 F) := ⁅x, y⁆ with hξdef
  have hξv : (ξ : ModGL .G2 F) = Xu e₁ * Xv e₂ * Xb e₃ * Xc e₄ := by
    rw [← hξ]
    rfl
  set C : Subgroup ↥(posUnipotent .G2 F) := Subgroup.centralizer {ξ} with hC
  let a : F × F → ↥(posUnipotent .G2 F) := fun p => ⟨Xa p.1 * Xr p.2, mul_mem (Xa_mem _) (Xr_mem _)⟩
  have hA : ∀ p : F × F, ((a p : ↥(posUnipotent .G2 F)) : ModGL .G2 F) = Xa p.1 * Xr p.2 :=
    fun _ => rfl
  have key : ∀ A B ζ : ModGL .G2 F, A⁻¹ * B * ζ = ζ * (A⁻¹ * B) → B * ζ * B⁻¹ = A * ζ * A⁻¹ :=
    fun A B ζ h => by
      calc B * ζ * B⁻¹ = A * (A⁻¹ * B * ζ) * B⁻¹ := by group
        _ = A * (ζ * (A⁻¹ * B)) * B⁻¹ := by rw [h]
        _ = A * ζ * A⁻¹ := by group
  have hinj : Function.Injective
      (fun p : F × F => (QuotientGroup.mk (a p) : ↥(posUnipotent .G2 F) ⧸ C)) := by
    intro p q hpq
    have hmem : (a p)⁻¹ * a q ∈ C := QuotientGroup.eq.1 hpq
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hmem
    have h := congrArg Subtype.val hmem
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hξv, hA] at h
    have hAB := key _ _ _ h
    rw [hconj, hconj] at hAB
    obtain ⟨-, h2, -, h4⟩ := inj4 hAB
    have ht : q.2 = p.2 :=
      mul_right_cancel₀ (g2_sign_ne_zero he₁)
        (mul_left_cancel₀ (g2_sign_ne_zero hδ) (add_left_cancel h2))
    have hs : q.1 = p.1 :=
      mul_right_cancel₀ (g2_sign_ne_zero he₃)
        (mul_left_cancel₀ (g2_sign_ne_zero hγ) (add_left_cancel h4))
    exact Prod.ext hs.symm ht.symm
  have h1 : Nat.card (F × F) ≤ Nat.card (↥(posUnipotent .G2 F) ⧸ C) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, ← sq, ← Subgroup.index_eq_card] at h1
  calc Nat.card ↥C * Nat.card F ^ 2 ≤ Nat.card ↥C * C.index := Nat.mul_le_mul_left _ h1
    _ = Nat.card ↥(posUnipotent .G2 F) := C.card_mul_index

theorem g2_no_abelian_index_le_three [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 3 ^ n)
    (h3 : (3 : F) = 0) (B : Subgroup ↥(posUnipotent .G2 F))
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card ↥(posUnipotent .G2 F) ≤ 3 * Nat.card ↥B) : False := by
  have hU : Nat.card ↥(posUnipotent .G2 F) = 3 ^ (6 * n) := by
    rw [card_posUnipotent, ncard_posRoots_G2, hF, ← pow_mul, mul_comm]
  have : Finite (ModGL .G2 F) := finite_modGL
  obtain ⟨x, y, hxy⟩ := exists_card_centralizer_mul_le (F := F) h3
  have hξB := commutator_mem_of_index_le_three (k := 6 * n) (by omega) hU B hcard x y
  have hBC : B ≤ Subgroup.centralizer {⁅x, y⁆} := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hB _ hb _ hξB
  have hle := Subgroup.card_le_of_le hBC
  have hq : 3 ≤ Nat.card F := hF ▸ Nat.le_self_pow (by omega) 3
  have hq9 : 9 ≤ Nat.card F ^ 2 := by nlinarith
  have hCpos : 0 < Nat.card ↥(Subgroup.centralizer {⁅x, y⁆}) := Nat.card_pos
  have : Nat.card ↥(Subgroup.centralizer {⁅x, y⁆}) * 9 ≤
      Nat.card ↥(Subgroup.centralizer {⁅x, y⁆}) * Nat.card F ^ 2 := Nat.mul_le_mul_left _ hq9
  omega

end CFSG.GH74.GLS.Stage4.Rest.L72
