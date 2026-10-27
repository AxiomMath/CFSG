module

public import CFSG.CGT.Stroth77.Extension24Basis
public import CFSG.CGT.Stroth77.Extension24C4
public import CFSG.CGT.Stroth77.Extension24IndexTwo
public import CFSG.CGT.Stroth77.ExtensionOver
public import CFSG.CGT.Stroth77.Extension23

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (s + 1)) j

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem torus_endo_ext_Idx4 {k : Fin 3 → ℕ} (f g : Torus k →+ Torus k)
    (h : ∀ j, f (gen k j) = g (gen k j)) : f = g := by
  refine torus_hom_ext f g fun j z => ?_
  have e : Pi.single j (z : ZMod (2 ^ k j)) = z • gen k j := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [gen, Pi.single_eq_same, zsmul_eq_mul]
    · simp [gen, Pi.single_eq_of_ne hij]
  rw [e, map_zsmul, map_zsmul, h j]

theorem ofMul_conjBy_toMul_Idx4 {k : Fin 3 → ℕ} (E : Torus k ≃+ Additive C) {g : S}
    (hg : g ∈ Subgroup.normalizer C) (v : Torus k) :
    Additive.ofMul (conjBy hg (Additive.toMul (E v))) = E (conjTorusIdx4 E hg v) := by
  rw [conjTorusIdx4_apply, AddEquiv.apply_symm_apply]

theorem hasStrothTypeOver_of_conjTorus_Idx4 {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hL : D.L ≤ Subgroup.normalizer C) (τ' : StrothTypeIndex) (E : Torus τ'.k ≃+ Additive C)
    (h : ∀ j : Fin 3,
      conjTorusIdx4 E (hL D.uv_mem_L) (gen τ'.k j) = τ'.action.φuv (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.t_mem_L) (gen τ'.k j) = τ'.action.φt (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.u_mem_L) (gen τ'.k j) = τ'.action.φu (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.ρ_mem_L) (gen τ'.k j) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothTypeOver D C τ' := by
  have conj_of {g : S} (hg : g ∈ Subgroup.normalizer C) {φ : Torus τ'.k →+ Torus τ'.k}
      (hφ : conjTorusIdx4 E hg = φ) (x : C) :
      E.symm (Additive.ofMul (conjBy hg x)) = φ (E.symm (Additive.ofMul x)) := by
    rw [← hφ, conjTorusIdx4_apply_symm]
  refine ⟨{
    e := E.symm
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_cube := D.rho_cube
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := hL D.uv_mem_L
    t_mem := hL D.t_mem_L
    u_mem := hL D.u_mem_L
    ρ_mem := hL D.ρ_mem_L
    uv_conj := conj_of (hL D.uv_mem_L) (torus_endo_ext_Idx4 _ _ fun j => (h j).1)
    t_conj := conj_of (hL D.t_mem_L) (torus_endo_ext_Idx4 _ _ fun j => (h j).2.1)
    u_conj := conj_of (hL D.u_mem_L) (torus_endo_ext_Idx4 _ _ fun j => (h j).2.2.1)
    ρ_conj := conj_of (hL D.ρ_mem_L) (torus_endo_ext_Idx4 _ _ fun j => (h j).2.2.2) },
    rfl, rfl, rfl, rfl⟩

theorem hasStrothType_of_conjTorus_Idx4 {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hL : D.L ≤ Subgroup.normalizer C) (τ' : StrothTypeIndex) (E : Torus τ'.k ≃+ Additive C)
    (h : ∀ j : Fin 3,
      conjTorusIdx4 E (hL D.uv_mem_L) (gen τ'.k j) = τ'.action.φuv (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.t_mem_L) (gen τ'.k j) = τ'.action.φt (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.u_mem_L) (gen τ'.k j) = τ'.action.φu (gen τ'.k j) ∧
      conjTorusIdx4 E (hL D.ρ_mem_L) (gen τ'.k j) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothType C τ' :=
  (hasStrothTypeOver_of_conjTorus_Idx4 D hL τ' E h).hasStrothType

section Normalize

variable {s : ℕ} (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1))) (hBC : B ≤ C)
  (hL : D.L ≤ Subgroup.normalizer C)

theorem conjTorus_ρ_two300 {e : C} (E : Torus (Type100.k (s + 1)) ≃+ Additive C)
    (hE0 : E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩) (hE1 : E (𝔤 s 1) = Additive.ofMul e)
    (hE2 : E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e))
    (hnorm : Additive.ofMul e + Additive.ofMul (conjBy (hL D.ρ_mem_L) e) +
      Additive.ofMul (conjBy (hL D.ρ_mem_L) (conjBy (hL D.ρ_mem_L) e)) =
      (-2 : ℤ) • Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) :
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) +
        (-1 : ℤ) • (𝔤 s 2) := by
  have h2 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) e)) = (𝔤 s 2) :=
    (AddEquiv.symm_apply_eq E).mpr hE2.symm
  have h1 : E.symm (Additive.ofMul e) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E).mpr hE1.symm
  have h0 : E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (𝔤 s 0) :=
    (AddEquiv.symm_apply_eq E).mpr hE0.symm
  rw [← h2, conjTorusIdx4_apply_symm, eq_neg_add_of_add_eq hnorm, map_add, map_neg, map_add,
    map_zsmul, h0, h1, h2]
  module

end Normalize

theorem hasStrothTypeOver_t100_or_t101_of_noInvolutionsCentralizing {n : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t300 n)) (hn : 1 ≤ n)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t100 n) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t101 (n - 1)) := by
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  have hncyc := not_isCyclic_quotient_t300_of_data D hBC hC hrel hL hH hcS
  let hρC := hL D.ρ_mem_L
  let hu := hL D.u_mem_L
  let cC : C := ⟨D.c, hBC D.c.2⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  obtain ⟨e₀, he₀⟩ := exists_sq_eq_a300_of_data D hn hBC hC hrel hL hH hcS hncyc
  obtain ⟨E₀, hE₀0, hE₀1, hE₀2⟩ := exists_torusBasis300_of_data D hBC hC hrel hL hncyc he₀
  have T₀ := transport300 D hBC hL E₀ hE₀0 hE₀1 hE₀2 he₀
  have rels₀ := conjTorusIdx4_rels E₀ D hL
  obtain ⟨w, hw⟩ := rho_normalize300 (conjTorusIdx4 E₀ hρC)
    (fun x => DFunLike.congr_fun rels₀.rho_cube x) T₀.1 T₀.2.1 T₀.2.2.1
  let v₁ : Torus (Type100.k (s + 1)) := (𝔤 s 1) + tor300 s w 0 0
  let e₁ : C := Additive.toMul (E₀ v₁)
  have he₁ : e₁ * e₁ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₀ v₁ + E₀ v₁ = Additive.ofMul aC
    rw [← map_add, show v₁ + v₁ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₁]
      rw [show (𝔤 s 1) + tor300 s w 0 0 + ((𝔤 s 1) + tor300 s w 0 0) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor300 s w 0 0 by module, two_zsmul_tor300, add_zero],
      map_zsmul, hE₀1, two_zsmul, ← ofMul_mul, he₀]
  have hnorm₁ : Additive.ofMul e₁ + Additive.ofMul (conjBy hρC e₁) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₁)) = (-2 : ℤ) • Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₁) = E₀ (conjTorusIdx4 E₀ hρC v₁) :=
      ofMul_conjBy_toMul_Idx4 E₀ hρC v₁
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₁)) =
        E₀ (conjTorusIdx4 E₀ hρC (conjTorusIdx4 E₀ hρC v₁)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₀ hρC, ← h1]
      rfl
    rw [h1, h2, show Additive.ofMul e₁ = E₀ v₁ from rfl, ← map_add, ← map_add, hw, map_zsmul,
      hE₀0]
  obtain ⟨E₁, hE₁0, hE₁1, hE₁2⟩ := exists_torusBasis300_of_data D hBC hC hrel hL hncyc he₁
  have T₁ := transport300 D hBC hL E₁ hE₁0 hE₁1 hE₁2 he₁
  have rels₁ := conjTorusIdx4_rels E₁ D hL
  have hR2₁ := conjTorus_ρ_two300 D hBC hL E₁ hE₁0 hE₁1 hE₁2 hnorm₁
  obtain ⟨x, -, hUx, -, -⟩ := lifts300 _ _ _ _ rels₁ T₁.1 T₁.2.1 hR2₁ T₁.2.2.2.1
    T₁.2.2.2.2.1 T₁.2.2.2.2.2.2.1 T₁.2.2.2.2.2.2.2.1 T₁.2.2.2.2.2.2.2.2
  have hRt₁ := R_tor300 (conjTorusIdx4 E₁ hρC) T₁.1 T₁.2.1 T₁.2.2.1
  have hUt₁ := U_tor300 (conjTorusIdx4 E₁ hu) T₁.2.2.2.1 T₁.2.2.2.2.1 T₁.2.2.2.2.2.1
  let v₂ : Torus (Type100.k (s + 1)) := (𝔤 s 1) + tor300 s 0 0 x
  let e₂ : C := Additive.toMul (E₁ v₂)
  have he₂ : e₂ * e₂ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₁ v₂ + E₁ v₂ = Additive.ofMul aC
    rw [← map_add, show v₂ + v₂ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₂]
      rw [show (𝔤 s 1) + tor300 s 0 0 x + ((𝔤 s 1) + tor300 s 0 0 x) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor300 s 0 0 x by module, two_zsmul_tor300, add_zero],
      map_zsmul, hE₁1, two_zsmul, ← ofMul_mul, he₁]
  have hRv₂ : conjTorusIdx4 E₁ hρC v₂ = (𝔤 s 2) + tor300 s (0 - 4 * x) (-x) (0 - x) := by
    simp only [v₂, map_add, T₁.2.1, hRt₁]
  have hnorm₂ : Additive.ofMul e₂ + Additive.ofMul (conjBy hρC e₂) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₂)) = (-2 : ℤ) • Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₂) = E₁ (conjTorusIdx4 E₁ hρC v₂) :=
      ofMul_conjBy_toMul_Idx4 E₁ hρC v₂
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₂)) =
        E₁ (conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₁ hρC, ← h1]
      rfl
    have hsum : v₂ + conjTorusIdx4 E₁ hρC v₂ + conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂) =
        (-2 : ℤ) • (𝔤 s 0) := by
      rw [hRv₂, map_add, hR2₁, hRt₁]
      have hz : tor300 s (4 * (-x)) 0 0 = 0 := by
        rw [← tor300_zero]
        exact tor300_congr ⟨2 * x, by ring⟩ (by omega) (by omega)
      calc _ = (-2 : ℤ) • (𝔤 s 0) + tor300 s (4 * (-x)) 0 0 := by
            simp only [v₂, tor300]
            module
        _ = (-2 : ℤ) • (𝔤 s 0) := by rw [hz, add_zero]
    rw [h1, h2, show Additive.ofMul e₂ = E₁ v₂ from rfl, ← map_add, ← map_add, hsum,
      map_zsmul, hE₁0]
  have hue₂ : conjBy hu e₂ = conjBy hρC e₂ := by
    apply Additive.ofMul.injective
    rw [ofMul_conjBy_toMul_Idx4 E₁ hu v₂, ofMul_conjBy_toMul_Idx4 E₁ hρC v₂, hRv₂]
    congr 1
    simp only [v₂, map_add, hUx, hUt₁]
    rw [add_assoc, tor300_add]
    congr 1
    exact tor300_congr (by omega) (by omega) (by omega)
  obtain ⟨E₂, hE₂0, hE₂1, hE₂2⟩ := exists_torusBasis300_of_data D hBC hC hrel hL hncyc he₂
  have T₂ := transport300 D hBC hL E₂ hE₂0 hE₂1 hE₂2 he₂
  have rels₂ := conjTorusIdx4_rels E₂ D hL
  have hR2₂ := conjTorus_ρ_two300 D hBC hL E₂ hE₂0 hE₂1 hE₂2 hnorm₂
  have hUe₂ : conjTorusIdx4 E₂ hu (𝔤 s 1) = (𝔤 s 2) := by
    have h1 : E₂.symm (Additive.ofMul e₂) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E₂).mpr hE₂1.symm
    have h2 : E₂.symm (Additive.ofMul (conjBy hρC e₂)) = (𝔤 s 2) :=
      (AddEquiv.symm_apply_eq E₂).mpr hE₂2.symm
    rw [← h1, conjTorusIdx4_apply_symm, hue₂, h2]
  rcases images300 _ _ _ _ rels₂ T₂.1 T₂.2.1 hR2₂ T₂.2.2.2.1 T₂.2.2.2.2.1 T₂.2.2.2.2.2.2.1
    T₂.2.2.2.2.2.2.2.1 T₂.2.2.2.2.2.2.2.2 hUe₂ with h100 | h101
  · exact Or.inl (hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t100 (s + 1)) E₂ h100)
  · exact Or.inr (hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t101 s) E₂ h101)

end CFSG.CGT.Stroth77
