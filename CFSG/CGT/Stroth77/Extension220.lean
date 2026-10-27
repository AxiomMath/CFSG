module

public import CFSG.CGT.Stroth77.Extension220Basis

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type230.k s) j

public section

namespace CFSG.CGT.Stroth77

open Matrix Ext218 Ext220

variable {S : Type*} [Group S]

theorem conjTorus_ρ_two_t131 [Finite S] {B C : Subgroup S} {s : ℕ} {hm : 3 ≤ s + 2}
    (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e : C} (E : Torus (Type230.k s) ≃+ Additive C)
    (hE0 : E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩) (hE1 : E (𝔤 s 1) = Additive.ofMul e)
    (hE2 : E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e))
    (hnorm : Additive.ofMul e + Additive.ofMul (conjBy (hL D.ρ_mem_L) e) +
      Additive.ofMul (conjBy (hL D.ρ_mem_L) (conjBy (hL D.ρ_mem_L) e)) =
      -Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) :
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 2) = (Type230.action (Type230.data s)).φρ (𝔤 s 2) := by
  have h2 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) e)) = (𝔤 s 2) :=
    (AddEquiv.symm_apply_eq E).mpr hE2.symm
  have h1 : E.symm (Additive.ofMul e) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E).mpr hE1.symm
  have h0 : E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (𝔤 s 0) :=
    (AddEquiv.symm_apply_eq E).mpr hE0.symm
  rw [← h2, conjTorusIdx4_apply_symm, eq_neg_add_of_add_eq hnorm, map_add, map_neg, map_add,
    map_neg, h0, h1, h2, phiR_gen2_t230 (Type230.data s)]
  module

theorem hasStrothType_t230_or_t231_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {m : ℕ} {hm : 3 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t131 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t230 (m - 2) (by omega)) ∨
    HasStrothType C (StrothTypeIndex.t231 (m - 2) (by omega)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  have hs : 1 ≤ s := by omega
  suffices key : HasStrothType C (StrothTypeIndex.t230 s hs) ∨
      HasStrothType C (StrothTypeIndex.t231 s hs) from key
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · exfalso
    obtain ⟨C₂, hBC₂, hC₂C, hcard₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 hB.data hBC hC hrel hL hcyc
    exact false_of_index_two_t131 hB hBC₂ (hC₂C.trans hC) hcard₂ hL₂ hH (hC₂C.trans hcS)
  let D := hB.data
  let hρC := hL D.ρ_mem_L
  let hu := hL D.u_mem_L
  let cC : C := ⟨D.c, hBC D.c.2⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  have h230 := Type230.data s
  obtain ⟨e₀, he₀⟩ := exists_sq_eq_a_Idx4 hB t131_k_pos parityTorus_rho_t131
    (fun _ hρ ht => t131_fixed_rho_t_of_mem D hρ ht) hBC hC hrel hL hH hcS hcyc
  obtain ⟨E₀, hE₀0, hE₀1, hE₀2⟩ := exists_torusBasis_t131 hB hBC hC hrel hL hcyc he₀
  have T₀ := transport_t131 D hBC hL E₀ hE₀0 hE₀1 hE₀2 he₀
  have rels₀ := conjTorusIdx4_rels E₀ D hL
  obtain ⟨w, hw⟩ := rho_normalize_t230 (conjTorusIdx4 E₀ hρC)
    (fun x => DFunLike.congr_fun rels₀.rho_cube x) (T₀.1.trans (phiR_gen0_t230 h230))
    (T₀.2.1.trans (phiR_gen1_t230 h230)) (T₀.2.2.1.trans (by rw [phiR_gen2_t230 h230]))
  let v₁ : Torus (Type230.k s) := (𝔤 s 1) + tor230 s w 0 0
  let e₁ : C := Additive.toMul (E₀ v₁)
  have he₁ : e₁ * e₁ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₀ v₁ + E₀ v₁ = Additive.ofMul aC
    rw [← map_add, show v₁ + v₁ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₁]
      rw [show (𝔤 s 1) + tor230 s w 0 0 + ((𝔤 s 1) + tor230 s w 0 0) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor230 s w 0 0 by module, two_zsmul_tor230, add_zero],
      map_zsmul, hE₀1, two_zsmul, ← ofMul_mul, he₀]
  have hnorm₁ : Additive.ofMul e₁ + Additive.ofMul (conjBy hρC e₁) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₁)) = -Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₁) = E₀ (conjTorusIdx4 E₀ hρC v₁) :=
      ofMul_conjBy_toMul_Idx4 E₀ hρC v₁
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₁)) =
        E₀ (conjTorusIdx4 E₀ hρC (conjTorusIdx4 E₀ hρC v₁)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₀ hρC, ← h1]
      rfl
    rw [h1, h2, show Additive.ofMul e₁ = E₀ v₁ from rfl, ← map_add, ← map_add, hw, map_neg,
      hE₀0]
  obtain ⟨E₁, hE₁0, hE₁1, hE₁2⟩ := exists_torusBasis_t131 hB hBC hC hrel hL hcyc he₁
  have T₁ := transport_t131 D hBC hL E₁ hE₁0 hE₁1 hE₁2 he₁
  have rels₁ := conjTorusIdx4_rels E₁ D hL
  have hR2₁ := conjTorus_ρ_two_t131 D hBC hL E₁ hE₁0 hE₁1 hE₁2 hnorm₁
  obtain ⟨x, -, hUx, hUx', -, -⟩ := lifts_t131 h230 _ _ _ _ rels₁ T₁.1 T₁.2.1 hR2₁
    T₁.2.2.2.1 T₁.2.2.2.2.1 T₁.2.2.2.2.2.1 T₁.2.2.2.2.2.2.1 T₁.2.2.2.2.2.2.2.1
    T₁.2.2.2.2.2.2.2.2
  have hR₁ : conjTorusIdx4 E₁ hρC = (Type230.action h230).φρ :=
    torus_endo_ext_Idx4 _ _ fun j => by
      fin_cases j
      · exact T₁.1
      · exact T₁.2.1
      · exact hR2₁
  have hUt₁ : ∀ a b c : ℤ, conjTorusIdx4 E₁ hu (tor230 s a b c) = tor230 s a c b := fun a b c => by
    rw [dev_tor230 _ _ T₁.2.2.2.1 hUx hUx', phiU_tor230 h230]
  let v₂ : Torus (Type230.k s) := (𝔤 s 1) + tor230 s 0 0 x
  let e₂ : C := Additive.toMul (E₁ v₂)
  have he₂ : e₂ * e₂ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₁ v₂ + E₁ v₂ = Additive.ofMul aC
    rw [← map_add, show v₂ + v₂ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₂]
      rw [show (𝔤 s 1) + tor230 s 0 0 x + ((𝔤 s 1) + tor230 s 0 0 x) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor230 s 0 0 x by module, two_zsmul_tor230, add_zero],
      map_zsmul, hE₁1, two_zsmul, ← ofMul_mul, he₁]
  have hRv₂ : conjTorusIdx4 E₁ hρC v₂ = (𝔤 s 2) + tor230 s 0 x x := by
    simp only [v₂, map_add, hR₁, phiR_gen1_t230 h230, phiR_tor230 h230, zero_add]
  have hnorm₂ : Additive.ofMul e₂ + Additive.ofMul (conjBy hρC e₂) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₂)) = -Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₂) = E₁ (conjTorusIdx4 E₁ hρC v₂) :=
      ofMul_conjBy_toMul_Idx4 E₁ hρC v₂
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₂)) =
        E₁ (conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₁ hρC, ← h1]
      rfl
    have hsum : v₂ + conjTorusIdx4 E₁ hρC v₂ +
        conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂) = -(𝔤 s 0) := by
      rw [hRv₂, map_add, hR₁, phiR_gen2_t230 h230, phiR_tor230 h230]
      have hz : tor230 s 0 0 x + tor230 s 0 x x + tor230 s 0 x (x + x) = 0 := by
        simp only [tor230_add]
        exact (tor230_congr (by norm_num) ⟨-x, by ring⟩ ⟨-(2 * x), by ring⟩).trans tor230_zero
      simp only [v₂]
      linear_combination (norm := module) hz
    rw [h1, h2, show Additive.ofMul e₂ = E₁ v₂ from rfl, ← map_add, ← map_add, hsum, map_neg,
      hE₁0]
  have hue₂ : Additive.ofMul (conjBy hu e₂) =
      (-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • Additive.ofMul cC +
        Additive.ofMul (conjBy hρC e₂) := by
    rw [ofMul_conjBy_toMul_Idx4 E₁ hu v₂, ofMul_conjBy_toMul_Idx4 E₁ hρC v₂, hRv₂,
      show (-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • Additive.ofMul cC =
        E₁ ((-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • (𝔤 s 0)) by rw [map_zsmul, hE₁0],
      ← map_add]
    congr 1
    simp only [v₂, map_add]
    rw [hUx, hUt₁, phiU_gen1_exact_t230 h230]
    have hz : tor230 s 0 0 x + tor230 s 0 x 0 = tor230 s 0 x x := by
      rw [tor230_add]
      congr 1 <;> ring
    rw [add_assoc, hz]
    module
  obtain ⟨E₂, hE₂0, hE₂1, hE₂2⟩ := exists_torusBasis_t131 hB hBC hC hrel hL hcyc he₂
  have T₂ := transport_t131 D hBC hL E₂ hE₂0 hE₂1 hE₂2 he₂
  have rels₂ := conjTorusIdx4_rels E₂ D hL
  have hR2₂ := conjTorus_ρ_two_t131 D hBC hL E₂ hE₂0 hE₂1 hE₂2 hnorm₂
  have hUe₂ : conjTorusIdx4 E₂ hu (𝔤 s 1) = (Type230.action h230).φu (𝔤 s 1) := by
    have h1 : E₂.symm (Additive.ofMul e₂) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E₂).mpr hE₂1.symm
    have h2 : E₂.symm (Additive.ofMul (conjBy hρC e₂)) = (𝔤 s 2) :=
      (AddEquiv.symm_apply_eq E₂).mpr hE₂2.symm
    have h0 : E₂.symm (Additive.ofMul cC) = (𝔤 s 0) := (AddEquiv.symm_apply_eq E₂).mpr hE₂0.symm
    rw [← h1, conjTorusIdx4_apply_symm, show conjBy (hL D.u_mem_L) e₂ = conjBy hu e₂ from rfl,
      hue₂, map_add, map_zsmul, h0, h2, h1, phiU_gen1_exact_t230 h230]
    module
  rcases images_t131 h230 (Type231.data s) _ _ _ _ rels₂ T₂.1 T₂.2.1 hR2₂ T₂.2.2.2.1
      T₂.2.2.2.2.1 T₂.2.2.2.2.2.1 T₂.2.2.2.2.2.2.1 T₂.2.2.2.2.2.2.2.1 T₂.2.2.2.2.2.2.2.2 hUe₂
    with ⟨hV, hW, hU, hR⟩ | ⟨hV, hW, hU, hR⟩
  · exact Or.inl (hasStrothType_of_conjTorus_Idx4 D hL (StrothTypeIndex.t230 s hs) E₂
      fun j => ⟨DFunLike.congr_fun hV _, DFunLike.congr_fun hW _, DFunLike.congr_fun hU _,
        DFunLike.congr_fun hR _⟩)
  · exact Or.inr (hasStrothType_of_conjTorus_Idx4 D hL (StrothTypeIndex.t231 s hs) E₂
      fun j => ⟨DFunLike.congr_fun hV _, DFunLike.congr_fun hW _, DFunLike.congr_fun hU _,
        DFunLike.congr_fun hR _⟩)

theorem hasStrothTypeOver_t230_or_t231_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t131 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t230 (m - 2) (by omega)) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t231 (m - 2) (by omega)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  have hs : 1 ≤ s := by omega
  suffices key : HasStrothTypeOver D C (StrothTypeIndex.t230 s hs) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t231 s hs) from key
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · exfalso
    obtain ⟨C₂, hBC₂, hC₂C, hcard₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t131_of_data D hBC₂ (hC₂C.trans hC) hcard₂ hL₂ hH (hC₂C.trans hcS)
  let hρC := hL D.ρ_mem_L
  let hu := hL D.u_mem_L
  let cC : C := ⟨D.c, hBC D.c.2⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  have h230 := Type230.data s
  obtain ⟨e₀, he₀⟩ := exists_sq_eq_a_of_data_Idx4 D t131_k_pos parityTorus_rho_t131
    (fun _ hρ ht => t131_fixed_rho_t_of_mem D hρ ht) hBC hC hrel hL hH hcS hcyc
  obtain ⟨E₀, hE₀0, hE₀1, hE₀2⟩ := exists_torusBasis_t131_of_data D hBC hC hrel hL hcyc he₀
  have T₀ := transport_t131 D hBC hL E₀ hE₀0 hE₀1 hE₀2 he₀
  have rels₀ := conjTorusIdx4_rels E₀ D hL
  obtain ⟨w, hw⟩ := rho_normalize_t230 (conjTorusIdx4 E₀ hρC)
    (fun x => DFunLike.congr_fun rels₀.rho_cube x) (T₀.1.trans (phiR_gen0_t230 h230))
    (T₀.2.1.trans (phiR_gen1_t230 h230)) (T₀.2.2.1.trans (by rw [phiR_gen2_t230 h230]))
  let v₁ : Torus (Type230.k s) := (𝔤 s 1) + tor230 s w 0 0
  let e₁ : C := Additive.toMul (E₀ v₁)
  have he₁ : e₁ * e₁ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₀ v₁ + E₀ v₁ = Additive.ofMul aC
    rw [← map_add, show v₁ + v₁ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₁]
      rw [show (𝔤 s 1) + tor230 s w 0 0 + ((𝔤 s 1) + tor230 s w 0 0) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor230 s w 0 0 by module, two_zsmul_tor230, add_zero],
      map_zsmul, hE₀1, two_zsmul, ← ofMul_mul, he₀]
  have hnorm₁ : Additive.ofMul e₁ + Additive.ofMul (conjBy hρC e₁) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₁)) = -Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₁) = E₀ (conjTorusIdx4 E₀ hρC v₁) :=
      ofMul_conjBy_toMul_Idx4 E₀ hρC v₁
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₁)) =
        E₀ (conjTorusIdx4 E₀ hρC (conjTorusIdx4 E₀ hρC v₁)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₀ hρC, ← h1]
      rfl
    rw [h1, h2, show Additive.ofMul e₁ = E₀ v₁ from rfl, ← map_add, ← map_add, hw, map_neg,
      hE₀0]
  obtain ⟨E₁, hE₁0, hE₁1, hE₁2⟩ := exists_torusBasis_t131_of_data D hBC hC hrel hL hcyc he₁
  have T₁ := transport_t131 D hBC hL E₁ hE₁0 hE₁1 hE₁2 he₁
  have rels₁ := conjTorusIdx4_rels E₁ D hL
  have hR2₁ := conjTorus_ρ_two_t131 D hBC hL E₁ hE₁0 hE₁1 hE₁2 hnorm₁
  obtain ⟨x, -, hUx, hUx', -, -⟩ := lifts_t131 h230 _ _ _ _ rels₁ T₁.1 T₁.2.1 hR2₁
    T₁.2.2.2.1 T₁.2.2.2.2.1 T₁.2.2.2.2.2.1 T₁.2.2.2.2.2.2.1 T₁.2.2.2.2.2.2.2.1
    T₁.2.2.2.2.2.2.2.2
  have hR₁ : conjTorusIdx4 E₁ hρC = (Type230.action h230).φρ :=
    torus_endo_ext_Idx4 _ _ fun j => by
      fin_cases j
      · exact T₁.1
      · exact T₁.2.1
      · exact hR2₁
  have hUt₁ : ∀ a b c : ℤ, conjTorusIdx4 E₁ hu (tor230 s a b c) = tor230 s a c b := fun a b c => by
    rw [dev_tor230 _ _ T₁.2.2.2.1 hUx hUx', phiU_tor230 h230]
  let v₂ : Torus (Type230.k s) := (𝔤 s 1) + tor230 s 0 0 x
  let e₂ : C := Additive.toMul (E₁ v₂)
  have he₂ : e₂ * e₂ = aC := by
    apply Additive.ofMul.injective
    rw [ofMul_mul]
    change E₁ v₂ + E₁ v₂ = Additive.ofMul aC
    rw [← map_add, show v₂ + v₂ = (2 : ℤ) • (𝔤 s 1) by
      simp only [v₂]
      rw [show (𝔤 s 1) + tor230 s 0 0 x + ((𝔤 s 1) + tor230 s 0 0 x) =
        (2 : ℤ) • (𝔤 s 1) + (2 : ℤ) • tor230 s 0 0 x by module, two_zsmul_tor230, add_zero],
      map_zsmul, hE₁1, two_zsmul, ← ofMul_mul, he₁]
  have hRv₂ : conjTorusIdx4 E₁ hρC v₂ = (𝔤 s 2) + tor230 s 0 x x := by
    simp only [v₂, map_add, hR₁, phiR_gen1_t230 h230, phiR_tor230 h230, zero_add]
  have hnorm₂ : Additive.ofMul e₂ + Additive.ofMul (conjBy hρC e₂) +
      Additive.ofMul (conjBy hρC (conjBy hρC e₂)) = -Additive.ofMul cC := by
    have h1 : Additive.ofMul (conjBy hρC e₂) = E₁ (conjTorusIdx4 E₁ hρC v₂) :=
      ofMul_conjBy_toMul_Idx4 E₁ hρC v₂
    have h2 : Additive.ofMul (conjBy hρC (conjBy hρC e₂)) =
        E₁ (conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂)) := by
      rw [← ofMul_conjBy_toMul_Idx4 E₁ hρC, ← h1]
      rfl
    have hsum : v₂ + conjTorusIdx4 E₁ hρC v₂ +
        conjTorusIdx4 E₁ hρC (conjTorusIdx4 E₁ hρC v₂) = -(𝔤 s 0) := by
      rw [hRv₂, map_add, hR₁, phiR_gen2_t230 h230, phiR_tor230 h230]
      have hz : tor230 s 0 0 x + tor230 s 0 x x + tor230 s 0 x (x + x) = 0 := by
        simp only [tor230_add]
        exact (tor230_congr (by norm_num) ⟨-x, by ring⟩ ⟨-(2 * x), by ring⟩).trans tor230_zero
      simp only [v₂]
      linear_combination (norm := module) hz
    rw [h1, h2, show Additive.ofMul e₂ = E₁ v₂ from rfl, ← map_add, ← map_add, hsum, map_neg,
      hE₁0]
  have hue₂ : Additive.ofMul (conjBy hu e₂) =
      (-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • Additive.ofMul cC +
        Additive.ofMul (conjBy hρC e₂) := by
    rw [ofMul_conjBy_toMul_Idx4 E₁ hu v₂, ofMul_conjBy_toMul_Idx4 E₁ hρC v₂, hRv₂,
      show (-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • Additive.ofMul cC =
        E₁ ((-2 * Type120.FV (s + 4) + 2 * 2 ^ s : ℤ) • (𝔤 s 0)) by rw [map_zsmul, hE₁0],
      ← map_add]
    congr 1
    simp only [v₂, map_add]
    rw [hUx, hUt₁, phiU_gen1_exact_t230 h230]
    have hz : tor230 s 0 0 x + tor230 s 0 x 0 = tor230 s 0 x x := by
      rw [tor230_add]
      congr 1 <;> ring
    rw [add_assoc, hz]
    module
  obtain ⟨E₂, hE₂0, hE₂1, hE₂2⟩ := exists_torusBasis_t131_of_data D hBC hC hrel hL hcyc he₂
  have T₂ := transport_t131 D hBC hL E₂ hE₂0 hE₂1 hE₂2 he₂
  have rels₂ := conjTorusIdx4_rels E₂ D hL
  have hR2₂ := conjTorus_ρ_two_t131 D hBC hL E₂ hE₂0 hE₂1 hE₂2 hnorm₂
  have hUe₂ : conjTorusIdx4 E₂ hu (𝔤 s 1) = (Type230.action h230).φu (𝔤 s 1) := by
    have h1 : E₂.symm (Additive.ofMul e₂) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E₂).mpr hE₂1.symm
    have h2 : E₂.symm (Additive.ofMul (conjBy hρC e₂)) = (𝔤 s 2) :=
      (AddEquiv.symm_apply_eq E₂).mpr hE₂2.symm
    have h0 : E₂.symm (Additive.ofMul cC) = (𝔤 s 0) := (AddEquiv.symm_apply_eq E₂).mpr hE₂0.symm
    rw [← h1, conjTorusIdx4_apply_symm, show conjBy (hL D.u_mem_L) e₂ = conjBy hu e₂ from rfl,
      hue₂, map_add, map_zsmul, h0, h2, h1, phiU_gen1_exact_t230 h230]
    module
  rcases images_t131 h230 (Type231.data s) _ _ _ _ rels₂ T₂.1 T₂.2.1 hR2₂ T₂.2.2.2.1
      T₂.2.2.2.2.1 T₂.2.2.2.2.2.1 T₂.2.2.2.2.2.2.1 T₂.2.2.2.2.2.2.2.1 T₂.2.2.2.2.2.2.2.2 hUe₂
    with ⟨hV, hW, hU, hR⟩ | ⟨hV, hW, hU, hR⟩
  · exact Or.inl (hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t230 s hs) E₂
      fun j => ⟨DFunLike.congr_fun hV _, DFunLike.congr_fun hW _, DFunLike.congr_fun hU _,
        DFunLike.congr_fun hR _⟩)
  · exact Or.inr (hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t231 s hs) E₂
      fun j => ⟨DFunLike.congr_fun hV _, DFunLike.congr_fun hW _, DFunLike.congr_fun hU _,
        DFunLike.congr_fun hR _⟩)

end CFSG.CGT.Stroth77
