module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.Sec8

open scoped commutatorElement

theorem eq_one_or_eq_neg_one_of_mul_self {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Matrix (Fin 2) (Fin 2) (ZMod p)} (hM : M * M = 1) (hdet : M.det = 1) :
    M = 1 ∨ M = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have e : ∀ i j, (M * M) i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := fun i j => by
    rw [hM]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e01 e10
  rw [Matrix.det_fin_two] at hdet
  have hs : (M 0 0 + M 1 1) * M 0 0 = 2 := by linear_combination e00 + hdet
  have hs' : (M 0 0 + M 1 1) * M 1 1 = 2 := by linear_combination e11 + hdet
  have hne : M 0 0 + M 1 1 ≠ 0 := fun h => h2 (by rw [← hs, h, zero_mul])
  have hβ : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hne
  have hγ : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hne
  have hαδ : M 1 1 = M 0 0 := mul_left_cancel₀ hne (hs'.trans hs.symm)
  have hα2 : M 0 0 * M 0 0 = 1 := by rw [← e00, hβ, zero_mul, add_zero]
  rcases mul_self_eq_one_iff.mp hα2 with h | h
  · left
    rw [Matrix.eta_fin_two M, hβ, hγ, hαδ, h, Matrix.one_fin_two]
  · right
    have h' : M 0 0 + 1 = 0 := by rw [h]; exact neg_add_cancel 1
    have hM1 : M + 1 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hβ, hγ, hαδ, h']
    exact eq_neg_of_add_eq_zero_left hM1

theorem exists_det_aux {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {W : Type*} [CommGroup W]
    [Finite W] [Module (ZMod p) (Additive W)] (hW : Nat.card W = p ^ 2) {K : Type*} [Group K]
    (act : K →* MulAut W) : ∃ δ : K →* ZMod p, ∀ k : K, (∀ w, act k (act k w) = w) →
      δ k = 1 → (∀ w, act k w = w) ∨ (∀ w, act k w = w⁻¹) := by
  classical
  let f : K → (Additive W →ₗ[ZMod p] Additive W) := fun k =>
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (act k).toMonoidHom)
  have hf : ∀ k x, (f k x).toMul = act k x.toMul := fun k x => rfl
  let ρ : K →* Module.End (ZMod p) (Additive W) :=
    { toFun := f
      map_one' := LinearMap.ext fun x => Additive.toMul.injective (by
        rw [hf, map_one]; rfl)
      map_mul' := fun g h => LinearMap.ext fun x => Additive.toMul.injective (by
        rw [hf, Module.End.mul_apply, hf, hf, map_mul]; rfl) }
  have : Fintype (Additive W) := Fintype.ofFinite _
  have hcard : Fintype.card (Additive W) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, ← hW]
    exact Nat.card_congr Additive.toMul
  have hfin : Module.finrank (ZMod p) (Additive W) = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive W)
    rw [hcard, ZMod.card] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  refine ⟨LinearMap.det.comp ρ, fun k hk2 hdet => ?_⟩
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive W) hfin
  set M := LinearMap.toMatrix b b (ρ k) with hMdef
  have hL2 : ρ k * ρ k = 1 := LinearMap.ext fun x => Additive.toMul.injective (by
    rw [Module.End.mul_apply]
    change act k (act k x.toMul) = x.toMul
    exact hk2 _)
  have hM2 : M * M = 1 := by
    rw [hMdef, ← LinearMap.toMatrix_mul, hL2, LinearMap.toMatrix_one]
  have hMdet : M.det = 1 := by
    rw [hMdef, LinearMap.det_toMatrix]
    exact hdet
  rcases eq_one_or_eq_neg_one_of_mul_self hp2 hM2 hMdet with h | h
  · have hρ : ρ k = 1 := (LinearMap.toMatrix b b).injective (by
      rw [← hMdef, h, LinearMap.toMatrix_one])
    exact Or.inl fun w =>
      congrArg (fun L : Module.End (ZMod p) (Additive W) => (L (Additive.ofMul w)).toMul) hρ
  · have hρ : ρ k = -1 := (LinearMap.toMatrix b b).injective (by
      rw [← hMdef, h, map_neg, LinearMap.toMatrix_one])
    exact Or.inr fun w =>
      congrArg (fun L : Module.End (ZMod p) (Additive W) => (L (Additive.ofMul w)).toMul) hρ

variable {G : Type} [Group G]

theorem exists_det [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Subgroup G}
    (hVab : IsMulCommutative V) (hVp : ∀ v ∈ V, v ^ p = 1) (hVc : Nat.card V = p ^ 2) :
    ∃ δ : Subgroup.normalizer (V : Set G) →* ZMod p, ∀ g : Subgroup.normalizer (V : Set G),
      (∀ v ∈ V, (g : G) * ((g : G) * v * (g : G)⁻¹) * (g : G)⁻¹ = v) → δ g = 1 →
      (∀ v ∈ V, (g : G) * v * (g : G)⁻¹ = v) ∨ (∀ v ∈ V, (g : G) * v * (g : G)⁻¹ = v⁻¹) := by
  let _inst1 : CommGroup V := { (inferInstance : Group V) with mul_comm := hVab.is_comm.comm }
  let _inst2 : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hVp _ x.toMul.2)
  obtain ⟨δ, hδ⟩ := exists_det_aux hp2 (W := V) hVc V.normalizerMonoidHom
  refine ⟨δ, fun g hg2 hg => ?_⟩
  rcases hδ g (fun w => Subtype.ext (hg2 w w.2)) hg with h | h
  · exact Or.inl fun v hv => congrArg Subtype.val (h ⟨v, hv⟩)
  · exact Or.inr fun v hv => congrArg Subtype.val (h ⟨v, hv⟩)

theorem det_eq_one_of_mem_commutator {p : ℕ} {N K : Subgroup G} (δ : N →* ZMod p) (hKN : K ≤ N)
    {y : G} (hy : y ∈ ⁅K, K⁆) (hyN : y ∈ N) : δ ⟨y, hyN⟩ = 1 := by
  set D : Subgroup G := (δ.toHomUnits.ker).map N.subtype with hD
  have hKD : ⁅K, K⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro k₁ h₁ k₂ h₂
    refine ⟨⁅(⟨k₁, hKN h₁⟩ : N), ⟨k₂, hKN h₂⟩⁆, MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨n, hn, hny⟩ := hKD hy
  have hn' : n = ⟨y, hyN⟩ := Subtype.ext hny
  rw [← hn']
  have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hn)
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h1

end CFSG.Goldschmidt.Sec8
