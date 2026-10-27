module

public import CFSG.LieType.SeitzGeneration.HyperExParabolic
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley CFSG.Open

section SL2

variable {K : Type*} [Field K]

@[expose] def uSLHom (K : Type*) [Field K] : Multiplicative K →* SL2 K where
  toFun c := uSL (Multiplicative.toAdd c)
  map_one' := by refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]
  map_mul' a b := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem uSL_one_ne_one' : (uSL 1 : SL2 K) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [coe_uSL] at h'

theorem eq_one_of_commute_uSL_vSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : SL2 K}
    (hxp : x ^ p = 1) (hu : Commute x (uSL 1)) (hv : Commute x (vSL 1)) : x = 1 := by
  have hu' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) hu.eq
  have hv' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) hv.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL] at hu' hv'
  set M := (x : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hdet : M.det = 1 := x.2
  have hpow : M ^ p = 1 := by
    have h := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) hxp
    simpa [hMdef] using h
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two] at hu' hv'
  have e00 := congrFun (congrFun hu' 0) 0
  have e01 := congrFun (congrFun hu' 0) 1
  have f00 := congrFun (congrFun hv' 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 f00
  have h10 : M 1 0 = 0 := by linear_combination -e00
  have h11 : M 1 1 = M 0 0 := by linear_combination -e01
  have h01 : M 0 1 = 0 := by linear_combination f00
  have hM : M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]
  rw [Matrix.det_fin_two, h10, h01, h11, mul_zero, sub_zero] at hdet
  rw [hM, smul_pow, one_pow] at hpow
  have hap : M 0 0 ^ p = 1 := by
    have := congrFun (congrFun hpow 0) 0
    simpa using this
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have ha1 : M 0 0 = 1 := by
    rw [hk, pow_succ, pow_mul, sq, hdet, one_pow, one_mul] at hap
    exact hap
  apply Subtype.ext
  change M = 1
  rw [hM, ha1, one_smul]

end SL2

theorem exists_cube_of_four_sl2 {C : Type*} [Group C] {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) (ρ : Fin 4 → SL2 K →* C)
    (hinj : ∀ i, Function.Injective (ρ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) :
    ∃ E : Subgroup C, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∀ x ∈ E, ∀ A, Commute x (ρ 3 A) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hdet, hxp, hx1⟩ := exists_sl2_order hp hpq
  let g : SL2 K := ⟨x, hdet⟩
  have hgp : g ^ p = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hxp)
  have hg1 : g ≠ 1 := fun h => hx1 (by simpa [g] using congrArg Subtype.val h)
  have hog : orderOf g = p := orderOf_eq_prime hgp hg1
  have key : ∀ i (a : ℤ), (∀ A, Commute (ρ i (g ^ a)) (ρ i A)) → (p : ℤ) ∣ a := by
    intro i a h
    have hcomm' : ∀ A, Commute (g ^ a) A := fun A =>
      hinj i (by rw [map_mul, map_mul]; exact (h A).eq)
    have hga : g ^ a = 1 := by
      refine eq_one_of_commute_uSL_vSL hp hp2 ?_ (hcomm' _) (hcomm' _)
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hgp, one_zpow]
    rw [← hog]
    exact orderOf_dvd_iff_zpow_eq_one.2 hga
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  obtain ⟨E, hE, hc, hgen, -, -, -⟩ := exists_cube_of_three hp
    (hcomm 0 1 h01 g g) (hcomm 0 2 h02 g g) (hcomm 1 2 h12 g g)
    (by rw [← map_pow, hgp, map_one]) (by rw [← map_pow, hgp, map_one])
    (by rw [← map_pow, hgp, map_one]) (by
      intro a b c habc
      have h0 : (p : ℤ) ∣ a := by
        refine key 0 a fun A => ?_
        have he : ρ 0 (g ^ a) = (ρ 1 g ^ b * ρ 2 g ^ c)⁻¹ := by
          rw [map_zpow]
          exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact habc)
        rw [he]
        refine Commute.inv_left (Commute.mul_left ?_ ?_)
        · exact ((hcomm 0 1 h01 A g).symm).zpow_left b
        · exact ((hcomm 0 2 h02 A g).symm).zpow_left c
      have ha : ρ 0 g ^ a = 1 := by
        obtain ⟨k, hk⟩ := h0
        rw [hk, ← map_zpow, _root_.zpow_mul, zpow_natCast, hgp, one_zpow, map_one]
      rw [ha, one_mul] at habc
      have h1 : (p : ℤ) ∣ b := by
        refine key 1 b fun A => ?_
        have he : ρ 1 (g ^ b) = (ρ 2 g ^ c)⁻¹ := by
          rw [map_zpow]
          exact eq_inv_of_mul_eq_one_left habc
        rw [he]
        exact Commute.inv_left (((hcomm 1 2 h12 A g).symm).zpow_left c)
      have hb : ρ 1 g ^ b = 1 := by
        obtain ⟨k, hk⟩ := h1
        rw [hk, ← map_zpow, _root_.zpow_mul, zpow_natCast, hgp, one_zpow, map_one]
      rw [hb, one_mul] at habc
      refine ⟨h0, h1, ?_⟩
      refine key 2 c fun A => ?_
      rw [map_zpow, habc]
      exact Commute.one_left _)
  refine ⟨E, hE, hc, fun y hy A => ?_⟩
  obtain ⟨i, j, k, rfl⟩ := hgen y hy
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  exact (((hcomm 0 3 h03 g A).zpow_left i).mul_left ((hcomm 1 3 h13 g A).zpow_left j)).mul_left
    ((hcomm 2 3 h23 g A).zpow_left k)

theorem normalizesRSub_of_commute_sl2 {d : TauCeti.ValidLieTypeIndex} {K : Type} [Field K]
    [CharP K d.1.characteristic] (ρ : SL2 K →* Cat d) (hρ : Function.Injective ρ)
    {E : Subgroup (Cat d)} (hE : ∀ x ∈ E, ∀ A, Commute x (ρ A)) : NormalizesRSub d E := by
  have : Fact d.1.characteristic.Prime := ⟨TauCeti.ValidLieTypeIndex.characteristic_prime d⟩
  refine ⟨(ρ.comp (uSLHom K)).range, ?_, ?_, ?_⟩
  · intro h
    have h1 : ρ (uSL 1) ∈ (ρ.comp (uSLHom K)).range := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact uSL_one_ne_one' (hρ (h1.trans (map_one ρ).symm))
  · have hK : IsPGroup d.1.characteristic (Multiplicative K) := fun c => ⟨1, by
      rw [pow_one, ← ofAdd_toAdd c, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl⟩
    exact hK.of_surjective _ (ρ.comp (uSLHom K)).rangeRestrict_surjective
  · intro x hx
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := hz
      change x * ρ (uSL (Multiplicative.toAdd c)) * x⁻¹ ∈ _
      rw [(hE x hx _).eq, mul_inv_cancel_right]
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨ρ (uSL (Multiplicative.toAdd c)), ⟨c, rfl⟩, ?_⟩
      change x * ρ (uSL (Multiplicative.toAdd c)) * x⁻¹ = _
      rw [(hE x hx _).eq, mul_inv_cancel_right]
      rfl

end CFSG.LieType.SeitzGeneration
