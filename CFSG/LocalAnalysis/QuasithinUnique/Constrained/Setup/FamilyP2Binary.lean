module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section SixSpace

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]

theorem pow_eight_eq_one_of_pow_sixteen (hW : Module.finrank (ZMod 2) W ≤ 6)
    (g : W ≃ₗ[ZMod 2] W) (hg : g ^ 16 = 1) : g ^ 8 = 1 := by
  let G : Module.End (ZMod 2) W := (g : W →ₗ[ZMod 2] W)
  have h2 : (1 : Module.End (ZMod 2) W) + 1 = 0 := LinearMap.ext fun x => by
    simp [add_self_eq_zero_of_zmod_two]
  have hdbl : ∀ X : Module.End (ZMod 2) W, X + X = 0 := fun X => by
    calc X + X = ((1 : Module.End (ZMod 2) W) + 1) * X := by rw [add_mul, one_mul]
      _ = 0 := by rw [h2, zero_mul]
  have hsq : ∀ X : Module.End (ZMod 2) W, (1 + X) ^ 2 = 1 + X ^ 2 := fun X => by
    calc (1 + X) ^ 2 = 1 + (X + X) + X ^ 2 := by noncomm_ring
      _ = 1 + X ^ 2 := by rw [hdbl, add_zero]
  have hfrob : ∀ (X : Module.End (ZMod 2) W) (k : ℕ), (1 + X) ^ (2 ^ k) = 1 + X ^ (2 ^ k) := by
    intro X k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, hsq, ← pow_mul, ← pow_succ]
  have hpow : ∀ k : ℕ, ((g ^ k : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) = G ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl
  let N : Module.End (ZMod 2) W := G - 1
  have hGN : G = 1 + N := by simp [N]
  have hN16 : N ^ 16 = 0 := by
    have h1 : G ^ 16 = 1 := by rw [← hpow]; rw [hg]; rfl
    have h3 := hfrob N 4
    rw [← hGN] at h3
    norm_num at h3
    rw [h1] at h3
    exact (add_left_cancel (a := (1 : Module.End (ZMod 2) W)) (by simpa using h3.symm))
  have hnil : IsNilpotent N := ⟨16, hN16⟩
  have hNn : N ^ Module.finrank (ZMod 2) W = 0 := by
    have h1 := hnil.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly N
    rw [h1] at h2
    simpa using h2
  have hN8 : N ^ 8 = 0 := pow_eq_zero_of_le (by omega) hNn
  have hG8 : G ^ 8 = 1 := by
    have h3 := hfrob N 3
    rw [← hGN] at h3
    norm_num at h3
    rw [h3, hN8, add_zero]
  refine LinearEquiv.ext fun x => ?_
  have := congrArg (fun T : Module.End (ZMod 2) W => T x) (hpow 8)
  simp only [hG8] at this
  exact this

theorem prime_factor_bound' : ∀ p ∈ List.range 65, p.Prime → 5 ≤ p →
    ∀ n ∈ List.range 7, ∀ i ∈ List.range n, p ∣ 2 ^ n - 2 ^ i → p = 5 ∨ p = 7 ∨ p = 31 := by
  decide +kernel

theorem prime_factor_bound : ∀ n, n ≤ 6 → ∀ i, i < n → ∀ p, p ≤ 64 → p.Prime → 5 ≤ p →
    p ∣ 2 ^ n - 2 ^ i → p = 5 ∨ p = 7 ∨ p = 31 := by
  intro n hn i hi p hp hpp h5 hd
  exact prime_factor_bound' p (List.mem_range.2 (by omega)) hpp h5 n (List.mem_range.2 (by omega))
    i (List.mem_range.2 hi) hd

theorem card_automorphisms_binary {n : ℕ} (hn : Module.finrank (ZMod 2) W = n) :
    Nat.card (W ≃ₗ[ZMod 2] W) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hn
  let eW : (W ≃ₗ[ZMod 2] W) ≃* GL (Fin n) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr eW.toEquiv, Matrix.card_GL_field]
  simp

def c31 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 31) := ⟨!![0, 30; 1, 4], by decide +kernel⟩

theorem c31_pow_eight : ((c31 ^ 8 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 31)) :
    Matrix (Fin 2) (Fin 2) (ZMod 31)) = !![3, 17; 14, 28] := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show (!![0, 30; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 8 = _
  decide +kernel

theorem c31_pow_sixteen : ((c31 ^ 16 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 31)) :
    Matrix (Fin 2) (Fin 2) (ZMod 31)) = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show (!![0, 30; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 16 = _
  decide +kernel

theorem zmod31_seventeen_ne_zero : (17 : ZMod 31) ≠ 0 := by decide

theorem p2_exists_order_sixteen [Fact (Nat.Prime 31)] :
    ∃ g : projectiveSL 2 (ZMod 31), orderOf g = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : c31 ^ 8 ∉ scalars 2 (ZMod 31) := by
    rintro ⟨c, -, hc⟩
    have h1 := congrFun (congrFun hc 0) 1
    rw [c31_pow_eight] at h1
    simp [Matrix.scalar_apply] at h1
    exact zmod31_seventeen_ne_zero h1
  have hB : c31 ^ 16 ∈ scalars 2 (ZMod 31) := by
    refine ⟨-1, neg_one_sq, ?_⟩
    rw [c31_pow_sixteen]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  refine ⟨proj 2 (ZMod 31) c31, orderOf_eq_prime_pow (p := 2) (n := 3) ?_ ?_⟩
  · show ¬ (proj 2 (ZMod 31) c31) ^ 8 = 1
    rw [← map_pow, proj_eq_one_iff]
    exact hA
  · show (proj 2 (ZMod 31) c31) ^ 16 = 1
    rw [← map_pow, proj_eq_one_iff]
    exact hB

end SixSpace

theorem p2_binary_six_space {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (hW : Module.finrank (ZMod 2) W ≤ 6)
    (φ : projectiveSL 2 (ZMod p) →* (W ≃ₗ[ZMod 2] W)) (hφ : Function.Injective φ) :
    p = 5 ∨ p = 7 := by
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hdvd : p ∣ Nat.card (projectiveSL 2 (ZMod p)) := by
    rw [p2_card hp2, Nat.mul_div_assoc _ (two_dvd_sq_sub_one_of_odd hodd)]
    exact Dvd.intro _ rfl
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (φ g) = p := by rw [orderOf_injective φ hφ g, hg]
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have hlag : p ∣ Nat.card (W ≃ₗ[ZMod 2] W) := hord ▸ orderOf_dvd_natCard (φ g)
  rw [card_automorphisms_binary (n := Module.finrank (ZMod 2) W) rfl] at hlag
  obtain ⟨i, -, hpi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 hlag
  have hi : (i : ℕ) < Module.finrank (ZMod 2) W := i.2
  have hpos : 0 < 2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ) :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)
  have hp64 : p ≤ 64 := by
    refine (Nat.le_of_dvd hpos hpi).trans ?_
    have h6 : 2 ^ Module.finrank (ZMod 2) W ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hW
    exact ((Nat.sub_le _ _).trans h6).trans (by norm_num)
  rcases prime_factor_bound _ hW i hi p hp64 hp hp5 hpi with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    subst h
    obtain ⟨h16, hh16⟩ := p2_exists_order_sixteen
    have h1 : (φ h16) ^ 16 = 1 := by
      rw [← map_pow, ← hh16, pow_orderOf_eq_one, map_one]
    have h8 := pow_eight_eq_one_of_pow_sixteen hW (φ h16) h1
    have h2 : orderOf (φ h16) ∣ 8 := orderOf_dvd_of_pow_eq_one h8
    rw [orderOf_injective φ hφ h16, hh16] at h2
    omega

end CFSG.QuasithinUnique.Setup.Family