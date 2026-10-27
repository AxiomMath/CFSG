module

public import CFSG.HardMathSupport.U4FF.ClassInvol
public import CFSG.HardMathSupport.U4FF.ClassTmodIrr

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups


section LocalRank

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem locR_mul_self (a b c : Bool) {g : SL(4, k)} (hg : g * g = 1) :
    locR a b c k g * locR a b c k g = 1 := by
  rw [← map_mul, hg, map_one]

theorem locR_invol_rank_ge (a b c : Bool) (g : SL(4, k)) (hg : g * g = 1) (hne : g ≠ 1) :
    (locData a b c).rk1.r ≤ (locR a b c k g - 1).rank := by
  obtain ⟨P, hP⟩ := involution_conj_a g hg hne
  set M := locR a b c k with hM
  have h1 : M P * M P⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have key : M (P * g * P⁻¹) - 1 = M P * (M g - 1) * M P⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, map_mul, map_mul]
  have hQP : M P⁻¹ * M P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hr : (M (P * g * P⁻¹) - 1).rank = (M g - 1).rank := by
    rw [key]
    exact CFSG.QuasithinUnique.Setup.X7b.rank_conj_eq _ _ _ hQP
  have hv := locValid a b c
  rcases hP with h | h
  · rw [h] at hr
    rw [← hr]
    exact (rank_locMat_a1 a b c hv).ge
  · rw [h] at hr
    rw [← hr]
    refine le_trans hv.2.1.2.2.2.1 (rank_locMat_a2 a b c hv).ge

end LocalRank

section TmodRank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k] [Finite k]
  [CharP k 2] [Algebra K k]

theorem twistHom_ne_one (φ : K →+* k) {t : SU4 K n} (ht1 : t ≠ 1) : twistHom n φ t ≠ 1 := by
  intro h
  apply ht1
  have h1 : ((twistHom n φ t : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) = 1 := by rw [h]; rfl
  rw [twistHom_val] at h1
  have h2 : (((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map φ =
      (1 : Matrix (Fin 4) (Fin 4) K).map φ := by
    rw [h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have h3 := Matrix.map_injective φ.injective h2
  exact Subtype.ext (Units.ext h3)

theorem rank_Tmod_invol_ge (l : Lbl n) {t : SU4 K n} (ht : t * t = 1) (ht1 : t ≠ 1) :
    l.rk1 ≤ (Tmod K l k t - 1).rank := by
  classical
  set κ : Fin n → Type := fun i => Fin (locM (l.a i) (l.b i) (l.c i)) with hκ
  set z : (i : Fin n) → Matrix (κ i) (κ i) k := fun i =>
    locR (l.a i) (l.b i) (l.c i) k (twistHom n (frobTw K k i) t) with hz
  have hzz : ∀ i, z i * z i = 1 := fun i =>
    locR_mul_self _ _ _ (by rw [← map_mul, ht, map_one])
  have hfrob : ∀ i : Fin n, Function.Injective (frobTw K k i) := fun i =>
    (frobTw K k i).injective
  have hne : ∀ i, twistHom n (frobTw K k i) t ≠ 1 := fun i => twistHom_ne_one _ ht1
  have h := CFSG.HardMathSupport.U4FF.rank_kronDep_sub_one (κ := κ) z hzz
  have hT : Tmod K l k t = kronDep κ z := rfl
  have hloc : ∀ i : Fin n, Fintype.card (κ i) - 2 * (z i - 1).rank ≤
      locF1 (l.a i) (l.b i) (l.c i) := by
    intro i
    have h1 := locR_invol_rank_ge (l.a i) (l.b i) (l.c i) _ (by
      rw [← map_mul, ht, map_one]) (hne i)
    have h2 := (locValid (l.a i) (l.b i) (l.c i)).2.1.2.2.1
    have h3 : Fintype.card (κ i) = locM (l.a i) (l.b i) (l.c i) := Fintype.card_fin _
    have h4 : (locData (l.a i) (l.b i) (l.c i)).rk1.r ≤ (z i - 1).rank := h1
    omega
  have hprod : ∏ i, (Fintype.card (κ i) - 2 * (z i - 1).rank) ≤ l.fix1 :=
    Finset.prod_le_prod' fun i _ => hloc i
  have hdim : ∏ i, Fintype.card (κ i) = l.dim := by
    simp only [hκ, Fintype.card_fin]
    rfl
  have h2 := l.two_mul_rk1
  rw [hT]
  omega

end TmodRank

end CFSG.HardMathSupport.U4FF
