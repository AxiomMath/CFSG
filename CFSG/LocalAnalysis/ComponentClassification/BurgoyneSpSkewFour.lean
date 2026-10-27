module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

@[expose] def skStep {R : Type} [CommRing R] (e : R) (v w : R × R × R × R) : R × R × R × R :=
  (v.1 * w.1 + e * v.2.1 * w.2.1 - v.2.2.1 * w.2.2.1 - e * v.2.2.2 * w.2.2.2,
    v.1 * w.2.1 + v.2.1 * w.1 - v.2.2.1 * w.2.2.2 - v.2.2.2 * w.2.2.1,
    v.1 * w.2.2.1 + e * v.2.1 * w.2.2.2 + v.2.2.1 * w.1 + e * v.2.2.2 * w.2.1,
    v.1 * w.2.2.2 + v.2.1 * w.2.2.1 + v.2.2.1 * w.2.1 + v.2.2.2 * w.1)

@[expose] def skIter {R : Type} [CommRing R] (e : R) (w : R × R × R × R) : ℕ → R × R × R × R
  | 0 => (1, 0, 0, 0)
  | n + 1 => skStep e (skIter e w n) w

theorem zmod_three_skIter : ∀ e x₀ x₁ y₀ y₁ : ZMod 3, e ^ 2 = 1 →
    skIter e (x₀, x₁, y₀, y₁) 9 = (x₀, x₁, y₀, y₁) := by
  decide

abbrev skMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (v : R × R × R × R) :
    S × S × S × S :=
  (f v.1, f v.2.1, f v.2.2.1, f v.2.2.2)

theorem skMap_skIter {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : R)
    (w : R × R × R × R) (n : ℕ) : skMap f (skIter e w n) = skIter (f e) (skMap f w) n := by
  induction n with
  | zero => simp [skIter]
  | succ n ih =>
    rw [skIter, skIter, ← ih]
    simp only [skStep, skMap, map_add, map_sub, map_mul]

theorem skIter_nine [Finite K] (h3 : Nat.card K = 3) {e : K} (he : e ^ 2 = 1)
    (w : K × K × K × K) : skIter e w 9 = w := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set f := FiniteField.ringEquivOfCardEq hc
  have hinj : Function.Injective (skMap f.toRingHom) := by
    intro v v' h
    simp only [skMap, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3', h4⟩ := h
    exact Prod.ext (f.injective h1) (Prod.ext (f.injective h2)
      (Prod.ext (f.injective h3') (f.injective h4)))
  apply hinj
  rw [skMap_skIter]
  exact zmod_three_skIter _ _ _ _ _ (by rw [← map_pow, he, map_one])

abbrev skEmb (g : Matrix (Fin r) (Fin r) K) (v : K × K × K × K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  epsM (-1) (v.1 • 1 + v.2.1 • g) (v.2.2.1 • 1 + v.2.2.2 • g)

theorem skEmb_mul {g : Matrix (Fin r) (Fin r) K} {e : K} (hg : g * g = e • 1)
    (v w : K × K × K × K) : skEmb g v * skEmb g w = skEmb g (skStep e v w) := by
  rw [skEmb, skEmb, epsM_mul, skEmb, skStep]
  congr 1 <;>
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hg, smul_smul]
    module

theorem skEmb_pow {g : Matrix (Fin r) (Fin r) K} {e : K} (hg : g * g = e • 1)
    (w : K × K × K × K) (n : ℕ) : skEmb g w ^ n = skEmb g (skIter e w n) := by
  induction n with
  | zero =>
    rw [pow_zero, skIter, skEmb, epsM]
    simp [fromBlocks_one]
  | succ n ih => rw [pow_succ, ih, skEmb_mul hg, skIter]

theorem exists_eq_of_commute_fourMat (h2 : (2 : K) ≠ 0) (k : Fin 3)
    {P : Matrix (Fin 2) (Fin 2) K} (hP : P * fourMat K k = fourMat K k * P) :
    ∃ x₀ x₁ : K, P = x₀ • 1 + x₁ • fourMat K k := by
  have e00 := congrFun (congrFun hP 0) 0
  have e01 := congrFun (congrFun hP 0) 1
  have e10 := congrFun (congrFun hP 1) 0
  fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  · have h01 : P 0 1 = 0 := by
      have : (2 : K) * P 0 1 = 0 := by linear_combination -e01
      exact (mul_eq_zero.1 this).resolve_left h2
    have h10 : P 1 0 = 0 := by
      have : (2 : K) * P 1 0 = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_left h2
    refine ⟨(P 0 0 + P 1 1) / 2, (P 0 0 - P 1 1) / 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h01, h10] <;> field_simp <;> ring
  · refine ⟨P 0 0, P 0 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp <;>
      first | linear_combination -e00 | linear_combination e10
  · refine ⟨P 0 0, P 0 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp <;>
      first | linear_combination -e00 | linear_combination e10

theorem conjAut_pow_eight_of_commute_skewNs [Finite K] (h3 : Nat.card K = 3) (k : Fin 3)
    {D : gsp 2 K}
    (hDA : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      skewNs 2 K (-1) = skewNs 2 K (-1) * ((D : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hDS : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks (fourMat K k) 0 0 (fourMat K k) = fromBlocks (fourMat K k) 0 0 (fourMat K k) *
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K (D ^ 2 ^ 3) = 1 := by
  have h2 := two_ne_zero_of_three h3
  set M := ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hblk : M = epsM (-1) M.toBlocks₁₁ M.toBlocks₂₁ := eq_epsM_of_commute hDA
  have hG : fromBlocks (fourMat K k) 0 0 (fourMat K k) = epsM (-1) (fourMat K k) 0 := by
    rw [epsM, smul_zero]
  rw [hG, hblk, epsM_mul, epsM_mul] at hDS
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add] at hDS
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 hDS
  obtain ⟨x₀, x₁, hx⟩ := exists_eq_of_commute_fourMat h2 k h11
  obtain ⟨y₀, y₁, hy⟩ := exists_eq_of_commute_fourMat h2 k h21
  have hMe : M = skEmb (fourMat K k) (x₀, x₁, y₀, y₁) := by
    rw [hblk, hx, hy]
  set e : K := if k = 2 then -1 else 1 with he
  have he2 : e ^ 2 = 1 := by
    rw [he]
    split_ifs <;> norm_num
  have h9 : M ^ 9 = M := by
    rw [hMe, skEmb_pow (fourMat_sq k), skIter_nine h3 he2]
  have h8 : M ^ 8 = 1 := by
    have hMi : M * ((D⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc M ^ 8 = M ^ 8 * (M * ((D⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [hMi, Matrix.mul_one]
      _ = M ^ 9 * ((D⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
          rw [← Matrix.mul_assoc, ← pow_succ]
      _ = 1 := by rw [h9, hMi]
  rw [conjAut_eq_one_iff (by norm_num)]
  refine ⟨1, Units.ext ?_⟩
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hM, show 2 ^ 3 = 8 by norm_num, h8, map_one,
    Units.val_one]

theorem skewNs_oddCoreIn_eq_bot_two_three [Finite K] (h3 : Nat.card K = 3)
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) :
    oddCoreIn B (conjAut 2 K (skewNsGsp 2 K hd0)) = ⊥ := by
  have hdm : d = -1 := by
    rcases three_elements h3 d with h | h | h
    · exact absurd h hd0
    · exact absurd (by rw [h, one_pow]) (hd 1)
    · exact h
  subst hdm
  set S₁ := orthLevi (fourMat K 0) (fourMat_orth 0) with hS₁
  set S₂ := orthLevi (fourMat K 1) (fourMat_orth 1) with hS₂
  have hmat : ∀ k : Fin 3, ∀ S : StatedSp 2 K,
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (fourMat K k) 0 0 (fourMat K k) →
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (if k = 2 then (-1 : K) else 1) • 1 := by
    intro k S hS
    rw [hS, fromBlocks_multiply, fourMat_sq]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
  have hcomA : ∀ k : Fin 3, ∀ S : StatedSp 2 K,
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (fourMat K k) 0 0 (fourMat K k) →
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro k S hS
    rw [hS, coe_skewNsGsp, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have h12 : ((S₁ * S₂ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      ((orthLevi (fourMat K 2) (fourMat_orth 2) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hS₁, hS₂, coe_orthLevi, coe_orthLevi, coe_orthLevi,
      fromBlocks_multiply, fourMat_mul]
    simp
  have hm₁ : ((S₁ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (fourMat K 0) 0 0 (fourMat K 0) := coe_orthLevi _ _
  have hm₂ : ((S₂ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (fourMat K 1) 0 0 (fourMat K 1) := coe_orthLevi _ _
  have hm₃ : (((S₁ * S₂ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (fourMat K 2) 0 0 (fourMat K 2) := by
    rw [h12, coe_orthLevi]
  have hS1sq := hmat 0 S₁ hm₁
  have hS2sq := hmat 1 S₂ hm₂
  have hS3sq := hmat 2 _ hm₃
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
    at hS1sq hS2sq hS3sq
  refine oddCoreIn_eq_bot_of_four h3 le_rfl hB hd0 (skewNs_mul_self (-1)) one_ne_zero
    one_ne_zero (neg_ne_zero.2 one_ne_zero) hS1sq hS2sq hS3sq (hcomA 0 _ hm₁) (hcomA 1 _ hm₂) ?_
  rintro S hS D hDA hDS
  refine ⟨3, ?_⟩
  rw [coe_skewNsGsp] at hDA
  rcases hS with rfl | rfl | rfl
  · rw [hm₁] at hDS
    exact conjAut_pow_eight_of_commute_skewNs h3 0 hDA hDS
  · rw [hm₂] at hDS
    exact conjAut_pow_eight_of_commute_skewNs h3 1 hDA hDS
  · rw [hm₃] at hDS
    exact conjAut_pow_eight_of_commute_skewNs h3 2 hDA hDS

end CFSG.ComponentClassification.Burgoyne.Sp
