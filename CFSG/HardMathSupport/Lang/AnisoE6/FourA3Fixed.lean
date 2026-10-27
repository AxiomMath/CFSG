module

public import CFSG.HardMathSupport.Lang.AnisoE6.FourA3
public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2Fixed
public import CFSG.RankThree.PartOne.KE.E6A3Sigma

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

@[expose] def ωγFold : List (Fin TwistTag.E6.foldedTag.rank) :=
  [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

@[expose] def ωγWord : List (Fin Tag.E6.rank) := (ωγFold.map TwistTag.E6.orbitWord).flatten

theorem ωγWord_eq : ωγWord =
    [e6Index 2, e6Index 4, e6Index 0, e6Index 5, e6Index 3, e6Index 2, e6Index 4, e6Index 3] := by
  decide +kernel

section Fixed4


theorem ωγWord_smul_e1 :
    (coxeterSystem Tag.E6).wordProd ωγWord • (Pi.single (e6Index 1) 1 : Fin Tag.E6.rank → ℤ) =
      gammaVec := by
  simp only [ωγWord_eq, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul, gammaVec]
  decide +kernel

variable (K : Type) [Field K]

theorem nElt_flatten_mem (ωf : List (Fin TwistTag.E6.foldedTag.rank)) :
    nElt TwistTag.E6.tag K (ωf.map TwistTag.E6.orbitWord).flatten ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  rw [nElt_flatten]
  refine list_prod_mem fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
  exact graphFixedRootGroup_le _ _ _
    (canonicalRep_orbitReflection_mem_graphFixedRootGroup (t := TwistTag.E6) (σ := RingHom.id K) a)

theorem pinnedX_gamma_mem_fixed (c : K) :
    pinnedX Tag.E6 K gammaVec c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ∧
    pinnedX Tag.E6 K (-gammaVec) c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  have hn : nElt Tag.E6 K ωγWord ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    nElt_flatten_mem K ωγFold
  obtain ⟨ε, hε, hx⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ωγWord
    (isRoot_single Tag.E6 (e6Index 1))
  obtain ⟨ε', hε', hy⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ωγWord
    (isRoot_neg_single Tag.E6 (e6Index 1))
  have hxy := xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero (ε * c)
  have hxy' := xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero (ε' * c)
  constructor
  · have h := hx (ε * c)
    rw [ωγWord_smul_e1, ← mul_assoc, hε, one_mul] at h
    rw [← h, pinnedX_single]
    exact mul_mem (mul_mem hn hxy.1) (inv_mem hn)
  · have h := hy (ε' * c)
    rw [smul_neg, ωγWord_smul_e1, ← mul_assoc, hε', one_mul] at h
    rw [← h, pinnedX_neg_single]
    exact mul_mem (mul_mem hn hxy'.2) (inv_mem hn)

theorem conj_wWord4_mem_fixed {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K support134) :
    nElt Tag.E6 K wWord4 * b * (nElt Tag.E6 K wWord4)⁻¹ ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hy
    · obtain ⟨ε, -, hx⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K wWord4
        (isRoot_single Tag.E6 j)
      have ex : nElt Tag.E6 K wWord4 * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹ =
          pinnedX Tag.E6 K ((coxeterSystem Tag.E6).wordProd wWord4 • Pi.single j 1) (ε * c) := by
        rw [← pinnedX_single]
        exact hx c
      rcases (show j = e6Index 0 ∨ j = e6Index 2 ∨ j = e6Index 3 from hj) with rfl | rfl | rfl
      · rw [ex, wWord4_smul_e0, pinnedX_single]
        exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero _).1
      · rw [ex, wWord4_smul_e2, pinnedX_single]
        exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ _ orbitWord_f4_one _).1
      · rw [ex, wWord4_smul_e3]
        exact (pinnedX_gamma_mem_fixed K _).1
    · obtain ⟨ε, -, hy⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K wWord4
        (isRoot_neg_single Tag.E6 j)
      have ey : nElt Tag.E6 K wWord4 * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹ =
          pinnedX Tag.E6 K (-((coxeterSystem Tag.E6).wordProd wWord4 • Pi.single j 1))
            (ε * c) := by
        rw [← pinnedX_neg_single, ← smul_neg]
        exact hy c
      rcases (show j = e6Index 0 ∨ j = e6Index 2 ∨ j = e6Index 3 from hj) with rfl | rfl | rfl
      · rw [ey, wWord4_smul_e0, pinnedX_neg_single]
        exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero _).2
      · rw [ey, wWord4_smul_e2, pinnedX_neg_single]
        exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ _ orbitWord_f4_one _).2
      · rw [ey, wWord4_smul_e3]
        exact (pinnedX_gamma_mem_fixed K _).2
  | one =>
    simp only [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : nElt Tag.E6 K wWord4 * (x * y) * (nElt Tag.E6 K wWord4)⁻¹ =
        (nElt Tag.E6 K wWord4 * x * (nElt Tag.E6 K wWord4)⁻¹) *
          (nElt Tag.E6 K wWord4 * y * (nElt Tag.E6 K wWord4)⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : nElt Tag.E6 K wWord4 * x⁻¹ * (nElt Tag.E6 K wWord4)⁻¹ =
        (nElt Tag.E6 K wWord4 * x * (nElt Tag.E6 K wWord4)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

end Fixed4

section Base4


variable {k K : Type} [Field k] [Field K] (ι : k →+* K)

theorem natCard_SL4_dvd {p : ℕ} (q : ℕ) (hq : 1 ≤ q) (hp : p ∣ q ^ 2 + 1) :
    p ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    zify [Nat.one_le_pow 4 (m + 1) (by omega), Nat.one_le_pow 2 (m + 1) (by omega)]
    ring
  have : p ∣ q ^ 4 - 1 := h4 ▸ Dvd.dvd.mul_left hp _
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left this _) _

theorem exists_e4 [Finite k] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card k ^ 2 + 1) :
    ∃ e : ModGL Tag.E6 K,
      e ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) ∧
      orderOf e = p ∧
      ∀ i, (i = e6Index 0 ∨ i = e6Index 5) →
        ∀ d : K, Commute e (xUnit Tag.E6 K i d) ∧ Commute e (yUnit Tag.E6 K i d) := by
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) k) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
    have := natCard_SL4_dvd (p := p) (Nat.card k) hq hp
    simpa [Finset.prod_Icc_succ_top, Nat.mul_assoc] using this
  obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card' p hcard
  set b₁ : ModGL Tag.E6 k := (((e6a3Equiv k) A₀ : subsystemGroup Tag.E6 k support134) :
    ModGL Tag.E6 k) with hb₁
  have hb₁mem : b₁ ∈ subsystemGroup Tag.E6 k support134 := ((e6a3Equiv k) A₀).2
  have hord₁ : orderOf b₁ = p := by
    rw [hb₁, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hA₀]
  refine ⟨baseChangeGL ι (nElt Tag.E6 k wWord4 * b₁ * (nElt Tag.E6 k wWord4)⁻¹),
    ⟨_, conj_wWord4_mem_fixed k hb₁mem, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective (baseChangeGL ι) (baseChangeGL_injective ι),
      ← orderOf_injective (MulAut.conj (nElt Tag.E6 k wWord4)).toMonoidHom
        (MulAut.conj (nElt Tag.E6 k wWord4)).injective b₁] at *
    · exact hord₁
  · intro i hi d
    rw [map_mul, map_mul, map_inv, baseChangeGL_nElt]
    exact commute_conj_support134 K (baseChangeGL_mem_subsystemGroup ι hb₁mem) i hi d

end Base4


end CFSG.HardMathSupport.Lang.AnisoE6
