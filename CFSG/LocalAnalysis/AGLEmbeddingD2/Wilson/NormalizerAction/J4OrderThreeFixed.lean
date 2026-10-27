module

public import CFSG.Sporadic.Schreier.J4SRank
public import Certificates.Certificate12601

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem toVecD_vecMulRows (X : Array ℕ) (v n : ℕ) (j : Fin 112) :
    toVecD 112 (vecMulRows X v n) j =
      ∑ i ∈ Finset.range n, if v.testBit i then toVecD 112 X[i]! j else 0 := by
  induction n with
  | zero => simp [vecMulRows, toVecD_zero]
  | succ n ih =>
    rw [vecMulRows, toVecD_xor, Pi.add_apply, ih, Finset.sum_range_succ]
    congr 1
    split_ifs
    · rfl
    · rw [toVecD_zero]; rfl

theorem vecMul_rowsMatrix (X : Array ℕ) (v : ℕ) :
    toVecD 112 v ᵥ* SmallF2.rowsMatrix 112 X = toVecD 112 (vecMulRows X v 112) := by
  funext j
  rw [toVecD_vecMulRows, ← Fin.sum_univ_eq_sum_range
    (fun i => if v.testBit i then toVecD 112 X[i]! j else 0) 112, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toVecD_apply, SmallF2.rowsMatrix, Matrix.of_apply, ← getElem!_eq_getD']
  split_ifs <;> simp

theorem three_le_finrank_ker {M : Matrix (Fin 112) (Fin 112) (ZMod 2)}
    (h : 8 ≤ Nat.card (LinearMap.ker (Matrix.mulVecLin Mᵀ))) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin Mᵀ)) := by
  set R := LinearMap.ker (Matrix.mulVecLin Mᵀ)
  have key : 2 ^ Module.finrank (ZMod 2) R = Nat.card R :=
    @FiniteField.pow_finrank_eq_natCard 2 _ R (Submodule.addCommGroup R) _ (Submodule.module R)
  rw [← key] at h
  by_contra hlt3
  have h3 : Module.finrank (ZMod 2) R ≤ 2 := by omega
  have : 2 ^ Module.finrank (ZMod 2) R ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem three_le_finrank_ker_of_fix3 {X vs : Array ℕ} (h : fix3OK X vs = true) :
    3 ≤ Module.finrank (ZMod 2)
      (LinearMap.ker (Matrix.mulVecLin (SmallF2.rowsMatrix 112 X - 1)ᵀ)) := by
  unfold fix3OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hla, hlb⟩, hlc⟩, hfa⟩, hfb⟩, hfc⟩, hinj⟩ := h
  set a := vs[0]!
  set b := vs[1]!
  set c := vs[2]!
  set K := LinearMap.ker (Matrix.mulVecLin (SmallF2.rowsMatrix 112 X - 1)ᵀ)
  have hfix : ∀ v, vecMulRows X v 112 = v → toVecD 112 v ∈ K := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_sub,
      Matrix.vecMul_one, vecMul_rowsMatrix, hv, sub_self]
  have hlt : ∀ i, comb3 a b c i < 2 ^ 112 := by
    intro i
    unfold comb3
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_ <;> split_ifs <;>
      first | assumption | positivity
  have hmem : ∀ i, toVecD 112 (comb3 a b c i) ∈ K := by
    intro i
    unfold comb3
    rw [toVecD_xor, toVecD_xor]
    refine K.add_mem (K.add_mem ?_ ?_) ?_ <;> split_ifs
    · exact hfix a hfa
    · rw [toVecD_zero]; exact K.zero_mem
    · exact hfix b hfb
    · rw [toVecD_zero]; exact K.zero_mem
    · exact hfix c hfc
    · rw [toVecD_zero]; exact K.zero_mem
  have hf : Function.Injective fun i : Fin 8 => (⟨toVecD 112 (comb3 a b c i), hmem i⟩ : K) := by
    intro i j hij
    have e := congrArg Subtype.val hij
    dsimp only at e
    rcases hinj i i.isLt j j.isLt with h | h
    · exact Fin.ext h
    · exact absurd (toVecD_injective (hlt _) (hlt _) e) h
  refine three_le_finrank_ker ?_
  have := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fin] at this

theorem finrank_ker_transpose_add_rank (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin Mᵀ)) + M.rank = 112 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Mᵀ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have e : (Mᵀ).rank = M.rank := Matrix.rank_transpose M
  rw [Matrix.rank] at e
  omega

theorem rank_le_of_fix3OK {X vs : Array ℕ} (h : fix3OK X vs = true) :
    (SmallF2.rowsMatrix 112 X - 1).rank ≤ 109 := by
  have h1 := three_le_finrank_ker_of_fix3 h
  have h2 := finrank_ker_transpose_add_rank (SmallF2.rowsMatrix 112 X - 1)
  omega

theorem rank_le_of_rep {g : J} {P : Pair} {vs : Array ℕ} (hg : Rep Sp φ g P)
    (h : fix3OK P.1 vs = true) : (φ g - 1).rank ≤ 109 := by
  rw [← hg.2.2.1]
  exact rank_le_of_fix3OK h

theorem q3Fix_eq : q3FixOK Q3GenPairs = true :=
  Certificates.certificate12601

theorem R3E_J4_elements_of_order_three_have_rank_at_most_109 :
    ∀ g : J, orderOf g = 3 →
      (((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) - 1).rank ≤ 109 := by
  intro g h3
  rw [← φ_apply]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (Sylow.ofCard Q3 card_Q3_sylow_J) hP
  rw [Sylow.coe_ofCard] at hc
  obtain ⟨k, hk, hke⟩ := mem_Q3_iff.1 hc
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [q3Elt_zero] at hke
    have : g = 1 := by
      have e : g = c⁻¹ * (c * g * c⁻¹) * c := by group
      rw [e, ← hke]; group
    rw [this, orderOf_one] at h3
    omega
  rw [← rank_conj c g, ← hke]
  refine rank_le_of_rep (vs := q3FixVecs[k - 1]!) (rep_q3PairK k hk) ?_
  have h := q3Fix_eq
  unfold q3FixOK at h
  have := List.all_eq_true.1 h (k - 1) (List.mem_range.2 (by omega))
  rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)] at this

theorem R3E_J4_elements_of_order_three_left_fixed_space_dim_ge_three :
    ∀ g : J, orderOf g = 3 →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin
        ((((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) - 1)ᵀ))) := by
  intro g hg
  have h1 := R3E_J4_elements_of_order_three_have_rank_at_most_109 g hg
  have h2 := finrank_ker_transpose_add_rank
    ((((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) - 1))
  omega

end CFSG.Sporadic.J4Schreier
