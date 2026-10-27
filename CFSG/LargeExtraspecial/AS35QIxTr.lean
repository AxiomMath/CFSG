module

public import CFSG.LargeExtraspecial.AS35QIxCo
public import CFSG.LargeExtraspecial.AS35QIxLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem frob_mul_self_zero : frob (0 : K) * 0 = 0 := by rw [mul_zero]

namespace IxSetup

variable (T : IxSetup S)

theorem q_l (x : Fin 3 → K) : S.q (T.l x) = AS35QTh.tr2 (ω * herm frob x x) := by
  rw [q_eq_polar T.hζ2 (fun v => AS35QTh.q_apply T.ζ v), ← T.l_omega, T.hl.polar,
    herm_smul_right]

theorem herm_self (x : Fin 3 → K) :
    herm frob x x = frob (x 0) * x 0 + frob (x 1) * x 1 + frob (x 2) * x 2 := by
  rw [herm_def, Fin.sum_univ_three]

theorem singular_cases {x : Fin 3 → K} (hx : x ≠ 0) (hq : S.q (T.l x) = 0) :
    (x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 2 = 0) ∨ (x 0 ≠ 0 ∧ x 1 = 0 ∧ x 2 ≠ 0) ∨
      (x 0 = 0 ∧ x 1 ≠ 0 ∧ x 2 ≠ 0) := by
  rw [q_l, herm_self] at hq
  have h1K : (1 : K) + 1 = 0 := add_self_K 1
  by_cases h0 : x 0 = 0 <;> by_cases h1 : x 1 = 0 <;> by_cases h2 : x 2 = 0
  · exact absurd (funext fun i => by fin_cases i <;> simp [h0, h1, h2]) hx
  · exfalso
    rw [h0, h1, frob_mul_self_zero, frob_mul_self h2, zero_add, zero_add, mul_one,
      AS35QTh.tr2_omega] at hq
    exact one_ne_zero hq
  · exfalso
    rw [h0, h2, frob_mul_self_zero, frob_mul_self h1, zero_add, add_zero, mul_one,
      AS35QTh.tr2_omega] at hq
    exact one_ne_zero hq
  · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
  · exfalso
    rw [h1, h2, frob_mul_self_zero, frob_mul_self h0, add_zero, add_zero, mul_one,
      AS35QTh.tr2_omega] at hq
    exact one_ne_zero hq
  · exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
  · exact Or.inl ⟨h0, h1, h2⟩
  · exfalso
    rw [frob_mul_self h0, frob_mul_self h1, frob_mul_self h2, h1K, zero_add, mul_one,
      AS35QTh.tr2_omega] at hq
    exact one_ne_zero hq

@[expose] def Orb (v : S.Qt) : Prop := ∃ ξ ∈ T.X, (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 1, 1]) = v

theorem orb_base : T.Orb (T.l ![0, 1, 1]) := ⟨1, T.X.one_mem, rfl⟩

theorem orb_apply {s : S.O} (hs : s ∈ T.X) {v : S.Qt} (h : T.Orb v) :
    T.Orb ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  obtain ⟨ξ, hξ, e⟩ := h
  exact ⟨s * ξ, T.X.mul_mem hs hξ, by rw [apply_O, e]⟩

theorem orb_act {c : K} (hc : c ≠ 0) {v : S.Qt} (h : T.Orb v) :
    T.Orb (AS35QTh.act T.zL c v) := by
  rcases AS35QTh.K_cases c with rfl | rfl | rfl | rfl
  · exact absurd rfl hc
  · rwa [AS35QTh.act_one]
  · rw [AS35QTh.act_omega]
    exact T.orb_apply T.hζX h
  · rw [AS35QTh.act_frob_omega, add_comm]
    have e : T.zL v + v = T.zL (T.zL v) := (AS35QTh.zeta_zeta T.zeta_sq v).symm
    rw [e]
    exact T.orb_apply T.hζX (T.orb_apply T.hζX h)

theorem orb_110 : T.Orb (T.l ![1, 1, 0]) := by
  have h := T.orb_apply T.hβX (T.orb_apply T.hβX T.orb_base)
  rwa [T.hlβ, T.hlβ] at h

theorem orb_1c0 {c : K} (hc : c ≠ 0) : T.Orb (T.l ![1, c, 0]) := by
  rcases AS35QTh.K_cases c with rfl | rfl | rfl | rfl
  · exact absurd rfl hc
  · exact T.orb_110
  · have h := T.orb_apply T.hαX T.orb_110
    rw [T.hlα] at h
    simpa using h
  · have h := T.orb_apply T.hαX (T.orb_apply T.hαX T.orb_110)
    rw [T.hlα, T.hlα] at h
    simpa [AS35QTh.omega_mul_omega] using h

theorem orb_ab0 {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : T.Orb (T.l ![a, b, 0]) := by
  have hc : frob a * b ≠ 0 := mul_ne_zero (fun h => ha (by
    rw [← frob_frob a, h, map_zero])) hb
  have h := T.orb_act ha (T.orb_1c0 hc)
  rw [T.act_l] at h
  have e : a • ![(1 : K), frob a * b, 0] = ![a, b, 0] := by
    funext i
    fin_cases i
    · simp
    · show a * (frob a * b) = b
      rw [← mul_assoc, mul_frob_self ha, one_mul]
    · simp
  rwa [e] at h

theorem orb_a0b {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : T.Orb (T.l ![a, 0, b]) := by
  have h := T.orb_apply T.hβX (T.orb_apply T.hβX (T.orb_ab0 hb ha))
  rw [T.hlβ, T.hlβ] at h
  simpa using h

theorem orb_0ab {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : T.Orb (T.l ![0, a, b]) := by
  have h := T.orb_apply T.hβX (T.orb_ab0 ha hb)
  rw [T.hlβ] at h
  simpa using h

theorem exists_mem_X_apply {v : S.Qt} (hv : v ≠ 0) (hq : S.q v = 0) :
    ∃ ξ ∈ T.X, (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 1, 1]) = v := by
  obtain ⟨x, rfl⟩ := T.l_surjective v
  have hx : x ≠ 0 := fun h => hv (by rw [h, T.l_zero])
  rcases T.singular_cases hx hq with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have e : x = ![x 0, x 1, 0] := funext fun i => by fin_cases i <;> simp [h2]
    rw [e]
    exact T.orb_ab0 h0 h1
  · have e : x = ![x 0, 0, x 2] := funext fun i => by fin_cases i <;> simp [h1]
    rw [e]
    exact T.orb_a0b h0 h2
  · have e : x = ![0, x 1, x 2] := funext fun i => by fin_cases i <;> simp [h0]
    rw [e]
    exact T.orb_0ab h1 h2

theorem beta_fix {x : Fin 3 → K} (h : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x) = T.l x) :
    x 1 = x 0 ∧ x 2 = x 0 := by
  rw [T.hlβ] at h
  have h' := T.l_injective h
  have e0 := congrFun h' 0
  have e1 := congrFun h' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  exact ⟨e1.symm, e0⟩

theorem tb_fix_of_beta_fix {v : S.Qt} (h : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨x, rfl⟩ := T.l_surjective v
  obtain ⟨h1, h2⟩ := T.beta_fix h
  rw [tb_l]
  congr 1
  funext i
  fin_cases i <;> simp [h1, h2]

theorem mem_commSpace_tb_iff {v : S.Qt} :
    v ∈ commSpace (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ ∃ d : K, v = T.l ![0, d, d] := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    obtain ⟨y, rfl⟩ := T.l_surjective w
    refine ⟨y 1 + y 2, ?_⟩
    rw [tb_l, sub_eq_add_neg, AS35QTh.neg_V, ← T.l_add]
    congr 1
    funext i
    fin_cases i
    · simp [add_self_K]
    · simp [add_comm]
    · simp
  · rintro ⟨d, rfl⟩
    refine mem_commSpace.mpr ⟨T.l ![0, d, 0], ?_⟩
    rw [tb_l, sub_eq_add_neg, AS35QTh.neg_V, ← T.l_add]
    congr 1
    funext i
    fin_cases i <;> simp

theorem eq_zero_of_beta_fix_of_mem_commSpace {v : S.Qt}
    (h1 : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (h2 : v ∈ commSpace (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt)) : v = 0 := by
  obtain ⟨d, rfl⟩ := (T.mem_commSpace_tb_iff).mp h2
  obtain ⟨e1, -⟩ := T.beta_fix h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1
  rw [e1]
  convert T.l_zero
  funext i
  fin_cases i <;> rfl

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
