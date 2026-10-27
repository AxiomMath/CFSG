module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Siegel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Matrix CFSG.GH74.Exceptional CFSG.Open Subgroup

@[expose] def o2 : Fin 8 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![!![1, 0; 0, 1], !![2, 0; 0, 1], !![1, 0; 0, 2], !![2, 0; 0, 2], !![0, 1; 1, 0],
    !![0, 2; 1, 0], !![0, 1; 2, 0], !![0, 2; 2, 0]]

theorem o2_orth (i : Fin 8) : (o2 i)ᵀ * o2 i = 1 := by
  revert i
  decide +kernel

theorem o2_orth' (i : Fin 8) : o2 i * (o2 i)ᵀ = 1 := by
  revert i
  decide +kernel

theorem o2_injective : Function.Injective o2 := by
  intro i j h
  revert i j
  decide +kernel

theorem o2_complete_entries : ∀ a b c d : ZMod 3,
    (!![a, b; c, d])ᵀ * !![a, b; c, d] = 1 → ∃ i, o2 i = !![a, b; c, d] := by
  decide +kernel

theorem o2_complete (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : Aᵀ * A = 1) : ∃ i, o2 i = A := by
  rw [Matrix.eta_fin_two A] at hA ⊢
  exact o2_complete_entries _ _ _ _ hA

@[expose] def Φ (p : Fin 8 × T3) : SpMat3 := fromBlocks (o2 p.1) (o2 p.1 * symM p.2) 0 (o2 p.1)

theorem Φ_injective : Function.Injective Φ := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have h' := fromBlocks_inj.mp h
  have hij : i = j := o2_injective h'.1
  subst hij
  have hst : symM s = symM t := by
    have := congrArg (fun M => (o2 i)ᵀ * M) h'.2.1
    simpa [← Matrix.mul_assoc, o2_orth] using this
  have e00 := congrFun (congrFun hst 0) 0
  have e01 := congrFun (congrFun hst 0) 1
  have e11 := congrFun (congrFun hst 1) 1
  simp only [symM, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, head_cons] at e00 e01 e11
  exact Prod.ext rfl (Prod.ext e00 (Prod.ext e01 e11))

theorem symM_one : symM (1, 0, 1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def u0 : StatedSp 2 (ZMod 3) := uSpHom (Multiplicative.ofAdd (1, 0, 1))

theorem coe_u0 : (((u0 : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) =
    fromBlocks 1 1 0 1 := by
  show uMat (1, 0, 1) = _
  rw [uMat, symM_one]

abbrev J4 : SpMat3 := fromBlocks 0 1 (-1) 0

theorem mem_range_Φ (M : SpMat3) (hc : M * fromBlocks 1 1 0 1 = fromBlocks 1 1 0 1 * M)
    (hs : Mᵀ * J4 * M = J4) : M ∈ Set.range Φ := by
  rw [← fromBlocks_toBlocks M] at hc hs ⊢
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  rw [fromBlocks_multiply, fromBlocks_multiply] at hc
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.mp hc
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add] at h1 h2 h4
  have hC : C = 0 := by
    have := h1
    rwa [left_eq_add] at this
  have hD : D = A := by
    rw [add_comm] at h2
    exact (add_left_cancel h2).symm
  rw [hC, hD] at hs ⊢
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hs
  obtain ⟨-, k2, -, k4⟩ := fromBlocks_inj.mp hs
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add, transpose_zero, Matrix.mul_neg, Matrix.neg_mul, neg_zero] at k2 k4
  have hA : Aᵀ * A = 1 := k2
  obtain ⟨i, hi⟩ := o2_complete A hA
  have hA' : A * Aᵀ = 1 := hi ▸ o2_orth' i
  have hsym : Bᵀ * A = Aᵀ * B := by
    have := k4
    rw [neg_add_eq_zero] at this
    exact this.symm
  set S := Aᵀ * B with hS
  have hST : Sᵀ = S := by rw [hS, transpose_mul, transpose_transpose, hsym]
  have h10 : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hST 0) 1
    simpa [transpose_apply] using this
  have hsymS : symM (S 0 0, S 0 1, S 1 1) = S := by
    ext a b
    fin_cases a <;> fin_cases b
    · rfl
    · rfl
    · exact h10.symm
    · rfl
  refine ⟨(i, (S 0 0, S 0 1, S 1 1)), ?_⟩
  simp only [Φ]
  rw [hsymS, hi, hS, ← Matrix.mul_assoc, hA', Matrix.one_mul]

theorem block_facts (A S : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : Aᵀ * A = 1) (hA' : A * Aᵀ = 1)
    (hS : Sᵀ = S) :
    fromBlocks A (A * S) 0 A * fromBlocks Aᵀ (-(S * Aᵀ)) 0 Aᵀ = 1 ∧
    fromBlocks Aᵀ (-(S * Aᵀ)) 0 Aᵀ * fromBlocks A (A * S) 0 A = 1 ∧
    (fromBlocks A (A * S) 0 A)ᵀ * J4 * fromBlocks A (A * S) 0 A = J4 ∧
    fromBlocks A (A * S) 0 A * fromBlocks 1 1 0 1 =
      fromBlocks 1 1 0 1 * fromBlocks A (A * S) 0 A := by
  have hA2 : ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod 3), Aᵀ * (A * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have hA'2 : ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod 3), A * (Aᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [hA']
    · simp [Matrix.mul_neg, Matrix.mul_assoc, hA'2]
    · simp
    · simp [hA']
  · rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [hA]
    · simp [Matrix.neg_mul, Matrix.mul_assoc, hA2, hA]
    · simp
    · simp [hA]
  · rw [J4, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · simp
    · simp [hA]
    · simp [hA]
    · simp [transpose_mul, hS, Matrix.mul_assoc, hA2, hA]
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · simp
    · simp [add_comm]
    · simp
    · simp

theorem exists_of_Φ (p : Fin 8 × T3) :
    ∃ g ∈ centralizer ({u0} : Set (StatedSp 2 (ZMod 3))),
      (((g : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = Φ p := by
  obtain ⟨i, s⟩ := p
  obtain ⟨hl, hr, hsymp, hcomm⟩ :=
    block_facts (o2 i) (symM s) (o2_orth i) (o2_orth' i) (symM_transpose s)
  let g : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ⟨Φ (i, s), _, hl, hr⟩
  have hg : g ∈ StatedSp 2 (ZMod 3) := by
    rw [StatedAPI.mem_statedSp_iff]
    exact hsymp
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  show Φ (i, s) * (((u0 : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) =
    (((u0 : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) * Φ (i, s)
  rw [coe_u0]
  exact hcomm

theorem card_centralizer_u0 :
    Nat.card (centralizer ({u0} : Set (StatedSp 2 (ZMod 3)))) = 216 := by
  set C := centralizer ({u0} : Set (StatedSp 2 (ZMod 3)))
  let f : ↥C → SpMat3 := fun c => (((c : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) :
    SpMat3)
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Units.ext h))
  have hrange : Set.range f = Set.range Φ := by
    ext M
    constructor
    · rintro ⟨c, rfl⟩
      have hcm := mem_centralizer_singleton_iff.mp c.2
      apply mem_range_Φ
      · have := congrArg (fun y : StatedSp 2 (ZMod 3) =>
          ((y : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3)) hcm
        simp only [Subgroup.coe_mul, Units.val_mul] at this
        rw [coe_u0] at this
        exact this
      · exact StatedAPI.mem_statedSp_iff.mp (c : StatedSp 2 (ZMod 3)).2
    · rintro ⟨p, rfl⟩
      obtain ⟨g, hg, hgp⟩ := exists_of_Φ p
      exact ⟨⟨g, hg⟩, hgp⟩
  have h1 : Nat.card ↥C = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
  rw [h1, hrange, Nat.card_range_of_injective Φ_injective, Nat.card_eq_fintype_card]
  rfl

theorem trace_u0 : trace (fromBlocks 1 1 0 1 : SpMat3) = 1 := by
  decide +kernel

abbrev π43 : StatedSp 2 (ZMod 3) →* PSp43 := QuotientGroup.mk' Z43

theorem comap_centralizer_u0 :
    (centralizer ({π43 u0} : Set PSp43)).comap π43 =
      centralizer ({u0} : Set (StatedSp 2 (ZMod 3))) := by
  ext g
  rw [mem_comap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul]
  constructor
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    rcases units_zmod_three c with rfl | rfl
    · rw [map_one] at hc
      have h1 : (g * u0)⁻¹ * (u0 * g) = 1 := Subtype.ext hc.symm
      exact inv_mul_eq_one.mp h1
    · exfalso
      rw [scalar_neg_one] at hc
      set G : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ↑g
      set U : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ↑u0
      have hc' : (G * U)⁻¹ * (U * G) = -1 := hc.symm
      have hUG : U * G = -(G * U) := by
        rw [← mul_neg_one, ← hc', mul_inv_cancel_left]
      have hconj : G⁻¹ * U * G = -U := by
        rw [mul_assoc, hUG, mul_neg, inv_mul_cancel_left]
      have htr := congrArg (fun y : GL (Fin 2 ⊕ Fin 2) (ZMod 3) => trace (y : SpMat3)) hconj
      simp only [Units.val_mul, Units.val_neg] at htr
      rw [trace_mul_cycle, Units.mul_inv, Matrix.one_mul, trace_neg] at htr
      have hU : (U : SpMat3) = fromBlocks 1 1 0 1 := coe_u0
      rw [hU, trace_u0] at htr
      exact absurd htr (by decide)
  · intro h
    rw [h]

theorem card_PSp43 : Nat.card PSp43 = 25920 := by
  rw [Nat.card_congr psp43EquivU2.toEquiv]
  exact card_U2_four

theorem card_centralizer_uPSp :
    Nat.card (centralizer ({uPSp (Multiplicative.ofAdd (1, 0, 1))} : Set PSp43)) = 108 := by
  have hu : uPSp (Multiplicative.ofAdd (1, 0, 1)) = π43 u0 := rfl
  rw [hu]
  set H := centralizer ({π43 u0} : Set PSp43)
  have hidx : (H.comap π43).index = H.index :=
    Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective _)
  rw [comap_centralizer_u0] at hidx
  have h1 := Subgroup.card_mul_index H
  have h2 := Subgroup.card_mul_index (centralizer ({u0} : Set (StatedSp 2 (ZMod 3))))
  rw [card_PSp43] at h1
  rw [card_centralizer_u0, card_statedSp_two_three, hidx] at h2
  have hi : H.index = 240 := by omega
  rw [hi] at h1
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
