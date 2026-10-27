module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin

section Rho

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

@[expose] noncomputable def peRho : spinGroup (quadPlus n K) →* StatedOmega (StatedQuadPlus n K) :=
  (spinMatrix (quadPlus n K)).codRestrict _
    (spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn))

theorem peRho_mulVec (x : spinGroup (quadPlus n K)) (w : Fin n ⊕ Fin n → K) :
    (((peRho hn x : StatedOmega (StatedQuadPlus n K)) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = spinAction (quadPlus n K) x w :=
  spinMatrix_mulVec _ x w

theorem peRho_surjective : Function.Surjective (peRho (K := K) hn) := by
  rintro ⟨A, hA⟩
  rw [← range_spinMatrix_quadPlus hn] at hA
  obtain ⟨x, hx⟩ := hA
  exact ⟨x, Subtype.ext hx⟩

theorem peRho_injective [CharP K 2] : Function.Injective (peRho (K := K) hn) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : x ∈ (spinAction (quadPlus n K)).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun w => ?_
    rw [← peRho_mulVec hn x w, hx]
    simp
  have h2 := ker_spinAction_le_center (quadPlus n K) h1
  rwa [q2Omega_center_spinGroup_quadPlus_eq_bot hn] at h2

@[expose] noncomputable def peRhoEquiv [CharP K 2] :
    spinGroup (quadPlus n K) ≃* StatedOmega (StatedQuadPlus n K) :=
  MulEquiv.ofBijective (peRho hn) ⟨peRho_injective hn, peRho_surjective hn⟩

theorem peRhoEquiv_apply [CharP K 2] (x : spinGroup (quadPlus n K)) :
    peRhoEquiv (K := K) hn x = peRho hn x := rfl

end Rho

section Pieces

variable {n : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def peSpinFix (P : (Fin n ⊕ Fin n → K) → Prop) : Subgroup (spinGroup (quadPlus n K)) where
  carrier := {x | ∀ w, P w → spinAction (quadPlus n K) x w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {x y} hx hy w hw => by
    rw [map_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  inv_mem' := fun {x} hx w hw => by
    conv_lhs => rw [← hx w hw]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

@[expose] def PEOff (S : Finset (Fin n)) (w : Fin n ⊕ Fin n → K) : Prop :=
  ∀ a ∈ S, w (.inl a) = 0 ∧ w (.inr a) = 0

@[expose] def peSupp (J : Finset (Fin n)) : Finset (Fin n) :=
  J.biUnion fun j => {rootIdxD n j, rootIdxD' n j}

theorem mem_peSupp {J : Finset (Fin n)} {a : Fin n} :
    a ∈ peSupp J ↔ ∃ j ∈ J, a = rootIdxD n j ∨ a = rootIdxD' n j := by
  simp [peSupp]

theorem polar_plusVec_of_peOff {S : Finset (Fin n)} {w : Fin n ⊕ Fin n → K} (hw : PEOff S w)
    {a : Fin n} (ha : a ∈ S) (s : Bool) : polar (quadPlus n K) w (plusVec n K a s) = 0 := by
  cases s
  · rw [plusVec_false, polar_quadPlus_single_inr]
    exact (hw a ha).1
  · rw [plusVec_true, polar_quadPlus_single_inl]
    exact (hw a ha).2

variable (hn : 3 ≤ n)

theorem longRoot_mem_peSpinFix {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : Multiplicative K)
    {S : Finset (Fin n)} (hi : i ∈ S) (hj : j ∈ S) :
    (plusFrame n K hn).longRoot hij s t c ∈ peSpinFix K (PEOff S) := by
  intro w hw
  have hc : c = Multiplicative.ofAdd (Multiplicative.toAdd c) := rfl
  rw [hc]
  exact (plusFrame n K hn).spinAction_longRoot_of_polar hij s t _
    (by rw [plusFrame_vec]; exact polar_plusVec_of_peOff hw hi s)
    (by rw [plusFrame_vec]; exact polar_plusVec_of_peOff hw hj t)

theorem rankOne_le_peSpinFix (j : Fin n) {S : Finset (Fin n)} (h1 : rootIdxD n j ∈ S)
    (h2 : rootIdxD' n j ∈ S) :
    CFSG.LieType.CurtisTits.rankOne (plusRootGroup n K hn) j ≤ peSpinFix K (PEOff S) := by
  rw [CFSG.LieType.CurtisTits.rankOne, plusRootGroup_single, plusRootGroup_neg_single, sup_le_iff]
  constructor
  · rintro _ ⟨c, rfl⟩
    exact longRoot_mem_peSpinFix hn _ _ _ c h1 h2
  · rintro _ ⟨c, rfl⟩
    exact longRoot_mem_peSpinFix hn _ _ _ c h2 h1

theorem levi_le_peSpinFix (J : Finset (Fin n)) :
    CFSG.LieType.CurtisTits.levi (plusRootGroup n K hn) J ≤ peSpinFix K (PEOff (peSupp J)) := by
  refine iSup₂_le fun j hj => rankOne_le_peSpinFix hn j ?_ ?_
  · exact mem_peSupp.2 ⟨j, hj, Or.inl rfl⟩
  · exact mem_peSupp.2 ⟨j, hj, Or.inr rfl⟩

theorem spinAction_levi_of_peOff {J : {J : Finset (Fin n) // J.card ≤ 2}}
    (x : (plusDatum n K hn).leviAmalgam J) {w : Fin n ⊕ Fin n → K} (hw : PEOff (peSupp J.1) w) :
    spinAction (quadPlus n K) x w = w :=
  levi_le_peSpinFix hn J.1 x.2 w hw

end Pieces

section Eichler

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def peEich {u w a : Fin n ⊕ Fin n → K} (hu : quadPlus n K u = 0)
    (huw : polar (quadPlus n K) u w = 0) (hua : polar (quadPlus n K) u a = 0)
    (hwa : polar (quadPlus n K) w a = 0) (ha : IsUnit (quadPlus n K a)) :
    spinGroup (quadPlus n K) :=
  rootHom (quadPlus n K) hu huw
    (one_add_smul_ι_mul_ι_mem_spinGroup (quadPlus n K) hu huw hua hwa ha) (.ofAdd 1)

theorem spinAction_peEich {u w a : Fin n ⊕ Fin n → K} (hu : quadPlus n K u = 0)
    (hw : quadPlus n K w = 0) (huw : polar (quadPlus n K) u w = 0)
    (hua : polar (quadPlus n K) u a = 0) (hwa : polar (quadPlus n K) w a = 0)
    (ha : IsUnit (quadPlus n K a)) (z : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (peEich hu huw hua hwa ha) z =
      z + polar (quadPlus n K) z u • w - polar (quadPlus n K) z w • u := by
  rw [peEich, spinAction_rootHom, one_smul, hw, zero_mul, zero_smul, sub_zero]

end Eichler

section Fork

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {a b : Fin n}

theorem pe_rootIdxD_a (ha : a.val + 2 = n) : rootIdxD n a = a := rootIdxD_of_lt n (by omega)

theorem pe_rootIdxD'_a (ha : a.val + 2 = n) (hb : b.val + 1 = n) : rootIdxD' n a = b := by
  rw [rootIdxD'_of_lt n (by omega)]
  exact Fin.ext (by simp; omega)

theorem pe_rootSignD_a (ha : a.val + 2 = n) : rootSignD n a = false := rootSignD_of_lt n (by omega)

theorem pe_rootIdxD_b (ha : a.val + 2 = n) (hb : b.val + 1 = n) : rootIdxD n b = a :=
  Fin.ext (by rw [val_rootIdxD_of_not_lt n (by omega)]; omega)

theorem pe_rootIdxD'_b (hb : b.val + 1 = n) : rootIdxD' n b = b :=
  Fin.ext (by rw [val_rootIdxD'_of_not_lt n (by omega)]; omega)

theorem pe_rootSignD_b (hb : b.val + 1 = n) : rootSignD n b = true :=
  rootSignD_of_not_lt n (by omega)

theorem pe_ne_ab (ha : a.val + 2 = n) (hb : b.val + 1 = n) : a ≠ b := fun h => by
  have := congrArg Fin.val h
  omega

variable (ha : a.val + 2 = n) (hb : b.val + 1 = n)
include ha hb

theorem spinAction_rootD_a (y : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (rootD K hn a (.ofAdd 1)) y =
      y + y (.inl b) • Pi.single (.inl a) 1 - y (.inr a) • Pi.single (.inr b) 1 := by
  rw [rootD, (plusFrame n K hn).spinAction_longRoot, plusFrame_vec, pe_rootIdxD_a ha,
    pe_rootIdxD'_a ha hb, pe_rootSignD_a ha]
  simp only [plusVec_true, plusVec_false, polar_quadPlus_single_inr, polar_quadPlus_single_inl,
    one_mul]

theorem spinAction_negRootD_a (y : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (negRootD K hn a (.ofAdd 1)) y =
      y + y (.inl a) • Pi.single (.inl b) 1 - y (.inr b) • Pi.single (.inr a) 1 := by
  rw [negRootD, (plusFrame n K hn).spinAction_longRoot, plusFrame_vec, pe_rootIdxD_a ha,
    pe_rootIdxD'_a ha hb, pe_rootSignD_a ha, Bool.not_false]
  simp only [plusVec_true, plusVec_false, polar_quadPlus_single_inr, polar_quadPlus_single_inl,
    one_mul]

theorem spinAction_rootD_b (y : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (rootD K hn b (.ofAdd 1)) y =
      y + y (.inr b) • Pi.single (.inl a) 1 - y (.inr a) • Pi.single (.inl b) 1 := by
  rw [rootD, (plusFrame n K hn).spinAction_longRoot, plusFrame_vec, pe_rootIdxD_b ha hb,
    pe_rootIdxD'_b hb, pe_rootSignD_b hb]
  simp only [plusVec_true, polar_quadPlus_single_inl, one_mul]

theorem spinAction_negRootD_b (y : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (negRootD K hn b (.ofAdd 1)) y =
      y + y (.inl a) • Pi.single (.inr b) 1 - y (.inl b) • Pi.single (.inr a) 1 := by
  rw [negRootD, (plusFrame n K hn).spinAction_longRoot, plusFrame_vec, pe_rootIdxD_b ha hb,
    pe_rootIdxD'_b hb, pe_rootSignD_b hb, Bool.not_true]
  simp only [plusVec_false, polar_quadPlus_single_inr, one_mul]

omit ha hb in
variable (K) in
@[expose] noncomputable def peTorusWord (a b : Fin n) : spinGroup (quadPlus n K) :=
  rootD K hn a (.ofAdd 1) * negRootD K hn a (.ofAdd 1) * rootD K hn b (.ofAdd 1) *
    negRootD K hn b (.ofAdd 1)

theorem spinAction_peTorusWord [CharP K 2] (x : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (peTorusWord K hn a b) x =
      x + (x (.inl a) + x (.inr b) + x (.inl b)) •
          (Pi.single (.inl a) 1 + Pi.single (.inr a) 1) +
        (x (.inr a) + x (.inr b) + x (.inl b)) •
          (Pi.single (.inl a) 1 + (Pi.single (.inl b) 1 + Pi.single (.inr b) 1)) := by
  have hab := pe_ne_ab ha hb
  have hba := hab.symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [peTorusWord, map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, spinAction_negRootD_b hn ha hb, spinAction_rootD_b hn ha hb,
    spinAction_negRootD_a hn ha hb, spinAction_rootD_a hn ha hb]
  funext c
  rcases c with c | c
  · by_cases hca : c = a
    · subst hca
      simp [hab, hba]
      linear_combination (x (.inl c) - x (.inr c)) * h2
    · by_cases hcb : c = b
      · subst hcb
        simp [hab, hba]
        linear_combination (x (.inl a) - x (.inr a)) * h2
      · simp [Pi.single_apply, hca, hcb]
  · by_cases hca : c = a
    · subst hca
      simp [hab, hba]
      linear_combination (-(x (.inl b) + x (.inr b) + x (.inl c))) * h2
    · by_cases hcb : c = b
      · subst hcb
        simp [hab, hba]
        linear_combination (x (.inl a) - x (.inr a)) * h2
      · simp [Pi.single_apply, hca, hcb]

end Fork

section Weyl

variable {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)

theorem spinAction_weylD_of_lt {k : Fin n} (hk : k.val + 1 < n) (m : Fin n) (s : Bool) :
    spinAction (quadPlus n K) (weylD K hn k) (plusVec n K m s) =
      plusVec n K (Equiv.swap k ⟨k.val + 1, hk⟩ m) s := by
  rw [spinAction_weylD, rootIdxD_of_lt n hk, rootIdxD'_of_lt n hk, rootSignD_of_lt n hk]
  have hsign : (longWeylSign k m : K) = 1 := by
    unfold longWeylSign
    split_ifs
    · exact CharTwo.neg_eq 1
    · rfl
  have hbool : longWeylBool k ⟨k.val + 1, hk⟩ true false m s = s := by
    unfold longWeylBool
    split_ifs <;> simp
  rw [hsign, hbool, one_smul]

end Weyl

section Mem

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem rootD_mem_rankOne (k : Fin n) (c : Multiplicative K) :
    rootD K hn k c ∈ CFSG.LieType.CurtisTits.rankOne (plusRootGroup n K hn) k := by
  rw [CFSG.LieType.CurtisTits.rankOne, plusRootGroup_single]
  exact mem_sup_left ⟨c, rfl⟩

theorem negRootD_mem_rankOne (k : Fin n) (c : Multiplicative K) :
    negRootD K hn k c ∈ CFSG.LieType.CurtisTits.rankOne (plusRootGroup n K hn) k := by
  rw [CFSG.LieType.CurtisTits.rankOne, plusRootGroup_neg_single]
  exact mem_sup_right ⟨c, rfl⟩

theorem peTorusWord_mem_levi {a b : Fin n} {J : Finset (Fin n)} (hJa : a ∈ J) (hJb : b ∈ J) :
    peTorusWord K hn a b ∈ CFSG.LieType.CurtisTits.levi (plusRootGroup n K hn) J := by
  have ha := CFSG.LieType.CurtisTits.rankOne_le_levi (plusRootGroup n K hn) hJa
  have hb := CFSG.LieType.CurtisTits.rankOne_le_levi (plusRootGroup n K hn) hJb
  exact mul_mem (mul_mem (mul_mem (ha (rootD_mem_rankOne hn a _))
    (ha (negRootD_mem_rankOne hn a _))) (hb (rootD_mem_rankOne hn b _)))
    (hb (negRootD_mem_rankOne hn b _))

theorem weylD_mem_levi {k : Fin n} {J : Finset (Fin n)} (hk : k ∈ J) :
    weylD K hn k ∈ CFSG.LieType.CurtisTits.levi (plusRootGroup n K hn) J :=
  CFSG.LieType.CurtisTits.rankOne_le_levi (plusRootGroup n K hn) hk (plusDatum_n_mem hn k)

end Mem

end CFSG.SeitzReduction.SymplecticPilot
