module

public import CFSG.GroupTheory.GL52.Basic

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem inv_add_self_M5 (A : M5) : A + A = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem inv_add_self_V5 (v : V5) : v + v = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem inv_sub_eq_add_M5 (A B : M5) : A - B = A + B := by
  rw [sub_eq_iff_eq_add, add_assoc, inv_add_self_M5, add_zero]

@[expose] def invN (x : G52) : M5 :=
  (x : M5) - 1

theorem inv_mulVec_eq (x : G52) (v : V5) : (x : M5) *ᵥ v = invN x *ᵥ v + v := by
  rw [invN, sub_mulVec, one_mulVec, sub_add_cancel]

theorem inv_invN_sq {x : G52} (hx : x ^ 2 = 1) : invN x * invN x = 0 := by
  have hxx : (x : M5) * (x : M5) = 1 := by
    rw [← Units.val_mul, ← sq, hx, Units.val_one]
  rw [invN, inv_sub_eq_add_M5, add_mul, mul_add, mul_add, hxx, mul_one, one_mul, one_mul,
    add_assoc, ← add_assoc (x : M5), inv_add_self_M5, zero_add, inv_add_self_M5]

theorem inv_invN_ne_zero {x : G52} (hx1 : x ≠ 1) : invN x ≠ 0 := by
  intro h
  apply hx1
  refine Units.ext ?_
  rw [Units.val_one, ← sub_eq_zero]
  exact h

theorem inv_range_le_ker {x : G52} (hx : x ^ 2 = 1) :
    LinearMap.range (toLin' (invN x)) ≤ LinearMap.ker (toLin' (invN x)) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, inv_invN_sq hx, zero_mulVec]

theorem inv_finrank_V5 : finrank (ZMod 2) V5 = 5 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem inv_rank_nullity (x : G52) :
    commDim x + finrank (ZMod 2) (LinearMap.ker (toLin' (invN x))) = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker (toLin' (invN x))
  rw [inv_finrank_V5] at h
  exact h

theorem inv_commDim_pos {x : G52} (hx1 : x ≠ 1) : 0 < commDim x := by
  rw [Nat.pos_iff_ne_zero, commDim, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro h
  exact inv_invN_ne_zero hx1 (Matrix.toLin'.map_eq_zero_iff.1 h)

theorem inv_commDim_eq_one_or_two {x : G52} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    commDim x = 1 ∨ commDim x = 2 := by
  have h1 := inv_commDim_pos hx1
  have h2 := inv_rank_nullity x
  have h3 : commDim x ≤ finrank (ZMod 2) (LinearMap.ker (toLin' (invN x))) :=
    Submodule.finrank_mono (inv_range_le_ker hx)
  omega

@[expose] def invT0M : M5 :=
  !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def invU0M : M5 :=
  !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def invT0 : G52 :=
  mk5 invT0M invT0M (by decide)

@[expose] def invU0 : G52 :=
  mk5 invU0M invU0M (by decide)

theorem inv_exists_extend {W : Submodule (ZMod 2) V5} {n : ℕ} (v : Fin n → V5)
    (hv : LinearIndependent (ZMod 2) v) (hvW : ∀ i, v i ∈ W) (hn : n < finrank (ZMod 2) W) :
    ∃ u ∈ W, LinearIndependent (ZMod 2) (Fin.snoc v u : Fin (n + 1) → V5) := by
  have hle : Submodule.span (ZMod 2) (Set.range v) ≤ W :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvW i)
  have hlt : Submodule.span (ZMod 2) (Set.range v) < W := by
    refine lt_of_le_of_ne hle fun h => ?_
    have h1 := finrank_range_le_card (R := ZMod 2) v
    rw [Set.finrank, h, Fintype.card_fin] at h1
    omega
  obtain ⟨u, huW, hu⟩ := IsConcreteLE.exists_of_lt hlt
  exact ⟨u, huW, linearIndependent_finSnoc.2 ⟨hv, hu⟩⟩

theorem inv_snoc_mem {W : Submodule (ZMod 2) V5} {n : ℕ} {v : Fin n → V5} {u : V5}
    (hv : ∀ i, v i ∈ W) (hu : u ∈ W) : ∀ i, (Fin.snoc v u : Fin (n + 1) → V5) i ∈ W := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hu
  · simpa using hv j

theorem inv_isConj_t0 {x : G52} (hx : x ^ 2 = 1) (h1 : commDim x = 1) : IsConj invT0 x := by
  set N := invN x with hN
  have hker : finrank (ZMod 2) (LinearMap.ker (toLin' N)) = 4 := by
    have := inv_rank_nullity x
    rw [← hN] at this
    omega
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h0 : commDim 1 = 0 := by
      rw [commDim, Units.val_one, sub_self, map_zero, LinearMap.range_zero, finrank_bot]
    omega
  obtain ⟨b4, hb4⟩ : ∃ b4 : V5, N *ᵥ b4 ≠ 0 := by
    by_contra h
    apply inv_invN_ne_zero hx1
    refine ext_cols fun j => ?_
    rw [zero_mulVec]
    by_contra hj
    exact h ⟨_, hj⟩
  set w := N *ᵥ b4 with hw
  have hmemK : ∀ v : V5, v ∈ LinearMap.ker (toLin' N) ↔ N *ᵥ v = 0 := fun v => by
    rw [LinearMap.mem_ker, toLin'_apply]
  have hwK : w ∈ LinearMap.ker (toLin' N) := by
    rw [hmemK, hw, mulVec_mulVec, hN, inv_invN_sq hx, zero_mulVec]
  have hl0 : LinearIndependent (ZMod 2) (Fin.snoc (Fin.elim0 : Fin 0 → V5) w : Fin 1 → V5) := by
    refine linearIndependent_finSnoc.2 ⟨linearIndependent_empty_type, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot]
    exact hb4
  have hm0 : ∀ i, (Fin.snoc (Fin.elim0 : Fin 0 → V5) w : Fin 1 → V5) i ∈
      LinearMap.ker (toLin' N) := inv_snoc_mem (fun i => i.elim0) hwK
  obtain ⟨k1, hk1, hl1⟩ := inv_exists_extend _ hl0 hm0 (by rw [hker]; norm_num)
  obtain ⟨k2, hk2, hl2⟩ := inv_exists_extend _ hl1 (inv_snoc_mem hm0 hk1)
    (by rw [hker]; norm_num)
  obtain ⟨k3, hk3, hl3⟩ := inv_exists_extend _ hl2
    (inv_snoc_mem (inv_snoc_mem hm0 hk1) hk2) (by rw [hker]; norm_num)
  set v4 : Fin 4 → V5 :=
    Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → V5) w) k1) k2) k3 with hv4
  have hv4K : ∀ i, v4 i ∈ LinearMap.ker (toLin' N) :=
    inv_snoc_mem (inv_snoc_mem (inv_snoc_mem hm0 hk1) hk2) hk3
  have hb4K : b4 ∉ Submodule.span (ZMod 2) (Set.range v4) := by
    intro h
    have hle : Submodule.span (ZMod 2) (Set.range v4) ≤ LinearMap.ker (toLin' N) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv4K i)
    exact hb4 ((hmemK b4).1 (hle h))
  have hb : LinearIndependent (ZMod 2) (Fin.snoc v4 b4 : Fin 5 → V5) :=
    linearIndependent_finSnoc.2 ⟨hl3, hb4K⟩
  have hbe : (Fin.snoc v4 b4 : Fin 5 → V5) = ![w, k1, k2, k3, b4] := by
    funext i
    fin_cases i <;> rfl
  rw [hbe] at hb
  refine isConj_of_basis _ hb fun j => ?_
  have hfix : ∀ v ∈ LinearMap.ker (toLin' N), (x : M5) *ᵥ v = v := fun v hv => by
    rw [inv_mulVec_eq, (hmemK v).1 hv, zero_add]
  have hwK' := hfix w hwK
  have hk1' := hfix k1 hk1
  have hk2' := hfix k2 hk2
  have hk3' := hfix k3 hk3
  fin_cases j <;> simp [invT0, invT0M, Fin.sum_univ_five, hwK', hk1', hk2', hk3',
    inv_mulVec_eq x b4, ← hN, ← hw, add_comm]

theorem inv_isConj_u0 {x : G52} (hx : x ^ 2 = 1) (h2 : commDim x = 2) : IsConj invU0 x := by
  set N := invN x with hN
  have hker : finrank (ZMod 2) (LinearMap.ker (toLin' N)) = 3 := by
    have := inv_rank_nullity x
    rw [← hN] at this
    omega
  have hmemK : ∀ v : V5, v ∈ LinearMap.ker (toLin' N) ↔ N *ᵥ v = 0 := fun v => by
    rw [LinearMap.mem_ker, toLin'_apply]
  have h2' : finrank (ZMod 2) (LinearMap.range (toLin' N)) = 2 := h2
  let bs := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range (toLin' N)) h2'
  set w1 : V5 := (bs 0 : V5) with hw1
  set w2 : V5 := (bs 1 : V5) with hw2
  have hli : LinearIndependent (ZMod 2) ![w1, w2] := by
    have := bs.linearIndependent.map' (LinearMap.range (toLin' N)).subtype
      (Submodule.ker_subtype _)
    convert this using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨b3, hb3⟩ : w1 ∈ LinearMap.range (toLin' N) := (bs 0).2
  obtain ⟨b4, hb4⟩ : w2 ∈ LinearMap.range (toLin' N) := (bs 1).2
  rw [toLin'_apply] at hb3 hb4
  have hRK := inv_range_le_ker hx
  have hlt : LinearMap.range (toLin' N) < LinearMap.ker (toLin' N) := by
    refine lt_of_le_of_ne hRK fun h => ?_
    have := congrArg (fun S : Submodule (ZMod 2) V5 => finrank (ZMod 2) S) h
    simp only [h2', hker] at this
    norm_num at this
  obtain ⟨k, hkK, hkR⟩ := IsConcreteLE.exists_of_lt hlt
  have hw1K : N *ᵥ w1 = 0 := (hmemK _).1 (hRK (bs 0).2)
  have hw2K : N *ᵥ w2 = 0 := (hmemK _).1 (hRK (bs 1).2)
  have hkK' : N *ᵥ k = 0 := (hmemK _).1 hkK
  have hl3 : LinearIndependent (ZMod 2) ![w1, w2, k] := by
    have hspan : Submodule.span (ZMod 2) (Set.range ![w1, w2]) ≤ LinearMap.range (toLin' N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [(bs 0).2, (bs 1).2]
    have := linearIndependent_finSnoc.2 ⟨hli, fun h => hkR (hspan h)⟩
    convert this using 1
    funext i
    fin_cases i <;> rfl
  have hb : LinearIndependent (ZMod 2) ![w1, w2, k, b3, b4] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    replace hc : c 0 • w1 + c 1 • w2 + c 2 • k + c 3 • b3 + c 4 • b4 = 0 := by
      simpa [Fin.sum_univ_five] using hc
    have hNc : N *ᵥ (c 0 • w1 + c 1 • w2 + c 2 • k + c 3 • b3 + c 4 • b4) = 0 := by
      rw [hc, mulVec_zero]
    rw [mulVec_add, mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
      mulVec_smul, mulVec_smul, hw1K, hw2K, hkK', hb3, hb4, smul_zero, smul_zero, smul_zero,
      zero_add, zero_add, zero_add] at hNc
    obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.1 hli _ _ hNc
    rw [h3, h4, zero_smul, zero_smul, add_zero, add_zero] at hc
    have h012 := Fintype.linearIndependent_iff.1 hl3 ![c 0, c 1, c 2] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      exact hc)
    intro i
    fin_cases i
    · exact h012 0
    · exact h012 1
    · exact h012 2
    · exact h3
    · exact h4
  refine isConj_of_basis _ hb fun j => ?_
  have hfix : ∀ v, N *ᵥ v = 0 → (x : M5) *ᵥ v = v := fun v hv => by
    rw [inv_mulVec_eq, ← hN, hv, zero_add]
  have e1 := hfix w1 hw1K
  have e2 := hfix w2 hw2K
  have e3 := hfix k hkK'
  have e4 : (x : M5) *ᵥ b3 = w1 + b3 := by rw [inv_mulVec_eq, ← hN, hb3]
  have e5 : (x : M5) *ᵥ b4 = w2 + b4 := by rw [inv_mulVec_eq, ← hN, hb4]
  fin_cases j <;> simp [invU0, invU0M, Fin.sum_univ_five, e1, e2, e3, e4, e5, add_comm]

end CFSG.GroupTheory.GL52
