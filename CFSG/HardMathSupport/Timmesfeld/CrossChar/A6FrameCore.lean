module

public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent
public import CFSG.ClassicalInvolution.WeakCT.Standard

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

variable {τ : Tag}

private theorem iform_neg_left_a6
    (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

private theorem iform_neg_right_a6
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

section Braid

variable {K : Type} [Field K]

private theorem braid_one_a6 :
    uSL (1 : K) * vSL (-1) * uSL 1 = vSL (-1) * uSL 1 * vSL (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem braid_unit_a6 {a b : K} (ha : a ≠ 0)
    (h : uSL a * vSL (-b) * uSL a = vSL (-b) * uSL a * vSL (-b)) : a * b = 1 := by
  have h0 := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h0
  have h1 := congrFun (congrFun h0 0) 1
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h1
  rcases h1 with h1 | h1
  · linear_combination -h1
  · exact absurd h1 ha

private theorem blk0_uSL_a6 (t : K) : blockSL K 3 2 0 (by omega) (uSL t) =
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_zero, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [uSL]

private theorem blk0_vSL_a6 (t : K) : blockSL K 3 2 0 (by omega) (vSL t) =
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_zero, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [vSL]

private theorem blk1_uSL_a6 (t : K) : blockSL K 3 2 1 (by omega) (uSL t) =
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_one, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [uSL]

private theorem blk1_vSL_a6 (t : K) : blockSL K 3 2 1 (by omega) (vSL t) =
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_one, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [vSL]

end Braid


section Normalize

variable {L : Type} [Field L]

theorem mul_eq_one_of_sl2_hom_a6 (j : Fin τ.rank) (ψ : SL2 L →* ModGL τ L) (a b : L)
    (ha : a ≠ 0) (hu : ∀ t, ψ (uSL t) = xUnit τ L j (a * t))
    (hv : ∀ t, ψ (vSL t) = yUnit τ L j (b * t)) : a * b = 1 := by
  have hS := simpleRootSL2_injective_of_field (Ω := L) τ j
  have h := congrArg ψ (braid_one_a6 (K := L))
  simp only [map_mul, hu, hv, mul_one, mul_neg_one] at h
  have h' : simpleRootSL2 τ L j (uSL a * vSL (-b) * uSL a) =
      simpleRootSL2 τ L j (vSL (-b) * uSL a * vSL (-b)) := by
    simp only [map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL]
    exact h
  exact braid_unit_a6 ha (hS h')

theorem exists_normalized_a2Frame_a6 (ρ : SL(3, L) →* ModGL τ L) (j j' : Fin τ.rank)
    (he01 : ∃ e : Lˣ, ∀ t, ρ (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) t) = xUnit τ L j ((e : L) * t))
    (he10 : ∃ e : Lˣ, ∀ t, ρ (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) t) = yUnit τ L j ((e : L) * t))
    (he12 : ∃ e : Lˣ, ∀ t, ρ (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) t) = xUnit τ L j' ((e : L) * t))
    (he21 : ∃ e : Lˣ, ∀ t, ρ (Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) t) = yUnit τ L j' ((e : L) * t)) :
    ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = simpleRootSL2 τ L j ∧
      θ.comp (blockSL L 3 2 1 (by omega)) = simpleRootSL2 τ L j' := by
  obtain ⟨e01, he01⟩ := he01
  obtain ⟨e10, he10⟩ := he10
  obtain ⟨e12, he12⟩ := he12
  obtain ⟨e21, he21⟩ := he21
  have hu1 : (e01 : L) * e10 = 1 := by
    refine mul_eq_one_of_sl2_hom_a6 j (ρ.comp (blockSL L 3 2 0 (by omega))) e01 e10 e01.ne_zero
      (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk0_uSL_a6, he01]
    · rw [MonoidHom.comp_apply, blk0_vSL_a6, he10]
  have hu2 : (e12 : L) * e21 = 1 := by
    refine mul_eq_one_of_sl2_hom_a6 j' (ρ.comp (blockSL L 3 2 1 (by omega))) e12 e21
      e12.ne_zero (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk1_uSL_a6, he12]
    · rw [MonoidHom.comp_apply, blk1_vSL_a6, he21]
  let d : Fin 3 → Lˣ := ![(e01 * e12)⁻¹, e12⁻¹, 1]
  let θ : SL(3, L) →* ModGL τ L := ρ.comp (conjDiag3Hom d)
  have hθ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      θ (Matrix.SpecialLinearGroup.transvection hij t) =
      ρ (Matrix.SpecialLinearGroup.transvection hij ((d i : L) * t * ((d j)⁻¹ : Lˣ))) := by
    intro i j hij t
    rw [MonoidHom.comp_apply, conjDiag3Hom_apply, conjDiag3_transvection]
  refine ⟨θ, ?_, ?_⟩
  · refine eq_simpleRootSL2 j (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk0_uSL_a6, hθ, he01]
      congr 1
      simp [d]
      field_simp
    · rw [MonoidHom.comp_apply, blk0_vSL_a6, hθ, he10]
      congr 1
      simp [d]
      field_simp
      linear_combination hu1 * t
  · refine eq_simpleRootSL2 j' (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk1_uSL_a6, hθ, he12]
      congr 1
      simp [d]
    · rw [MonoidHom.comp_apply, blk1_vSL_a6, hθ, he21]
      congr 1
      simp [d]
      linear_combination hu2 * t

end Normalize

section Commute

variable {L : Type} [Field L]

theorem not_isRoot_single_add_of_cartan_zero_a6 (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p q : Fin τ.rank} (hc : τ.cartan p q = 0) {α β : Fin τ.rank → ℤ}
    (hα : α = Pi.single p 1 ∨ α = -Pi.single p 1)
    (hβ : β = Pi.single q 1 ∨ β = -Pi.single q 1) : ¬ IsRoot τ (α + β) := by
  intro hroot
  have hs : ∀ j : Fin τ.rank, τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hpp : iform α α = 2 := by
    rcases hα with rfl | rfl
    · rw [iform_single_single, hs]
      rfl
    · rw [iform_neg_left_a6, iform_neg_right_a6, neg_neg, iform_single_single, hs]
      rfl
  have hqq : iform β β = 2 := by
    rcases hβ with rfl | rfl
    · rw [iform_single_single, hs]
      rfl
    · rw [iform_neg_left_a6, iform_neg_right_a6, neg_neg, iform_single_single, hs]
      rfl
  have h0 : iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single q 1) = 0 := by
    rw [iform_single_left, Finset.sum_eq_single q (fun k _ hk => by simp [hk]) (by simp)]
    simp [hc]
  have hpq : iform α β = 0 := by
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      simp only [iform_neg_left_a6, iform_neg_right_a6, h0, neg_zero]
  have hqp : iform β α = 0 := by rw [iform_comm, hpq]
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hroot
  rw [iform_add_left, iform_add_right, iform_add_right, hpp, hqq, hpq, hqp, hs] at hj
  omega

theorem commute_pinnedX_of_cartan_zero_a6 (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p q : Fin τ.rank} (hpq : p ≠ q) (hc : τ.cartan p q = 0) {α β : Fin τ.rank → ℤ}
    (hα : α = Pi.single p 1 ∨ α = -Pi.single p 1)
    (hβ : β = Pi.single q 1 ∨ β = -Pi.single q 1) (s t : L) :
    Commute (pinnedX τ L α s) (pinnedX τ L β t) := by
  have hαr : IsRoot τ α := by
    rcases hα with rfl | rfl
    exacts [IsRoot.basis p, IsRoot.neg (IsRoot.basis p)]
  have hβr : IsRoot τ β := by
    rcases hβ with rfl | rfl
    exacts [IsRoot.basis q, IsRoot.neg (IsRoot.basis q)]
  have hne : α ≠ β := by
    intro h
    have := congrFun h p
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> simp [hpq] at this
  have hne' : α ≠ -β := by
    intro h
    have := congrFun h p
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> simp [hpq] at this
  exact (simply_laced_root_commutator_unit τ hτ hαr hβr hne hne').2
    (not_isRoot_single_add_of_cartan_zero_a6 hτ hc hα hβ) L _
    (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨s, rfl⟩) _
    (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem commute_simpleRootSL2_of_cartan_zero_a6 (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p q : Fin τ.rank} (hpq : p ≠ q) (hc : τ.cartan p q = 0) (A B : SL2 L) :
    Commute (simpleRootSL2 τ L p A) (simpleRootSL2 τ L q B) := by
  have hxy : ∀ s t : L, Commute (xUnit τ L p s) (xUnit τ L q t) ∧
      Commute (xUnit τ L p s) (yUnit τ L q t) ∧ Commute (yUnit τ L p s) (xUnit τ L q t) ∧
      Commute (yUnit τ L p s) (yUnit τ L q t) := fun s t => by
    rw [← pinnedX_single, ← pinnedX_single, ← pinnedX_neg_single, ← pinnedX_neg_single]
    exact ⟨commute_pinnedX_of_cartan_zero_a6 hτ hpq hc (Or.inl rfl) (Or.inl rfl) s t,
      commute_pinnedX_of_cartan_zero_a6 hτ hpq hc (Or.inl rfl) (Or.inr rfl) s t,
      commute_pinnedX_of_cartan_zero_a6 hτ hpq hc (Or.inr rfl) (Or.inl rfl) s t,
      commute_pinnedX_of_cartan_zero_a6 hτ hpq hc (Or.inr rfl) (Or.inr rfl) s t⟩
  have h1 : ∀ g : ModGL τ L, (∀ t, Commute g (xUnit τ L q t)) →
      (∀ t, Commute g (yUnit τ L q t)) → ∀ B : SL2 L, Commute g (simpleRootSL2 τ L q B) := by
    intro g hx hy B
    have hB : B ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
      rw [sl2_closure_upper_lower]
      trivial
    induction hB using Subgroup.closure_induction with
    | mem x hx' =>
      rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact (simpleRootSL2_uSL q c) ▸ hx c
      · exact (simpleRootSL2_vSL q c) ▸ hy c
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_right
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
    rw [sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx' =>
    rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [show sl2Upper L c = uSL c from rfl, simpleRootSL2_uSL]
      exact h1 _ (fun t => (hxy c t).1) (fun t => (hxy c t).2.1) B
    · rw [show sl2Lower L c = vSL c from rfl, simpleRootSL2_vSL]
      exact h1 _ (fun t => (hxy c t).2.2.1) (fun t => (hxy c t).2.2.2) B
  | one => rw [map_one]; exact Commute.one_left _
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_left

end Commute

structure A6ChainData (τ : Tag) (nd : Fin 6 → Fin τ.rank) : Prop where
  simplyLaced : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8
  isRoot : ∀ a b : Fin 7, a ≠ b → IsRoot τ (chainRoot nd a b)
  add : ∀ a b c : Fin 7, chainRoot nd a b + chainRoot nd b c = chainRoot nd a c
  succ : ∀ c : Fin 6, chainRoot nd c.castSucc c.succ = Pi.single (nd c) 1
  ne_pair : ∀ a k b : Fin 7, a ≠ k → k ≠ b → a ≠ b →
    chainRoot nd a k ≠ chainRoot nd k b ∧ chainRoot nd a k ≠ -chainRoot nd k b
  orth : ∀ i j : Fin 6, (i : ℕ) + 1 < j → nd i ≠ nd j ∧ τ.cartan (nd i) (nd j) = 0

variable (τ) in
@[expose] def A6ChainFrames (nd : Fin 6 → Fin τ.rank) : Prop :=
  ∀ (L : Type) [Field L] (c : Fin 5), ∃ θ : SL(3, L) →* ModGL τ L,
    θ.comp (blockSL L 3 2 0 (by omega)) = simpleRootSL2 τ L (nd c.castSucc) ∧
    θ.comp (blockSL L 3 2 1 (by omega)) = simpleRootSL2 τ L (nd c.succ)

section Family

variable {nd : Fin 6 → Fin τ.rank} (hD : A6ChainData τ nd) (hF : A6ChainFrames τ nd)

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

variable (L : Type) [Field L]

noncomputable def a6CTFamily : CTFamily L (ModGL τ L) 6 where
  ι i := simpleRootSL2 τ L (nd i)
  θ i := if h : i.val < 5 then (hF L ⟨i.val, h⟩).choose else 1
  left i hi := by
    have h : i.val < 5 := by omega
    simp only [dite_eq_left h]
    exact (hF L ⟨i.val, h⟩).choose_spec.1
  right i hi := by
    have h : i.val < 5 := by omega
    simp only [dite_eq_left h]
    exact (hF L ⟨i.val, h⟩).choose_spec.2
  comm i j hij a b :=
    (commute_simpleRootSL2_of_cartan_zero_a6 hD.simplyLaced (hD.orth i j hij).1
      (hD.orth i j hij).2 a b).eq

@[expose] noncomputable def a6Frame : SL(7, L) →* ModGL τ L :=
  (exists_hom_of_ctFamily (a6CTFamily hD hF L)).choose

theorem a6Frame_comp_blockSL2 (i : Fin 6) :
    (a6Frame hD hF L).comp (blockSL2 L 6 i) = simpleRootSL2 τ L (nd i) :=
  (exists_hom_of_ctFamily (a6CTFamily hD hF L)).choose_spec.1 i

variable {L}

theorem blockSL2_uSL_a6 (i : Fin 6) (t : L) : blockSL2 L 6 i (uSL t) =
    Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, uSL]

theorem blockSL2_vSL_a6 (i : Fin 6) (t : L) : blockSL2 L 6 i (vSL t) =
    Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne' t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, vSL]

theorem a6Frame_castSucc (i : Fin 6) (t : L) :
    a6Frame hD hF L (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne t) =
      xUnit τ L (nd i) t := by
  rw [← blockSL2_uSL_a6, ← MonoidHom.comp_apply, a6Frame_comp_blockSL2, simpleRootSL2_uSL]

theorem a6Frame_succ (i : Fin 6) (t : L) :
    a6Frame hD hF L
        (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne' t) =
      yUnit τ L (nd i) t := by
  rw [← blockSL2_vSL_a6, ← MonoidHom.comp_apply, a6Frame_comp_blockSL2, simpleRootSL2_vSL]

theorem a6Frame_ne_one : ∃ B : SL(7, L), a6Frame hD hF L B ≠ 1 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := 0)).ne 1, ?_⟩
  rw [a6Frame_castSucc]
  intro h
  have h' : xUnit τ L (nd 0) 1 = xUnit τ L (nd 0) 0 := by
    rw [h, xUnit_zero]
  rw [← pinnedX_single, ← pinnedX_single] at h'
  exact one_ne_zero (pinnedX_injective τ L _ h')

theorem ker_a6Frame_le_center : (a6Frame hD hF L).ker ≤ Subgroup.center SL(7, L) :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
    (a6Frame_ne_one hD hF)

end Family

section Transv

variable {nd : Fin 6 → Fin τ.rank} (hD : A6ChainData τ nd) (hF : A6ChainFrames τ nd)
  {L : Type} [Field L]

private def adj7 (a b : Fin 7) : Bool := (a.val + 1 == b.val) || (b.val + 1 == a.val)

private def reach7 : ℕ → Fin 7 → Fin 7 → Bool
  | 0, a, b => adj7 a b
  | n + 1, a, b => reach7 n a b ||
      decide (∃ k : Fin 7, a ≠ k ∧ k ≠ b ∧ a ≠ b ∧ reach7 n a k = true ∧ reach7 n k b = true)

private theorem reach7_all : ∀ a b : Fin 7, a ≠ b → reach7 3 a b = true := by
  decide +kernel

variable (L) in
@[expose] def A6Transv (a b : Fin 7) : Prop :=
  ∃ ε : Lˣ, ∀ (hab : a ≠ b) (t : L),
    a6Frame hD hF L (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX τ L (chainRoot nd a b) ((ε : L) * t)

theorem A6Transv.step {a k b : Fin 7} (hak : a ≠ k) (hkb : k ≠ b) (hab : a ≠ b)
    (h1 : A6Transv hD hF L a k) (h2 : A6Transv hD hF L k b) : A6Transv hD hF L a b := by
  obtain ⟨ε1, he1⟩ := h1
  obtain ⟨ε2, he2⟩ := h2
  have hα : IsRoot τ (chainRoot nd a k) := hD.isRoot a k hak
  have hβ : IsRoot τ (chainRoot nd k b) := hD.isRoot k b hkb
  obtain ⟨hne, hne'⟩ := hD.ne_pair a k b hak hkb hab
  obtain ⟨hκ, hcomm⟩ := (simply_laced_root_commutator_unit τ hD.simplyLaced hα hβ hne hne').1
    (by rw [hD.add]; exact hD.isRoot a b hab)
  have hκ' : ((commConst τ (chainRoot nd a k) (chainRoot nd k b) (1, 1) : ℤ) : L) ≠ 0 := by
    rcases hκ with h | h <;> simp [h]
  refine ⟨ε1 * ε2 * Units.mk0 _ hκ', fun hab' t => ?_⟩
  have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection hak hkb hab' t 1
  rw [mul_one] at hc
  rw [← hc, map_commutatorElement, he1 hak t, he2 hkb 1, hcomm L, hD.add]
  congr 1
  simp only [Units.val_mul, Units.val_mk0]
  ring

private theorem A6Transv.adjacent {a b : Fin 7} (h : adj7 a b = true) : A6Transv hD hF L a b := by
  simp only [adj7, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · obtain ⟨c, rfl, rfl⟩ : ∃ c : Fin 6, c.castSucc = a ∧ c.succ = b :=
      ⟨⟨a.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp [h])⟩
    refine ⟨1, fun hab t => ?_⟩
    rw [show hab = (Fin.castSucc_lt_succ (i := c)).ne from rfl, a6Frame_castSucc, hD.succ,
      ← pinnedX_single, Units.val_one, one_mul]
  · obtain ⟨c, rfl, rfl⟩ : ∃ c : Fin 6, c.succ = a ∧ c.castSucc = b :=
      ⟨⟨b.val, by omega⟩, Fin.ext (by simp [h]), Fin.ext rfl⟩
    refine ⟨1, fun hab t => ?_⟩
    rw [show hab = (Fin.castSucc_lt_succ (i := c)).ne' from rfl, a6Frame_succ,
      CFSG.RankThree.E6.chainRoot_swap, hD.succ, ← pinnedX_neg_single, Units.val_one, one_mul]

private theorem A6Transv.of_reach7 : ∀ (n : ℕ) (a b : Fin 7), reach7 n a b = true →
    A6Transv hD hF L a b := by
  intro n
  induction n with
  | zero => exact fun a b h => A6Transv.adjacent hD hF h
  | succ n ih =>
    intro a b h
    simp only [reach7, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨k, hak, hkb, hab, h1, h2⟩
    · exact ih a b h
    · exact A6Transv.step hD hF hak hkb hab (ih a k h1) (ih k b h2)

theorem a6Frame_transv (a b : Fin 7) (hab : a ≠ b) :
    ∃ ε : Lˣ, ∀ t : L, a6Frame hD hF L (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX τ L (chainRoot nd a b) ((ε : L) * t) := by
  obtain ⟨ε, hε⟩ := A6Transv.of_reach7 hD hF (L := L) 3 a b (reach7_all a b hab)
  exact ⟨ε, hε hab⟩

end Transv

end CFSG.HardMathSupport.Timmesfeld.CrossChar
