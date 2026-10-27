module

public import CFSG.LieType.Chevalley.CorootCoordinates

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.RankThree.PartOne.KA5L.Frames
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups commutatorElement

section Blocks

variable {L : Type} [Field L]

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

theorem blockSL2_uSL_eq {m : ℕ} (c : Fin m) (t : L) :
    blockSL2 L m c (uSL t) =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  rw [blockMat_apply]
  split_ifs with h
  · obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := h
    have hca : a = c.castSucc ∨ a = c.succ := by
      rcases (by omega : a.val = c.val ∨ a.val = c.val + 1) with e | e
      · exact Or.inl (Fin.ext (by simpa using e))
      · exact Or.inr (Fin.ext (by simpa using e))
    have hcb : b = c.castSucc ∨ b = c.succ := by
      rcases (by omega : b.val = c.val ∨ b.val = c.val + 1) with e | e
      · exact Or.inl (Fin.ext (by simpa using e))
      · exact Or.inr (Fin.ext (by simpa using e))
    rcases hca with rfl | rfl <;> rcases hcb with rfl | rfl <;>
      simp [uSL, Fin.ext_iff]
  · simp only [Matrix.add_apply, Matrix.single_apply]
    have : ¬ (c.castSucc = a ∧ c.succ = b) := by
      rintro ⟨rfl, rfl⟩
      apply h
      simp
    simp [this]

theorem blockSL2_vSL_eq {m : ℕ} (c : Fin m) (t : L) :
    blockSL2 L m c (vSL t) =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne' t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  rw [blockMat_apply]
  split_ifs with h
  · obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := h
    have hca : a = c.castSucc ∨ a = c.succ := by
      rcases (by omega : a.val = c.val ∨ a.val = c.val + 1) with e | e
      · exact Or.inl (Fin.ext (by simpa using e))
      · exact Or.inr (Fin.ext (by simpa using e))
    have hcb : b = c.castSucc ∨ b = c.succ := by
      rcases (by omega : b.val = c.val ∨ b.val = c.val + 1) with e | e
      · exact Or.inl (Fin.ext (by simpa using e))
      · exact Or.inr (Fin.ext (by simpa using e))
    rcases hca with rfl | rfl <;> rcases hcb with rfl | rfl <;>
      simp [vSL, Fin.ext_iff]
  · simp only [Matrix.add_apply, Matrix.single_apply]
    have : ¬ (c.succ = a ∧ c.castSucc = b) := by
      rintro ⟨rfl, rfl⟩
      apply h
      simp
    simp [this]

end Blocks

section RankOne

variable
  {τ : Tag} {L : Type} [Field L]

theorem exists_rootSL2_units {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ u e : Lˣ, (∀ t, rootSL2 τ L β (uSL t) = pinnedX τ L β ((u : L) * t)) ∧
      ∀ t, rootSL2 τ L β (vSL t) = pinnedX τ L (-β) ((e : L) * t) := by
  obtain ⟨u, -, hu⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ β)
  obtain ⟨e, he, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  refine ⟨u, Units.mkOfMulEqOne e e he, fun t => ?_, fun t => ?_⟩
  · rw [rootSL2_uSL_eq, hu]
  · rw [hv, Units.val_mkOfMulEqOne]

theorem eq_rootSL2 {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (φ : SL2 L →* ModGL τ L)
    (hu : ∀ t, φ (uSL t) = rootSL2 τ L β (uSL t)) (κ : Lˣ)
    (hv : ∀ t, φ (vSL t) = pinnedX τ L (-β) ((κ : L) * t)) : φ = rootSL2 τ L β := by
  obtain ⟨u, e, hu', hv'⟩ := exists_rootSL2_units (L := L) hβ
  have hrange : φ.range ≤ rootSubgroup τ L β ⊔ rootSubgroup τ L (-β) := by
    rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨A, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · change φ (uSL c) ∈ _
      rw [hu, hu']
      exact Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨_, rfl⟩)
    · change φ (vSL c) ∈ _
      rw [hv]
      exact Subgroup.mem_sup_right (mem_rootSubgroup.2 ⟨_, rfl⟩)
  let cR : SL2 L →* ↥(rootSubgroup τ L β ⊔ rootSubgroup τ L (-β)) :=
    φ.codRestrict _ fun A => hrange ⟨A, rfl⟩
  let T : SL2 L →* SL2 L := (rootSL2Equiv (K := L) hβ).symm.toMonoidHom.comp cR
  have hT : ∀ A, rootSL2 τ L β (T A) = φ A := fun A => by
    rw [← coe_rootSL2Equiv hβ]
    change (((rootSL2Equiv hβ) ((rootSL2Equiv hβ).symm (cR A)) : ModGL τ L)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hTu : ∀ c, T (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L c) =
      CFSG.LocalAnalysis.ComponentInitial.sl2Upper L ((1 : Lˣ) * (RingEquiv.refl L) c) :=
    fun c => by
      apply rootSL2_injective_of_field β
      rw [hT]
      change φ (uSL c) = rootSL2 τ L β (uSL ((1 : Lˣ) * c))
      rw [hu, Units.val_one, one_mul]
  have hTl : ∀ c, T (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      CFSG.LocalAnalysis.ComponentInitial.sl2Lower L ((κ * e⁻¹ : Lˣ) * (RingEquiv.refl L) c) :=
    fun c => by
      apply rootSL2_injective_of_field β
      rw [hT]
      change φ (vSL c) = rootSL2 τ L β (vSL (((κ * e⁻¹ : Lˣ) : L) * c))
      rw [hv, hv']
      congr 1
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
  obtain ⟨hab, -⟩ := sl2_semilinear_root_compatibility (RingEquiv.refl L) 1 (κ * e⁻¹) T hTu hTl
  have hκ : κ = e := by
    rw [one_mul, mul_inv_eq_one] at hab
    exact hab
  refine MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hu c
  · change φ (vSL c) = rootSL2 τ L β (vSL c)
    rw [hv, hv', hκ]

theorem exists_comp_conjSL_eq_rootSL2 {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (φ : SL2 L →* ModGL τ L) (a b : Lˣ) (hu : ∀ t, φ (uSL t) = pinnedX τ L β ((a : L) * t))
    (hv : ∀ t, φ (vSL t) = pinnedX τ L (-β) ((b : L) * t)) :
    ∃ s : Lˣ, φ.comp (conjSL (diagUnitOne s)) = rootSL2 τ L β := by
  obtain ⟨u, e, hu', -⟩ := exists_rootSL2_units (L := L) hβ
  refine ⟨a⁻¹ * u, eq_rootSL2 hβ _ (fun t => ?_) (b * (a⁻¹ * u)⁻¹) fun t => ?_⟩
  · rw [MonoidHom.comp_apply, hu']
    change φ (conjSL (diagUnitOne (a⁻¹ * u)) (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L t)) = _
    rw [conjSL_sl2Upper]
    change φ (uSL _) = _
    rw [hu]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · rw [MonoidHom.comp_apply]
    change φ (conjSL (diagUnitOne (a⁻¹ * u)) (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L t)) = _
    rw [conjSL_sl2Lower]
    change φ (vSL _) = _
    rw [hv]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

theorem rootSL2_HSL_mem_torusGroup {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (t : Lˣ) :
    rootSL2 τ L β (HSL t) ∈ torusGroup τ L :=
  (exceptional_Lang_root_rank_one_torus_transport τ L hβ).2.1 t

end RankOne

section A2

variable {L : Type} [Field L]

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

theorem conjDiag3_blk0 (d : Fin 3 → Lˣ) :
    (conjDiag3Hom d).comp (blockSL L 3 2 0 (by omega)) =
      (blockSL L 3 2 0 (by omega)).comp (conjSL (diagUnitOne (d 0 * (d 1)⁻¹))) := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · simp only [MonoidHom.comp_apply, conjDiag3Hom_apply, conjSL_sl2Upper]
    change conjDiag3 d (blockSL L 3 2 0 _ (uSL c)) = blockSL L 3 2 0 _ (uSL _)
    rw [CFSG.RankThree.PartOne.KA5L.blk0_uSL, CFSG.RankThree.PartOne.KA5L.blk0_uSL,
      conjDiag3_transvection]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  · simp only [MonoidHom.comp_apply, conjDiag3Hom_apply, conjSL_sl2Lower]
    change conjDiag3 d (blockSL L 3 2 0 _ (vSL c)) = blockSL L 3 2 0 _ (vSL _)
    rw [CFSG.RankThree.PartOne.KA5L.blk0_vSL, CFSG.RankThree.PartOne.KA5L.blk0_vSL,
      conjDiag3_transvection]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, inv_inv]
    field_simp

theorem conjDiag3_blk1 (d : Fin 3 → Lˣ) :
    (conjDiag3Hom d).comp (blockSL L 3 2 1 (by omega)) =
      (blockSL L 3 2 1 (by omega)).comp (conjSL (diagUnitOne (d 1 * (d 2)⁻¹))) := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · simp only [MonoidHom.comp_apply, conjDiag3Hom_apply, conjSL_sl2Upper]
    change conjDiag3 d (blockSL L 3 2 1 _ (uSL c)) = blockSL L 3 2 1 _ (uSL _)
    rw [CFSG.RankThree.PartOne.KA5L.blk1_uSL, CFSG.RankThree.PartOne.KA5L.blk1_uSL,
      conjDiag3_transvection]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  · simp only [MonoidHom.comp_apply, conjDiag3Hom_apply, conjSL_sl2Lower]
    change conjDiag3 d (blockSL L 3 2 1 _ (vSL c)) = blockSL L 3 2 1 _ (vSL _)
    rw [CFSG.RankThree.PartOne.KA5L.blk1_vSL, CFSG.RankThree.PartOne.KA5L.blk1_vSL,
      conjDiag3_transvection]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, inv_inv]
    field_simp

variable
  {τ : Tag}

theorem exists_normalized_a2Frame {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (σ 0 1) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (σ 1 2) := by
  obtain ⟨e01, h01⟩ := h.transv 0 1 (by decide)
  obtain ⟨e10, h10⟩ := h.transv 1 0 (by decide)
  obtain ⟨e12, h12⟩ := h.transv 1 2 (by decide)
  obtain ⟨e21, h21⟩ := h.transv 2 1 (by decide)
  obtain ⟨s0, hs0⟩ := exists_comp_conjSL_eq_rootSL2 (h.isRoot 0 1 (by decide))
    (ρ.comp (blockSL L 3 2 0 (by omega))) e01 e10
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk0_uSL, h01])
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk0_vSL, h10, h.neg])
  obtain ⟨s1, hs1⟩ := exists_comp_conjSL_eq_rootSL2 (h.isRoot 1 2 (by decide))
    (ρ.comp (blockSL L 3 2 1 (by omega))) e12 e21
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk1_uSL, h12])
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk1_vSL, h21, h.neg])
  set d : Fin 3 → Lˣ := ![s0, 1, s1⁻¹] with hd
  refine ⟨ρ.comp (conjDiag3Hom d), ?_, ?_⟩
  · rw [MonoidHom.comp_assoc, conjDiag3_blk0, ← MonoidHom.comp_assoc]
    convert hs0 using 3
    simp [hd]
  · rw [MonoidHom.comp_assoc, conjDiag3_blk1, ← MonoidHom.comp_assoc]
    convert hs1 using 3
    simp [hd]

end A2

section Chain

variable {τ : Tag} {m : ℕ}

@[expose] def chainω (β : Fin m → Fin τ.rank → ℤ) (k : ℕ) : Fin τ.rank → ℤ :=
  ∑ c : Fin m, if (c : ℕ) < k then β c else 0

@[expose] def chainσ (β : Fin m → Fin τ.rank → ℤ) (a b : Fin (m + 1)) : Fin τ.rank → ℤ :=
  chainω β b - chainω β a

theorem chainσ_neg (β : Fin m → Fin τ.rank → ℤ) (a b : Fin (m + 1)) :
    chainσ β b a = -chainσ β a b := by
  simp only [chainσ, neg_sub]

theorem chainσ_add (β : Fin m → Fin τ.rank → ℤ) (a b c : Fin (m + 1)) :
    chainσ β a b + chainσ β b c = chainσ β a c := by
  simp only [chainσ]
  abel

theorem chainω_zero (β : Fin m → Fin τ.rank → ℤ) : chainω β 0 = 0 := by
  simp [chainω]

theorem chainω_succ (β : Fin m → Fin τ.rank → ℤ) {k : ℕ} (hk : k < m) :
    chainω β (k + 1) = chainω β k + β ⟨k, hk⟩ := by
  classical
  simp only [chainω]
  have hs : β ⟨k, hk⟩ = ∑ c : Fin m, if (⟨k, hk⟩ : Fin m) = c then β c else 0 := by
    rw [Finset.sum_ite_eq]
    simp
  rw [hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : (c : ℕ) < k
  · have h2 : ¬ (⟨k, hk⟩ : Fin m) = c := fun h => by rw [← h] at h1; exact lt_irrefl _ h1
    simp only [h1, Nat.lt_succ_of_lt h1, h2, ite_true, ite_false, add_zero]
  · by_cases h3 : (c : ℕ) = k
    · have h4 : c = ⟨k, hk⟩ := Fin.ext h3
      subst h4
      simp
    · have h5 : ¬ (c : ℕ) < k + 1 := by omega
      have h6 : ¬ ⟨k, hk⟩ = c := fun h => h3 (by rw [← h])
      simp [h1, h5, h6]

theorem chainσ_castSucc_succ (β : Fin m → Fin τ.rank → ℤ) (c : Fin m) :
    chainσ β c.castSucc c.succ = β c := by
  rw [chainσ, Fin.val_succ, Fin.val_castSucc, chainω_succ β c.2]
  abel

theorem chainσ_of_val_eq (β : Fin m → Fin τ.rank → ℤ) {a b : Fin (m + 1)}
    (h : (b : ℕ) = a + 1) : chainσ β a b = β ⟨a, by omega⟩ := by
  have e1 : (⟨a, by omega⟩ : Fin m).castSucc = a := Fin.ext rfl
  have e2 : (⟨a, by omega⟩ : Fin m).succ = b := Fin.ext (by simp [h])
  rw [← chainσ_castSucc_succ β ⟨a, by omega⟩, e1, e2]

@[expose] def chainGram (c d : Fin m) : ℤ :=
  if c = d then 2 else if (c : ℕ) + 1 = d ∨ (d : ℕ) + 1 = c then -1 else 0

theorem iform_chainω
    {β : Fin m → Fin τ.rank → ℤ} (hG : ∀ c d, iform (β c) (β d) = chainGram c d)
    (d : Fin m) : ∀ k, k ≤ m → iform (chainω β k) (β d) =
      (if (d : ℕ) < k then 2 else 0) - (if 1 ≤ (d : ℕ) ∧ (d : ℕ) ≤ k then 1 else 0) -
        (if (d : ℕ) + 1 < k then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [chainω_zero]
    simp [iform]
    omega
  | succ k ih =>
    intro hk
    rw [chainω_succ β (by omega), iform_add_left, ih (by omega), hG, chainGram]
    have hd := d.2
    by_cases e1 : (⟨k, by omega⟩ : Fin m) = d
    · have : (d : ℕ) = k := by rw [← e1]
      simp only [e1, ite_true]
      split_ifs <;> omega
    · have hne : (d : ℕ) ≠ k := fun h => e1 (Fin.ext h.symm)
      simp only [e1, ite_false]
      split_ifs <;> simp_all <;> omega

theorem iform_chainσ
    {β : Fin m → Fin τ.rank → ℤ} (hG : ∀ c d, iform (β c) (β d) = chainGram c d)
    (a b : Fin (m + 1)) (d : Fin m) :
    iform (chainσ β a b) (β d) =
      ((if (d : ℕ) < b then 2 else 0) - (if 1 ≤ (d : ℕ) ∧ (d : ℕ) ≤ b then 1 else 0) -
        (if (d : ℕ) + 1 < b then 1 else 0)) -
      ((if (d : ℕ) < a then 2 else 0) - (if 1 ≤ (d : ℕ) ∧ (d : ℕ) ≤ a then 1 else 0) -
        (if (d : ℕ) + 1 < a then 1 else 0)) := by
  rw [chainσ, iform_sub_left, iform_chainω hG d b (by omega), iform_chainω hG d a (by omega)]

theorem isRoot_chainσ
    {β : Fin m → Fin τ.rank → ℤ} (hβ : ∀ c, IsRoot τ (β c))
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d) {a b : Fin (m + 1)} (hab : a ≠ b) :
    IsRoot τ (chainσ β a b) := by
  have up : ∀ (a : Fin (m + 1)) (k : ℕ) (hk : (a : ℕ) + k + 1 < m + 1),
      IsRoot τ (chainσ β a ⟨a + k + 1, hk⟩) := by
    intro a k
    induction k with
    | zero =>
      intro hk
      have ha : (a : ℕ) < m := by omega
      have e : chainσ β a ⟨a + 0 + 1, hk⟩ = β ⟨a, ha⟩ := by
        have := chainσ_castSucc_succ β ⟨a, ha⟩
        convert this using 2 <;> ext <;> simp
      rw [e]
      exact hβ _
    | succ k ih =>
      intro hk
      have hk' : (a : ℕ) + k + 1 < m := by omega
      set b : Fin (m + 1) := ⟨a + k + 1, by omega⟩ with hb
      have hσ := ih (by omega)
      have hstep : chainσ β a ⟨a + (k + 1) + 1, hk⟩ = chainσ β a b + β ⟨a + k + 1, hk'⟩ := by
        simp only [chainσ, hb]
        rw [show (a : ℕ) + (k + 1) + 1 = a + k + 1 + 1 by ring, chainω_succ β hk']
        abel
      have hi : iform (β ⟨a + k + 1, hk'⟩) (chainσ β a b) = -1 := by
        rw [iform_comm, iform_chainσ hG]
        simp only [hb]
        split_ifs <;> omega
      have hcp : corootPair (β ⟨a + k + 1, hk'⟩) (chainσ β a b) = -1 := by
        have h2 : iform (β ⟨a + k + 1, hk'⟩) (β ⟨a + k + 1, hk'⟩) = 2 := by
          rw [hG, chainGram]
          exact ite_eq_left_iff.2 fun h => absurd rfl h
        rw [corootPair, hi, h2]
        rfl
      have := IsRoot.smul hσ (rootReflection (β ⟨a + k + 1, hk'⟩))
      rwa [rootReflection_smul (hβ _), hcp, neg_one_smul, sub_neg_eq_add, ← hstep] at this
  rcases lt_or_gt_of_ne hab with h | h
  · have := up a ((b : ℕ) - a - 1) (by omega)
    convert this using 2
    ext
    simp only
    omega
  · have := up b ((a : ℕ) - b - 1) (by omega)
    rw [chainσ_neg]
    convert IsRoot.neg this using 3
    ext
    simp only
    omega

section Hom

variable
  {L : Type} [Field L]

theorem commute_rootSL2_of_iform_eq_zero (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hγ : IsRoot τ γ) (h0 : iform α γ = 0)
    (A B : SL2 L) : Commute (rootSL2 τ L α A) (rootSL2 τ L γ B) := by
  have hpair : ∀ s t : Fin τ.rank → ℤ, (s = α ∨ s = -α) → (t = γ ∨ t = -γ) →
      ∀ x ∈ rootSubgroup τ L s, ∀ y ∈ rootSubgroup τ L t, Commute x y := by
    intro s t hs ht
    have hsr : IsRoot τ s := by rcases hs with rfl | rfl; exacts [hα, IsRoot.neg hα]
    have htr : IsRoot τ t := by rcases ht with rfl | rfl; exacts [hγ, IsRoot.neg hγ]
    have hst : iform s t = 0 := by
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
        simp only [show ∀ v : Fin τ.rank → ℤ, -v = (-1 : ℤ) • v from fun v => by
          rw [neg_one_smul], iform_smul_left, iform_smul_right, h0, mul_zero]
    have hss := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hsr
    have htt := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ htr
    have hne : s ≠ t := fun h => by rw [h] at hst; omega
    have hne' : s ≠ -t := fun h => by
      rw [h, show -t = (-1 : ℤ) • t by rw [neg_one_smul], iform_smul_left] at hst
      omega
    have hnot : ¬ IsRoot τ (s + t) := by
      intro hr
      have := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hr
      rw [iform_add_left, iform_add_right, iform_add_right, hst, iform_comm t s, hst] at this
      omega
    exact (simply_laced_root_commutator_unit τ hτ hsr htr hne hne').2 hnot L
  obtain ⟨uα, eα, huα, hvα⟩ := exists_rootSL2_units (L := L) hα
  obtain ⟨uγ, eγ, huγ, hvγ⟩ := exists_rootSL2_units (L := L) hγ
  have h1 : ∀ g, (g ∈ rootSubgroup τ L α ∨ g ∈ rootSubgroup τ L (-α)) →
      ∀ B : SL2 L, Commute g (rootSL2 τ L γ B) := by
    intro g hg B
    have hB : B ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
      trivial
    induction hB using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change Commute g (rootSL2 τ L γ (uSL c))
        rw [huγ]
        rcases hg with hg | hg
        · exact hpair α γ (Or.inl rfl) (Or.inl rfl) g hg _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
        · exact hpair (-α) γ (Or.inr rfl) (Or.inl rfl) g hg _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
      · change Commute g (rootSL2 τ L γ (vSL c))
        rw [hvγ]
        rcases hg with hg | hg
        · exact hpair α (-γ) (Or.inl rfl) (Or.inr rfl) g hg _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
        · exact hpair (-α) (-γ) (Or.inr rfl) (Or.inr rfl) g hg _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_right
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change Commute (rootSL2 τ L α (uSL c)) _
      rw [huα]
      exact h1 _ (Or.inl (mem_rootSubgroup.2 ⟨_, rfl⟩)) B
    · change Commute (rootSL2 τ L α (vSL c)) _
      rw [hvα]
      exact h1 _ (Or.inr (mem_rootSubgroup.2 ⟨_, rfl⟩)) B
  | one => rw [map_one]; exact Commute.one_left _
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_left

theorem exists_chainHom (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (β : Fin m → Fin τ.rank → ℤ) (hβ : ∀ c, IsRoot τ (β c))
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d)
    (hθ : ∀ (c : Fin m) (h : (c : ℕ) + 1 < m), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β ⟨c + 1, h⟩)) :
    ∃ ψ : SL(m + 1, L) →* ModGL τ L, ∀ c, ψ.comp (blockSL2 L m c) = rootSL2 τ L (β c) := by
  classical
  let F : CTFamily L (ModGL τ L) m :=
    { ι := fun c => rootSL2 τ L (β c)
      θ := fun c => if h : (c : ℕ) + 1 < m then (hθ c h).choose else 1
      left := fun c h => by
        simp only [h, dite_true]
        exact (hθ c h).choose_spec.1
      right := fun c h => by
        simp only [h, dite_true]
        exact (hθ c h).choose_spec.2
      comm := fun c d hcd a b => by
        have h0 : iform (β c) (β d) = 0 := by
          rw [hG, chainGram]
          have hne : c ≠ d := fun h => by rw [h] at hcd; omega
          simp only [hne, ite_false]
          split_ifs with h
          · omega
          · rfl
        exact (commute_rootSL2_of_iform_eq_zero hτ (hβ c) (hβ d) h0 a b).eq }
  obtain ⟨ψ, hψ, -⟩ := exists_hom_of_ctFamily F
  exact ⟨ψ, hψ⟩

theorem exists_commutator_step (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hγ : IsRoot τ γ) (hαγ : iform α γ = -1)
    (hr : IsRoot τ (α + γ)) (ε ε' : Lˣ) :
    ∃ ε'' : Lˣ, ∀ t : L, ⁅pinnedX τ L α ((ε : L) * t), pinnedX τ L γ ((ε' : L) * 1)⁆ =
      pinnedX τ L (α + γ) ((ε'' : L) * t) := by
  have hαα := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hα
  have hγγ := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ
  have hne : α ≠ γ := fun h => by rw [h] at hαγ; omega
  have hne' : α ≠ -γ := fun h => by
    rw [h, show -γ = (-1 : ℤ) • γ by rw [neg_one_smul], iform_smul_left] at hαγ
    omega
  obtain ⟨hN, hF⟩ := (simply_laced_root_commutator_unit τ hτ hα hγ hne hne').1 hr
  have hNu : IsUnit ((commConst τ α γ (1, 1) : ℤ) : L) := by
    rcases hN with h | h <;> rw [h] <;> simp
  refine ⟨hNu.unit * ε * ε', fun t => ?_⟩
  rw [hF L]
  congr 1
  simp only [Units.val_mul, IsUnit.unit_spec]
  ring

theorem chainHom_transvection (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin m → Fin τ.rank → ℤ} (hβ : ∀ c, IsRoot τ (β c))
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d) {ψ : SL(m + 1, L) →* ModGL τ L}
    (hψ : ∀ c, ψ.comp (blockSL2 L m c) = rootSL2 τ L (β c)) (a b : Fin (m + 1))
    (hab : a ≠ b) : ∃ ε : Lˣ, ∀ t,
      ψ (Matrix.SpecialLinearGroup.transvection hab t) = pinnedX τ L (chainσ β a b) (ε * t) := by
  have hup : ∀ (a b : Fin (m + 1)) (h : a ≠ b), (b : ℕ) = a + 1 → ∃ ε : Lˣ, ∀ t,
      ψ (Matrix.SpecialLinearGroup.transvection h t) = pinnedX τ L (chainσ β a b) (ε * t) := by
    intro a b h hb
    obtain ⟨c, rfl⟩ : ∃ c : Fin m, c.castSucc = a := ⟨⟨a, by omega⟩, Fin.ext rfl⟩
    obtain rfl : b = c.succ := Fin.ext (by simp [hb])
    obtain ⟨u, -, hu, -⟩ := exists_rootSL2_units (L := L) (hβ c)
    refine ⟨u, fun t => ?_⟩
    have := blockSL2_uSL_eq (L := L) c t
    rw [← this, ← MonoidHom.comp_apply, hψ, hu, chainσ_castSucc_succ]
  have hdown : ∀ (a b : Fin (m + 1)) (h : a ≠ b), (a : ℕ) = b + 1 → ∃ ε : Lˣ, ∀ t,
      ψ (Matrix.SpecialLinearGroup.transvection h t) = pinnedX τ L (chainσ β a b) (ε * t) := by
    intro a b h ha
    obtain ⟨c, rfl⟩ : ∃ c : Fin m, c.castSucc = b := ⟨⟨b, by omega⟩, Fin.ext rfl⟩
    obtain rfl : a = c.succ := Fin.ext (by simp [ha])
    obtain ⟨-, e, -, he⟩ := exists_rootSL2_units (L := L) (hβ c)
    refine ⟨e, fun t => ?_⟩
    have := blockSL2_vSL_eq (L := L) c t
    rw [← this, ← MonoidHom.comp_apply, hψ, he, chainσ_neg, chainσ_castSucc_succ]
  have up : ∀ (k : ℕ) (a b : Fin (m + 1)) (h : a ≠ b), (b : ℕ) = a + k + 1 → ∃ ε : Lˣ, ∀ t,
      ψ (Matrix.SpecialLinearGroup.transvection h t) = pinnedX τ L (chainσ β a b) (ε * t) := by
    intro k
    induction k with
    | zero => exact fun a b h hb => hup a b h (by omega)
    | succ k ih =>
      intro a b hab hb
      set j : Fin (m + 1) := ⟨a + k + 1, by omega⟩ with hj
      have haj : a ≠ j := fun h => by
        have := congrArg Fin.val h
        simp [hj] at this
        omega
      have hjb : j ≠ b := fun h => by
        have := congrArg Fin.val h
        simp [hj] at this
        omega
      obtain ⟨ε, hε⟩ := ih a j haj rfl
      obtain ⟨ε', hε'⟩ := hup j b hjb (by simp [hj]; omega)
      have hrα : IsRoot τ (chainσ β a j) := isRoot_chainσ hβ hG haj
      have hrγ : IsRoot τ (chainσ β j b) := isRoot_chainσ hβ hG hjb
      have hsum : chainσ β a j + chainσ β j b = chainσ β a b := chainσ_add β _ _ _
      have hi : iform (chainσ β a j) (chainσ β j b) = -1 := by
        rw [chainσ_of_val_eq β (a := j) (b := b) (by simp [hj]; omega), iform_chainσ hG]
        simp only [hj]
        split_ifs <;> omega
      have hr : IsRoot τ (chainσ β a j + chainσ β j b) := by
        rw [hsum]
        exact isRoot_chainσ hβ hG hab
      obtain ⟨ε'', hε''⟩ := exists_commutator_step hτ hrα hrγ hi hr ε ε'
      refine ⟨ε'', fun t => ?_⟩
      have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection haj hjb hab t 1
      rw [mul_one] at hcomm
      rw [← hcomm, map_commutatorElement, hε, hε', ← hsum]
      exact hε'' t
  have down : ∀ (k : ℕ) (a b : Fin (m + 1)) (h : a ≠ b), (a : ℕ) = b + k + 1 → ∃ ε : Lˣ, ∀ t,
      ψ (Matrix.SpecialLinearGroup.transvection h t) = pinnedX τ L (chainσ β a b) (ε * t) := by
    intro k
    induction k with
    | zero => exact fun a b h ha => hdown a b h (by omega)
    | succ k ih =>
      intro a b hab ha
      set j : Fin (m + 1) := ⟨b + k + 1, by omega⟩ with hj
      have haj : a ≠ j := fun h => by
        have := congrArg Fin.val h
        simp [hj] at this
        omega
      have hjb : j ≠ b := fun h => by
        have := congrArg Fin.val h
        simp [hj] at this
        omega
      obtain ⟨ε', hε'⟩ := ih j b hjb rfl
      obtain ⟨ε, hε⟩ := hdown a j haj (by simp [hj]; omega)
      have hrα : IsRoot τ (chainσ β a j) := isRoot_chainσ hβ hG haj
      have hrγ : IsRoot τ (chainσ β j b) := isRoot_chainσ hβ hG hjb
      have hsum : chainσ β a j + chainσ β j b = chainσ β a b := chainσ_add β _ _ _
      have hi : iform (chainσ β a j) (chainσ β j b) = -1 := by
        have hneg : ∀ v w : Fin τ.rank → ℤ, iform (-v) w = -iform v w := fun v w => by
          rw [show -v = (-1 : ℤ) • v by rw [neg_one_smul], iform_smul_left]
          ring
        rw [chainσ_neg β j a, chainσ_of_val_eq β (a := j) (b := a) (by simp [hj]; omega), hneg,
          iform_comm, iform_chainσ hG]
        simp only [hj]
        split_ifs <;> omega
      have hr : IsRoot τ (chainσ β a j + chainσ β j b) := by
        rw [hsum]
        exact isRoot_chainσ hβ hG hab
      obtain ⟨ε'', hε''⟩ := exists_commutator_step hτ hrα hrγ hi hr ε ε'
      refine ⟨ε'', fun t => ?_⟩
      have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection haj hjb hab t 1
      rw [mul_one] at hcomm
      rw [← hcomm, map_commutatorElement, hε, hε', ← hsum]
      exact hε'' t
  rcases lt_or_gt_of_ne hab with h | h
  · exact up ((b : ℕ) - a - 1) a b hab (by omega)
  · exact down ((a : ℕ) - b - 1) a b hab (by omega)

theorem isSLFrame_chainHom (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin m → Fin τ.rank → ℤ} (hβ : ∀ c, IsRoot τ (β c))
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d) {ψ : SL(m + 1, L) →* ModGL τ L}
    (hψ : ∀ c, ψ.comp (blockSL2 L m c) = rootSL2 τ L (β c)) : IsSLFrame ψ (chainσ β) where
  isRoot a b hab := isRoot_chainσ hβ hG hab
  neg a b := chainσ_neg β a b
  add a b c := chainσ_add β a b c
  transv a b hab := chainHom_transvection hτ hβ hG hψ a b hab
  range := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨a, b, hab, t, rfl⟩, rfl⟩
      obtain ⟨ε, hε⟩ := chainHom_transvection hτ hβ hG hψ a b hab
      rw [SetLike.mem_coe, hε]
      exact Subgroup.mem_iSup_of_mem (chainσ β a b) (Subgroup.mem_iSup_of_mem ⟨a, b, hab, rfl⟩
        (mem_rootSubgroup.2 ⟨_, rfl⟩))
    · refine iSup₂_le fun r hr => ?_
      obtain ⟨a, b, hab, rfl⟩ := hr
      obtain ⟨ε, hε⟩ := chainHom_transvection hτ hβ hG hψ a b hab
      intro x hx
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      refine ⟨Matrix.SpecialLinearGroup.transvection hab (((ε⁻¹ : Lˣ) : L) * c), ?_⟩
      rw [hε, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem rootSL2_HSL_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (t : Lˣ) :
    rootSL2 τ L β (HSL t) =
      rootDiagUnit τ (fun i => t ^ corootPair β (Pi.single i 1)) :=
  CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hβ _
    (fun δ _ => corootPair_eq_sum hβ δ) t

section Block

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

theorem coe_blockSL2_HSL (c : Fin m) (t : Lˣ) :
    ((blockSL2 L m c (HSL t) : SL(m + 1, L)) : Matrix (Fin (m + 1)) (Fin (m + 1)) L) =
      Matrix.diagonal fun j : Fin (m + 1) => if (j : ℕ) = c then (t : L)
        else if (j : ℕ) = c + 1 then ((t⁻¹ : Lˣ) : L) else 1 := by
  rw [blockSL2, coe_blockSL]
  ext a b
  rw [blockMat_apply, Matrix.diagonal_apply]
  have hHSL : ((HSL t : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![(t : L), 0; 0, ((t⁻¹ : Lˣ) : L)] :=
    rfl
  by_cases hb : ((c : ℕ) ≤ a.val ∧ a.val < c + 2) ∧ ((c : ℕ) ≤ b.val ∧ b.val < c + 2)
  · rw [dite_eq_left hb, hHSL]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl]
      rcases (by omega : (a : ℕ) = c ∨ (a : ℕ) = c + 1) with h | h
      · have e : (⟨a.val - c, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
        rw [e, ite_eq_left h]
        simp
      · have e : (⟨a.val - c, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
        rw [e, ite_eq_right (by omega), ite_eq_left h]
        simp
    · rw [ite_eq_right hab]
      rcases (by omega : (a : ℕ) = c ∨ (a : ℕ) = c + 1) with h | h <;>
        rcases (by omega : (b : ℕ) = c ∨ (b : ℕ) = c + 1) with h' | h'
      · exact absurd (Fin.ext (by omega)) hab
      · have e1 : (⟨a.val - c, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
        have e2 : (⟨b.val - c, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
        rw [e1, e2]
        simp
      · have e1 : (⟨a.val - c, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
        have e2 : (⟨b.val - c, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
        rw [e1, e2]
        simp
      · exact absurd (Fin.ext (by omega)) hab
  · rw [dite_eq_right hb, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right hab, ite_eq_right hab]

@[expose] noncomputable def blockTorusProd (ζ : Lˣ) : ℕ → SL(m + 1, L)
  | 0 => 1
  | k + 1 => blockTorusProd ζ k *
      (if h : k < m then blockSL2 L m ⟨k, h⟩ (HSL (ζ ^ (k + 1))) else 1)

theorem coe_blockTorusProd (ζ : Lˣ) : ∀ k, k ≤ m →
    ((blockTorusProd (m := m) ζ k : SL(m + 1, L)) : Matrix (Fin (m + 1)) (Fin (m + 1)) L) =
      Matrix.diagonal fun j : Fin (m + 1) => if (j : ℕ) < k then (ζ : L)
        else if (j : ℕ) = k then ((ζ ^ (-(k : ℤ)) : Lˣ) : L) else 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [blockTorusProd, Matrix.SpecialLinearGroup.coe_one]
    ext a b
    rw [Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  | succ k ih =>
    intro hk
    have hkm : k < m := by omega
    rw [blockTorusProd, dite_eq_left hkm, Matrix.SpecialLinearGroup.coe_mul, ih (by omega),
      coe_blockSL2_HSL, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    have e1 : ((ζ ^ (-(k : ℤ)) : Lˣ) : L) * ((ζ ^ (k + 1) : Lˣ) : L) = (ζ : L) := by
      rw [← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add]
      congr 1
      rw [show -(k : ℤ) + ((k + 1 : ℕ) : ℤ) = 1 by push_cast; ring, zpow_one]
    have e2 : (((ζ ^ (k + 1))⁻¹ : Lˣ) : L) = ((ζ ^ (-((k + 1 : ℕ) : ℤ)) : Lˣ) : L) := by
      rw [_root_.zpow_neg, zpow_natCast]
    split_ifs <;> (try simp only at *) <;>
      first | (exfalso; omega) | simp only [mul_one, one_mul, e1, e2]

theorem coe_blockTorusProd_eq_scalar (ζ : Lˣ) (hζ : ζ ^ (m + 1) = 1) :
    ((blockTorusProd (m := m) ζ m : SL(m + 1, L)) : Matrix (Fin (m + 1)) (Fin (m + 1)) L) =
      Matrix.scalar (Fin (m + 1)) (ζ : L) := by
  rw [coe_blockTorusProd ζ m le_rfl, Matrix.scalar_apply]
  congr 1
  funext j
  by_cases h1 : (j : ℕ) < m
  · rw [ite_eq_left h1]
  · have h2 : (j : ℕ) = m := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    have : ζ ^ (-(m : ℤ)) = ζ := by
      rw [_root_.zpow_neg, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv, zpow_natCast,
        ← pow_succ]
      exact hζ
    rw [this]

@[expose] noncomputable def chainExp (β : Fin m → Fin τ.rank → ℤ) (k : ℕ) (i : Fin τ.rank) : ℤ :=
  ∑ c : Fin m, if (c : ℕ) < k then ((c : ℤ) + 1) * corootPair (β c) (Pi.single i 1) else 0

theorem chainExp_succ (β : Fin m → Fin τ.rank → ℤ) {k : ℕ} (hk : k < m) (i : Fin τ.rank) :
    chainExp β (k + 1) i =
      chainExp β k i + ((k : ℤ) + 1) * corootPair (β ⟨k, hk⟩) (Pi.single i 1) := by
  classical
  simp only [chainExp]
  have hs : ((k : ℤ) + 1) * corootPair (β ⟨k, hk⟩) (Pi.single i 1) =
      ∑ c : Fin m, if (⟨k, hk⟩ : Fin m) = c then ((c : ℤ) + 1) * corootPair (β c) (Pi.single i 1)
        else 0 := by
    rw [Finset.sum_ite_eq]
    simp
  rw [hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : (c : ℕ) < k
  · have h2 : ¬ (⟨k, hk⟩ : Fin m) = c := fun h => by rw [← h] at h1; exact lt_irrefl _ h1
    simp only [h1, Nat.lt_succ_of_lt h1, h2, ite_true, ite_false, add_zero]
  · by_cases h3 : (c : ℕ) = k
    · have h4 : c = ⟨k, hk⟩ := Fin.ext h3
      subst h4
      simp
    · have h5 : ¬ (c : ℕ) < k + 1 := by omega
      have h6 : ¬ (⟨k, hk⟩ : Fin m) = c := fun h => h3 (by rw [← h])
      simp only [h1, h5, h6, ite_false, add_zero]

theorem chainHom_blockTorusProd {β : Fin m → Fin τ.rank → ℤ} (hβ : ∀ c, IsRoot τ (β c))
    {ψ : SL(m + 1, L) →* ModGL τ L}
    (hψ : ∀ c, ψ.comp (blockSL2 L m c) = rootSL2 τ L (β c)) (ζ : Lˣ) :
    ∀ k, k ≤ m → ψ (blockTorusProd (m := m) ζ k) =
      rootDiagUnit τ (fun i => ζ ^ chainExp β k i) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [blockTorusProd, map_one]
    have : (fun i : Fin τ.rank => ζ ^ chainExp β 0 i) = 1 := by
      funext i
      simp [chainExp]
    rw [this, rootDiagUnit_one]
  | succ k ih =>
    intro hk
    have hkm : k < m := by omega
    rw [blockTorusProd, dite_eq_left hkm, map_mul, ih (by omega), ← MonoidHom.comp_apply, hψ,
      rootSL2_HSL_eq (hβ _), ← rootDiagUnit_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, chainExp_succ β hkm, _root_.zpow_add, ← zpow_natCast, ← _root_.zpow_mul]
    congr 2

end Block

theorem chainHom_injective (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin m → Fin τ.rank → ℤ} (hβ : ∀ c, IsRoot τ (β c))
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d) {ψ : SL(m + 1, L) →* ModGL τ L}
    (hψ : ∀ c, ψ.comp (blockSL2 L m c) = rootSL2 τ L (β c)) (hm : 2 ≤ m)
    (hcenter : ∀ ζ : Lˣ, ζ ^ (m + 1) = 1 → (∀ i, ζ ^ chainExp β m i = 1) → ζ = 1) :
    Function.Injective ψ := by
  have hnt : ∃ x, ψ x ≠ 1 := by
    obtain ⟨ε, hε⟩ := chainHom_transvection hτ hβ hG hψ 0 1 (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)
    refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin (m + 1)) ≠ 1 by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega) 1, ?_⟩
    rw [hε, mul_one]
    intro h
    rw [← pinnedX_zero τ L (chainσ β 0 1)] at h
    exact ε.ne_zero (pinnedX_injective τ L _ h)
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := L) (n := m + 1)
      (by omega)) hnt
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hker hx)
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := fun h => by
    rw [h, zero_pow (by omega)] at hr
    exact zero_ne_one hr
  set ζ : Lˣ := Units.mk0 r hr0 with hζ
  have hζp : ζ ^ (m + 1) = 1 := Units.ext (by simp [hζ, hr])
  have hxQ : x = blockTorusProd (m := m) ζ m := by
    apply Subtype.ext
    rw [coe_blockTorusProd_eq_scalar ζ hζp, ← hrx]
    rfl
  have h1 : ψ x = 1 := hx
  rw [hxQ, chainHom_blockTorusProd hβ hψ ζ m le_rfl, ← rootDiagUnit_one] at h1
  have h2 := rootDiagUnit_injective h1
  have h3 : ζ = 1 := hcenter ζ hζp fun i => congrFun h2 i
  rw [Subgroup.mem_bot, hxQ]
  apply Subtype.ext
  rw [coe_blockTorusProd_eq_scalar ζ hζp, h3, Units.val_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.scalar_apply, Matrix.diagonal_one]



end Hom

end Chain

end CFSG.HardMathSupport.Timmesfeld.CrossChar
