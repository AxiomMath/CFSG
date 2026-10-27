module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.RankThree.PartOne.KE6.E6LComm27
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6X2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiE6Sc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
open scoped MatrixGroups

set_option linter.unusedSectionVars false


variable {k : Type} [Field k] [Finite k]

abbrev G (k : Type) [Field k] := ↥(e6Data_valid.minGroup k)

@[expose] def Qh (k : Type) [Field k] (J : Set (Fin Tag.E6.rank)) : Subgroup (G k) :=
  Subgroup.closure {g | ∃ j ∈ J, ∃ c : k, g = e6Data_valid.xm k (Pi.single j 1) c ∨
    g = e6Data_valid.xm k (-Pi.single j 1) c}

@[expose] def piGL (k : Type) [Field k] [Finite k] : G k →* ModGL Tag.E6 k :=
  (adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k)

theorem piGL_xm_single (i : Fin Tag.E6.rank) (c : k) :
    piGL k (e6Data_valid.xm k (Pi.single i 1) c) = xUnit Tag.E6 k i c := by
  show ((e6Isogeny k (e6Data_valid.xm k (Pi.single i 1) c) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
  rfl

theorem piGL_xm_neg_single (i : Fin Tag.E6.rank) (c : k) :
    piGL k (e6Data_valid.xm k (-Pi.single i 1) c) = yUnit Tag.E6 k i c := by
  show ((e6Isogeny k (e6Data_valid.xm k (-Pi.single i 1) c) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
  rfl

theorem map_Qh (J : Set (Fin Tag.E6.rank)) :
    (Qh k J).map (piGL k) = subsystemGroup Tag.E6 k J := by
  unfold Qh subsystemGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨j, hj, c, rfl | rfl⟩, rfl⟩
    · exact ⟨j, hj, c, Or.inl (piGL_xm_single j c)⟩
    · exact ⟨j, hj, c, Or.inr (piGL_xm_neg_single j c)⟩
  · rintro ⟨j, hj, c, rfl | rfl⟩
    · exact ⟨_, ⟨j, hj, c, Or.inl rfl⟩, piGL_xm_single j c⟩
    · exact ⟨_, ⟨j, hj, c, Or.inr rfl⟩, piGL_xm_neg_single j c⟩

theorem endo_fix_of_mem_Qh {J : Set (Fin Tag.E6.rank)} {a : Fin e6Data.d}
    (ha : ∀ j ∈ J, e6Data.wt a j = 0) {g : G k} (hg : g ∈ Qh k J) :
    e6Data_valid.endo k g (Finsupp.single a 1) = Finsupp.single a 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hx
    · rw [e6Data_valid.endo_xm k, LinearMap.add_apply, LinearMap.smul_apply,
        e6Data_valid.rootOp_single_apply (R := k), if_neg (by rw [ha j hj]; decide)]
      simp
    · rw [e6Data_valid.endo_xm k, LinearMap.add_apply, LinearMap.smul_apply,
        e6Data_valid.rootOp_neg_single_apply (R := k), if_neg (by rw [ha j hj]; decide)]
      simp
  | one => simp [e6Data_valid.endo_one]
  | mul x y _ _ hx hy => rw [e6Data_valid.endo_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    have h := e6Data_valid.endo_inv_mul k x
    calc e6Data_valid.endo k x⁻¹ (Finsupp.single a 1)
        = e6Data_valid.endo k x⁻¹ (e6Data_valid.endo k x (Finsupp.single a 1)) := by rw [hx]
      _ = (e6Data_valid.endo k x⁻¹ * e6Data_valid.endo k x) (Finsupp.single a 1) := rfl
      _ = Finsupp.single a 1 := by rw [h]; rfl

theorem commute_rootOp_of_center {z : G k} (hz : z ∈ Subgroup.center (G k))
    (γ : Fin Tag.E6.rank → ℤ) :
    Commute (e6Data_valid.endo k z) (e6Data.rootOp k γ) := by
  have h := Subgroup.mem_center_iff.1 hz (e6Data_valid.xm k γ 1)
  have h' := congrArg (e6Data_valid.endo k) h
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_xm] at h'
  have h'' : e6Data.rootOp k γ * e6Data_valid.endo k z = e6Data_valid.endo k z * e6Data.rootOp k γ := by
    simpa [add_mul, mul_add] using h'
  exact h''.symm

theorem endo_center_scalar {z : G k} (hz : z ∈ Subgroup.center (G k)) :
    ∃ c : k, e6Data_valid.endo k z = c • (1 : Module.End k (Fin e6Data.d →₀ k)) :=
  CFSG.RankThree.PartOne.KE6.eq_smul_one_of_commute
    (fun j => commute_rootOp_of_center hz (Pi.single j 1))
    (fun j => commute_rootOp_of_center hz (-Pi.single j 1))

theorem ker_piGL_le_center {z : G k} (hz : piGL k z = 1) : z ∈ Subgroup.center (G k) := by
  have h : z ∈ (e6Isogeny k).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hz
  rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center] at h
  exact h

theorem piGL_injective_on_Qh {J : Set (Fin Tag.E6.rank)}
    (hJ : ∃ a : Fin e6Data.d, ∀ j ∈ J, e6Data.wt a j = 0) {x : G k} (hx : x ∈ Qh k J)
    (h1 : piGL k x = 1) : x = 1 := by
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨c, hc⟩ := endo_center_scalar (ker_piGL_le_center h1)
  have hfix := endo_fix_of_mem_Qh ha hx
  rw [hc] at hfix
  have hc1 : c = 1 := by
    have := congrArg (fun f : Fin e6Data.d →₀ k => f a) hfix
    simpa using this
  rw [hc1, one_smul] at hc
  exact e6Data_valid.endo_injective k (by rw [hc]; rfl)

theorem exists_weight_13 : ∃ a : Fin e6Data.d, ∀ j ∈ support13, e6Data.wt a j = 0 := by
  obtain ⟨a, h0, h2⟩ : ∃ a : Fin e6Data.d,
      e6Data.wt a (e6Index 0) = 0 ∧ e6Data.wt a (e6Index 2) = 0 := by decide +kernel
  exact ⟨a, fun j hj => by rcases (mem_support13 j).1 hj with rfl | rfl <;> assumption⟩

theorem exists_weight_56 : ∃ a : Fin e6Data.d, ∀ j ∈ support56, e6Data.wt a j = 0 := by
  obtain ⟨a, h4, h5⟩ : ∃ a : Fin e6Data.d,
      e6Data.wt a (e6Index 4) = 0 ∧ e6Data.wt a (e6Index 5) = 0 := by decide +kernel
  exact ⟨a, fun j hj => by rcases (mem_support56 j).1 hj with rfl | rfl <;> assumption⟩

theorem not_isRoot_sum :
    ∀ i j : Fin Tag.E6.rank, (i = e6Index 0 ∨ i = e6Index 2) → (j = e6Index 4 ∨ j = e6Index 5) →
      (¬ IsRoot Tag.E6 (Pi.single i 1 + Pi.single j 1) ∧
        ¬ IsRoot Tag.E6 (Pi.single i 1 + -Pi.single j 1) ∧
        ¬ IsRoot Tag.E6 (-Pi.single i 1 + Pi.single j 1) ∧
        ¬ IsRoot Tag.E6 (-Pi.single i 1 + -Pi.single j 1)) ∧
      (Pi.single i 1 + Pi.single j 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
        Pi.single i 1 + -Pi.single j 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
        -Pi.single i 1 + Pi.single j 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
        -Pi.single i 1 + -Pi.single j 1 ≠ (0 : Fin Tag.E6.rank → ℤ)) := by
  intro i j hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [← mem_rootFinset] <;> decide +kernel

theorem xm_comm_of_not_root {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hδ : IsRoot Tag.E6 δ) (hne : γ + δ ≠ 0) (hnr : ¬ IsRoot Tag.E6 (γ + δ)) (c d : k) :
    Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k δ d) := by
  have h := (e6Data_valid.commutator_xm k hγ hδ hne).2 hnr c d
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem commute_Qh {x y : G k} (hx : x ∈ Qh k support13) (hy : y ∈ Qh k support56) :
    Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx <;> obtain ⟨j, hj, d, rfl | rfl⟩ := hy <;>
        obtain ⟨⟨n1, n2, n3, n4⟩, ⟨z1, z2, z3, z4⟩⟩ :=
          not_isRoot_sum i j ((mem_support13 i).1 hi) ((mem_support56 j).1 hj)
      · exact xm_comm_of_not_root (isRoot_single _ _) (isRoot_single _ _) z1 n1 c d
      · exact xm_comm_of_not_root (isRoot_single _ _) (isRoot_neg_single _ _) z2 n2 c d
      · exact xm_comm_of_not_root (isRoot_neg_single _ _) (isRoot_single _ _) z3 n3 c d
      · exact xm_comm_of_not_root (isRoot_neg_single _ _) (isRoot_neg_single _ _) z4 n4 c d
    | one => exact Commute.one_right _
    | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂
    | inv y _ h => exact h.inv_right
  | one => exact Commute.one_left _
  | mul x₁ x₂ _ _ h₁ h₂ => exact h₁.mul_left h₂
  | inv x _ h => exact h.inv_left

@[expose] def QhEquiv (J : Set (Fin Tag.E6.rank))
    (hJ : ∃ a : Fin e6Data.d, ∀ j ∈ J, e6Data.wt a j = 0) :
    ↥(Qh k J) ≃* ↥(subsystemGroup Tag.E6 k J) :=
  MulEquiv.ofBijective
    (((piGL k).comp (Qh k J).subtype).codRestrict (subsystemGroup Tag.E6 k J) (fun x => by
      rw [← map_Qh]
      exact ⟨x, x.2, rfl⟩))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      exact piGL_injective_on_Qh hJ x.2 (congrArg Subtype.val hx),
     fun t => by
      have ht : (t : ModGL Tag.E6 k) ∈ (Qh k J).map (piGL k) := by
        rw [map_Qh]
        exact t.2
      obtain ⟨x, hx, hxt⟩ := ht
      exact ⟨⟨x, hx⟩, Subtype.ext hxt⟩⟩

theorem coe_QhEquiv (J : Set (Fin Tag.E6.rank))
    (hJ : ∃ a : Fin e6Data.d, ∀ j ∈ J, e6Data.wt a j = 0) (x : ↥(Qh k J)) :
    ((QhEquiv J hJ x : ↥(subsystemGroup Tag.E6 k J)) : ModGL Tag.E6 k) = piGL k (x : G k) := rfl

@[expose] def rho₁ (k : Type) [Field k] [Finite k] : SL(3, k) →* G k :=
  (Qh k support13).subtype.comp
    ((QhEquiv support13 exists_weight_13).symm.toMonoidHom.comp (a2Equiv₁ k).symm.toMonoidHom)

@[expose] def rho₂ (k : Type) [Field k] [Finite k] : SL(3, k) →* G k :=
  (Qh k support56).subtype.comp
    ((QhEquiv support56 exists_weight_56).symm.toMonoidHom.comp (a2Equiv₂ k).symm.toMonoidHom)

theorem rho₁_mem (A : SL(3, k)) : rho₁ k A ∈ Qh k support13 :=
  ((QhEquiv support13 exists_weight_13).symm ((a2Equiv₁ k).symm A)).2

theorem rho₂_mem (A : SL(3, k)) : rho₂ k A ∈ Qh k support56 :=
  ((QhEquiv support56 exists_weight_56).symm ((a2Equiv₂ k).symm A)).2

theorem piGL_rho₁ (A : SL(3, k)) :
    piGL k (rho₁ k A) = (((a2Equiv₁ k).symm A : ↥(subsystemGroup Tag.E6 k support13)) :
      ModGL Tag.E6 k) := by
  have := coe_QhEquiv support13 exists_weight_13
    ((QhEquiv support13 exists_weight_13).symm ((a2Equiv₁ k).symm A))
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem piGL_rho₂ (A : SL(3, k)) :
    piGL k (rho₂ k A) = (((a2Equiv₂ k).symm A : ↥(subsystemGroup Tag.E6 k support56)) :
      ModGL Tag.E6 k) := by
  have := coe_QhEquiv support56 exists_weight_56
    ((QhEquiv support56 exists_weight_56).symm ((a2Equiv₂ k).symm A))
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] def rhoSC (k : Type) [Field k] [Finite k] : SL(3, k) × SL(3, k) →* G k :=
  MonoidHom.noncommCoprod (rho₁ k) (rho₂ k) fun A B => commute_Qh (rho₁_mem A) (rho₂_mem B)

theorem rhoSC_apply (A B : SL(3, k)) : rhoSC k (A, B) = rho₁ k A * rho₂ k B := by
  simp [rhoSC]

theorem piGL_rhoSC (s : SL(3, k) × SL(3, k)) : piGL k (rhoSC k s) = twoA2Mul k s := by
  obtain ⟨A, B⟩ := s
  rw [rhoSC_apply, map_mul, piGL_rho₁, piGL_rho₂, twoA2Mul_apply]

theorem nt_mem_Qh {J : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank} (hi : i ∈ J) (t : kˣ) :
    e6Data_valid.nt k i t ∈ Qh k J :=
  mul_mem (mul_mem (Subgroup.subset_closure ⟨i, hi, t, Or.inl rfl⟩)
    (Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩))
    (Subgroup.subset_closure ⟨i, hi, t, Or.inl rfl⟩)

theorem hm_mem_Qh {J : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank} (hi : i ∈ J) (t : kˣ) :
    e6Data_valid.hm k i t ∈ Qh k J :=
  mul_mem (nt_mem_Qh hi t) (inv_mem (nt_mem_Qh hi 1))

theorem piGL_hm (i : Fin Tag.E6.rank) (t : kˣ) :
    piGL k (e6Data_valid.hm k i t) = torusElt Tag.E6 k i t := by
  show ((e6Isogeny k (e6Data_valid.hm k i t) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq, ← torusElt_eq_rootDiagUnit]

theorem rho₁_scalar {l : k} (hl : l ^ 3 = 1) (A : SL(3, k))
    (hA : (A : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) l) :
    rho₁ k A = e6Data_valid.hm k (e6Index 0) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 2) (cubeUnit hl ^ 2) := by
  have hmem : e6Data_valid.hm k (e6Index 0) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 2) (cubeUnit hl ^ 2) ∈ Qh k support13 :=
    mul_mem (hm_mem_Qh ((mem_support13 _).2 (Or.inl rfl)) _)
      (hm_mem_Qh ((mem_support13 _).2 (Or.inr rfl)) _)
  have h1 : piGL k (rho₁ k A) = piGL k (e6Data_valid.hm k (e6Index 0) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 2) (cubeUnit hl ^ 2)) := by
    rw [piGL_rho₁, a2Equiv₁_symm_scalar hl A hA, map_mul, piGL_hm, piGL_hm]
    rfl
  have := piGL_injective_on_Qh exists_weight_13 (mul_mem (rho₁_mem A) (inv_mem hmem))
    (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem rho₂_scalar {l : k} (hl : l ^ 3 = 1) (A : SL(3, k))
    (hA : (A : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) l) :
    rho₂ k A = e6Data_valid.hm k (e6Index 4) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 5) (cubeUnit hl ^ 2) := by
  have hmem : e6Data_valid.hm k (e6Index 4) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 5) (cubeUnit hl ^ 2) ∈ Qh k support56 :=
    mul_mem (hm_mem_Qh ((mem_support56 _).2 (Or.inl rfl)) _)
      (hm_mem_Qh ((mem_support56 _).2 (Or.inr rfl)) _)
  have h1 : piGL k (rho₂ k A) = piGL k (e6Data_valid.hm k (e6Index 4) (cubeUnit hl) *
      e6Data_valid.hm k (e6Index 5) (cubeUnit hl ^ 2)) := by
    rw [piGL_rho₂, a2Equiv₂_symm_scalar hl A hA, map_mul, piGL_hm, piGL_hm]
    rfl
  have := piGL_injective_on_Qh exists_weight_56 (mul_mem (rho₂_mem A) (inv_mem hmem))
    (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem endo_rhoSC_scalar {l : k} (hl : l ^ 3 = 1) (A B : SL(3, k))
    (hA : (A : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) l)
    (hB : (B : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) l) (a : Fin e6Data.d) :
    e6Data_valid.endo k (rhoSC k (A, B)) (Finsupp.single a 1) =
      (((cubeUnit hl) ^ (e6Data.wt a (e6Index 0) + 2 * e6Data.wt a (e6Index 2) +
        e6Data.wt a (e6Index 4) + 2 * e6Data.wt a (e6Index 5)) : kˣ) : k) •
          Finsupp.single a 1 := by
  rw [rhoSC_apply, rho₁_scalar hl A hA, rho₂_scalar hl B hB]
  simp only [e6Data_valid.endo_mul, e6Data_valid.endo_hm, Module.End.mul_apply,
    e6Data.hDiag_single, map_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
  congr 1
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
  ring_nf

theorem rhoSC_injective : Function.Injective (rhoSC k) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ h
  have h1 : twoA2Mul k (A, B) = 1 := by rw [← piGL_rhoSC, h, map_one]
  obtain ⟨l, hl, hA, hB⟩ := (twoA2Mul_eq_one_iff A B).1 h1
  obtain ⟨a, ha⟩ : ∃ a : Fin e6Data.d,
      (e6Data.wt a (e6Index 0) + 2 * e6Data.wt a (e6Index 2) + e6Data.wt a (e6Index 4) +
        2 * e6Data.wt a (e6Index 5)) % 3 ≠ 0 := by decide +kernel
  have h2 := endo_rhoSC_scalar hl A B hA hB a
  rw [h, e6Data_valid.endo_one] at h2
  set e := e6Data.wt a (e6Index 0) + 2 * e6Data.wt a (e6Index 2) + e6Data.wt a (e6Index 4) +
    2 * e6Data.wt a (e6Index 5) with he
  have h3 : (((cubeUnit hl) ^ e : kˣ) : k) = 1 := by
    have := congrArg (fun f : Fin e6Data.d →₀ k => f a) h2
    simpa using this.symm
  have h4 : (cubeUnit hl) ^ e = 1 := Units.ext (by rw [h3, Units.val_one])
  have hu3 : (cubeUnit hl) ^ 3 = 1 := cubeUnit_pow hl
  have h5 : (cubeUnit hl) ^ (e % 3) = 1 := by
    have h6 : e = 3 * (e / 3) + e % 3 := (Int.mul_ediv_add_emod e 3).symm
    rw [h6, zpow_add, zpow_mul] at h4
    simpa [hu3] using h4
  have hu1 : cubeUnit hl = 1 := by
    have h7 : e % 3 = 1 ∨ e % 3 = 2 := by omega
    rcases h7 with h7 | h7
    · rw [h7, zpow_one] at h5
      exact h5
    · rw [h7] at h5
      have h8 : (cubeUnit hl) ^ 2 = 1 := by simpa using h5
      calc cubeUnit hl = (cubeUnit hl) ^ 3 * ((cubeUnit hl) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hu3, h8]; simp
  have hl1 : l = 1 := by
    have := congrArg Units.val hu1
    simpa [cubeUnit] using this
  subst hl1
  have hA1 : A = 1 := Subtype.ext (by rw [hA]; simp)
  have hB1 : B = 1 := Subtype.ext (by rw [hB]; simp)
  rw [hA1, hB1]
  rfl

instance : Finite (G k) := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid

theorem center_le_range_rhoSC : Subgroup.center (G k) ≤ (rhoSC k).range := by
  classical
  let η : Subgroup.center SL(3, k) →* G k :=
    (rhoSC k).comp (((MonoidHom.id SL(3, k)).prod (MonoidHom.id SL(3, k))).comp (Subgroup.center SL(3, k)).subtype)
  have hη : Function.Injective η := by
    intro x y h
    have := rhoSC_injective h
    have h2 := congrArg Prod.fst this
    exact Subtype.ext h2
  have hηker : ∀ z : Subgroup.center SL(3, k), piGL k (η z) = 1 := by
    intro z
    show piGL k (rhoSC k ((z : SL(3, k)), (z : SL(3, k)))) = 1
    rw [piGL_rhoSC]
    obtain ⟨l, hl, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 z.2
    rw [Fintype.card_fin] at hl
    exact (twoA2Mul_eq_one_iff _ _).2 ⟨l, hl, hz.symm, hz.symm⟩
  have hηle : η.range ≤ Subgroup.center (G k) := by
    rintro _ ⟨z, rfl⟩
    exact ker_piGL_le_center (hηker z)
  have hcard : Nat.card (Subgroup.center (G k)) ≤ Nat.card η.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective hη).symm.toEquiv,
      CFSG.RankThree.Classical2.natCard_center_specialLinearGroup (K := k) (n := 3) (by norm_num),
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := k)).1,
      Nat.gcd_comm]
  have heq : η.range = Subgroup.center (G k) := Subgroup.eq_of_le_of_card_ge hηle hcard
  rw [← heq]
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

theorem mem_range_rhoSC_of_piGL_mem {x : G k} (hx : piGL k x ∈ (twoA2Mul k).range) :
    x ∈ (rhoSC k).range := by
  obtain ⟨s, hs⟩ := hx
  have h1 : piGL k (x * (rhoSC k s)⁻¹) = 1 := by
    rw [map_mul, map_inv, piGL_rhoSC, hs, mul_inv_cancel]
  have h2 := center_le_range_rhoSC (ker_piGL_le_center h1)
  have h3 : x = (x * (rhoSC k s)⁻¹) * rhoSC k s := by group
  rw [h3]
  exact mul_mem h2 ⟨s, rfl⟩

abbrev wE6 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd TwClass.wordE6

@[expose] def sigmaGL (k : Type) [Field k] (σ : k →+* k) :
    ModGL Tag.E6 k →* ModGL Tag.E6 k :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) k wE6)).toMonoidHom.comp
    (Units.map (entrywiseHom σ))

theorem sigmaGL_apply (σ : k →+* k) (x : ModGL Tag.E6 k) :
    sigmaGL k σ x = canonicalRep (coxeterSystem Tag.E6) k wE6 * Units.map (entrywiseHom σ) x *
      (canonicalRep (coxeterSystem Tag.E6) k wE6)⁻¹ := rfl

theorem wE6_smul_13 (i j : Fin 3) (hij : i ≠ j) :
    wE6 • (chainRoot chain13 i j : Fin Tag.E6.rank → ℤ) = chainRoot chain56 i j :=
  QuasiE6X2.w_smul_13 i j hij

theorem wE6_smul_56 (i j : Fin 3) (hij : i ≠ j) :
    wE6 • (chainRoot chain56 i j : Fin Tag.E6.rank → ℤ) = chainRoot chain13 i j :=
  QuasiE6X2.w_smul_56 i j hij

theorem twist_13_gen (σ : k →+* k) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : k, e * e = 1 ∧ ∀ c : k, sigmaGL k σ (pinnedX Tag.E6 k (chainRoot chain13 i j) c) =
      pinnedX Tag.E6 k (chainRoot chain56 i j) (e * σ c) := by
  have hroot : IsRoot Tag.E6 (chainRoot chain13 i j) :=
    (CFSG.RankThree.Classical2.chainRoot13_mem_parabolicRoots hij).1
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv k wE6 hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (σ c)
  rw [wE6_smul_13 i j hij] at h'
  rw [sigmaGL_apply, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX σ _ c]
  exact h'

theorem twist_56_gen (σ : k →+* k) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : k, e * e = 1 ∧ ∀ c : k, sigmaGL k σ (pinnedX Tag.E6 k (chainRoot chain56 i j) c) =
      pinnedX Tag.E6 k (chainRoot chain13 i j) (e * σ c) := by
  have hroot : IsRoot Tag.E6 (chainRoot chain56 i j) :=
    CFSG.RankThree.Classical2.isRoot_chainRoot56 hij
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv k wE6 hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (σ c)
  rw [wE6_smul_56 i j hij] at h'
  rw [sigmaGL_apply, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX σ _ c]
  exact h'

theorem sigmaGL_twoA2Mul_mem (σ : k →+* k) (s : SL(3, k) × SL(3, k)) :
    sigmaGL k σ (twoA2Mul k s) ∈ (twoA2Mul k).range := by
  obtain ⟨hQ12, -⟩ := CFSG.RankThree.PartOne.KE6.exists_sl3_root_permuting_12 (Fr := σ)
    (sigmaGL k σ) 1 (fun i j hij => twist_13_gen σ i j hij)
  obtain ⟨hQ21, -⟩ := CFSG.RankThree.PartOne.KE6.exists_sl3_root_permuting_21 (Fr := σ)
    (sigmaGL k σ) 1 (fun i j hij => twist_56_gen σ i j hij)
  obtain ⟨A, B⟩ := s
  rw [twoA2Mul_apply, map_mul]
  have h1 := hQ12 _ ((a2Equiv₁ k).symm A).2
  have h2 := hQ21 _ ((a2Equiv₂ k).symm B).2
  rw [(commute_Q₁_Q₂ h2 h1).eq.symm]
  have hr : (sigmaGL k σ ((a2Equiv₂ k).symm B : ModGL Tag.E6 k)) *
      (sigmaGL k σ ((a2Equiv₁ k).symm A : ModGL Tag.E6 k)) ∈ Set.range (twoA2Mul k) := by
    rw [range_twoA2Mul]
    exact Set.mul_mem_mul h2 h1
  exact hr

theorem reduced_wordE6 : (coxeterSystem Tag.E6).IsReduced TwClass.wordE6 :=
  isReduced_of_reducedCheck (by decide +kernel)

@[expose] def tilde (k : Type) [Field k] : G k := CFSG.HardMathSupport.Timmesfeld.CrossChar.e6NWord k TwClass.wordE6

theorem piGL_tilde (k : Type) [Field k] [Finite k] :
    piGL k (tilde k) = canonicalRep (coxeterSystem Tag.E6) k wE6 :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_nWord_eq_canonicalRep reduced_wordE6

@[expose] def Fsc (σ : k →+* k) : G k →* G k := CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid σ

theorem piGL_Fsc (σ : k →+* k) (x : G k) :
    piGL k (Fsc σ x) = Units.map (entrywiseHom σ) (piGL k x) := by
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_minBC σ x

theorem minBC_comp {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ι : k →+* k')
    (κ : k' →+* k'') :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid (κ.comp ι) =
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid κ).comp
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid ι) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
  rintro _ ⟨i, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply, CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC_xm_single,
      RingHom.comp_apply]
  · simp only [MonoidHom.comp_apply, CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC_xm_neg_single,
      RingHom.comp_apply]

theorem Fsc_minBC {K : Type} [Field K] (ι : K →+* k) (σ : k →+* k) (hσι : σ.comp ι = ι)
    (x : ↥(e6Data_valid.minGroup K)) :
    Fsc σ (CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid ι x) =
      CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid ι x := by
  have h := congrArg (fun f => f x) (minBC_comp (k := K) ι σ)
  simp only [MonoidHom.comp_apply, hσι] at h
  exact h.symm

theorem Fsc_tilde (σ : k →+* k) : Fsc σ (tilde k) = tilde k := by
  unfold tilde CFSG.HardMathSupport.Timmesfeld.CrossChar.e6NWord Fsc
  rw [map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  show CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid σ (e6Data_valid.nt k i 1) =
    e6Data_valid.nt k i 1
  unfold CFSG.LieType.Steinberg.Minuscule.MinData.Valid.nt
  rw [map_mul, map_mul, CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC_xm_single,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC_xm_neg_single]
  simp

@[expose] def sigmaTilde (σ : k →+* k) : G k →* G k :=
  (MulAut.conj (tilde k)).toMonoidHom.comp (Fsc σ)

theorem piGL_sigmaTilde (σ : k →+* k) (x : G k) :
    piGL k (sigmaTilde σ x) = sigmaGL k σ (piGL k x) := by
  show piGL k (tilde k * Fsc σ x * (tilde k)⁻¹) = _
  rw [map_mul, map_mul, map_inv, piGL_tilde, piGL_Fsc]
  rfl

theorem sigmaTilde_rhoSC_mem (σ : k →+* k) (s : SL(3, k) × SL(3, k)) :
    sigmaTilde σ (rhoSC k s) ∈ (rhoSC k).range := by
  apply mem_range_rhoSC_of_piGL_mem
  rw [piGL_sigmaTilde, piGL_rhoSC]
  exact sigmaGL_twoA2Mul_mem σ s

@[expose] def sigmaHat (σ : k →+* k) : SL(3, k) × SL(3, k) →* SL(3, k) × SL(3, k) :=
  (MonoidHom.ofInjective (rhoSC_injective (k := k))).symm.toMonoidHom.comp
    (((sigmaTilde σ).comp (rhoSC k)).codRestrict (rhoSC k).range (sigmaTilde_rhoSC_mem σ))

theorem rhoSC_sigmaHat (σ : k →+* k) (s : SL(3, k) × SL(3, k)) :
    rhoSC k (sigmaHat σ s) = sigmaTilde σ (rhoSC k s) := by
  have h := (MonoidHom.ofInjective (rhoSC_injective (k := k))).apply_symm_apply
    ⟨sigmaTilde σ (rhoSC k s), sigmaTilde_rhoSC_mem σ s⟩
  exact congrArg Subtype.val h

theorem twoA2Mul_sigmaHat (σ : k →+* k) (s : SL(3, k) × SL(3, k)) :
    twoA2Mul k (sigmaHat σ s) = sigmaGL k σ (twoA2Mul k s) := by
  rw [← piGL_rhoSC, rhoSC_sigmaHat, piGL_sigmaTilde, piGL_rhoSC]

theorem exists_fixed_pair {K : Type} [Field K] [Finite K] (ι : K →+* k) (σ : k →+* k)
    (hσι : σ.comp ι = ι) {x₀ : ModGL Tag.E6 K} (hx₀ : x₀ ∈ adjointGroup Tag.E6 K)
    {g₀ : ModGL Tag.E6 k} (hg₀ : g₀ ∈ adjointGroup Tag.E6 k)
    (hlang : Units.map (entrywiseHom σ) g₀ = g₀ * canonicalRep (coxeterSystem Tag.E6) k wE6)
    {s : SL(3, k) × SL(3, k)} (hs : twoA2Mul k s = g₀⁻¹ * baseChangeGL ι x₀ * g₀) :
    ∃ s' : SL(3, k) × SL(3, k), twoA2Mul k s' = g₀⁻¹ * baseChangeGL ι x₀ * g₀ ∧
      sigmaHat σ s' = s' := by
  obtain ⟨xS₀, hxS₀⟩ := e6Isogeny_surjective K ⟨x₀, hx₀⟩
  obtain ⟨gS, hgS⟩ := e6Isogeny_surjective k ⟨g₀, hg₀⟩
  set xS : G k := CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid ι xS₀ with hxS
  have hpx : piGL k xS = baseChangeGL ι x₀ := by
    show ((e6Isogeny k (CFSG.HardMathSupport.Timmesfeld.CrossChar.minBC e6Data_valid ι xS₀) :
      adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_minBC, hxS₀]
  have hpg : piGL k gS = g₀ := congrArg Subtype.val hgS
  set tS : G k := gS⁻¹ * xS * gS with htS
  have hpt : piGL k tS = g₀⁻¹ * baseChangeGL ι x₀ * g₀ := by
    rw [htS, map_mul, map_mul, map_inv, hpx, hpg]
  have hmem : tS ∈ (rhoSC k).range :=
    mem_range_rhoSC_of_piGL_mem ⟨s, by rw [hs, ← hpt]⟩
  obtain ⟨s', hs'⟩ := hmem
  set z : G k := (gS * tilde k)⁻¹ * Fsc σ gS with hz
  have hzc : z ∈ Subgroup.center (G k) := by
    apply ker_piGL_le_center
    rw [hz, map_mul, map_inv, map_mul, piGL_tilde, piGL_Fsc, hpg, hlang]
    group
  have hcomm : ∀ a : G k, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hzc a).symm
  have hFg : Fsc σ gS = gS * tilde k * z := by rw [hz]; group
  have hFx : Fsc σ xS = xS := Fsc_minBC ι σ hσι xS₀
  have hfix : sigmaTilde σ tS = tS := by
    show tilde k * Fsc σ tS * (tilde k)⁻¹ = tS
    rw [htS, map_mul, map_mul, map_inv, hFx, hFg]
    have h1 : z⁻¹ * (tilde k)⁻¹ * gS⁻¹ * xS * (gS * tilde k * z) =
        (tilde k)⁻¹ * gS⁻¹ * xS * gS * tilde k := by
      have hz' : z⁻¹ * (tilde k)⁻¹ * gS⁻¹ * xS * (gS * tilde k * z) =
          z⁻¹ * (((tilde k)⁻¹ * gS⁻¹ * xS * (gS * tilde k)) * z) := by group
      rw [hz', ← hcomm, inv_mul_cancel_left]
      group
    calc tilde k * ((gS * tilde k * z)⁻¹ * xS * (gS * tilde k * z)) * (tilde k)⁻¹
        = tilde k * (z⁻¹ * (tilde k)⁻¹ * gS⁻¹ * xS * (gS * tilde k * z)) * (tilde k)⁻¹ := by group
      _ = gS⁻¹ * xS * gS := by rw [h1]; group
  refine ⟨s', ?_, ?_⟩
  · rw [← hpt, ← hs', piGL_rhoSC]
  · apply rhoSC_injective (k := k)
    rw [rhoSC_sigmaHat, hs']
    exact hfix

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiE6Sc
