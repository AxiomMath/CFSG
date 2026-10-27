module

public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple
public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidWeights
public import CFSG.LieType.HighestRoot.Defs

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
  CFSG.ClassicalInvolution.ModelFacts.D4Rigid CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.LieType.HighestRoot
open scoped MatrixGroups

@[expose] def triPerm : Fin 4 → Fin 4 := ![2, 1, 3, 0]

theorem cartanD_triPerm (i j : Fin 4) : cartanD 4 (triPerm i) (triPerm j) = cartanD 4 i j := by
  fin_cases i <;> fin_cases j <;> simp [triPerm, LevisSpin.cartanD_apply]

@[expose] def triEquiv : Fin 4 ≃ Fin 4 where
  toFun := triPerm
  invFun := ![3, 1, 0, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {p f : ℕ} [Fact p.Prime]

theorem exists_triality (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    (hq : 4 ≤ Nat.card (GaloisField p f)) (hF : Nat.card (GaloisField p f) = p ^ f) :
    ∃ ρ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)),
      ∀ k : Fin 4, (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k).map
        ρ.toMonoidHom = rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup
          (triPerm k) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by omega)
  have hgen : ⨆ k, rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup (triPerm k) = ⊤ := by
    have h := Balance.iSup_rankOne_eq_top (plusDatum 4 (GaloisField p f) hn3)
      (Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top 4 _ hn3))
    rw [← h]
    exact (Equiv.iSup_comp (g := fun k => rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup k)
      triEquiv)
  obtain ⟨Ψ, hΨsurj, -, -, -, -, hΨ⟩ := weakCT_spinPlus hadm hn3 hF hq
    (X := spinGroup (quadPlus 4 (GaloisField p f)))
    (fun k => rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup (triPerm k)) hgen
    (fun i j hij h1 h2 a ha b hb => by
      have h0 := (LevisSpin.cartanD_of_not_edgeD hij h1 h2).1
      rw [← cartanD_triPerm] at h0
      exact commutes_rankOne_plusDatum hn3 h0 a ha b hb)
    (fun i j h => by
      have h0 := (LevisSpin.cartanD_of_edgeD h).1
      rw [← cartanD_triPerm] at h0
      exact standardPair_plusDatum_of_cartan hn3 h0)
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup (quadPlus 4 (GaloisField p f))) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hinj : Function.Injective Ψ := Finite.injective_iff_surjective.mpr hΨsurj
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hΨsurj⟩, hΨ⟩

section Nodes

variable {F : Type} [Field F]

theorem rankOne_zero :
    rankOne (plusDatum 4 F (by norm_num)).rootGroup (0 : Fin 4) =
      ((fr F).longSL2 ne01 true false).range :=
  rankOne_plusDatum_of_lt (K := F) (m := 4) (by norm_num) (k := 0) (by decide)

theorem rankOne_two :
    rankOne (plusDatum 4 F (by norm_num)).rootGroup (2 : Fin 4) =
      ((fr F).longSL2 ne23 true false).range :=
  rankOne_plusDatum_of_lt (K := F) (m := 4) (by norm_num) (k := 2) (by decide)

theorem rankOne_three :
    rankOne (plusDatum 4 F (by norm_num)).rootGroup (3 : Fin 4) =
      ((fr F).longSL2 ne23 true true).range := by
  have h := toStdD_single_eq (n := 4) (by norm_num) (3 : Fin 4)
  have h1 : rootIdxD 4 (3 : Fin 4) = 2 :=
    Fin.ext (by simpa using val_rootIdxD_of_not_lt 4 (k := (3 : Fin 4)) (by decide))
  have h2 : rootIdxD' 4 (3 : Fin 4) = 3 :=
    Fin.ext (by simpa using val_rootIdxD'_of_not_lt 4 (k := (3 : Fin 4)) (by decide))
  have h3 : rootSignD 4 (3 : Fin 4) = true := by decide
  rw [h1, h2, h3] at h
  exact rootGroup_sup_eq_longSL2_range (by norm_num) ne23 true true h

@[expose] noncomputable def z0 (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longSL2 ne01 true false (-1)

@[expose] noncomputable def z2 (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longSL2 ne23 true false (-1)

@[expose] noncomputable def z3 (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longSL2 ne23 true true (-1)

theorem z0_mem : z0 F ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (0 : Fin 4) := by
  rw [rankOne_zero]
  exact ⟨-1, rfl⟩

theorem z2_mem : z2 F ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (2 : Fin 4) := by
  rw [rankOne_two]
  exact ⟨-1, rfl⟩

theorem z3_mem : z3 F ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (3 : Fin 4) := by
  rw [rankOne_three]
  exact ⟨-1, rfl⟩

theorem orderOf_z0 (h2 : (2 : F) ≠ 0) : orderOf (z0 F) = 2 :=
  orderOf_longSL2_neg_one _ _ _ _ h2

theorem orderOf_z2 (h2 : (2 : F) ≠ 0) : orderOf (z2 F) = 2 :=
  orderOf_longSL2_neg_one _ _ _ _ h2

theorem orderOf_z3 (h2 : (2 : F) ≠ 0) : orderOf (z3 F) = 2 :=
  orderOf_longSL2_neg_one _ _ _ _ h2

theorem z0_mul_self : z0 F * z0 F = 1 := by
  rw [z0, ← map_mul]
  simp

theorem z2_mul_self : z2 F * z2 F = 1 := by
  rw [z2, ← map_mul]
  simp

theorem z3_mul_self : z3 F * z3 F = 1 := by
  rw [z3, ← map_mul]
  simp

end Nodes

section Fund

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PreservesFund (p f : ℕ) [Fact p.Prime]
    (σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f))) :
    Prop :=
  ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)),
    R.map σ.toMonoidHom ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num))

theorem PreservesFund.refl : PreservesFund p f (MulEquiv.refl _) := fun R hR => by
  simpa using hR

theorem PreservesFund.comp {σ τ : spinGroup (quadPlus 4 (GaloisField p f)) ≃*
    spinGroup (quadPlus 4 (GaloisField p f))} (hσ : PreservesFund p f σ)
    (hτ : PreservesFund p f τ) : PreservesFund p f (σ.trans τ) := fun R hR => by
  have := hτ _ (hσ R hR)
  rwa [Subgroup.map_map] at this

theorem preservesFund_of_nodes (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    (σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)))
    (π : Fin 4 → Fin 4)
    (hσ : ∀ k : Fin 4, (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k).map
      σ.toMonoidHom = rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup (π k)) :
    PreservesFund p f σ := by
  intro R hR
  have hn3 : 3 ≤ 4 := by norm_num
  have hsingle : FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 4 p f Fact.out trivial
      hadm (by decide) (by decide)
  obtain ⟨g, hg⟩ := hsingle _ (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (0 : Fin 4)) R hR
  have hmap : R.map σ.toMonoidHom = conjSub (σ g)
      ((rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup (0 : Fin 4)).map σ.toMonoidHom) := by
    rw [hg, conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [hmap, hσ 0]
  exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (π 0)) _

theorem symm_nodes
    (σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)))
    (π : Fin 4 ≃ Fin 4)
    (hσ : ∀ k : Fin 4, (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k).map
      σ.toMonoidHom = rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup (π k))
    (k : Fin 4) :
    (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k).map
      σ.symm.toMonoidHom = rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup
        (π.symm k) := by
  conv_lhs => rw [← π.apply_symm_apply k, ← hσ (π.symm k)]
  rw [Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {F : Type} [Field F]

theorem triality_z0 [Finite F] (h2 : (2 : F) ≠ 0)
    (ρ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
    (hρ : ∀ k : Fin 4, (rankOne (plusDatum 4 F (by norm_num)).rootGroup k).map ρ.toMonoidHom =
      rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm k)) : ρ (z0 F) = z2 F := by
  have hmem : ρ (z0 F) ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm 0) := by
    rw [← hρ 0]
    exact ⟨z0 F, z0_mem, rfl⟩
  have h02 : triPerm 0 = 2 := rfl
  rw [h02, rankOne_two] at hmem
  have hord : orderOf (ρ (z0 F)) = 2 := by rw [MulEquiv.orderOf_eq]; exact orderOf_z0 h2
  exact eq_of_mem_range_longSL2_of_orderOf_eq_two _ _ _ _ h2 hmem hord

theorem triality_z2 [Finite F] (h2 : (2 : F) ≠ 0)
    (ρ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
    (hρ : ∀ k : Fin 4, (rankOne (plusDatum 4 F (by norm_num)).rootGroup k).map ρ.toMonoidHom =
      rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm k)) : ρ (z2 F) = z3 F := by
  have hmem : ρ (z2 F) ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm 2) := by
    rw [← hρ 2]
    exact ⟨z2 F, z2_mem, rfl⟩
  have h23 : triPerm 2 = 3 := rfl
  rw [h23, rankOne_three] at hmem
  have hord : orderOf (ρ (z2 F)) = 2 := by rw [MulEquiv.orderOf_eq]; exact orderOf_z2 h2
  exact eq_of_mem_range_longSL2_of_orderOf_eq_two _ _ _ _ h2 hmem hord

theorem triality_z3 [Finite F] (h2 : (2 : F) ≠ 0)
    (ρ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
    (hρ : ∀ k : Fin 4, (rankOne (plusDatum 4 F (by norm_num)).rootGroup k).map ρ.toMonoidHom =
      rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm k)) : ρ (z3 F) = z0 F := by
  have hmem : ρ (z3 F) ∈ rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm 3) := by
    rw [← hρ 3]
    exact ⟨z3 F, z3_mem, rfl⟩
  have h30 : triPerm 3 = 0 := rfl
  rw [h30, rankOne_zero] at hmem
  have hord : orderOf (ρ (z3 F)) = 2 := by rw [MulEquiv.orderOf_eq]; exact orderOf_z3 h2
  exact eq_of_mem_range_longSL2_of_orderOf_eq_two _ _ _ _ h2 hmem hord

end Fund

end CFSG.ClassicalInvolution.G2D4Models.Twin
