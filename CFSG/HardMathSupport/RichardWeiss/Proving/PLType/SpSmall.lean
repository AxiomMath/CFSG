module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Quasithin.Background.HSp4A6Data
public import CFSG.LargeExtraspecial.S7Perm

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving.PLType

open CFSG.Open Matrix

theorem statedSp_eq_lowTwoRank (n : ℕ) (K : Type) [Field K] :
    StatedSp n K = CFSG.Assembly.LowTwoRank.StatedSp n K := rfl

theorem card_statedSp_one_two : Nat.card (StatedSp 1 (ZMod 2)) = 6 := by
  rw [statedSp_eq_lowTwoRank, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_zmod]
  decide

theorem card_statedSp_two_two : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
  rw [statedSp_eq_lowTwoRank, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_zmod, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem nonempty_statedSp_two_mulEquiv_perm_six :
    Nonempty (↥(StatedSp 2 (ZMod 2)) ≃* Equiv.Perm (Fin 6)) := by
  have hmem : ∀ σ : Equiv.Perm (Fin 6), CFSG.Quasithin.H.Sp4A6.psiHom σ ∈ StatedSp 2 (ZMod 2) :=
    fun σ => Subgroup.subset_closure (CFSG.Quasithin.H.Sp4A6.psiMat_symplectic σ)
  let f : Equiv.Perm (Fin 6) →* ↥(StatedSp 2 (ZMod 2)) :=
    (CFSG.Quasithin.H.Sp4A6.psiHom).codRestrict _ hmem
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    apply CFSG.Quasithin.H.Sp4A6.psiMat_eq_one σ
    have h1 : f σ = 1 := hσ
    have h2 : CFSG.Quasithin.H.Sp4A6.psiHom σ = 1 := congrArg Subtype.val h1
    rw [← CFSG.Quasithin.H.Sp4A6.coe_psiHom, h2]
    rfl
  have hcard : Nat.card (Equiv.Perm (Fin 6)) = Nat.card ↥(StatedSp 2 (ZMod 2)) := by
    rw [card_statedSp_two_two, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hbij : Function.Bijective f :=
    (Function.Injective.bijective_of_nat_card_le hinj hcard.ge)
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

@[expose] def tMat : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2) := Matrix.fromBlocks 1 1 0 1

@[expose] def gMat : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2) := Matrix.fromBlocks 0 1 1 0

theorem tMat_mul_self : tMat * tMat = 1 := by decide

theorem gMat_mul_self : gMat * gMat = 1 := by decide

@[expose] def tGL : GL (Fin 1 ⊕ Fin 1) (ZMod 2) := ⟨tMat, tMat, tMat_mul_self, tMat_mul_self⟩

@[expose] def gGL : GL (Fin 1 ⊕ Fin 1) (ZMod 2) := ⟨gMat, gMat, gMat_mul_self, gMat_mul_self⟩

theorem tGL_mem : tGL ∈ StatedSp 1 (ZMod 2) :=
  Subgroup.subset_closure (show tMatᵀ * Matrix.fromBlocks 0 1 (-1) 0 * tMat =
    Matrix.fromBlocks 0 1 (-1) 0 by decide)

theorem gGL_mem : gGL ∈ StatedSp 1 (ZMod 2) :=
  Subgroup.subset_closure (show gMatᵀ * Matrix.fromBlocks 0 1 (-1) 0 * gMat =
    Matrix.fromBlocks 0 1 (-1) 0 by decide)

theorem nonempty_statedSp_one_mulEquiv_perm_three :
    Nonempty (↥(StatedSp 1 (ZMod 2)) ≃* Equiv.Perm (Fin 3)) := by
  set t : ↥(StatedSp 1 (ZMod 2)) := ⟨tGL, tGL_mem⟩ with ht
  set g : ↥(StatedSp 1 (ZMod 2)) := ⟨gGL, gGL_mem⟩ with hg
  have hmat : ∀ x y : ↥(StatedSp 1 (ZMod 2)),
      ((x : GL (Fin 1 ⊕ Fin 1) (ZMod 2)) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2)) =
        ((y : GL (Fin 1 ⊕ Fin 1) (ZMod 2)) : Matrix _ _ _) → x = y :=
    fun x y h => Subtype.ext (Units.ext h)
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact hmat _ _ tMat_mul_self
  have ht1 : t ≠ 1 := fun h => by
    have := congrArg (fun x : ↥(StatedSp 1 (ZMod 2)) =>
      ((x : GL (Fin 1 ⊕ Fin 1) (ZMod 2)) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2))) h
    exact absurd this (by decide : tMat ≠ 1)
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hT : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  refine CFSG.LargeExtraspecial.S7.nonempty_mulEquiv_perm_three card_statedSp_one_two hT ?_
  intro hN
  have hc : g * t * g⁻¹ ∈ Subgroup.zpowers t := hN.conj_mem t (Subgroup.mem_zpowers t) g
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hc
  simp only [Finset.mem_image, Finset.mem_range] at hc
  obtain ⟨k, hk, hk'⟩ := hc
  have hginv : g⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one]
    exact hmat _ _ gMat_mul_self
  rw [hginv] at hk'
  interval_cases k
  · have := congrArg (fun x : ↥(StatedSp 1 (ZMod 2)) =>
      ((x : GL (Fin 1 ⊕ Fin 1) (ZMod 2)) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2))) hk'
    exact absurd this (by decide : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2)) ≠
      gMat * tMat * gMat)
  · have := congrArg (fun x : ↥(StatedSp 1 (ZMod 2)) =>
      ((x : GL (Fin 1 ⊕ Fin 1) (ZMod 2)) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2))) hk'
    simp only [pow_one] at this
    exact absurd this (by decide : tMat ≠ gMat * tMat * gMat)

theorem spSmall_holds :
    CFSG.HardMathSupport.Curtis.Coordinator.PLType.SpSmall :=
  ⟨nonempty_statedSp_one_mulEquiv_perm_three, nonempty_statedSp_two_mulEquiv_perm_six⟩

end CFSG.HardMathSupport.RichardWeiss.Proving.PLType
