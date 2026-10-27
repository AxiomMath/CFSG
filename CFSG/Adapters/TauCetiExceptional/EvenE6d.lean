module

public import CFSG.Adapters.TauCetiExceptional.EvenBlockEndgame
public import CFSG.Adapters.TauCetiExceptional.EvenMono
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Carrier
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Dual

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell Twisted
open TauCeti.DynkinType TauCeti.E6DoubledMinuscule
open scoped Matrix

@[expose] def tableMono {r n : ℕ} (T : MinusculeWeightTable (Fin r) (Fin n)) (L : Type)
    [Field L] : MonoRoots L n r where
  E i := (T.raisingMatrix i).map (Int.cast : ℤ → L)
  F i := (T.loweringMatrix i).map (Int.cast : ℤ → L)
  wt := T.weight
  refl := T.reflection
  E_apply i a b := by
    rw [Matrix.map_apply, T.raisingMatrix_apply]
    split_ifs <;> simp
  F_apply i a b := by
    rw [Matrix.map_apply, T.loweringMatrix_apply]
    split_ifs <;> simp
  refl_refl := T.reflection_apply_apply
  wt_refl := T.weight_reflection_self

theorem e6_isDiag_of_commute_two {L : Type} [Field L] (z : ↥(E6DoubledMinuscule.points L))
    (h : ∀ i, ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) *
        e6E L i = e6E L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) :
          Matrix (Fin 54) (Fin 54) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6F L i =
        e6F L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L))
    {a b : Fin 54} (hab : a ≠ b) :
    ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) a b = 0 := by
  set Z := ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) with hZ
  have hZd : IsBlockDiag e6Blk L Z := points_isBlockDiag L z
  have hU := (commute_iff_ulBlock L z).1 h
  simp only [raisingMatrix_eq_weightTable, loweringMatrix_eq_weightTable] at hU
  have hUd : ∀ x y, x ≠ y → ulBlock Z x y = 0 := fun x y hxy =>
    (tableMono E6Minuscule.weightTable L).isDiag_of_commute
      E6Minuscule.weightTable.weight_injective
      E6Minuscule.weightTable.weight_eq_neg_one_or_eq_zero_or_eq_one
      (fun i => (hU i).1) (fun i => (hU i).2) hxy
  have hdual := lrBlock_transpose_mul_ulBlock (z : Matrix.GeneralLinearGroup (Fin 54) L) z.2
  rw [← hZ] at hdual
  have hsum : ∀ y x, ((lrBlock Z)ᵀ * ulBlock Z) y x = lrBlock Z x y * ulBlock Z x x := by
    intro y x
    rw [Matrix.mul_apply, Finset.sum_eq_single x (fun c _ hc => by rw [hUd c x hc, mul_zero])
      (by simp), Matrix.transpose_apply]
  have hxx : ∀ x, ulBlock Z x x ≠ 0 := fun x h0 => by
    have e := congrFun (congrFun hdual x) x
    rw [hsum, h0, mul_zero, Matrix.one_apply_eq] at e
    exact zero_ne_one e
  have hLd : ∀ x y, x ≠ y → lrBlock Z x y = 0 := by
    intro x y hxy
    have e := congrFun (congrFun hdual y) x
    rw [hsum, Matrix.one_apply_ne hxy.symm] at e
    exact (mul_eq_zero.1 e).resolve_right (hxx x)
  obtain ⟨x, rfl⟩ := matrixIndexEquiv.surjective a
  obtain ⟨y, rfl⟩ := matrixIndexEquiv.surjective b
  rcases x with x | x <;> rcases y with y | y
  · exact hUd x y fun e => hab (by rw [e])
  · exact hZd _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide)
  · exact hZd _ _ (by rw [e6Blk_inr, e6Blk_inl]; decide)
  · exact hLd x y fun e => hab (by rw [e])

theorem e6_table_head : (∀ i, e6MinusculeWeight 0 i ≠ -1) ∧
    ∀ b : Fin 27, b ≠ 0 → ∃ i, e6MinusculeWeight b i = -1 := by
  decide +kernel

theorem e6_table_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .E6)),
    (∀ ij : Fin (Tag.rank .E6) × Fin (Tag.rank .E6),
      Tag.cartan .E6 (π' ij.1) (π' ij.2) = Tag.cartan .E6 ij.1 ij.2) →
      (∀ j, e6MinusculeWeight 0 j = 1 ↔ e6MinusculeWeight 0 (π' j) = 1) → π' = 1 := by
  decide +kernel

namespace E6PushDown

variable {L : Type} [Field L] (P : Twisted.E6PushDown L)

theorem mem_center_of_commute_two {z : ↥(E6DoubledMinuscule.points L)}
    (h : ∀ i, ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) *
        e6E L i = e6E L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) :
          Matrix (Fin 54) (Fin 54) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6F L i =
        e6F L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)) :
    z ∈ Subgroup.center ↥(E6DoubledMinuscule.points L) := by
  have hdiag : ∀ a b, a ≠ b →
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) a b = 0 :=
    fun _ _ hab => e6_isDiag_of_commute_two z h hab
  rw [Subgroup.mem_center_iff]
  intro w
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact (commute_of_diag e6Blk hdiag
    (fun a b hab => e6_diag_eq_of_commute hdiag (fun i => (h i).1) (fun i => (h i).2) hab)
    (e6d_points_isBlockDiag L _ w.2)).symm

@[expose] def blockCarrierTwo : BlockCarrier .E6 L 54 2 where
  C := E6DoubledMinuscule.points L
  π := P.π
  u := Twisted.E6PushDown.u
  v := Twisted.E6PushDown.v
  E := e6E L
  F := e6F L
  coe_u := Twisted.E6PushDown.coe_u
  coe_v := Twisted.E6PushDown.coe_v
  u_add i c d := by simp only [Twisted.E6PushDown.u, ofAdd_add, map_mul]
  v_add i c d := by simp only [Twisted.E6PushDown.v, ofAdd_add, map_mul]
  π_u i c := P.π_u i c
  π_v i c := P.π_v i c
  blk := e6Blk
  block z := e6d_points_isBlockDiag L _ z.2
  ker_diag z hz _ _ hab := e6_isDiag_of_commute_two z ((P.ker_iff z).1 hz) hab
  ker_center z hz := mem_center_of_commute_two ((P.ker_iff z).1 hz)
  wt := e6Wt
  wt_mem := e6Wt_mem
  comm := e6E_comm L
  comm_HE := e6E_commH L
  E_ne := e6E_ne_zero L
  cartan_off := cartan_E6_off
  excl := fun π' hc h => e6_excl π' hc h

end E6PushDown

theorem exclTwo_e6
    {L : Type} [Field L] (P : Twisted.E6PushDown L) :
    ExclTwo (E6PushDown.blockCarrierTwo P) := by
  intro z π' c hc hcart hE hF
  set Z : Matrix (Fin 54) (Fin 54) L := (E6PushDown.blockCarrierTwo P).mat z with hZ
  set Zi : Matrix (Fin 54) (Fin 54) L := (E6PushDown.blockCarrierTwo P).mat z⁻¹ with hZi
  have hZd : IsBlockDiag e6Blk L Z := points_isBlockDiag L z
  have hZd' : IsBlockDiag e6Blk L Zi := points_isBlockDiag L z⁻¹
  have hzi : ulBlock Zi * ulBlock Z = 1 := by
    rw [← ulBlock_mul hZd', hZi, hZ, (E6PushDown.blockCarrierTwo P).mat_inv_mul z, ulBlock_one]
  have hE' : ∀ j, ulBlock Z * (tableMono E6Minuscule.weightTable L).E j * ulBlock Zi =
      c j • (tableMono E6Minuscule.weightTable L).E (π' j) := by
    intro j
    have e : ulBlock (Z * e6E L j * Zi) = ulBlock (c j • e6E L (π' j)) := congrArg ulBlock (hE j)
    rw [ulBlock_mul (hZd.mul (isBlockDiag_e6E L j)), ulBlock_mul hZd, ulBlock_smul,
      ulBlock_e6E L j, ulBlock_e6E L (π' j), raisingMatrix_eq_weightTable j,
      raisingMatrix_eq_weightTable (π' j)] at e
    exact e
  have hF' : ∀ j, ulBlock Z * (tableMono E6Minuscule.weightTable L).F j * ulBlock Zi =
      (c j)⁻¹ • (tableMono E6Minuscule.weightTable L).F (π' j) := by
    intro j
    have e : ulBlock (Z * e6F L j * Zi) = ulBlock ((c j)⁻¹ • e6F L (π' j)) :=
      congrArg ulBlock (hF j)
    rw [ulBlock_mul (hZd.mul (isBlockDiag_e6F L j)), ulBlock_mul hZd, ulBlock_smul,
      ulBlock_e6F L j, ulBlock_e6F L (π' j), loweringMatrix_eq_weightTable j,
      loweringMatrix_eq_weightTable (π' j)] at e
    exact e
  have hwt : (tableMono E6Minuscule.weightTable L).wt = e6MinusculeWeight :=
    E6Minuscule.weightTable_weight
  refine e6_table_excl π' (fun ij => hcart ij.1 ij.2) fun j => ?_
  have key := (tableMono E6Minuscule.weightTable L).wt_eq_one_iff_of_conj (fun _ => (0 : Fin 1))
    hzi (fun _ _ h => absurd rfl h) π' hc hE' hF' (h := 0) (by rw [hwt]; exact e6_table_head.1)
    (fun b _ hb => by rw [hwt]; exact e6_table_head.2 b hb) j
  rwa [hwt] at key

end CFSG.TauCetiBridge.Even
