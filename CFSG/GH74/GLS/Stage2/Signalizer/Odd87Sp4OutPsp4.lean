module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutPair
import CFSG.GH74.Generic.BProg.B2.ShapeOrders
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank Matrix CFSG.GH74.Generic.BProg
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat statedSp_ext
  isSupp_pairMat IsSupp.commute)
open CFSG.ComponentClassification.Burgoyne.Sp (lam_injective longRoot_inf)
open scoped MatrixGroups

section Facts

variable {F : Type} [Field F]

theorem spLam_zero_commute_one (X Y : SL(2, F)) :
    lam (k := F) (0 : Fin 2) X * lam 1 Y = lam 1 Y * lam 0 X := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_lam]
  refine (IsSupp.commute (isSupp_pairMat _) (isSupp_pairMat _) ?_).eq
  rw [Set.disjoint_left]
  rintro x (rfl | rfl) (h | h) <;> simp_all

theorem proj_lam_injective (i : Fin 2) :
    Function.Injective ((proj 2 F).comp (lam (k := F) i)) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have h1 : lam (k := F) i X ∈ (proj 2 F).ker := hX
  rw [ker_proj] at h1
  exact (lam_injective (K := F) i) (by
    rw [map_one]
    exact longRoot_inf (r := 2) le_rfl i _ ⟨X, rfl⟩ h1)

theorem exists_commuting_sl2_psp4 :
    ∃ A B : Subgroup (StatedProj (StatedSp 2 F)), Nonempty (↥A ≃* SL(2, F)) ∧
      Nonempty (↥B ≃* SL(2, F)) ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  refine ⟨((proj 2 F).comp (lam (k := F) 0)).range, ((proj 2 F).comp (lam (k := F) 1)).range,
    ⟨(MonoidHom.ofInjective (proj_lam_injective 0)).symm⟩,
    ⟨(MonoidHom.ofInjective (proj_lam_injective 1)).symm⟩, ?_⟩
  rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
  simp only [MonoidHom.comp_apply, ← map_mul, spLam_zero_commute_one]

theorem sl2_exists_not_comm : ∃ x y : SL(2, F), x * y ≠ y * x := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have h0 := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change (( !![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 =
    (( !![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 at h0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h0

variable [Finite F]

theorem isSimpleGroup_psp4 (hodd : Odd (Nat.card F)) :
    IsSimpleGroup (StatedProj (StatedSp 2 F)) := by
  have hgt := Finite.one_lt_card (α := F)
  refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num) ?_
  by_cases h3 : Nat.card F = 3
  · exact Or.inr (Or.inl ⟨h3, le_refl 2⟩)
  · obtain ⟨m, hm⟩ := hodd
    exact Or.inl (Or.inr (by omega))

theorem psp4_centerless (hodd : Odd (Nat.card F)) :
    ∀ z : StatedProj (StatedSp 2 F), (∀ g, g * z = z * g) → z = 1 := by
  have hsimple := isSimpleGroup_psp4 (F := F) hodd
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (StatedProj (StatedSp 2 F))) with h | h
  · have : z ∈ center (StatedProj (StatedSp 2 F)) := Subgroup.mem_center_iff.2 hz
    rwa [h, Subgroup.mem_bot] at this
  · exfalso
    obtain ⟨x, y, hxy⟩ := sl2_exists_not_comm (F := F)
    refine hxy (proj_lam_injective (F := F) 0 ?_)
    have : (proj 2 F) (lam (k := F) 0 x) ∈ center (StatedProj (StatedSp 2 F)) := by
      rw [h]; exact Subgroup.mem_top _
    simp only [MonoidHom.comp_apply, map_mul]
    exact ((Subgroup.mem_center_iff.1 this) _).symm

end Facts

section Certified


theorem not_qShapeNS_of_psp4 {X : Type} [Group X] [Finite X] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : LieModel X .PSp 2 p e) : ¬ QShapeNS X := by
  intro hsh
  obtain ⟨-, -, F, _, _, hF, ⟨ψ⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hX
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  by_cases h3 : p ^ e = 3
  · have hcard := CFSG.ComponentClassification.CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hX
    rw [h3] at hcard
    have hcard' : Nat.card X = 25920 := by norm_num at hcard; omega
    exact B2.ShapeOrders.not_dvd_of_qShapeNS hsh (m := 25920)
      (B2.ShapeOrders.smallOrder_of_dvd_M0 (by norm_num))
      (by simp only [B2.ShapeOrders.NotJ1Order]; norm_num) (by rw [hcard'])
  · have h5 : 5 ≤ Nat.card F := by
      have hgt := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      rw [hF] at hm hgt
      omega
    obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hAB⟩ := exists_commuting_sl2_psp4 (F := F)
    refine not_qShapeNS_of_commuting_sl2 (X := X) ?_ (A := A.map ψ.symm.toMonoidHom)
      (B := B.map ψ.symm.toMonoidHom) hodd h5 hodd h5
      ((A.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).symm.trans eA)
      ((B.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).symm.trans eB) ?_ hsh
    · intro z hz
      have h1 := psp4_centerless hodd (ψ z) fun g => by
        have := hz (ψ.symm g)
        apply ψ.symm.injective
        simpa using this
      apply ψ.injective
      rw [h1, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hAB a ha b hb]

end Certified

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
