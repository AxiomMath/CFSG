module

public import CFSG.LargeExtraspecial.S12InspFamESpBasic
public import CFSG.LargeExtraspecial.S12InspXOrd
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.Fischer.Classification CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace S12InspSp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem nonempty_SpG_mulEquiv_isometryGroup (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) :
    Nonempty (SpG b ≃* TauCeti.BilinForm.isometryGroup b) := by
  let e : GL ι (ZMod 2) ≃* ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2))
  have he : ∀ (A : GL ι (ZMod 2)) x, e A x = (A : Matrix ι ι (ZMod 2)) *ᵥ x := fun _ _ => rfl
  have hcomap : SpG b = (TauCeti.BilinForm.isometryGroup b).comap e.toMonoidHom := by
    ext A
    rw [Subgroup.mem_comap, mem_fischerMatrixGroup_bilin_iff,
      TauCeti.BilinForm.mem_isometryGroup_iff]
    simp only [MulEquiv.coe_toMonoidHom, he]
  have hmap : (SpG b).map e.toMonoidHom = TauCeti.BilinForm.isometryGroup b := by
    rw [hcomap, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  exact ⟨(e.subgroupMap (SpG b)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem statedScalars_zmod_two_eq_bot (n : ℕ) :
    StatedScalars (Fin n ⊕ Fin n) (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  have hu : u = 1 := Units.ext ((zmod_two_cases (u : ZMod 2)).resolve_left (Units.ne_zero u))
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem nonempty_SpG_mulEquiv {m : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    Nonempty (SpG b ≃* StatedProj (StatedSp m (ZMod 2))) := by
  obtain ⟨e₁⟩ := nonempty_SpG_mulEquiv_isometryGroup b
  have hB : b.IsAlt := halt
  have hnd' : b.Nondegenerate :=
    ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => by rw [b_symm halt]; exact hy x⟩
  obtain ⟨m', hm', ⟨e₂⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      b hB hnd'
  rw [Module.finrank_fin_fun] at hm'
  obtain rfl : m' = m := by omega
  have hbot : (StatedScalars (Fin m' ⊕ Fin m') (ZMod 2)).subgroupOf (StatedSp m' (ZMod 2)) = ⊥ := by
    rw [statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  let e₃ : StatedSp m' (ZMod 2) ≃* StatedProj (StatedSp m' (ZMod 2)) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  exact ⟨(e₁.trans e₂).trans ((MulEquiv.subgroupCongr
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm).trans e₃)⟩

theorem card_outer_SpG {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) : Nat.card (Outer (SpG b)) = 1 := by
  obtain ⟨e⟩ := nonempty_SpG_mulEquiv (m := m) halt hnd
  have h := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    Nat.prime_two le_rfl hm (K := ZMod 2) (by rw [Nat.card_zmod, pow_one])).1
  rw [← Nat.card_congr (equivalence e).toEquiv] at h
  norm_num at h
  exact h

end S12InspSp

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem xbar12_eq_mbar_of_sp {g : G} {t : S.O} (hS : S.S12Standing g t) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (φ : S.Xbar12 g ≃* S12InspSp.SpG b) :
    S.Xbar12 g = S.Mbar := by
  have hO : Nat.card (Outer (S.Xbar12 g)) = 1 := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    exact S12InspSp.card_outer_SpG hm halt hnd
  have h := card_Mbar_dvd_card_Xbar12_mul_card_outer hS
  rw [hO, mul_one] at h
  exact Subgroup.eq_of_le_of_card_ge Xbar12_le_Mbar (Nat.le_of_dvd Nat.card_pos h)

end Setting

end CFSG.LargeExtraspecial
