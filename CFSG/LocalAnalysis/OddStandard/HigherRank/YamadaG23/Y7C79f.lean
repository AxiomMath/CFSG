module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Quasithin.Background.G119Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

private theorem isPerfect_GL32 :
    Group.IsPerfect (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.G11.g119_isPerfect_generalLinearGroup_zmod2 (n := 3) (by norm_num)

private theorem center_GL32_eq_bot :
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨r, rfl⟩
  rw [Subsingleton.elim r 1, map_one]
  exact Subgroup.one_mem _

theorem y7c_schur_quot
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2)
    {Q : Type} [Group Q] [Finite Q] {Zb : Subgroup Q} [Zb.Normal] (hZ : Zb ≤ Subgroup.center Q)
    (e : Nonempty ((Q ⧸ Zb) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :
    Nat.card ↥(commutator Q ⊓ Zb) ∣ 2 := by
  obtain ⟨e⟩ := e
  haveI : Group.IsPerfect (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := isPerfect_GL32
  haveI : Group.IsPerfect (Q ⧸ Zb) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f : Q →* Q ⧸ Zb := QuotientGroup.mk' Zb
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Zb
  have hmap : (commutator Q).map f = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective f hf]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator Q ⊔ Zb = ⊤ := by
    rw [← QuotientGroup.ker_mk' Zb, ← top_le_iff,
      ← Subgroup.map_le_map_iff (f := f) (H := ⊤) (K := commutator Q), Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective f hf, top_le_iff]
    exact hmap
  have hCZb : ⁅commutator Q, Zb⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr
        (hZ.trans (Subgroup.center_le_centralizer (commutator Q : Set Q))))
  have hZbC : ⁅(Zb : Subgroup Q), commutator Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZ.trans (Subgroup.center_le_centralizer (commutator Q : Set Q)))
  have hZbZb : ⁅(Zb : Subgroup Q), Zb⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZ.trans (Subgroup.center_le_centralizer (Zb : Set Q)))
  have hcomm : ⁅commutator Q ⊔ Zb, commutator Q ⊔ Zb⁆ = ⁅commutator Q, commutator Q⁆ := by
    rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left, Subgroup.commutator_sup_left,
      hCZb, hZbC, hZbZb]
    simp
  have hperfect : Group.IsPerfect ↥(commutator Q) := by
    rw [Subgroup.isPerfect_iff, ← hcomm, hsup]
    rfl
  let ψ : ↥(commutator Q) →* Q ⧸ Zb := f.comp (commutator Q).subtype
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (commutator Q).map f := by rw [hmap]; exact Subgroup.mem_top y
    obtain ⟨c, hc, hfc⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, hfc⟩
  have hψker : ψ.ker = Zb.subgroupOf (commutator Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : Q)
  let φ : ↥(commutator Q) →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    e.toMonoidHom.comp ψ
  have hφsurj : Function.Surjective φ := e.surjective.comp hψsurj
  have hφker : φ.ker = Zb.subgroupOf (commutator Q) := by
    rw [← hψker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    exact MulEquiv.map_eq_one_iff e
  have hcenter : Subgroup.center ↥(commutator Q) = Zb.subgroupOf (commutator Q) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyle : φ y ∈ (Subgroup.center ↥(commutator Q)).map φ :=
        Subgroup.mem_map_of_mem φ hy
      have hle : (Subgroup.center ↥(commutator Q)).map φ ≤
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
        Subgroup.map_center_le_center hφsurj
      have hbot : φ y ∈ (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
        rw [← center_GL32_eq_bot]
        exact hle hyle
      rw [← hφker, MonoidHom.mem_ker]
      simpa using hbot
    · intro y hy
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hy)) (x : Q)
  have hφcenter : φ.ker = Subgroup.center ↥(commutator Q) := hφker.trans hcenter.symm
  let e' : ↥(commutator Q) ⧸ Subgroup.center ↥(commutator Q) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hφcenter).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := φ) hφsurj)
  have hdvd : Nat.card (Subgroup.center ↥(commutator Q)) ∣ 2 :=
    (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperfect e').trans hM
  have hcard : Nat.card (Subgroup.center ↥(commutator Q)) =
      Nat.card ↥(commutator Q ⊓ Zb) := by
    rw [hcenter, ← Subgroup.inf_subgroupOf_left (H := Zb) (K := commutator Q)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rwa [hcard] at hdvd

end CFSG.OddStandard.HigherRank.YamadaG23
