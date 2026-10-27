module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshNormalKernel
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Model

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.CosetTable CFSG.EvenSporadicStandard.Fin76b

section Injective

variable {Q H : Type*} [Group Q] [Finite Q] [Group H]

theorem injective_of_selfCentralizing (M E : Subgroup Q) (hEM : E ≤ M)
    (hnorm : ∀ x ∈ M, ∀ y ∈ E, x * y * x⁻¹ ∈ E) (hp : IsPGroup 2 E)
    (hcen : ∀ x ∈ M, (∀ y ∈ E, x * y = y * x) → x ∈ E) {z : Q} (hzE : z ∈ E)
    (hz : ∀ y ∈ E, (∀ y' ∈ E, y * y' = y' * y) → y = 1 ∨ y = z)
    (Ψ : ↥M →* H) (hΨ : Ψ ⟨z, hEM hzE⟩ ≠ 1) : Function.Injective Ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  let E' : Subgroup ↥M := E.subgroupOf M
  haveI : E'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Q) ∈ E := hn
    show ((g * n * g⁻¹ : ↥M) : Q) ∈ E
    simpa using hnorm g g.2 n hn'
  have hp' : IsPGroup 2 E' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hEM).symm
  have hmem := mem_of_normal_of_selfCentralizing (E := E') (hp := hp')
    (z := ⟨z, hEM hzE⟩) (K := Ψ.ker) (by
      intro m hm
      have : (m : Q) ∈ E := hcen m m.2 (fun y hy => by
        have := hm ⟨y, hEM hy⟩ (show (⟨y, hEM hy⟩ : ↥M) ∈ E' from hy)
        exact congrArg Subtype.val this)
      exact this) hzE (by
      intro y hy hcomm
      have hy' : (y : Q) ∈ E := hy
      rcases hz y hy' (fun y' hy'' => by
        have := hcomm ⟨y', hEM hy''⟩ hy''
        exact congrArg Subtype.val this) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h) hker
  exact hΨ hmem

end Injective

section ModelHom

variable {n m k size : ℕ} {g : Array Table} {ws : List (List (Fin k × Bool))}

theorem lift_mem_modelGroup (n k : ℕ) (g : Array Table) (w : List (Fin k × Bool)) :
    FreeGroup.lift (modelGens n k g) (FreeGroup.mk w) ∈ modelGroup n k g := by
  have h : FreeGroup.lift (modelGens n k g) (FreeGroup.mk w) ∈
      (FreeGroup.lift (modelGens n k g)).range := ⟨_, rfl⟩
  rw [FreeGroup.range_lift_eq_closure] at h
  exact h

@[expose] noncomputable def modelHomOf (hn : n < 2 ^ 32) (hk : g.size = k)
    (h : ModelOK n m k g ws size) {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) : ↥(modelGroup n k g) →* H :=
  (presHom ws x hx).comp
    (presEquiv ws (modelGens n k g) (modelCheck_spec hn hk h).1.rel (modelCheck_spec hn hk h).1.fin
      ((modelCheck_spec hn hk h).1.card_pg.trans
        (le_of_eq (modelCheck_spec hn hk h).1.card_group.symm))).symm.toMonoidHom

theorem modelHomOf_lift (hn : n < 2 ^ 32) (hk : g.size = k)
    (h : ModelOK n m k g ws size) {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) (w : List (Fin k × Bool)) :
    modelHomOf hn hk h x hx
      ⟨FreeGroup.lift (modelGens n k g) (FreeGroup.mk w), lift_mem_modelGroup n k g w⟩ =
      FreeGroup.lift x (FreeGroup.mk w) := by
  have hs := (modelCheck_spec hn hk h).1
  have hle : Nat.card (PG k ws) ≤ Nat.card (closure (Set.range (modelGens n k g))) :=
    hs.card_pg.trans (le_of_eq hs.card_group.symm)
  have : (⟨FreeGroup.lift (modelGens n k g) (FreeGroup.mk w), lift_mem_modelGroup n k g w⟩ :
      ↥(modelGroup n k g)) =
      presEquiv ws (modelGens n k g) hs.rel hs.fin hle (PresentedGroup.mk _ (FreeGroup.mk w)) :=
    Subtype.ext (presEquiv_mk ws (modelGens n k g) hs.rel hs.fin hle w).symm
  unfold modelHomOf
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [this, MulEquiv.symm_apply_apply, presHom_mk]

theorem modelT_eq_of_lift_eq (hn : n < 2 ^ 32) (hk : g.size = k)
    (h : ModelOK n m k g ws size) {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (hinj : Function.Injective (modelHomOf hn hk h x hx)) {w₁ w₂ : List (Fin k × Bool)}
    (hw : FreeGroup.lift x (FreeGroup.mk w₁) = FreeGroup.lift x (FreeGroup.mk w₂)) :
    tblEq n (modelT n k g w₁) (modelT n k g w₂) = true := by
  rw [← modelHomOf_lift hn hk h x hx w₁, ← modelHomOf_lift hn hk h x hx w₂] at hw
  have := congrArg Subtype.val (hinj hw)
  exact (tblEq_iff_eq (rep_modelT hn hk h w₁) (rep_modelT hn hk h w₂)).2 this

theorem modelHomOf_injective (hn : n < 2 ^ 32) (hk : g.size = k)
    (h : ModelOK n m k g ws size) {gE : Array Table} {sizeE j : ℕ} {cT : Table}
    (hnc : normCenCheck n m g gE size sizeE cT = true) (hj : sizeE = 2 ^ j) {H : Type*} [Group H]
    (x : Fin k → H) (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (w : List (Fin k × Bool)) (hw : tblEq n (modelT n k g w) cT = true)
    (hx1 : FreeGroup.lift x (FreeGroup.mk w) ≠ 1) :
    Function.Injective (modelHomOf hn hk h x hx) := by
  obtain ⟨hle, -, hcardE, hnorm, hcen, hz, hcTrep, hcTE⟩ := normCenCheck_spec hn hnc
  have hMeq : modelGroup n k g = closure (tp n '' {x | x ∈ g}) := by
    show closure (Set.range (modelGens n k g)) = _
    rw [range_modelGens hk]
  have hEM : closure (tp n '' {x | x ∈ gE}) ≤ modelGroup n k g := hle.trans (le_of_eq hMeq.symm)
  have hz_eq : tp n cT = FreeGroup.lift (modelGens n k g) (FreeGroup.mk w) :=
    ((tblEq_iff_eq (rep_modelT hn hk h w) hcTrep).1 hw).symm
  have hΨ : modelHomOf hn hk h x hx ⟨tp n cT, hEM hcTE⟩ ≠ 1 := by
    have : (⟨tp n cT, hEM hcTE⟩ : ↥(modelGroup n k g)) =
        ⟨FreeGroup.lift (modelGens n k g) (FreeGroup.mk w), lift_mem_modelGroup n k g w⟩ :=
      Subtype.ext hz_eq
    rw [this, modelHomOf_lift]
    exact hx1
  exact injective_of_selfCentralizing (modelGroup n k g) (closure (tp n '' {x | x ∈ gE})) hEM
    (fun x hx' y hy => hnorm x (hMeq ▸ hx') y hy)
    (IsPGroup.of_card (n := j) (hcardE.trans hj))
    (fun x hx' hc => hcen x (hMeq ▸ hx') hc) hcTE hz _ hΨ

end ModelHom

end CFSG.EvenSporadicStandard.M12Std.Yosh
