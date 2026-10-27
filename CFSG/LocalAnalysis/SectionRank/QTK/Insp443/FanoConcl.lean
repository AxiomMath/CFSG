module

public import CFSG.Quasithin.Vol2.Ch7Fano
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Vol2.KGFactC31E8

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Fano CFSG.Blueprint
  CFSG.QuasithinUnique CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

theorem fanoPermAct_mem_fanoCore (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {f : PMod}
    (hf : f ∈ fanoCore) : fanoPermAct g f ∈ fanoCore := by
  rw [mem_fanoCore] at hf ⊢
  let e : FanoPoint ≃ FanoPoint :=
    ⟨fanoPointAct g⁻¹, fanoPointAct g,
      fun p => by rw [← fanoPointAct_mul, mul_inv_cancel, fanoPointAct_one],
      fun p => by rw [← fanoPointAct_mul, inv_mul_cancel, fanoPointAct_one]⟩
  simp only [fanoPermAct_apply]
  rw [show (∑ p, Multiplicative.toAdd f (fanoPointAct g⁻¹ p)) =
    ∑ p, Multiplicative.toAdd f (e p) from rfl, Equiv.sum_comp e (fun p => Multiplicative.toAdd f p)]
  exact hf

theorem realizes_of_equiv_sec {G : Type} [Group G] {A W : Subgroup G} [IsMulCommutative ↥W]
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (D : FFModel)
    (hker0 : ∀ x, x ∈ D.ker ↔ x = 1) (hsec : ∀ γ m, m ∈ D.sec → D.act γ m ∈ D.sec)
    (hact1 : ∀ γ, D.act γ 1 = 1) (α : ↥A →* D.Gam) (hα : Function.Surjective α)
    (hker : ∀ a : ↥A, α a = 1 → (a : G) ∈ Subgroup.centralizer (W : Set G))
    (f : ↥W ≃* ↥D.sec)
    (hf : ∀ (a : ↥A) (w w' : ↥W), (w' : G) = a * w * (a : G)⁻¹ →
      ((f w' : ↥D.sec) : D.Amb) = D.act (α a) (f w)) :
    D.Realizes (autOn A W) ⊤ ⊥ := by
  set ρ := T4213N.rhoAut hAW with hρ
  have hle : α.ker ≤ ρ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    apply Subtype.ext
    exact InternalSec.conjAct_eq_one_of_mem_centralizer _ (hker a ha)
  set e := QuotientGroup.quotientKerEquivOfSurjective α hα with he
  set π : D.Gam →* ↥(autOn A W) :=
    (QuotientGroup.lift α.ker ρ hle).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ a : ↥A, π (α a) = ρ a := by
    intro a
    have h1 : e.symm (α a) = (a : ↥A ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro χ
    obtain ⟨a, rfl⟩ := T4213N.rhoAut_surjective hAW χ
    exact ⟨α a, hπα a⟩
  set β : ↥(⊤ : Subgroup ↥W) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
      (f.toMonoidHom.comp (⊤ : Subgroup ↥W).subtype) with hβ
  have hβapp : ∀ u : ↥(⊤ : Subgroup ↥W),
      β u = (QuotientGroup.mk (f (u : ↥W)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) := fun _ => rfl
  have hmk : ∀ x y : ↥D.sec, (QuotientGroup.mk x : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
      QuotientGroup.mk y ↔ x = y := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hker0,
      inv_mul_eq_one]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  refine ⟨π, hπs, bot_le, fun x hx => by rw [(hker0 x).mp hx]; exact D.sec.one_mem,
    fun _ _ _ => trivial, ?_, fun γ m hm => hsec γ m hm, ?_, β, ?_, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ x hx
    rw [hker0] at hx ⊢
    rw [hx, hact1]
  · intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (D.ker.subgroupOf D.sec) y
    refine ⟨⟨f.symm y, trivial⟩, ?_⟩
    rw [hβapp, QuotientGroup.mk'_apply, MulEquiv.apply_symm_apply]
  · intro u
    rw [hβapp, Subgroup.mem_bot]
    have h1 : (QuotientGroup.mk (f (u : ↥W)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔
        f (u : ↥W) = 1 := by
      rw [show (1 : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk 1 from rfl, hmk]
    rw [h1, MulEquiv.map_eq_one_iff]
  · intro γ u m hu hm hum
    obtain ⟨a, rfl⟩ := hα γ
    rw [hβapp] at hum
    have hfu : f (u : ↥W) = m := (hmk _ _).mp hum
    rw [hβapp]
    apply (hmk _ _).mpr
    apply Subtype.ext
    show ((f (((π (α a) : ↥(autOn A W)) : MulAut ↥W) (u : ↥W)) : ↥D.sec) : D.Amb) =
      D.act (α a) (m : D.Amb)
    rw [← hfu]
    apply hf a (u : ↥W)
    rw [hπα, T4213N.rhoAut_apply]

@[expose] noncomputable def invTr : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun g := ⟨((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, by rw [Matrix.det_transpose]; exact (g⁻¹).2⟩
  map_one' := by
    apply Subtype.ext
    show (((1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = 1
    rw [inv_one]
    exact Matrix.transpose_one
  map_mul' g h := by
    apply Subtype.ext
    show (((g * h)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
          ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem coe_invTr (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((invTr g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ :=
  rfl

theorem invTr_injective : Function.Injective invTr := by
  intro g h hgh
  have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
        ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ :=
    congrArg Subtype.val hgh
  exact inv_injective (Subtype.ext (Matrix.transpose_inj.mp h1))

theorem invTr_surjective : Function.Surjective invTr :=
  Finite.injective_iff_surjective.mp invTr_injective

theorem KConfig.conclK_of_fanoEquiv {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hsurj : Function.Surjective α) (hker : CFSG.pCore 2 ↥L = α.ker)
    (hC : ∀ l : ↥L, α l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (f : ↥V ≃* ↥fanoCore)
    (hf : ∀ (l : ↥L) (w w' : ↥V), (w' : G) = l * w * (l : G)⁻¹ →
      ((f w' : ↥fanoCore) : PMod) = fanoPermAct (α l) (f w)) :
    ConclK G L V MK := by
  unfold ConclK
  letI : IsMulCommutative ↥V := h.elemAbelian.1
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)).trans
        (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).symm
  have hpsl : IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := E8.isPSL_of_equiv3 eQ
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) := Or.inr (Or.inl hLM)
  refine Or.inl ⟨hq, hshape, Or.inr (Or.inr ⟨hLM, h.elemAbelian.1, ?_⟩)⟩
  exact realizes_of_equiv_sec h.le_normalizer fanoCoreModel (fun x => Subgroup.mem_bot)
    (fun γ m hm => fanoPermAct_mem_fanoCore γ hm) (fun _ => rfl) α hsurj hC f hf

end CFSG.SectionRank.QTK.Insp443

end
