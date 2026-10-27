module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318D

public section
namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem le_normalizer_of_h14_F4 (h14 : Stmt3_3_14_F4) {T M L D : Subgroup G} (h : Hyp331 G T M L D) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  h.TM.trans (h14 G T M L D h).2

theorem exists_data_F4 (h14 : Stmt3_3_14_F4) (hGA : CFSG.Open.GriessAllModelsStatement)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin n) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] {k : ℕ} (hk : 1 ≤ k)
    (hDS : DirectSumOfCopies (autOn L (vPlus L T)) (commVPlus L T L) ⊥
      (FFModel.nat (StatedSL n (ZMod 2))) k) :
    ∃ (α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2))
      (Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)),
      Data G T M L D n k α Φ := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hTL := le_normalizer_of_h14_F4 h14 h
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  obtain ⟨α₀, Φ₀, hα₀s, hα₀k, hΦ₀i, hΦ₀r, hΦ₀e⟩ :=
    exists_coords hLV hk hDS (Nat.card_congr e.toEquiv)
  obtain ⟨α', -, hα'k, hα'c⟩ := Ln2.exists_modO2Surj h hGA hTL hK hn4 hn5 e
  have hker₀ : α₀.ker = CFSG.pCore 2 ↥L := by
    rw [← hα'k]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα₀k, hα'c]
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hS₀ (K := ZMod 2) (by omega) hα₀s
  refine ⟨(MulAut.conj g).toMonoidHom.comp α₀,
    Φ₀.comp (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))), ⟨h, hn4, hn5, hk, hTL, ?_, ?_, fun l => ?_, hg, ?_, ?_,
    coords_conj hΦ₀e g⟩⟩
  · rw [MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hα₀s
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hker₀]
  · rw [← hα₀k]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · have hinj : Function.Injective (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) := by
      intro c d hcd
      have := congrArg (vecAct k ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) hcd
      rwa [← vecAct_mul, ← vecAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, vecAct_one, vecAct_one] at this
    exact hΦ₀i.comp hinj
  · have hsurj : Function.Surjective (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) := by
      intro c
      refine ⟨vecAct k ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) c, ?_⟩
      rw [← vecAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, vecAct_one]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map, hΦ₀r]

end CFSG.Quasithin.H13.L3318
