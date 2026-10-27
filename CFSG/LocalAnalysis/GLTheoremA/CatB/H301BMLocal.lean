module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMLocalQ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1Bridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.Existence CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.Existence.Co1Bridge CFSG.HardMathSupport.Dickson.I271.TabMFive
  CFSG.Sporadic.Co1Schreier

open scoped Matrix

private theorem mem_Gvis_of_mem_cent {h : MGriess} (hh : h ∈ cent xGriess) :
    (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
  have : (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (cent xGriess).map AutO.subtype := ⟨h, hh, rfl⟩
  rwa [map_cent_xGriess] at this

private theorem le_of_quot_glaTwoLocalRank {C K : Type*} [Group C] [Group K] [Finite K]
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup C} [N.Normal] (hN : IsPGroup 2 N)
    (hrk : GLATwoLocalRank p K < r) (e : C ⧸ N ≃* K) {F T : Subgroup C}
    (hF : IsElemAbelian p F) (hFc : Nat.card F = p ^ r) (hT : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set C)) : T ≤ N := by
  obtain ⟨hFπ, hFπc⟩ := H1017.H1016M5.isElemAbelian_card_map_quot hp hp2 hN e hF
  have hbot : T.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) = ⊥ :=
    Classical.byContradiction fun hT1 => absurd hrk (not_lt.2
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
        hp.one_lt hT1 (hT.map _) hFπ
        ((Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map _)) (hFπc.trans hFc)))
  intro t ht
  have h0 : e (QuotientGroup.mk t) = 1 :=
    MonoidHom.mem_ker.1 ((Subgroup.map_eq_bot_iff _).1 hbot ht)
  rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h0


private theorem card_pCore_inf_le_fixQ (H : Subgroup (cent xGriess)) (P : cent xGriess → Pvis)
    (hP : ∀ h, thetaEquiv (P h) = (((h : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) :
    Nat.card ↥(CFSG.pCore 2 (cent xGriess) ⊓ Subgroup.centralizer (H : Set (cent xGriess))) ≤
      Nat.card {r : Q // ∀ h ∈ H, conjQ (P h) r = r} := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; norm_num)
  have key : ∀ y : ↥(CFSG.pCore 2 (cent xGriess) ⊓ Subgroup.centralizer (H : Set (cent xGriess))),
      ∃ r : Q, rhoEquiv r = (((y.1 : cent xGriess) : MGriess) : AutO) ∧
        ∀ h ∈ H, conjQ (P h) r = r := by
    intro y
    obtain ⟨r, hr⟩ := exists_rho_of_mem_pCore (Subgroup.mem_inf.1 y.2).1
    refine ⟨r, hr, fun h hh => ?_⟩
    have hc : (y.1 : cent xGriess) * h = h * y.1 :=
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 h hh).symm
    have hc' : (((y.1 : cent xGriess) : MGriess) : AutO).1 * (((h : MGriess) : AutO)).1 =
        (((h : MGriess) : AutO)).1 * (((y.1 : cent xGriess) : MGriess) : AutO).1 :=
      congrArg (fun z : cent xGriess => (((z : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) hc
    apply rhoEquiv_injective
    rw [← thetaEquiv_conj_rhoEquiv (P h) r, hP h, hr]
    rw [← hc', mul_inv_cancel_right]
  refine Nat.card_le_card_of_injective
    (fun y => ⟨Classical.choose (key y), (Classical.choose_spec (key y)).2⟩) ?_
  intro y y' hyy
  have h1 := (Classical.choose_spec (key y)).1
  have h2 := (Classical.choose_spec (key y')).1
  have h3 : Classical.choose (key y) = Classical.choose (key y') := congrArg Subtype.val hyy
  rw [h3] at h1
  exact Subtype.ext (Subtype.ext (Subtype.ext (h1.symm.trans h2)))

private theorem natCard_fixL2_eq (H : Subgroup (cent xGriess)) (P : cent xGriess → Pvis)
    (hP : ∀ h, thetaEquiv (P h) = (((h : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) :
    Nat.card {v : L2 // ∀ h ∈ H, modTwoEnd (P h).1.2 v = v} =
      Nat.card {v : Fin 24 → ZMod 2 // ∀ h ∈ H,
        (((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) :
          Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} := by
  have hv : ∀ h : cent xGriess, ∀ v : L2, modTwoEnd (P h).1.2 v =
      Co1Bridge.theta ((((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ Co1Bridge.theta.symm v) := by
    intro h v
    have h1 := conjHom_apply ((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) v
    rw [conjHom_cosetEquivJ24 h (P h) (hP h)] at h1
    exact h1
  refine Nat.card_congr (Equiv.subtypeEquiv Co1Bridge.theta.symm.toEquiv fun v => ?_)
  show (∀ h ∈ H, modTwoEnd (P h).1.2 v = v) ↔ ∀ h ∈ H,
    (((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ Co1Bridge.theta.symm v = Co1Bridge.theta.symm v
  refine forall₂_congr fun h _ => ?_
  rw [hv h v]
  constructor
  · intro h'
    have := congrArg Co1Bridge.theta.symm h'
    rwa [LinearEquiv.symm_apply_apply] at this
  · intro h'
    rw [h', LinearEquiv.apply_symm_apply]

theorem card_pCore_inf_centralizer_le (H : Subgroup (cent xGriess)) :
    Nat.card ↥(CFSG.pCore 2 (cent xGriess) ⊓ Subgroup.centralizer (H : Set (cent xGriess))) ≤
      2 * Nat.card {v : Fin 24 → ZMod 2 // ∀ h ∈ H,
        (((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) :
          Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} := by
  choose P hP using fun h : cent xGriess => mem_Gvis.1 (mem_Gvis_of_mem_cent h.2)
  exact ((card_pCore_inf_le_fixQ H P hP).trans (card_fixed_conjQ_family_le (· ∈ H) P)).trans_eq
    (congrArg (2 * ·) (natCard_fixL2_eq H P hP))

theorem le_pCore_of_normalizer {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrk : GLATwoLocalRank p ↥GA < r) {F T : Subgroup (cent xGriess)} (hF : IsElemAbelian p F)
    (hFc : Nat.card F = p ^ r) (hT : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set (cent xGriess))) :
    T ≤ CFSG.pCore 2 (cent xGriess) :=
  le_of_quot_glaTwoLocalRank (Fact.out : p.Prime) hp2 CFSG.pCore_isPGroup hrk
    (cosetEquivJ24.trans (MulEquiv.subgroupCongr J24_eq_GA)) hF hFc hT hFT

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
