module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LieType.SeitzGeneration.SpPlaneThreeF2Exceptional
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d

open CFSG.Open (StatedSp StatedScalars StatedProj IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped Matrix

section SpModel

variable {n : ℕ} {F : Type} [Field F]

theorem statedScalars_subgroupOf_sp [CharP F 2] (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨u, hu⟩ := hx
  have hx2 := SymplecticTorusWeyl.mem_statedSp_iff.1 x.2
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hx2
  have hJ := congrFun (congrFun hx2 (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.fromBlocks] at hJ
  have hu1 : (u : F) = 1 := by
    have h2 : ((u : F) - 1) ^ 2 = 0 := by
      have h3 : ((u : F) - 1) ^ 2 = (u : F) * u - 1 - 2 * (u : F) + 2 := by ring
      rw [h3, hJ, CharTwo.two_eq_zero]
      ring
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, show u = 1 from Units.ext hu1, map_one, OneMemClass.coe_one]

noncomputable def projEquivSp [CharP F 2] (hn : 1 ≤ n) :
    StatedProj (StatedSp n F) ≃* ↥(StatedSp n F) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_sp hn)).trans QuotientGroup.quotientBot

theorem nonempty_typeBGroupEquiv_spTwo (hn : 3 ≤ n) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.B n q, hv⟩ ≃* ↥(StatedSp n (ZMod 2))) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B n q, hv⟩
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) = 2 ^ 1 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic ⟨.B n q, hv⟩ = q.p from
        TauCeti.LieTypeIndex.characteristic_B n q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B n q, hv⟩ = q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_B n q, hp, he]
  let φ : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨(CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hp hn).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ n)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans (projEquivSp (by omega)))⟩

theorem all_inner_spTwo (hn : 3 ≤ n) (α : MulAut ↥(StatedSp n (ZMod 2))) :
    ∃ g : ↥(StatedSp n (ZMod 2)), α = MulAut.conj g := by
  have key : ∀ β : MulAut (StatedProj (StatedSp n (ZMod 2))),
      ∃ g : StatedProj (StatedSp n (ZMod 2)), β = MulAut.conj g := by
    intro β
    obtain ⟨-, hform⟩ := automorphism_generation (K := ZMod 2) (r := n) hn
    obtain ⟨A, σ, hβ⟩ := hform β
    have hσ : fieldAut n (ZMod 2) σ = 1 := by
      rw [show σ = 1 from Subsingleton.elim _ _, map_one]
    have hA : (A : GL (Fin n ⊕ Fin n) (ZMod 2)) ∈ StatedSp n (ZMod 2) := by
      obtain ⟨μ, hμ⟩ := A.2
      have hμ1 : μ = 1 := Subsingleton.elim _ _
      subst hμ1
      rw [Units.val_one, one_smul] at hμ
      exact SymplecticTorusWeyl.mem_statedSp_iff.2 hμ
    refine ⟨SymplecticFlag.proj n (ZMod 2) ⟨A, hA⟩, ?_⟩
    rw [hβ, hσ, mul_one, ← conjAut_statedSp]
  have hn1 : 1 ≤ n := by omega
  obtain ⟨g, hg⟩ := key (MulAut.congr (projEquivSp (F := ZMod 2) hn1).symm α)
  refine ⟨projEquivSp hn1 g, ?_⟩
  have h1 : MulAut.congr (projEquivSp (F := ZMod 2) hn1)
      (MulAut.congr (projEquivSp (F := ZMod 2) hn1).symm α) = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [← h1, hg, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]

end SpModel

theorem isElemAbelian_comap_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {A : Subgroup H} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  · rw [map_pow, map_one]
    exact hA.2 _ hx

section HyperplaneFix

variable {F : Type} [Field F]

@[expose] noncomputable def vecAct (ι K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] :
    GL ι K →* MulAut (Multiplicative (ι → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ Multiplicative.toAdd v)
      invFun := fun v => Multiplicative.ofAdd ((↑g⁻¹ : Matrix ι ι K) *ᵥ Multiplicative.toAdd v)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ofAdd_toAdd]
      right_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, ofAdd_toAdd]
      map_mul' := fun v w => by
        simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  map_one' := by
    ext v
    simp
  map_mul' := fun g h => by
    ext v
    simp [Matrix.mulVec_mulVec]

theorem exists_hyperplane_fix [Finite F] (hF3 : ¬ 3 ∣ Nat.card F) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {E : Subgroup (GL ι F)} (hE : IsElemAbelian 3 E) (hE1 : E ≠ ⊥) :
    ∃ H : Subgroup (GL ι F), H ≤ E ∧ Nat.card E = 3 * Nat.card H ∧
      ∃ v : ι → F, v ≠ 0 ∧ ∀ h ∈ H, (h : Matrix ι ι F) *ᵥ v = v := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 ↥E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hE1
  letI : MulDistribMulAction ↥E (Multiplicative (ι → F)) :=
    MulDistribMulAction.compHom _ ((vecAct ι F).comp E.subtype)
  have hcop : ¬ 3 ∣ Nat.card (Multiplicative (ι → F)) := by
    rw [show Nat.card (Multiplicative (ι → F)) = Nat.card (ι → F) from rfl, Nat.card_fun]
    exact fun h => hF3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := 3) (A := ↥E)
    (H := Multiplicative (ι → F)) hcop
  obtain ⟨B, hBi, hBne⟩ : ∃ B : Subgroup ↥E, B.index = 3 ∧
      CFSG.fixedPointSubgroup B (Multiplicative (ι → F)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Subgroup (Multiplicative (ι → F))) = ⊥ := by
      rw [← hgen]
      exact iSup₂_eq_bot.2 fun B hB => hcon B hB
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hne : (Multiplicative.ofAdd (Pi.single i 1 : ι → F)) ≠ 1 := by
      intro h
      have := congrFun (congrArg Multiplicative.toAdd h) i
      simp at this
    exact hne (Subgroup.eq_bot_iff_forall _ |>.1 htop _ (Subgroup.mem_top _))
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  refine ⟨B.map E.subtype, Subgroup.map_subtype_le B, ?_, Multiplicative.toAdd (w : Multiplicative _), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, ← hBi, Subgroup.index_mul_card]
  · intro h0
    apply hw1
    apply Subtype.ext
    show (w : Multiplicative (ι → F)) = 1
    rw [← ofAdd_toAdd (w : Multiplicative (ι → F)), h0, ofAdd_zero]
  · rintro _ ⟨b, hb, rfl⟩
    have h1 := (FixedPoints.mem_subgroup ↥B (Multiplicative (ι → F))
      (w : Multiplicative (ι → F))).1 w.2 ⟨b, hb⟩
    have h3 := congrArg Multiplicative.toAdd h1
    exact h3

end HyperplaneFix

section Plane

variable {n : ℕ}

theorem closure_centralizers_eq_top_of_fixed {E : Subgroup (StatedSp n (ZMod 2))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 9) {v : Fin n ⊕ Fin n → ZMod 2} (hv0 : v ≠ 0)
    (hEv : ∀ x ∈ E, ((x : GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ v = v) :
    Subgroup.closure {g : StatedSp n (ZMod 2) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine CFSG.LieType.SeitzGeneration.closure_centralizers_spPlane_three_F2_of_big_or_fixed
    (by rw [Nat.card_zmod]) hcomm hE.2 hEc (Or.inl fun hbot => hv0 ?_)
  have hmem : v ∈ CFSG.RankThree.PartOne.KCSpFull.spPlaneFix E := by
    rw [CFSG.RankThree.PartOne.KCSpFull.spPlaneFix, CFSG.RankThree.Classical.mem_fixSub]
    intro x _
    rw [CFSG.RankThree.PartOne.KCSpFull.spRep_apply]
    exact hEv x x.2
  rw [hbot] at hmem
  exact (Submodule.mem_bot _).1 hmem

theorem exists_plane_closure_centralizers_eq_top (hn : 1 ≤ n) {D : Subgroup (StatedSp n (ZMod 2))}
    (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 27) :
    ∃ Q : Subgroup (StatedSp n (ZMod 2)), Q ≤ D ∧ Nat.card Q = 9 ∧
      Subgroup.closure {g : StatedSp n (ZMod 2) | ∃ x ∈ Q, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  let f := (StatedSp n (ZMod 2)).subtype
  have hf : Function.Injective f := Subgroup.subtype_injective _
  have hD'el : IsElemAbelian 3 (D.map f) := CFSG.SectionRank.isElemAbelian_map hD f
  have hD'c : Nat.card (D.map f) = 27 := by rw [Subgroup.card_map_of_injective hf, hDc]
  have hD'ne : D.map f ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hD'c
    omega
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨H, hHD, hHc, v, hv0, hHv⟩ :=
    exists_hyperplane_fix (F := ZMod 2) (by rw [Nat.card_zmod]; norm_num) hD'el hD'ne
  have hHr : H ≤ f.range := hHD.trans (Subgroup.map_le_range f D)
  have hHc' : Nat.card (H.comap f) = Nat.card H := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hHr]
    rw [Subgroup.card_map_of_injective hf]
  have hQD : H.comap f ≤ D := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hHD hx
    exact hf hyx ▸ hy
  have hQc : Nat.card (H.comap f) = 9 := by
    rw [hHc']
    rw [hD'c] at hHc
    omega
  refine ⟨H.comap f, hQD, hQc, closure_centralizers_eq_top_of_fixed
    (CFSG.Open.IsElemAbelian.mono hD hQD) hQc hv0 fun x hx => hHv _ hx⟩

end Plane

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d

end
