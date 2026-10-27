module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Invariance

theorem isChevSimple_of_mulEquiv {p : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsChevSimple p S) : IsChevSimple p T := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem isLTwoTwentySeven_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsLTwoTwentySeven S) : IsLTwoTwentySeven T := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hfin, hcard, ⟨e.symm.trans f⟩⟩

theorem isHatSix_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : IsHatSix S) :
    IsHatSix T := by
  obtain ⟨hperf, hcard, ⟨f⟩⟩ := h
  have hc : (Subgroup.center S).map e.toMonoidHom = Subgroup.center T := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr (Subgroup.center S) (Subgroup.center T) e hc).symm.trans f⟩⟩
  · have h1 := map_commutator_eq S e.toMonoidHom
    have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
    rw [hperf, hr, ← _root_.commutator_def] at h1
    rw [← h1, ← MonoidHom.range_eq_map, hr]
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact hcard

end Invariance

section PQuot

variable {G G' : Type} [Group G] [Group G']

@[expose] noncomputable def pQuotEquiv (p : ℕ) {L : Subgroup G} {L' : Subgroup G'}
    (e : ↥L ≃* ↥L') : PQuot p L ≃* PQuot p L' :=
  QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso p e)

@[expose] noncomputable def pSimpleEquiv (p : ℕ) {L : Subgroup G} {L' : Subgroup G'}
    (e : ↥L ≃* ↥L') : PSimple p L ≃* PSimple p L' :=
  QuotientGroup.congr _ _ (pQuotEquiv p e) (Subgroup.map_center_eq (pQuotEquiv p e))

theorem pQuotEquiv_mk (p : ℕ) {L : Subgroup G} {L' : Subgroup G'} (e : ↥L ≃* ↥L') (x : ↥L) :
    pQuotEquiv p e (QuotientGroup.mk x) = QuotientGroup.mk (e x) :=
  QuotientGroup.congr_mk _ _ e (glaPPrimeCore_map_iso p e) x

end PQuot

section Bar

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def pSimpleBarEquiv {p : ℕ} (hp : p.Prime) {C J : Subgroup X}
    (hJC : J ≤ C) (hsn : IsSubnormal J C) :
    PSimple p J ≃* (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J)) :=
  QuotientGroup.congr _ _ (quotEquivBarX hp hJC hsn)
    (Subgroup.map_center_eq (quotEquivBarX hp hJC hsn))

end Bar

section Fix

theorem fixSubgroup_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_fixSubgroup] at hy
    have h2 : e (α (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h3 := congrArg e.symm h2
    simpa using h3
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup] at hx
    rw [mem_fixSubgroup]
    show e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]

variable {X : Type} [Group X]

theorem fixSubgroup_normalizerMonoidHom {K : Subgroup X} {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    fixSubgroup (K.normalizerMonoidHom ⟨a, haN⟩) =
      (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨y.2, ?_⟩
    have h1 : a * (y : X) * a⁻¹ = y := congrArg Subtype.val h
    calc (y : X) * a = (a * y * a⁻¹) * a := by rw [h1]
      _ = a * y := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    show a * (y : X) * a⁻¹ = y
    calc a * (y : X) * a⁻¹ = (y * a) * a⁻¹ := by rw [h]
      _ = y := by group

end Fix

section Comp

variable {X : Type} [Group X] [Finite X]

theorem glaPComponent_fixSubgroup {p : ℕ} (hp : p.Prime) {K J : Subgroup X} {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X))
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    GLAPComponent p (fixSubgroup (K.normalizerMonoidHom ⟨a, haN⟩)) (J.subgroupOf K) := by
  rw [fixSubgroup_normalizerMonoidHom haN]
  exact glaPComponent_subgroupOf hp inf_le_left hJ

end Comp

end CFSG.HardMathSupport.Dickson.I271
