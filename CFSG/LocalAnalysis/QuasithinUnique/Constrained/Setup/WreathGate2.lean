module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate1
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathSolvable

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

structure GateHyp {H : Type*} [Group H] (R M V : Subgroup H) : Prop where
  sylow : IsSylowTwoOf R (⊤ : Subgroup H)
  nonnormal : ¬ R.Normal
  le_M : R ≤ M
  M_lt : M < ⊤
  M_max : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M
  J_not_le_centralizer : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set H)
  reduced : IsTwoReducedIn (⊤ : Subgroup H) V
  not_top_le : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H)
  solvable : Group.IsSolvable ↥(autOn (⊤ : Subgroup H) V)

section Finite

variable {H : Type} [Group H] [Finite H] {R M V : Subgroup H}

namespace GateHyp

variable (g : GateHyp R M V)

include g

omit [Finite H] in
theorem V_normal : V.Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp g.reduced.2.1)

omit [Finite H] in
theorem V_elem : CFSG.Open.IsElemAbelian 2 V := g.reduced.2.2.1

omit [Finite H] in
theorem not_top_le_normalizer : ¬ (⊤ : Subgroup H) ≤ Subgroup.normalizer (R : Set H) := fun h =>
  g.nonnormal (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h))

omit [Finite H] in
theorem V_le_R : V ≤ R := by
  have hn : (V.subgroupOf (⊤ : Subgroup H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr g.reduced.2.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using g.V_elem.2 _ x.2)⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 V ⊤ le_top hn
    hV2).trans g.sylow.pCoreOf_le

theorem frattini :
    ⊤ = oddOrderSubgroup (⊤ : Subgroup H) ⊔ R ∧
      HasNoTwoQuotient (oddOrderSubgroup (⊤ : Subgroup H)) ∧
      (⊤ : Subgroup H) ⊓ Subgroup.centralizer (V : Set H) ≤ M ∧
      R ⊓ Subgroup.centralizer (V : Set H) = CFSG.Open.pCoreOf 2 (⊤ : Subgroup H) ∧
      ∀ A : Subgroup H, A ≤ R → R ≤ Subgroup.normalizer (A : Set H) →
        (⁅oddOrderSubgroup (⊤ : Subgroup H), A⁆ < oddOrderSubgroup (⊤ : Subgroup H) ↔
          A ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup H)) ∧
        (A ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup H) ↔ A ≤ Subgroup.centralizer (V : Set H)) :=
  reduced_detects_commutator g.sylow g.not_top_le_normalizer g.le_M g.M_lt g.M_max g.reduced
    g.not_top_le

theorem exists_offender : ∃ A : Subgroup H, IsReducedOffender R V A := by
  have hJC : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set H) := g.J_not_le_centralizer
  obtain ⟨A, hAS, hAc⟩ : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (V : Set H) := by
    by_contra hno
    push Not at hno
    exact hJC (iSup₂_le fun A hA => hno A hA)
  exact ⟨A, hAS, hAc, inf_centralizer_eq_of_isMaxElemAbelian g.V_elem g.V_le_R hAS,
    card_le_relIndex_mul_card g.V_elem g.V_le_R hAS⟩

end GateHyp

theorem GateHyp.of_noChar (sylow : IsSylowTwoOf R (⊤ : Subgroup H)) (nonnormal : ¬ R.Normal)
    (le_M : R ≤ M) (M_lt : M < ⊤) (M_max : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M)
    (noChar : NoCharNormal R ⊤) (reduced : IsTwoReducedIn (⊤ : Subgroup H) V)
    (not_top_le : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H))
    (solvable : Group.IsSolvable ↥(autOn (⊤ : Subgroup H) V)) : GateHyp R M V := by
  refine ⟨sylow, nonnormal, le_M, M_lt, M_max, ?_, reduced, not_top_le, solvable⟩
  have hS2 : IsPGroup 2 R := sylow.isPGroup
  have hR1 : R ≠ ⊥ := fun hb => nonnormal (by rw [hb]; exact Subgroup.normal_bot)
  have hJne : thompsonJ R ≠ ⊥ := thompsonJ_ne_bot hS2 hR1
  have hJR : thompsonJ R ≤ R := B6.thompsonJ_le R
  have hQS : CFSG.Open.pCoreOf 2 (⊤ : Subgroup H) ≤ R := sylow.pCoreOf_le
  have hSJn : R ≤ Subgroup.normalizer (thompsonJ R : Set H) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ R)
  have hJQ : ¬ thompsonJ R ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup H) := by
    intro hJQ
    have heq : thompsonJ R = thompsonJ (CFSG.Open.pCoreOf 2 (⊤ : Subgroup H)) := by
      rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
      exact thompsonJi_eq_of_le (pRank_pos hS2 hR1)
        (by rwa [← thompsonJ_eq_thompsonJi_zero]) hQS
    refine noChar _ hJR hJne (characteristic_thompsonJ R) ?_
    rw [heq]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤).trans
      (normalizer_le_normalizer_thompsonJ _)
  have hnn : ¬ (⊤ : Subgroup H) ≤ Subgroup.normalizer (R : Set H) := fun h =>
    nonnormal (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h))
  have hJdet := (reduced_detects_commutator sylow hnn le_M M_lt M_max reduced
    not_top_le).2.2.2.2 (thompsonJ R) hJR hSJn
  exact fun hc => hJQ (hJdet.2.mpr hc)

omit [Finite H] in
theorem isElementaryAbelian_of_isElemAbelian {A : Subgroup H} (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.IsElementaryAbelian 2 ↥A := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA

section Model

variable [V.Normal] {Wm : Type} [AddCommGroup Wm] [Module (ZMod 2) Wm]

omit [Finite H] in
theorem card_fix_modelRho (θ : ↥V ≃* Multiplicative Wm) (A : Subgroup H) :
    Nat.card ↥(Offender.fixSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) (A.map (modelRho θ))) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set H)) := by
  have hfix : ∀ w : Wm,
      w ∈ Offender.fixSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) (A.map (modelRho θ)) ↔
        ∀ a ∈ A, modelRho θ a w = w := by
    intro w
    rw [Offender.mem_fixSub]
    constructor
    · intro hw a ha
      exact hw (modelRho θ a) ⟨a, ha, rfl⟩
    · rintro hw _ ⟨a, ha, rfl⟩
      exact hw a ha
  have hcomm : ∀ (a : H) (v : ↥V), modelRho θ a (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ v) ↔ a * (v : H) = (v : H) * a := by
    intro a v
    rw [modelRho_apply]
    constructor
    · intro h1
      have h2 : MulAut.conjNormal a v = v := θ.injective (Multiplicative.toAdd.injective h1)
      have h3 := congrArg (fun u : ↥V => (u : H)) h2
      simp only [MulAut.conjNormal_apply] at h3
      calc a * (v : H) = (a * v * a⁻¹) * a := by group
        _ = v * a := by rw [h3]
    · intro h1
      have h3 : a * (v : H) * a⁻¹ = (v : H) := by rw [h1]; group
      have h2 : MulAut.conjNormal a v = v :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; exact h3)
      rw [h2]
  let toV : ↥(Offender.fixSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) (A.map (modelRho θ))) →
      ↥(V ⊓ Subgroup.centralizer (A : Set H)) := fun w =>
    ⟨((θ.symm (Multiplicative.ofAdd (w : Wm)) : ↥V) : H), (θ.symm _).2, by
      show ((θ.symm (Multiplicative.ofAdd (w : Wm)) : ↥V) : H) ∈
        Subgroup.centralizer (A : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hw := (hfix w).1 w.2 a ha
      exact (hcomm a (θ.symm (Multiplicative.ofAdd (w : Wm)))).1 (by simpa using hw)⟩
  let toW : ↥(V ⊓ Subgroup.centralizer (A : Set H)) →
      ↥(Offender.fixSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) (A.map (modelRho θ))) := fun v =>
    ⟨Multiplicative.toAdd (θ ⟨(v : H), v.2.1⟩), by
      rw [hfix]
      intro a ha
      exact (hcomm a ⟨(v : H), v.2.1⟩).2 (Subgroup.mem_centralizer_iff.mp v.2.2 a ha)⟩
  exact Nat.card_congr
    { toFun := toV
      invFun := toW
      left_inv := fun w => Subtype.ext (by simp [toV, toW])
      right_inv := fun v => Subtype.ext (by simp [toV, toW]) }

end Model

section Node10

variable [V.Normal] {Wm : Type} [AddCommGroup Wm] [Module (ZMod 2) Wm] [Finite Wm]

theorem GateHyp.S3Wreath_model (g : GateHyp R M V) (θ : ↥V ≃* Multiplicative Wm) :
    S3Wreath ((⊤ : Subgroup H).map (modelRho θ)) (R.map (modelRho θ))
      ((CFSG.fittingSubgroup ↥((⊤ : Subgroup H).map (modelRho θ))).map
        ((⊤ : Subgroup H).map (modelRho θ)).subtype) := by
  classical
  have hP : (⊤ : Subgroup H) ≤ Subgroup.normalizer (V : Set H) := g.reduced.2.1
  set ψ := Layer.binPsi θ with hψ
  have hmap : ∀ X : Subgroup H, X.map (modelRho θ) = (autOn X V).map ψ.toMonoidHom :=
    fun X => map_modelRho θ X
  obtain ⟨-, -, hCX, hTC, -⟩ := g.frattini
  have hΛ : CFSG.Open.pCoreOf 2 (autOn (⊤ : Subgroup H) V) = ⊥ := pCoreOf_autOn_eq_bot g.reduced
  have hsyl : IsSylowTwoOf (autOn R V) (autOn (⊤ : Subgroup H) V) :=
    isSylowTwoOf_autOn g.sylow hP
  have hnnΛ : ¬ ((autOn R V).subgroupOf (autOn (⊤ : Subgroup H) V)).Normal :=
    not_normal_autOn g.sylow hP hΛ hTC g.not_top_le_normalizer
  have hmaxΛ := autOn_max hP g.le_M g.M_lt g.M_max hCX g.sylow.1
  have hRΛ : autOn R V ≤ autOn (⊤ : Subgroup H) V := autOn_le_autOn V le_top
  obtain ⟨A, hoff⟩ := g.exists_offender
  have hsolv : Group.IsSolvable ↥((⊤ : Subgroup H).map (modelRho θ)) := by
    rw [hmap]
    exact (Layer.solvable_map_mulEquiv_iff ψ).2 g.solvable
  have hO2 : ∀ N : Subgroup (Wm ≃ₗ[ZMod 2] Wm), N ≤ (⊤ : Subgroup H).map (modelRho θ) →
      (N.subgroupOf ((⊤ : Subgroup H).map (modelRho θ))).Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hNn hNp
    rw [hmap ⊤] at hN hNn
    have hNN₀ : (N.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = N := Layer.map_map_symm ψ N
    have hN₀le : N.map ψ.symm.toMonoidHom ≤ autOn (⊤ : Subgroup H) V := by
      rw [← Subgroup.map_le_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hNN₀]
      exact hN
    have hN₀n : ((N.map ψ.symm.toMonoidHom).subgroupOf (autOn (⊤ : Subgroup H) V)).Normal := by
      refine (Layer.normal_subgroupOf_map_iff ψ hN₀le).1 ?_
      rw [hNN₀]
      exact hNn
    have hN₀p : IsPGroup 2 ↥(N.map ψ.symm.toMonoidHom) := hNp.map ψ.symm.toMonoidHom
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (N.map ψ.symm.toMonoidHom) (autOn (⊤ : Subgroup H) V) hN₀le hN₀n hN₀p
    rw [hΛ] at hle
    have h0 : N.map ψ.symm.toMonoidHom = ⊥ := le_bot_iff.1 hle
    rw [← hNN₀, h0, Subgroup.map_bot]
  have hT : IsSylowTwoOf (R.map (modelRho θ)) ((⊤ : Subgroup H).map (modelRho θ)) := by
    rw [hmap ⊤, hmap R]
    exact (Layer.isSylowTwoOf_map_mulEquiv ψ).2 hsyl
  have hTn : ¬ ((R.map (modelRho θ)).subgroupOf ((⊤ : Subgroup H).map (modelRho θ))).Normal := by
    rw [hmap ⊤, hmap R]
    intro hn
    exact hnnΛ ((Layer.normal_subgroupOf_map_iff ψ hRΛ).1 hn)
  have hTM : R.map (modelRho θ) ≤ M.map (modelRho θ) := by
    rw [hmap R, hmap M]
    exact Subgroup.map_mono hmaxΛ.1
  have hMH : M.map (modelRho θ) < (⊤ : Subgroup H).map (modelRho θ) := by
    rw [hmap M, hmap ⊤]
    exact (Subgroup.map_lt_map_iff_of_injective ψ.injective).2 hmaxΛ.2.1
  have hmax : ∀ Y : Subgroup (Wm ≃ₗ[ZMod 2] Wm), R.map (modelRho θ) ≤ Y →
      Y < (⊤ : Subgroup H).map (modelRho θ) → Y ≤ M.map (modelRho θ) := by
    intro X' hSX' hX'Λ
    rw [hmap R] at hSX'
    rw [hmap ⊤] at hX'Λ
    rw [hmap M]
    have hXX' : (X'.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = X' := Layer.map_map_symm ψ X'
    have h1 : autOn R V ≤ X'.map ψ.symm.toMonoidHom := by
      rw [← Subgroup.map_le_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hXX']
      exact hSX'
    have h2 : X'.map ψ.symm.toMonoidHom < autOn (⊤ : Subgroup H) V := by
      rw [← Subgroup.map_lt_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hXX']
      exact hX'Λ
    have h3 := hmaxΛ.2.2 _ h1 h2
    rw [← hXX']
    exact Subgroup.map_mono h3
  have hAR : A ≤ R := hoff.1.1
  have hEne : A.map (modelRho θ) ≠ ⊥ := by
    intro hbot
    apply hoff.2.1
    have : A ≤ (modelRho θ).ker := (Subgroup.map_eq_bot_iff _).1 hbot
    rwa [ker_modelRho] at this
  have hEel : CFSG.IsElementaryAbelian 2 ↥(A.map (modelRho θ)) := by
    have := isElementaryAbelian_of_isElemAbelian hoff.1.2.1
    exact Layer.isElementaryAbelian_map (modelRho θ) A
  have hcardA : Nat.card ↥(A.map (modelRho θ)) =
      (A ⊓ Subgroup.centralizer (V : Set H)).relIndex A := by
    have h1 := card_map_mul_card_inf_ker (modelRho θ) A
    rw [ker_modelRho] at h1
    have h2 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set H)) A
    rw [inf_of_le_left inf_le_left] at h2
    have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set H)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hcardW : Nat.card Wm = Nat.card ↥V :=
    (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have hEoff : Nat.card Wm ≤ Offender.weight (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm))
      (A.map (modelRho θ)) := by
    show Nat.card Wm ≤ Nat.card ↥(A.map (modelRho θ)) *
      Nat.card ↥(Offender.fixSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) (A.map (modelRho θ)))
    rw [hcardA, card_fix_modelRho, hcardW]
    exact hoff.2.2.2
  exact solvable_minimal_parabolic_S3_wreath (T := R.map (modelRho θ)) (M := M.map (modelRho θ))
    (E := A.map (modelRho θ)) hsolv hO2 hT hTn hTM hMH hmax (Subgroup.map_mono le_top) hEne hEel
    hEoff

end Node10

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
