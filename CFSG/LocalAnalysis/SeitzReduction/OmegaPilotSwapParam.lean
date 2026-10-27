module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial SwapComponentData
  HasBLift oddCoreLift swapDiagHom swapDiagHom_injective range_swapDiagHom map_subtype_map_conj)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

section Case

variable {Y : Type} [Group Y]

theorem swapCase_of_neighbourOvergroupOmega [Finite Y] {s : Y} (hs : s ^ 2 = 1) {D : Subgroup Y}
    (hDperf : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) {m f : ℕ} (h : NeighbourOvergroupOmega s D m f)
    (hrow : NeighbourRowOmega s D .swap) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ OmegaNeighbourAlternative s D Kc m f ∧
      Kc.map (MulAut.conj s).toMonoidHom ≠ Kc := by
  obtain ⟨Kc, hKc, hK⟩ := h
  obtain ⟨r, hr, hiff⟩ := neighbourRowOmega_of_alternative hKc hK
  have hrs : r = .swap := NeighbourRowOmega.unique hs hDperf hD1 hr hrow
  refine ⟨Kc, hKc, hK, fun hKt => ?_⟩
  have := hiff.2 hKt
  rw [hrs] at this
  exact absurd this (by decide)

theorem OmegaNeighbourAlternative.swap_data {s : Y} {D Kc : Subgroup Y} {m f : ℕ}
    (h : OmegaNeighbourAlternative s D Kc m f) (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc) :
    D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D) := by
  obtain ⟨hDKK, ⟨hKt', -⟩ | ⟨-, hcomm, hZ, hφ⟩⟩ := h
  · exact absurd hKt' hKt
  · exact ⟨hDKK, hcomm, hZ, hφ⟩

end Case

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_of_swapCase {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hXo : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    (hDH : D ≤ centralizer (X : Set G)) (hDL : D ≤ L) (hZD : center D = ⊥)
    (hOutD : Group.IsSolvable (Outer D)) (hSchurD : OddSchurTrivial D)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {m f : ℕ}
    (hS : ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, hK, hne⟩ := hS
  obtain ⟨hDK, hcomm, -, ⟨eK⟩⟩ := hK.swap_data hne
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hτD : π t' ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (π t') Kb Db :=
    ⟨by rw [← map_mul, ht't', map_one], hKb, hne, hcomm, hDK, hτD, hsyl⟩
  let eD' : D ≃* D.subgroupOf H := (subgroupOfEquivOfLe hDH).symm
  have hDqo : CFSG.Open.IsQuasisimple D := by
    obtain ⟨h1, h2, -⟩ := hDq
    exact ⟨h1.commutator_eq_top, h2⟩
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eD' hDqo
  have hD'Z : center (D.subgroupOf H) = ⊥ := F4Pilot.center_eq_bot_congr eD' hZD
  let eDb : D.subgroupOf H ≃* Db :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H)
      (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eKD : Kb ≃* D := eK.trans (eDb.symm.trans eD'.symm)
  have hOutK : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eKD).2.mpr hOutD
  have hSchur : OddSchurTrivial Kb := hSchurD.of_mulEquiv eKD.symm
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp hKb.1.1
  obtain ⟨hBsup, hBK⟩ :=
    LinearPilot.hasBLift_sup_conj_of_forall_odd_mem htC ht hLt htX hD hDq hXo hKp hcomm
  obtain ⟨hcH, hdH', hsH, hKhp, hπK⟩ :=
    UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOutK hBK hBsup
  set Kh := oddCoreLift Kb with hKhdef
  set η : Kh →* Kb := (MulEquiv.subgroupCongr hπK).toMonoidHom.comp (π.subgroupMap Kh) with hη
  have hηapp : ∀ x : Kh, ((η x : Kb) : H ⧸ oddCore H) = π x := fun x => rfl
  have hηsurj : Function.Surjective η :=
    (MulEquiv.subgroupCongr hπK).surjective.comp (π.subgroupMap_surjective Kh)
  have hηker : η.ker = (oddCore H).subgroupOf Kh := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h2 : π x = 1 := by rw [← hηapp, h1]; rfl
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro h1
      apply Subtype.ext
      rw [hηapp, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 h1]
      rfl
  have hηinj : Function.Injective η :=
    hSchur Kh (isPerfect_iff.mpr hKhp) η hηsurj (hηker ▸ hBK.inf_le_center)
      (hηker ▸ F4Pilot.odd_card_oddCore_subgroupOf Kh)
  have hKO : Kh ⊓ oddCore H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxO⟩
    have h1 : η ⟨x, hxK⟩ = η 1 := by
      rw [map_one]
      exact (MonoidHom.mem_ker).1 (hηker ▸ (mem_subgroupOf.2 hxO))
    exact mem_bot.2 (congrArg Subtype.val (hηinj h1))
  have hcardK : Nat.card Kh = Nat.card Kb :=
    Nat.card_congr (Equiv.ofBijective η ⟨hηinj, hηsurj⟩)
  have hdH : Kh ⊓ Kh.map (MulAut.conj t').toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← hKO]
    exact ⟨hx.1, hdH' hx⟩
  have hKct : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      (Kh.map (MulAut.conj t').toMonoidHom).map H.subtype :=
    (map_subtype_map_conj Kh t').symm
  have hc1 : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Kh.map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact F4Pilot.map_le_centralizer_map H.subtype hcH
  have hd1 : Kh.map H.subtype ⊓ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hdH, Subgroup.map_bot]
  have he1 : Kh.map H.subtype ⊔ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      centralizerPerfectCore X := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  have hDperf : ⁅D, D⁆ = D := isPerfect_iff.mp hDq.1
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  have hrange := range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (centralizerPerfectCore X ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardK, Nat.card_congr eKD.toEquiv]
  have hfix : centralizerPerfectCore X ⊓ centralizer ({t} : Set G) = D :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm
  exact E8Pilot.exists_swapParam_of_decomposition htt hc1 hd1 he1 hfix

end Lift

section Instances

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_pairTorus (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {m f' : ℕ}
    (hS : ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f' ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  obtain ⟨-, -, -, -, -, -, hDXt, -, hZD, hDm, hOutD⟩ :=
    neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht hX htX hDe
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDXt.trans inf_le_left) hDL hZD
    hOutD (SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hDm) hsyl hS

theorem exists_swapParam_minusPairTorus (hset : SeitzSetting G L) {n f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (one_le_of_five_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (one_le_of_five_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    {m f' : ℕ}
    (hS : ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f' ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hLt, hD, hDq, hXo⟩ :=
    bLift_inputs_minusPairTorus hset hKc hq hn hirr k e htC ht hX hDe
  obtain ⟨-, -, -, -, -, -, hDXt, -, hZD, hDm, hOutD⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k e htC ht hX htX hDe
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDXt.trans inf_le_left) hDL hZD
    hOutD (SeitzQ2.oddSchurTrivial_of_lieModel_POmegaMinus hDm) hsyl hS

end Instances

end CFSG.SeitzReduction.OmegaPilot
