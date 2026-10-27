module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactParabolicWCent
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactOutDerived
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenOuter
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree (wSup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace KFour

section Generic

theorem isSolvable_centralizer_of_odd_index {Q : Type} [Group Q] [Finite Q] (W : Subgroup Q)
    [W.Normal] (hodd : ¬ 2 ∣ W.index) :
    Group.IsSolvable ↥(Subgroup.centralizer (W : Set Q)) := by
  set C := Subgroup.centralizer (W : Set Q) with hCdef
  let g : ↥C →* Q ⧸ W := (QuotientGroup.mk' W).comp C.subtype
  have hW : Odd W.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hrange : Odd (Nat.card g.range) := by
    have h1 : Nat.card g.range ∣ Nat.card (Q ⧸ W) := Subgroup.card_subgroup_dvd_card _
    rw [← Subgroup.index_eq_card] at h1
    exact hW.of_dvd_nat h1
  have : Group.IsSolvable g.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hrange
  have : Group.IsSolvable ↥(W.subgroupOf C) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hb : ((b : ↥C) : Q) ∈ W := Subgroup.mem_subgroupOf.mp b.2
    have hab := Subgroup.mem_centralizer_iff.mp (a : ↥C).2 _ hb
    exact Subtype.ext (Subtype.ext hab.symm)
  refine Group.isSolvable_of_ker_le_range (W.subgroupOf C).subtype g.rangeRestrict ?_
  intro x hx
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
  have hxW : (x : Q) ∈ W := (QuotientGroup.eq_one_iff _).mp hx
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hxW⟩, rfl⟩

theorem exists_mem_parabolic_conj_eq {A : Type} [Group A] [Finite A] {Y P R : Subgroup A}
    (hOut : Group.IsSolvable (Outer ↥Y)) (hP : IsParabolicTwo Y P)
    (hRY : R ≤ Subgroup.normalizer (Y : Set A)) (hRP : R ≤ Subgroup.normalizer (P : Set A))
    (hR : ⁅R, R⁆ = R) {r : A} (hr : r ∈ R) :
    ∃ y ∈ P, ∀ w ∈ Y, r * w * r⁻¹ = y * w * y⁻¹ := by
  have := hOut
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  obtain ⟨l, hl⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (Y.normalizerMonoidHom.comp (Subgroup.inclusion hRY)) ⟨r, hr⟩
  have hconj : ∀ w ∈ Y, r * w * r⁻¹ = (l : A) * w * (l : A)⁻¹ := by
    intro w hw
    have := congrArg (fun a : MulAut ↥Y => ((a ⟨w, hw⟩ : ↥Y) : A)) hl
    simpa [MulAut.conj_apply] using this
  have hlN : (l : A) ∈ Subgroup.normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [← hconj w (hP.1 hw)]
      exact (Subgroup.mem_normalizer_iff.mp (hRP hr) w).mp hw
    · intro hw
      have hwY : w ∈ Y := by
        have h1 : (l : A)⁻¹ * ((l : A) * w * (l : A)⁻¹) * (l : A) ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem l.2) (hP.1 hw)) l.2
        simpa [mul_assoc] using h1
      exact (Subgroup.mem_normalizer_iff.mp (hRP hr) w).mpr (by rwa [← hconj w hwY] at hw)
  have hlP : (l : A) ∈ P :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.mem_of_mem_normalizer_of_isParabolicTwo
      hP l.2 hlN
  exact ⟨l, hlP, hconj⟩

theorem mk_mem_centralizer_wSup_of_wCent {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hPY : P ≤ Y) {r y : A} (hyP : y ∈ P) (hconj : ∀ w ∈ Y, r * w * r⁻¹ = y * w * y⁻¹)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.WCent P r) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥P) (⟨y, hyP⟩ : ↥P) ∈
      Subgroup.centralizer (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P)) := by
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
  let ŷ : ↥P ⧸ CFSG.pCore 2 ↥P := q ⟨y, hyP⟩
  change ŷ ∈ _
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) w
  have hpP : (p : A) ∈ P := p.2
  have hz : y * (p : A) * y⁻¹ * (p : A)⁻¹ ∈ pCoreOf 2 P := by
    have h := hW (p : A) hpP (by simpa [q, QuotientGroup.mk'_apply] using hw)
    rwa [hconj (p : A) (hPY hpP)] at h
  have hzP : (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P) ∈ CFSG.pCore 2 ↥P := by
    rw [← CFSG.mem_openPCoreOf_iff (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hz
  have h1 : ŷ * q p * ŷ⁻¹ * (q p)⁻¹ = 1 := by
    have h := (QuotientGroup.eq_one_iff
      (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)).mpr hzP
    simpa [ŷ, q, map_mul, map_inv, QuotientGroup.mk'_apply] using h
  have h2' : ŷ * q p * ŷ⁻¹ = q p := by
    have := congrArg (fun t => t * q p) h1
    simpa [mul_assoc] using this
  have h2 : q p * ŷ = ŷ * q p := by
    have := congrArg (fun t => t * ŷ) h2'
    simpa [mul_assoc] using this.symm
  exact h2

theorem centralizes_of_perfect_of_conj_mem {A : Type} [Group A] {Y R : Subgroup A}
    (M : Subgroup A) (hM : Group.IsSolvable ↥M) (hMY : M ≤ Subgroup.normalizer (Y : Set A))
    (hRY : R ≤ Subgroup.normalizer (Y : Set A)) (hR : ⁅R, R⁆ = R)
    (h : ∀ r ∈ R, ∃ m ∈ M, ∀ w ∈ Y, r * w * r⁻¹ = m * w * m⁻¹) :
    ∀ r ∈ R, ∀ w ∈ Y, r * w = w * r := by
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  let ψ : ↥M →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hMY)
  let f : ↥R →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hRY)
  have : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hfψ : ∀ x : ↥R, f x ∈ ψ.range := by
    intro x
    obtain ⟨m, hm, hconj⟩ := h x x.2
    refine ⟨⟨m, hm⟩, ?_⟩
    ext w
    simp only [ψ, f, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
    exact (hconj w w.2).symm
  have hf1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (f.codRestrict ψ.range hfψ)
  intro r hr w hw
  have h1 : f ⟨r, hr⟩ = 1 := by
    have := congrArg (fun φ => ((φ ⟨r, hr⟩ : ψ.range) : MulAut ↥Y)) hf1
    simpa using this
  have h2 : r * w * r⁻¹ = w := by
    have := congrArg (fun a : MulAut ↥Y => ((a ⟨w, hw⟩ : ↥Y) : A)) h1
    simpa [f, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  calc r * w = r * w * r⁻¹ * r := by group
    _ = w * r := by rw [h2]

end Generic

section Outer


theorem isSolvable_outer_of_isClassicalTwoOrG2 {X : Type} [Group X] [Finite X]
    (h : IsClassicalTwoOrG2 X) : Group.IsSolvable (Outer X) := by
  have hodd := odd_card_commutator_outer_of_isClassicalTwoOrG2 h
  have : Finite ↥(commutator (Outer X)) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  exact Group.isSolvable_commutator_iff.mp (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem isSolvable_outer_of_quasisimple {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : CFSG.Open.IsQuasisimple ↥Y) (hcl : IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y)) :
    Group.IsSolvable (Outer ↥Y) := by
  have : Group.IsPerfect ↥Y := ⟨hY.1⟩
  have : Group.IsSolvable (Outer (↥Y ⧸ Subgroup.center ↥Y)) :=
    isSolvable_outer_of_isClassicalTwoOrG2 hcl
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥Y

end Outer

end KFour

section Census


theorem KFour.isSolvable_centralizer_wSup_of_parabolic (hGA : GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] {Y P : Subgroup A} (hY : CFSG.Open.IsQuasisimple ↥Y)
    (hO : pCoreOf 2 Y = ⊥) (hcl : IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y))
    (hP : IsParabolicTwo Y P) :
    Group.IsSolvable ↥(Subgroup.centralizer
      (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P))) := by
  by_cases hB2 : CFSG.AGLEmbedding.IsLieOf CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.IdxBTwo
      (↥Y ⧸ Subgroup.center ↥Y)
  · have hprod := CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.isSpTwoLeviProduct_of_parabolic
      (CFSG.AGLEmbedding.oddCenterRest_of_griess hGA) hY hO hB2 hP
    rw [hprod.centralizer_wSup_eq_bot]
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have := CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small.wSup_normal
      (↥P ⧸ CFSG.pCore 2 ↥P)
    exact isSolvable_centralizer_of_odd_index _
      (CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.not_two_dvd_index_wSup_of_parabolic
        hGA hY hO hcl hP hB2)

theorem kFactParabolicWCentSolvable_of_griess (hGA : GriessAllModelsStatement) :
    KFactParabolicWCentSolvable := by
  intro A _ _ Y P B hY hO hcl hP hBY hBP hW R hRB hR
  have hPY : P ≤ Y := hP.1
  have hOut : Group.IsSolvable (Outer ↥Y) := KFour.isSolvable_outer_of_quasisimple hY hcl
  set C := Subgroup.centralizer (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P))
    with hCdef
  have hC : Group.IsSolvable ↥C := KFour.isSolvable_centralizer_wSup_of_parabolic hGA hY hO hcl hP
  set M := (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).map P.subtype with hMdef
  have hM : Group.IsSolvable ↥M := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥P) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).isNilpotent
    have : Group.IsSolvable ↥(C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_comap_mk'
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ P.subtype
      P.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hMY : M ≤ Subgroup.normalizer (Y : Set A) :=
    (Subgroup.map_subtype_le _).trans (hPY.trans Subgroup.le_normalizer)
  refine KFour.centralizes_of_perfect_of_conj_mem M hM hMY (hRB.trans hBY) hR ?_
  intro r hr
  obtain ⟨y, hyP, hconj⟩ :=
    KFour.exists_mem_parabolic_conj_eq hOut hP (hRB.trans hBY) (hRB.trans hBP) hR hr
  refine ⟨y, Subgroup.mem_map.mpr ⟨⟨y, hyP⟩, ?_, rfl⟩, hconj⟩
  exact KFour.mk_mem_centralizer_wSup_of_wCent hPY hyP hconj (hW r (hRB hr))

end Census

section Holds


theorem kFactParabolicWCentSolvable_holds : KFactParabolicWCentSolvable :=
  kFactParabolicWCentSolvable_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end Holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
