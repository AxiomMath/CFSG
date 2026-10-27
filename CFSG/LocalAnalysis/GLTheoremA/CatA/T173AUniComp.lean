module

import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open scoped MatrixGroups

private theorem map_centralizer_singleton_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (y : G) :
    (Subgroup.centralizer ({y} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e y} : Set G') := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z * y = y * z := by
      simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hz
    have hgoal : e.toMonoidHom z * e y = e y * e.toMonoidHom z := by
      change e z * e y = e y * e z
      rw [← map_mul, ← map_mul, hz']
    simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hgoal
  · intro hx
    have hx' : x * e y = e y * x := by
      simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hgoal : e.symm x * y = y * e.symm x := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hx']
    simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hgoal

private theorem isComponentOf_map_mulEquiv' {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {L K : Subgroup G} (hL : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hL.1, CFSG.Open.IsSubnormal.map e.toMonoidHom hL.2.1, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm hL.2.2

private theorem not_solvable_of_open_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hsol
  obtain ⟨hperf, hsimple⟩ := hQ
  obtain ⟨n, hn⟩ := hsol.solvable
  have htop : ∀ m, derivedSeries Q m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact hperf
  rw [htop] at hn
  have hall : ∀ x : Q, x = 1 := fun x => Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top x)
  haveI : Subsingleton Q := ⟨fun a b => by rw [hall a, hall b]⟩
  haveI : Subsingleton (Q ⧸ Subgroup.center Q) := inferInstance
  exact not_subsingleton (Q ⧸ Subgroup.center Q) inferInstance

theorem uni_component_support {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A) {y : Q} (hy : y ∈ Bbar)
    (hy1 : y ≠ 1) {Kbar : Subgroup Q}
    (hK : CFSG.Open.IsComponentOf Kbar (Subgroup.centralizer ({y} : Set Q))) :
    ∃ I : Finset (Fin d), 2 ≤ I.card ∧
      (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I := by
  obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := h.2.2.2.2.2.1; omega⟩
  subst d
  have hmap : Bbar.map ψ.toMonoidHom =
      (A.subgroupOf (UniSU n (m + 1) F)).map (UniMk n (m + 1) F) := hfr.2.2.2
  have hy' : ψ y ∈ Bbar.map ψ.toMonoidHom := ⟨y, hy, rfl⟩
  rw [hmap] at hy'
  obtain ⟨a, ha, hπa⟩ := Subgroup.mem_map.mp hy'
  have haA : (a : GL (Fin (m + 1)) F) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hdiag : ∀ i j : Fin (m + 1), i ≠ j →
      (((a : GL (Fin (m + 1)) F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 :=
    hfr.2.2.1 _ haA
  let a' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F (m + 1)) := a
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, h.2.2.2.2.1, by rw [h.2.2.2.1, ← pow_mul, Nat.mul_comm]⟩
  let π' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F (m + 1)) →*
      UniPSU n (m + 1) F := UniMk n (m + 1) F
  have hπa' : π' a = ψ y := hπa
  have hπa'' : π' a' = ψ y := hπa
  have hπker : (UniMk n (m + 1) F).ker ≤ Subgroup.center ↥(UniSU n (m + 1) F) := by
    intro x hx
    have hx' : (x : GL (Fin (m + 1)) F) ∈ LargeEvenScalars (Fin (m + 1)) F := by
      have hmem : x ∈ (LargeEvenScalars (Fin (m + 1)) F).subgroupOf (UniSU n (m + 1) F) := by
        simpa only [UniMk, LargeEvenProjMk, QuotientGroup.ker_mk'] using hx
      exact Subgroup.mem_subgroupOf.mp hmem
    have hc : (x : GL (Fin (m + 1)) F) ∈ Subgroup.center (GL (Fin (m + 1)) F) :=
      CFSG.StandardType.TableB.scalars_le_center hx'
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    rw [Subgroup.mem_center_iff] at hc
    exact hc (z : GL (Fin (m + 1)) F)
  let J : Subgroup (UniPSU n (m + 1) F) := Kbar.map ψ.toMonoidHom
  have hJmap : CFSG.Open.IsComponentOf J
      ((Subgroup.centralizer ({y} : Set Q)).map ψ.toMonoidHom) :=
    isComponentOf_map_mulEquiv' ψ hK
  have hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({ψ y} : Set (UniPSU n (m + 1) F))) := by
    rw [← map_centralizer_singleton_mulEquiv ψ y]
    exact hJmap
  obtain ⟨σ, hσ⟩ := CFSG.StandardType.TableBUE.exists_diagHom_of_isDiag
    (d := m + 1) (g := (a : GL (Fin (m + 1)) F)) hdiag
  let δ : UniPSU n (m + 1) F → Fin (m + 1) → Fˣ := fun _ => σ
  have hδapp : CFSG.SectionRank.OddCover.diagHom (m + 1) (δ (ψ y)) =
      (a : GL (Fin (m + 1)) F) := hσ.symm
  have hsu : (ψ y, CFSG.SectionRank.OddCover.diagHom (m + 1) (δ (ψ y))) ∈
      CFSG.StandardType.SUTorus.suPairs π' := by
    rw [hδapp]
    refine (CFSG.StandardType.SUTorus.mem_suPairs (f := n) (K := F) (n := m + 1)
      (G := UniPSU n (m + 1) F)).mpr ⟨?_, ?_⟩
    · exact Subgroup.le_normalizer (show (a : GL (Fin (m + 1)) F) ∈
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F (m + 1) from a.2)
    · intro u v hv
      have hval : (v : GL (Fin (m + 1)) F) =
          (a' : GL (Fin (m + 1)) F) * (u : GL (Fin (m + 1)) F) *
            ((a' : GL (Fin (m + 1)) F))⁻¹ := by
        simpa only [a'] using hv
      have hv' : v = a' * u * a'⁻¹ := Subtype.ext hval
      rw [hv', ← hπa'']
      simp only [map_mul, map_inv]
  obtain ⟨i, hJI⟩ := CFSG.StandardType.SUTorus.exists_le_map_blockSU
    (f := n) (m := m) (G := UniPSU n (m + 1) F) (ψ := π')
    (S := {ψ y}) (δ := δ) (J := J) hUF h.1 h.2.1 hπker
    (by
      intro e he
      rw [Set.mem_singleton_iff.mp he]
      exact hsu)
    (by
      have hsurj : Function.Surjective π' := fun x =>
        (show Function.Surjective (UniMk n (m + 1) F) from
          fun z => QuotientGroup.mk'_surjective _ z) x
      rw [MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
      exact (CFSG.Assembly.isComponentOf_iff_open).mpr hJ)
  let I : Finset (Fin (m + 1)) :=
    CFSG.StandardType.LinTorus.diagClass ({ψ y} : Set (UniPSU n (m + 1) F)) δ i
  have hJI' : J ≤ (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map π' := hJI
  have hI2 : 2 ≤ I.card := by
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ I.card :=
      Finset.card_pos.mpr ⟨i, CFSG.StandardType.LinTorus.self_mem_diagClass _ δ i⟩
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp (show I.card = 1 by omega)
    rw [hi0, CFSG.StandardType.SUTorus.blockSU_singleton hUF, Subgroup.map_bot] at hJI'
    apply CFSG.StandardType.commutator_ne_bot_of_isQuasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open J).mpr hJ.2.2)
    rw [le_bot_iff.mp hJI', Subgroup.commutator_bot_left]
  have hKle : (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map π' ≤
      Subgroup.centralizer ({ψ y} : Set (UniPSU n (m + 1) F)) := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconst : ∀ p ∈ I, ∀ q ∈ I, σ p = σ q :=
      fun p hp q hq => CFSG.StandardType.LinTorus.eq_of_mem_diagClass hp hq (Set.mem_singleton _)
    have hσ' : (a' : GL (Fin (m + 1)) F) =
        CFSG.SectionRank.OddCover.diagHom (m + 1) σ := hσ
    have hcomm : w * a' = a' * w := by
      have := CFSG.StandardType.TableBUE.blockSU_le_centralizer (S := I) (τ := σ) hconst hσ' hw
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    rw [← hπa'']
    rw [← map_mul, ← map_mul, hcomm]
  have hKq : CFSG.Assembly.IsQuasisimple
      ↥((CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map π') := by
    by_cases hf2 : 2 ≤ n
    · exact CFSG.StandardType.SURepair.isQuasisimple_map_blockSU_of_two_le hUF hf2 hπker hI2
    · have hn1 : n = 1 := by
        have h1n : 1 ≤ n := h.2.2.2.2.1
        omega
      subst n
      have hI4 : 4 ≤ I.card := by
        by_contra hlt
        have hlt' : I.card < 4 := not_le.mp hlt
        have hk1 : 1 ≤ I.card := by omega
        have hk3 : I.card ≤ 3 := by omega
        haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F I.card) :=
          CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hUF hk1 hk3
        let e := CFSG.StandardType.TableBUE.blockSUEquiv (K := F) (n := 1) I hUF
        haveI : Group.IsSolvable ↥(CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I) :=
          Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
            (fun x y h => e.symm.injective h)
        have hsolv : Group.IsSolvable
            ↥((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map π') := by
          have hres := Group.isSolvable_of_surjective
            (f := ((π').comp
              (CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).subtype).rangeRestrict)
            (MonoidHom.rangeRestrict_surjective _)
          rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hres
        haveI : Group.IsSolvable
            ↥((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map π') := hsolv
        have hsolvJ : Group.IsSolvable ↥J := by
          let eJ := Subgroup.subgroupOfEquivOfLe hJI'
          haveI : Group.IsSolvable ↥(J.subgroupOf
              ((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map π')) :=
            Group.isSolvable_of_isSolvable_injective
              (f := (J.subgroupOf
                ((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map π')).subtype)
              (fun x y h => Subtype.ext h)
          exact Group.isSolvable_of_surjective (f := eJ.toMonoidHom)
            (fun z => ⟨eJ.symm z, by simp⟩)
        exact not_solvable_of_open_isQuasisimple hJ.2.2 hsolvJ
      have hblockq : CFSG.IsQuasisimple
          ↥(CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I) :=
        CFSG.StandardType.TableBUE.isQuasisimple_blockSU I hUF hUF.card_eq_sq
          (by omega) (by
            intro h'
            have h1 : I.card = 3 := (Prod.mk.inj h').1
            omega)
      exact CFSG.StandardType.SURepair.isQuasisimple_map_of_isQuasisimple hπker hblockq
  have hLeq : J = (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map π' :=
    CFSG.StandardType.LinTypeAk.eq_of_isComponentOf_of_le
      ((CFSG.Assembly.isComponentOf_iff_open).mpr hJ) hJI' hKle hKq
  refine ⟨I, hI2, ?_⟩
  change (J : Set (UniPSU n (m + 1) F)) = UniBlockImage n (m + 1) F I
  rw [hLeq]
  ext x
  constructor
  · intro hx
    rw [SetLike.mem_coe, Subgroup.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, ⟨g.2, hg⟩, rfl⟩
  · intro hx
    rw [UniBlockImage, Set.mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact Subgroup.mem_map.mpr ⟨g, hg.2, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
