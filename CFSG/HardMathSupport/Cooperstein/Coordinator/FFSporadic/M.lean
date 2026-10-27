module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.BHeis
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MAbstract
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterHopfMultiplier
import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.Generated CFSG.YGroups CFSG.YGroups.Y443

theorem heisCfg_lift_of_hom {C Q : Type} [Group C] [Group Q] (π : C →* Q)
    (hπs : Function.Surjective π) (hker : π.ker = Subgroup.center C)
    (hc2 : Nat.card (Subgroup.center C) = 2) {x y : Fin 4 → Q} {z : Q} (h : HeisCfg 3 4 x y z)
    (hy : ∀ i, y i ^ 3 = 1) :
    ∃ (x' y' : Fin 4 → C) (z' : C), HeisCfg 3 4 x' y' z' ∧ ∀ i, y' i ^ 3 = 1 := by
  have hKp : ¬ 3 ∣ Nat.card π.ker := by rw [hker, hc2]; norm_num
  obtain ⟨x', y', z', h', -, -, -, hy'⟩ := HeisCfg.exists_lift π hπs hker.le hKp h hy
  exact ⟨x', y', z', h', hy'⟩

theorem heis_in_centralizer_of_hom {Y Q : Type} [Group Y] [Group Q] {u : Y}
    (hu : orderOf u = 2)
    (hz : (Subgroup.center ↥(cent u)).map (cent u).subtype = Subgroup.zpowers u)
    (π : ↥(cent u) →* Q) (hπs : Function.Surjective π) (hker : π.ker = Subgroup.center ↥(cent u))
    {x y : Fin 4 → Q} {z : Q} (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    ∃ (x y : Fin 4 → Y) (z : Y), HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      (∀ i, x i * u = u * x i) ∧ (∀ i, y i * u = u * y i) ∧ z * u = u * z := by
  have hc2 : Nat.card (Subgroup.center ↥(cent u)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent u).subtype_injective, hz, Nat.card_zpowers, hu]
  obtain ⟨x', y', z', h', hy'⟩ := heisCfg_lift_of_hom π hπs hker hc2 h hy
  have hz1 : (cent u).subtype z' ≠ 1 := fun h1 =>
    h'.z1 ((cent u).subtype_injective (by rw [h1, map_one]))
  refine ⟨fun i => ((x' i : ↥(cent u)) : Y), fun i => ((y' i : ↥(cent u)) : Y),
    ((z' : ↥(cent u)) : Y), h'.map (cent u).subtype hz1, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · simpa using congrArg Subtype.val (hy' i)
  · exact Subgroup.mem_centralizer_singleton_iff.1 (x' i).2
  · exact Subgroup.mem_centralizer_singleton_iff.1 (y' i).2
  · exact Subgroup.mem_centralizer_singleton_iff.1 z'.2

theorem isConj_of_cube {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : IsConj a b := by
  have h6 : a * b * (a * b) * (a * b) = 1 := by
    simpa [pow_succ, mul_assoc] using h
  have hinv : (a * b)⁻¹ = b * a := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc a * b * (b * a) = a * (b * b) * a := by group
      _ = 1 := by rw [hb, mul_one, ha]
  refine isConj_iff.2 ⟨a * b, ?_⟩
  rw [hinv]
  calc a * b * a * (b * a) = a * b * a * b * a * (b * b) := by rw [hb, mul_one]; group
    _ = a * b * (a * b) * (a * b) * b := by group
    _ = b := by rw [h6, one_mul]

section Monster

theorem gmat_equiv_catalogue : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
  CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti

theorem gmat_autInner : ∀ φ : Gmat ≃* Gmat, ∃ s : Gmat, ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.SPOR.allInner_Gmat φ
  exact ⟨g, fun x => by rw [hg]; rfl⟩

theorem gmat_center_trivial (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (he : Nonempty (L ⧸ Subgroup.center L ≃* Gmat)) : Nat.card (Subgroup.center L) = 1 := by
  obtain ⟨e⟩ := he
  obtain ⟨f⟩ := gmat_equiv_catalogue
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans f)
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (TauCeti.CFSGIndex.sporadic .M).Group) = 1 :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.monsterHopfTrivial_holds
  rw [hM] at h
  exact Nat.dvd_one.1 h

theorem gmat_card_lt : Nat.card Gmat < 2 ^ 180 := by
  rw [natCard_Gmat_eq_monsterOrder]
  unfold CFSG.Open.monsterOrder
  norm_num

theorem gmat_twoA : IsTwoACentralizer (fM y443C) := by
  have hGA : Gmat = CFSG.Monster.Griess.AutO :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  have h2A := monster_clauses_MGriess.2.2
  have := CFSG.EvenSporadicStandard.Solomon78.IsTwoACentralizer.map (griessEquivGmat hGA) h2A
  rwa [griessEquivGmat_tGriess hGA] at this

theorem gmat_c_sq : fM y443C * fM y443C = 1 := fM_c_mul_self

theorem gmat_c_order : orderOf (fM y443C) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact gmat_c_sq) fM_C_ne_one

theorem fM_isConj {a b : CFSG.Open.MonsterY443Derived} (h : IsConj a b) : IsConj (fM a) (fM b) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨fM c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem fM_isConj_c_y : IsConj (fM y443C) (fM y443Y) := by
  have h := fM_S_conj fM_cx_cube
  refine isConj_iff.2 ⟨fM y443S, ?_⟩
  rw [← map_inv, y443S_inv]
  exact h

theorem y443Tl_isConj_of_edge {s t : ℕ} (hst : s < t) (ht : t < 12) (h : pairExp 4 4 3 s t = 3) :
    IsConj (y443Tl s) (y443Tl t) :=
  isConj_of_cube (y443Tl_mul_self s) (y443Tl_mul_self t)
    (by have := y443Tl_pair_pow hst ht; rwa [h] at this)

theorem y443Tl_isConj_three : ∀ k, k < 12 → IsConj (y443Tl 3) (y443Tl k) := by
  have adj : ∀ s t : ℕ, s < t → t < 12 → pairExp 4 4 3 s t = 3 →
      (IsConj (y443Tl 3) (y443Tl s) ↔ IsConj (y443Tl 3) (y443Tl t)) := fun s t hst ht h =>
    ⟨fun hs => hs.trans (y443Tl_isConj_of_edge hst ht h),
      fun hs => hs.trans (y443Tl_isConj_of_edge hst ht h).symm⟩
  have p3 : IsConj (y443Tl 3) (y443Tl 3) := IsConj.refl _
  have p2 := (adj 2 3 (by norm_num) (by norm_num) (by decide)).2 p3
  have p1 := (adj 1 2 (by norm_num) (by norm_num) (by decide)).2 p2
  have p0 := (adj 0 1 (by norm_num) (by norm_num) (by decide)).2 p1
  have p4 := (adj 3 4 (by norm_num) (by norm_num) (by decide)).1 p3
  have p5 := (adj 0 5 (by norm_num) (by norm_num) (by decide)).1 p0
  have p6 := (adj 5 6 (by norm_num) (by norm_num) (by decide)).1 p5
  have p7 := (adj 6 7 (by norm_num) (by norm_num) (by decide)).1 p6
  have p8 := (adj 7 8 (by norm_num) (by norm_num) (by decide)).1 p7
  have p9 := (adj 0 9 (by norm_num) (by norm_num) (by decide)).1 p0
  have p10 := (adj 9 10 (by norm_num) (by norm_num) (by decide)).1 p9
  have p11 := (adj 10 11 (by norm_num) (by norm_num) (by decide)).1 p10
  intro k hk
  interval_cases k <;> assumption

theorem gmat_gen : ∃ cs : List Gmat, cs.length ≤ 20 ∧
    Subgroup.closure {v : Gmat | ∃ c ∈ cs, v = c * fM y443C * c⁻¹} = ⊤ := by
  have hk : ∀ k : Fin 12, ∃ c : Gmat, c * fM y443C * c⁻¹ = fM (y443Tl k) := fun k => by
    have h1 := fM_isConj (y443Tl_isConj_three k k.2)
    rw [← y443Y_eq_Tl] at h1
    exact isConj_iff.1 (fM_isConj_c_y.trans h1)
  choose cfun hc using hk
  refine ⟨List.ofFn cfun, by simp, ?_⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨m, rfl⟩ := CFSG.RankThree.PartOne.SPOR.fM_surjective g
  have hm : m ∈ Subgroup.closure (Set.range y443T) := y443_closure_range_T ▸ Subgroup.mem_top m
  have := Subgroup.mem_map_of_mem fM hm
  rw [MonoidHom.map_closure] at this
  refine Subgroup.closure_mono ?_ this
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  have hs : y443T s = y443Tl (y443LetterOfGen s) := by rw [y443Tl, y443GenOfLetter_letterOfGen]
  refine ⟨cfun ⟨y443LetterOfGen s, y443LetterOfGen_lt s⟩, ?_, ?_⟩
  · exact List.mem_ofFn.2 (Set.mem_range_self _)
  · rw [hs]
    exact (hc ⟨_, y443LetterOfGen_lt s⟩).symm

theorem gmat_twoA_hom : ∃ π : ↥(cent (fM y443C)) →* NativeSporadic.B,
    Function.Surjective π ∧ π.ker = Subgroup.center ↥(cent (fM y443C)) := by
  obtain ⟨-, -, ⟨e⟩⟩ := gmat_twoA
  let ψ : (↥(cent (fM y443C)) ⧸ Subgroup.center ↥(cent (fM y443C))) →* NativeSporadic.B :=
    MonoidHom.mk' (fun x => e x) (fun x y => e.map_mul x y)
  have hψi : Function.Injective ψ := e.injective
  have hψs : Function.Surjective ψ := e.surjective
  refine ⟨ψ.comp (QuotientGroup.mk' _), hψs.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ hψi, QuotientGroup.ker_mk']

theorem noIrrFFOffender_Gmat_of_heisB
    (hB : ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B), HeisCfg 3 4 x y z ∧
      ∀ i, y i ^ 3 = 1) :
    NoIrrFFOffender Gmat := by
  obtain ⟨x, y, z, h, hy⟩ := hB
  obtain ⟨-, hz, -⟩ := gmat_twoA
  obtain ⟨π, hπs, hker⟩ := gmat_twoA_hom
  exact noIrrFFOffender_of_twoA_gen gmat_autInner gmat_center_trivial gmat_card_lt gmat_c_sq
    fM_C_ne_one (heis_in_centralizer_of_hom gmat_c_order hz π hπs hker h hy) gmat_gen

theorem noIrrFFOffender_M_of_heisB
    (hB : ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B), HeisCfg 3 4 x y z ∧
      ∀ i, y i ^ 3 = 1) :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M).Group :=
  noIrrFFOffender_transfer (noIrrFFOffender_Gmat_of_heisB hB) gmat_equiv_catalogue

theorem gf2NoFFSporadicFor_M_of_heisB
    (hB : ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B), HeisCfg 3 4 x y z ∧
      ∀ i, y i ^ 3 = 1) :
    GF2NoFFSporadicFor .M :=
  gf2NoFFSporadicFor_of_noIrrFFOffender (noIrrFFOffender_M_of_heisB hB)

theorem gf2NoFFSporadicFor_M : GF2NoFFSporadicFor .M :=
  gf2NoFFSporadicFor_M_of_heisB b_heisCfg

end Monster

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
