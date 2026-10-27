module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape
public import CFSG.ClassicalInvolution.RouteD.TWZAct

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open CFSG.Open (classicalInvolutionOddCore)

set_option linter.unusedSectionVars false

section Act

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem actX_fix_of_commutes {c : G} (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    {N : Subgroup G} (hcN : ∀ n ∈ N, c * n = n * c) :
    ∀ g ∈ locImg Ω x N, actX c hc g = g := by
  rintro _ ⟨y, hy, rfl⟩
  rw [actX_mk]
  congr 1
  apply Subtype.ext
  show c * (y : G) * c⁻¹ = y
  rw [hcN y (Subgroup.mem_subgroupOf.mp hy)]
  group

theorem actX_eq_conj_of_mem {c : G} (hcY : c ∈ locLayer Ω x)
    (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G)) (g : locQuot Ω x) :
    actX c hc g = locMk Ω x ⟨c, hcY⟩ * g * (locMk Ω x ⟨c, hcY⟩)⁻¹ := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  show actX c hc (locMk Ω x y) =
    locMk Ω x ⟨c, hcY⟩ * locMk Ω x y * (locMk Ω x ⟨c, hcY⟩)⁻¹
  rw [actX_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem actX_four_eq_one {c : G} (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    (hc4 : c * c * (c * c) = 1) :
    actX c hc * actX c hc * (actX c hc * actX c hc) = 1 := by
  have hcc : c * c ∈ Subgroup.normalizer (locLayer Ω x : Set G) := Subgroup.mul_mem _ hc hc
  have hc4N : c * c * (c * c) ∈ Subgroup.normalizer (locLayer Ω x : Set G) :=
    Subgroup.mul_mem _ hcc hcc
  have hαα : actX (Ω := Ω) (x := x) (c * c) hcc = actX c hc * actX c hc :=
    actX_mul c c hc hc hcc
  have e1 : actX (Ω := Ω) (x := x) (c * c * (c * c)) hc4N =
      actX (c * c) hcc * actX (c * c) hcc := actX_mul _ _ hcc hcc hc4N
  have e2 : actX (Ω := Ω) (x := x) (c * c * (c * c)) hc4N = 1 := by
    have h1 : (1 : G) ∈ Subgroup.normalizer (locLayer Ω x : Set G) := Subgroup.one_mem _
    rw [← actX_one h1]
    exact actX_congr hc4 hc4N h1
  rw [e1, hαα] at e2
  exact e2

theorem conjSub_mem_and_image (hΩ : InClass p f Ω) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (y : ↥(locLayer Ω x)) :
    conjSub (y : G) N ∈ centralizingMembers Ω {x} ∧
      ∀ n ∈ conjSub (y : G) N, ∃ (k : G) (hk : k ∈ N) (hn : n ∈ locLayer Ω x),
        locMk Ω x ⟨n, hn⟩ =
          locMk Ω x y * locMk Ω x ⟨k, le_centralizingLayer hN hk⟩ * (locMk Ω x y)⁻¹ := by
  have hyx : (y : G) * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {x} y.2)
  have hyx' : (y : G) * x * (y : G)⁻¹ = x := by rw [hyx]; group
  have hN' : conjSub (y : G) N ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ.conjInvariant (y : G) x
    rw [hyx'] at this
    rw [this]
    exact ⟨N, hN, rfl⟩
  refine ⟨hN', fun n hn => ?_⟩
  have hk : (y : G)⁻¹ * n * (y : G) ∈ N := mem_conjSub_iff.mp hn
  refine ⟨(y : G)⁻¹ * n * (y : G), hk, le_centralizingLayer hN' hn, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show n = (y : G) * ((y : G)⁻¹ * n * (y : G)) * (y : G)⁻¹
  group

end Act

section Component

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}


theorem component_package (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (D : LieSystemData p f X Φ)
    (hcard : D.card = 1) (i : Fin D.card) (hD : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) :
    D.exp i = f ∧
      FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧
      Group.IsPerfect (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K ∧
      Function.Surjective (D.hom i) := by
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hDall : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := fun j => by
    rw [hsub.elim j i]
    exact hD
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => hD.2 h.1
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨-, hperf⟩ := componentFacts_of_no_exotic D hp2 hq4 hDall
  have hperfK : Group.IsPerfect (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero (D.tag i)
      (D.rank i) p (D.exp i) Fact.out (D.isFundTag i) (D.admissible i)).1.1
  have hsurj : Function.Surjective (D.hom i) := by
    have h := D.generate
    have h2 : (⨆ j, (D.hom j).range) = (D.hom i).range := by
      refine le_antisymm (iSup_le fun j => ?_) (le_iSup (fun j => (D.hom j).range) i)
      rw [hsub.elim j i]
    rw [h2] at h
    exact MonoidHom.range_eq_top.mp h
  exact ⟨hexp, hperf i, hperfK, hsurj⟩

theorem involution_lift (D : LieSystemData p f X Φ) (i : Fin D.card)
    (hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) {R : Subgroup (modelUniv (D.tag i) (D.rank i) p
      (D.exp i) Fact.out).K} (hR : R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D) {y : (modelUniv (D.tag i)
      (D.rank i) p (D.exp i) Fact.out).K} (hy : y ∈ R) {g : X} (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (h : D.hom i y = g) : y * y = 1 ∧ y ≠ 1 := by
  have h1 : D.hom i (y * y) = 1 := by rw [map_mul, h, hg2]
  have hker : y * y ∈ Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i)
      Fact.out).K := D.ker_le_center i (MonoidHom.mem_ker.mpr h1)
  have h2 : y * y = 1 := by
    refine Gaps.fundNoncentral p (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i)
      (D.admissible i) hnc R hR (y * y) (R.mul_mem hy hy) (fun w => ?_)
    have h' := Subgroup.mem_center_iff.mp hker w
    have e : y * y * w * (y * y)⁻¹ * w⁻¹ = 1 := by
      calc y * y * w * (y * y)⁻¹ * w⁻¹ = w * (y * y) * (y * y)⁻¹ * w⁻¹ := by rw [h']
        _ = 1 := by group
    rw [e]
    exact one_mem _
  exact ⟨h2, fun h3 => hg1 (by rw [← h, h3, map_one])⟩

end Component

end CFSG.ClassicalInvolution.RouteD.TWZ
