module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralAlg
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G] [Finite G]

theorem hom_eq_one_of_coprime {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J)
    {H : Type*} [Group H] (φ : ↥X →* H) (hH : Nat.Coprime p (Nat.card H)) :
    ∀ g (hg : g ∈ J), φ ⟨g, hJ.1 hg⟩ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJX, hP⟩ := (i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hres := primeResidual_eq_top_of_pComponent p (J.subgroupOf X) hP
  set L : Subgroup ↥X := J.subgroupOf X with hL
  let ψ : ↥L →* H := φ.comp L.subtype
  have hle : primeResidual p ↥L ≤ ψ.ker := by
    refine sSup_le fun P hP' x hx => ?_
    obtain ⟨k, hk⟩ := hP' ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf (ψ x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
    have h2 : orderOf (ψ x) ∣ Nat.card H := orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hH.pow_left k) h1 h2)
  rw [hres] at hle
  intro g hg
  have hmem : (⟨g, hJX hg⟩ : ↥X) ∈ L := hg
  exact hle (Subgroup.mem_top (⟨⟨g, hJX hg⟩, hmem⟩ : ↥L))

theorem hom_eq_one_of_solvable {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J)
    {H : Type*} [Group H] [Group.IsSolvable H] (φ : ↥X →* H) :
    ∀ g (hg : g ∈ J), φ ⟨g, hJ.1 hg⟩ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJX, hP⟩ := (i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hperf := isPerfect_of_isPComponent p hP
  set L : Subgroup ↥X := J.subgroupOf X with hL
  let ψ : ↥L →* H := φ.comp L.subtype
  have hperfR : Group.IsPerfect ↥ψ.range := Group.IsPerfect.ofSurjective ψ.rangeRestrict_surjective
  have hss : Subsingleton ↥ψ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) inferInstance
  intro g hg
  have hmem : (⟨g, hJX hg⟩ : ↥X) ∈ L := hg
  have h1 : (⟨ψ ⟨⟨g, hJX hg⟩, hmem⟩, ⟨_, rfl⟩⟩ : ↥ψ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem isQuasisimple_of_glaPComponent_of_comm {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J)
    (hcomm : ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf p X, o * g = g * o) :
    CFSG.Open.IsQuasisimple ↥J := by
  have hsn : IsSubnormal J X := hJ.2.1
  have hbar : CFSG.Open.IsQuasisimple ↥(barX p X J) := hJ.2.2.1.2.2
  have hQ : CFSG.Open.IsQuasisimple (LocalBalance.barOf p J) :=
    (LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hp hsn).1 hbar
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  let f : ↥J →* LocalBalance.barOf p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hker : f.ker ≤ Subgroup.center ↥J := by
    intro y hy
    have hy1 : y ∈ GLAPPrimeCore p ↥J := by rwa [QuotientGroup.ker_mk'] at hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hy' : (y : G) ∈ GLAPPrimeCoreOf p J := ⟨y, hy1, rfl⟩
    have h2 := hcomm g g.2 y (LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hsn hy')
    exact Subtype.ext h2.symm
  have hQ' : CFSG.IsQuasisimple (LocalBalance.barOf p J) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hQ
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
    (isQuasisimple_of_central_cover f hf hperf hker hQ')

end CFSG.HardMathSupport.Solomon.Coordinator
