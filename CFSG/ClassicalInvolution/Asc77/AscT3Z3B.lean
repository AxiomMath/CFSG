module

public import CFSG.ClassicalInvolution.Asc77.AscT3Z3A
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg
public import CFSG.ClassicalInvolution.Asc77.AscT3RAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups commutatorElement

section Pure

theorem z3_hom_trivial_of_perfect_comm {P A : Type*} [Group P] [Group A] (hP : Group.IsPerfect P)
    (f : P →* A) (hc : ∀ g h : P, f g * f h = f h * f g) : f = 1 := by
  have hker : commutator P ≤ f.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc g h)
  rw [hP.commutator_eq_top] at hker
  ext g
  exact hker (Subgroup.mem_top g)

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


open Classical in
noncomputable def z3SwapHom (d : Std20 p f K K' J S R R' W V z t) :
    ↥(Subgroup.centralizer ({z} : Set G)) →* Multiplicative (ZMod 2) where
  toFun g := if conjSub (g : G) K = K then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' := by
    intro g h
    have hgK := d.late_conj_K g.2
    have hhK := d.late_conj_K h.2
    have hgK' := d.late_conj_K' g.2
    have hhK' := d.late_conj_K' h.2
    have hgi := d.late_conj_iff g.2
    have hhi := d.late_conj_iff h.2
    have e : conjSub ((g : G) * (h : G)) K =
        conjSub (g : G) (conjSub (h : G) K) := conjSub_mul _ _ _
    by_cases hg : conjSub (g : G) K = K <;> by_cases hh : conjSub (h : G) K = K
    · have : conjSub ((g : G) * (h : G)) K = K := by
        rw [e, hh, hg]
      simp [hg, hh, this]
    · have h1 : conjSub (h : G) K = K' := hhK.resolve_left hh
      have : conjSub ((g : G) * (h : G)) K ≠ K := by
        rw [e, h1, (hgi.mp hg)]
        exact d.ne
      simp [hg, hh, this]
    · have h1 : conjSub (g : G) K = K' := hgK.resolve_left hg
      have h2 : conjSub (g : G) K' = K := hgK'.resolve_right (fun h' => d.ne (by
        have := conjSub_injective (g : G) (h1.trans h'.symm)
        exact this.symm))
      have : conjSub ((g : G) * (h : G)) K ≠ K := by
        rw [e, hh, h1]
        exact d.ne
      simp [hg, hh, this]
    · have h1 : conjSub (g : G) K = K' := hgK.resolve_left hg
      have h1' : conjSub (h : G) K = K' := hhK.resolve_left hh
      have h2 : conjSub (g : G) K' = K := hgK'.resolve_right (fun h' => d.ne (by
        have := conjSub_injective (g : G) (h1.trans h'.symm)
        exact this.symm))
      have : conjSub ((g : G) * (h : G)) K = K := by
        rw [e, h1', h2]
      simp [hg, hh, this, ofAdd_one_mul_self]

theorem Std20.z_perfect_le_N_K (d : Std20 p f K K' J S R R' W V z t) {P : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer ({z} : Set G)) (hP : Group.IsPerfect ↥P) :
    P ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  set ψ : ↥P →* Multiplicative (ZMod 2) := (z3SwapHom d).comp (Subgroup.inclusion hPC) with hψ
  have h1 : ψ = 1 := z3_hom_trivial_of_perfect_comm hP ψ (fun g h => mul_comm _ _)
  have h2 : (z3SwapHom d) ⟨x, hPC hx⟩ = 1 := by
    have := congrArg (fun f : ↥P →* Multiplicative (ZMod 2) => f ⟨x, hx⟩) h1
    exact this
  by_contra hN
  have hne : ¬ conjSub x K = K := fun h => hN (mem_normalizer_iff_conjSub_eq.mpr h)
  have h3 : (z3SwapHom d) ⟨x, hPC hx⟩ = Multiplicative.ofAdd 1 := by
    simp [z3SwapHom, hne]
  rw [h3] at h2
  exact absurd h2 (by decide)

theorem Std20.z_perfect_le_N_K' (d : Std20 p f K K' J S R R' W V z t) {P : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer ({z} : Set G)) (hP : Group.IsPerfect ↥P) :
    P ≤ Subgroup.normalizer (K' : Set G) := fun _x hx =>
  mem_normalizer_iff_conjSub_eq.mpr ((d.late_conj_iff (hPC hx)).mp
    (mem_normalizer_iff_conjSub_eq.mp (d.z_perfect_le_N_K hPC hP hx)))

end Std

section Inner

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

noncomputable def z3Act {L P : Subgroup G} (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) : ↥P →* MulAut SL(2, F) where
  toFun g := phiG L e (g : G)
  map_one' := phiG_one
  map_mul' g h := phiG_mul (hPN g.2) (hPN h.2)

theorem z3_perfect_inner (hK : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {L P : Subgroup G} (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP : Group.IsPerfect ↥P) :
    ∀ g : ↥P, ∃ x : SL(2, F), z3Act e hPN g = MulAut.conj x := by
  have hε : (slEps F hK).comp (z3Act e hPN) = 1 :=
    z3_hom_trivial_of_perfect_comm hP _ (fun g h => mul_comm _ _)
  have hρ : (slRho F).comp (z3Act e hPN) = 1 := z3_hom_trivial_of_perfect_comm hP _ (fun g h => by
    exact CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F _ _)
  intro g
  have h1 : slEps F hK (z3Act e hPN g) = 1 := by
    have := congrArg (fun f : ↥P →* Multiplicative (ZMod 2) => f g) hε
    simpa using this
  have h2 : slRho F (z3Act e hPN g) = 1 := by
    have := congrArg (fun f : ↥P →* RingAut F => f g) hρ
    simpa using this
  obtain ⟨x, hx⟩ := (slEps_slRho_eq_one_iff F hK h4 (z3Act e hPN g)).mp ⟨h1, h2⟩
  exact ⟨x, hx.symm⟩

theorem z3_perfect_center_mem_cStar (hK : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {L P : Subgroup G} (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP : Group.IsPerfect ↥P) {c : G} (hcP : c ∈ P)
    (hcc : ∀ x ∈ P, c * x = x * c) : c ∈ cStar L := by
  have hc : (⟨c, hcP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcc g g.2).symm
  have h1 := z3_center_trivial_of_perfect_inner hP (z3Act e hPN)
    (z3_perfect_inner hK h4 e hPN hP) hc
  exact (phiG_eq_one_iff (hPN hcP)).mp h1

end Inner

end CFSG.ClassicalInvolution.Asc77.T3CII
