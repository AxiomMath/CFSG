module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClSplit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCov
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def ClosureFix (P : Type) [Group P] : Prop :=
  ∀ α : MulAut P, α * α = 1 → ∀ J : Subgroup P, IsComponentIn J (fixSub α) → InFStar J

theorem closureFix_of_mulEquiv {P P' : Type} [Group P] [Group P'] (e : P ≃* P')
    (h : ClosureFix P) : ClosureFix P' := by
  intro α' hα' J' hJ'
  set α : MulAut P := (e.trans α').trans e.symm with hαdef
  have hαapply : ∀ p : P, e (α p) = α' (e p) := by
    intro p
    rw [hαdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hα : α * α = 1 := by
    ext x
    have hxx : α (α x) = x := by
      apply e.injective
      rw [hαapply (α x), hαapply x]
      have hh := congrArg (fun f : MulAut P' => f (e x)) hα'
      simpa only [MulAut.mul_apply, MulAut.one_apply] using hh
    simpa only [MulAut.mul_apply, MulAut.one_apply] using hxx
  have hfix : fixSub α = (fixSub α').comap e.toMonoidHom := by
    ext p
    rw [mem_fixSub_iff, Subgroup.mem_comap, mem_fixSub_iff]
    change α p = p ↔ α' (e p) = e p
    constructor
    · intro hp
      rw [← hαapply p, hp]
    · intro hp
      exact e.injective (by rw [hαapply p, hp])
  have hJ0map : (J'.comap e.toMonoidHom).map e.toMonoidHom = J' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective J'
  have hJ : IsComponentIn (J'.comap e.toMonoidHom) (fixSub α) := by
    rw [← sec63PT_isComponentIn_map_iff e.toMonoidHom e.injective]
    rw [hJ0map, hfix, Subgroup.map_comap_eq_self_of_surjective e.surjective (fixSub α')]
    exact hJ'
  have hres : InFStar (J'.comap e.toMonoidHom) := h α hα _ hJ
  have hthis := l34g_x_inFStar_map_inj e.toMonoidHom e.injective hres
  rwa [hJ0map] at hthis

theorem closureFix_of_ne_one {P : Type} [Group P] [Finite P] (hq : CFSG.IsQuasisimple P)
    (hF : IsFStarGroup P)
    (h : ∀ α : MulAut P, α * α = 1 → α ≠ 1 →
      ∀ J : Subgroup P, IsComponentIn J (fixSub α) → InFStar J) : ClosureFix P := by
  intro α hα J hJ
  by_cases hα1 : α = 1
  · have htop : fixSub (1 : MulAut P) = ⊤ := by
      ext p
      simp [mem_fixSub_iff]
    have hJtop : IsComponentIn J (⊤ : Subgroup P) := by
      rw [← htop, ← hα1]
      exact hJ
    have hqtop : CFSG.IsQuasisimple ↥(⊤ : Subgroup P) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
    have hT : IsComponentIn (⊤ : Subgroup P) (⊤ : Subgroup P) :=
      isComponentIn_of_normal le_rfl hqtop inferInstance
    have hJeq : J = ⊤ := IsComponentIn.eq_of_le hJtop hT le_top
    rw [hJeq]
    exact isFStarGroup_of_mulEquiv Subgroup.topEquiv.symm hF
  · exact h α hα hα1 J hJ

theorem inFStar_of_isComponentIn_fixSub_conj {P : Type} [Group P] (α β : MulAut P)
    (h : ∀ J : Subgroup P, IsComponentIn J (fixSub (β⁻¹ * α * β)) → InFStar J)
    {J : Subgroup P} (hJ : IsComponentIn J (fixSub α)) : InFStar J := by
  have hfix : (fixSub α).map (β⁻¹).toMonoidHom = fixSub (β⁻¹ * α * β) := by
    ext p
    rw [Subgroup.mem_map, mem_fixSub_conj_iff]
    constructor
    · rintro ⟨q, hq, hqp⟩
      rw [← hqp]
      simpa using hq
    · intro hp
      exact ⟨β p, hp, MulEquiv.symm_apply_apply β p⟩
  have hJ' : IsComponentIn (J.map (β⁻¹).toMonoidHom) (fixSub (β⁻¹ * α * β)) := by
    have h1 := IsComponentIn.map_mulEquiv hJ β⁻¹
    rwa [hfix] at h1
  have hF' : IsFStarGroup ↥(J.map (β⁻¹).toMonoidHom) := h _ hJ'
  exact isFStarGroup_of_mulEquiv
    (Subgroup.equivMapOfInjective J (β⁻¹).toMonoidHom (β⁻¹).injective).symm hF'

theorem asc82ClosureAt_of_closureFix {P : (Q : Type) → [Group Q] → Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → P X → ClosureFix X) :
    Asc82ClosureAt P := by
  intro G _ _ L w hL hP hw hwN J hJ
  haveI : Finite ↥L := Finite.of_injective L.subtype L.subtype_injective
  have hw2 : w * w = 1 := by
    have h2 : w ^ 2 = 1 := by
      rw [← hw]
      exact pow_orderOf_eq_one w
    rwa [pow_two] at h2
  let σ : MulAut ↥L := conjAut L hw2 hwN
  have hσ : σ * σ = 1 := conjAut_mul_self L hw2 hwN
  have hfixσ : (fixSub σ).map L.subtype = L ⊓ centralizer ({w} : Set G) :=
    sec63PT_map_subtype_fixSub L hw2 hwN
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  let J₀ : Subgroup ↥L := J.comap L.subtype
  have hJ0map : J₀.map L.subtype = J := by
    show (J.comap L.subtype).map L.subtype = J
    exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hJ0 : IsComponentIn J₀ (fixSub σ) := by
    rw [← sec63PT_isComponentIn_map_iff L.subtype L.subtype_injective]
    rw [hJ0map, hfixσ]
    exact hJ
  haveI : Finite (↥L ⧸ oddCore ↥L) :=
    Finite.of_surjective (QuotientGroup.mk' (oddCore ↥L)) (QuotientGroup.mk'_surjective _)
  have hqL : CFSG.IsQuasisimple ↥L := hL.1
  have hqX : CFSG.IsQuasisimple (↥L ⧸ oddCore ↥L) := isQuasisimple_quotient_oddCore hqL
  haveI : Nontrivial (↥L ⧸ oddCore ↥L) := CFSG.LocalCores.isQuasisimple_nontrivial hqX
  let ρ : ↥L →* (↥L ⧸ oddCore ↥L) := QuotientGroup.mk' (oddCore ↥L)
  have hρker : ρ.ker = oddCore ↥L := QuotientGroup.ker_mk' (oddCore ↥L)
  have hρcov : OddCentralCover ρ := by
    refine ⟨QuotientGroup.mk'_surjective _, ?_, ?_⟩
    · rw [hρker]
      exact sec63PT_oddCore_le_center hqL (MulEquiv.refl _)
    · rw [hρker]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  obtain ⟨α, hαprop, hα2⟩ :=
    sec63PT_exists_induced_aut_quotient (A := ↥L) (P := ↥L ⧸ oddCore ↥L)
      (MulEquiv.refl _) (σ := σ) hσ
  have hρσ : ∀ a : ↥L, ρ (σ a) = α (ρ a) := by
    intro a
    simpa only [ρ, QuotientGroup.mk'_apply, MulEquiv.refl_apply] using hαprop a
  have hmapfix : (fixSub σ).map ρ = fixSub α := sec63PT_map_fixSub hρcov hσ hρσ
  have hJmap : IsComponentIn (J₀.map ρ) (fixSub α) := by
    have h1 := sec63PT_isComponentIn_map ρ hρcov.ker_le_center hJ0
    rwa [hmapfix] at h1
  have hFmap : IsFStarGroup ↥(J₀.map ρ) :=
    h (↥L ⧸ oddCore ↥L) hqX hP α hα2 (J₀.map ρ) hJmap
  haveI : Finite ↥J₀ := Finite.of_injective J₀.subtype J₀.subtype_injective
  haveI : Finite ↥(J₀.map ρ) :=
    Finite.of_injective (J₀.map ρ).subtype (J₀.map ρ).subtype_injective
  have hFJ0 : IsFStarGroup ↥J₀ :=
    l34g_x_isFStarGroup_of_cover (sec63PT_oddCentralCover_subgroupMap hρcov J₀)
      hJ0.isQuasisimple hFmap
  have hthis := l34g_x_inFStar_map_inj L.subtype L.subtype_injective (show InFStar J₀ from hFJ0)
  rwa [hJ0map] at hthis

theorem asc82ClosureAt_of_omegaStar_all {P : (Q : Type) → [Group Q] → Prop} {n : ℕ} {ε : ℤˣ}
    (hP : ∀ (X : Type) [Group X], P X → IsOmegaStar X n ε)
    (hM : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate), Module.finrank (ZMod 3) V = n →
        quadSign Q = ε → ClosureFix ↥(omegaProj hQ)) :
    Asc82ClosureAt P := by
  refine asc82ClosureAt_of_closureFix ?_
  intro X _ _ hq hPX
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨f⟩⟩ := hP X hPX
  letI := i1
  letI := i2
  letI := i3
  exact closureFix_of_mulEquiv f.symm (hM V Q hQ hdim hs)

theorem asc82ClosureAt_of_omegaStar {P : (Q : Type) → [Group Q] → Prop} {n : ℕ} {ε : ℤˣ}
    (hP : ∀ (X : Type) [Group X], P X → IsOmegaStar X n ε) (hn : 2 ≤ n)
    {V₀ : Type} [AddCommGroup V₀] [Module (ZMod 3) V₀] [FiniteDimensional (ZMod 3) V₀]
    {Q₀ : QuadraticForm (ZMod 3) V₀} (hQ₀ : Q₀.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V₀ = n) (hs : quadSign Q₀ = ε)
    (hM : ClosureFix ↥(omegaProj hQ₀)) : Asc82ClosureAt P := by
  refine asc82ClosureAt_of_closureFix ?_
  intro X _ _ hq hPX
  obtain ⟨f⟩ := IsOmegaStar.nonempty_equiv (hP X hPX) hn hQ₀ hdim hs
  exact closureFix_of_mulEquiv f.symm hM

end CFSG.OddStandard.SmallF3.Omega
