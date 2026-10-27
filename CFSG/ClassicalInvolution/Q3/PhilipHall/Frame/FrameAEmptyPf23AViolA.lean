module

public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf20OmegaA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isUniqueInvolution_core (hΩ : HypOmegaGen Ω) {J C P : Subgroup G} {z : G} (hJ : J ∈ Ω)
    (hP : IsSylow2In P J) (hPC : P ≤ C) (hz : IsUniqueInvolution J z) :
    IsUniqueInvolution (tightCore (J ⊓ C)) z := by
  obtain ⟨z', hz', hzm, -, -⟩ := member_data hΩ hJ hP hPC
  have : z = z' := hz.eq hz'
  subst this
  exact isUniqueInvolution_mono hz ((tightCore_le _).trans inf_le_left) hzm

theorem isSylow2In_of_core (hΩ : HypOmegaGen Ω) {J C P₀ R : Subgroup G} (hJ : J ∈ Ω)
    (hP₀ : IsSylow2In P₀ J) (hP₀C : P₀ ≤ C) (hR : IsSylow2In R (tightCore (J ⊓ C))) :
    IsSylow2In R J := by
  obtain ⟨-, -, -, hS, -⟩ := member_data hΩ hJ hP₀ hP₀C
  have hRJ : R ≤ J := hR.1.trans ((tightCore_le _).trans inf_le_left)
  have hcard : Nat.card P₀ ≤ Nat.card R := (natCard_eq_of_isSylow2In hS hR).ge
  exact hP₀.of_natCard_le hR.2.1 hRJ hcard

theorem core_ne_of_ne (hΩ : HypOmegaGen Ω) {J M C P : Subgroup G} (hM : M ∈ Ω) (hJ : J ∈ Ω)
    (hP : IsSylow2In P M) (hPC : P ≤ C) (hne : J ≠ M) :
    tightCore (J ⊓ C) ≠ tightCore (M ⊓ C) := by
  intro h
  obtain ⟨-, -, -, hS, -⟩ := member_data hΩ hM hP hPC
  have hP8 : 8 ≤ Nat.card P := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hP)
  have hle : P ≤ J := hS.1.trans (by rw [← h]; exact (tightCore_le _).trans inf_le_left)
  have := Sec6Gen.card_le_two_of_le_inf hΩ hM hJ hne.symm hP.2.1 hP.1 hle
  omega

end Core

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem aViol_omegaAFam (hΩ : HypOmegaGen Ω) {c : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω) (hv : AViol Ω M J zM zJ)
    (hMc : c ∈ trivialOnQuot M) (hJc : c ∈ trivialOnQuot J) :
    ∃ zK zL : ↥(Subgroup.centralizer ({c} : Set G)),
      AViol (omegaAFam Ω (Subgroup.centralizer ({c} : Set G)))
        ((tightCore (M ⊓ Subgroup.centralizer ({c} : Set G))).subgroupOf
          (Subgroup.centralizer ({c} : Set G)))
        ((tightCore (J ⊓ Subgroup.centralizer ({c} : Set G))).subgroupOf
          (Subgroup.centralizer ({c} : Set G))) zK zL := by
  set C : Subgroup G := Subgroup.centralizer ({c} : Set G) with hC
  have hJΩ : J ∈ Ω := hv.mem
  obtain ⟨PM, hPM, hPMC⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hMc
  obtain ⟨PJ, hPJ, hPJC⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hJc
  have hKmem : tightCore (M ⊓ C) ∈ omegaACore Ω C := ⟨M, hM, ⟨PM, hPM, hPMC⟩, rfl⟩
  have hJmem0 : tightCore (J ⊓ C) ∈ omegaACore Ω C := ⟨J, hJΩ, ⟨PJ, hPJ, hPJC⟩, rfl⟩
  have hKY : tightCore (M ⊓ C) ≤ C := (tightCore_le _).trans inf_le_right
  have hJY : tightCore (J ⊓ C) ≤ C := (tightCore_le _).trans inf_le_right
  have hΛ : HypOmegaGen (omegaAFam Ω C) := hypOmegaGen_omegaAFam hΩ C
  have hzM : IsUniqueInvolution (tightCore (M ⊓ C)) zM :=
    isUniqueInvolution_core hΩ hM hPM hPMC hv.hzK
  have hzJ : IsUniqueInvolution (tightCore (J ⊓ C)) zJ :=
    isUniqueInvolution_core hΩ hJΩ hPJ hPJC hv.hzJ
  have hne : tightCore (J ⊓ C) ≠ tightCore (M ⊓ C) :=
    core_ne_of_ne hΩ hM hJΩ hPM hPMC hv.ne
  have hJmem : (tightCore (J ⊓ C)).subgroupOf C ∈ omegaAFam Ω C :=
    subgroupOf_mem_restrictFamily hJmem0 hJY
  obtain ⟨-, -, U₀, hU₀, hU₀J, hU₀N⟩ := hv.star
  obtain ⟨R₀, hR₀rs, hU₀R₀, hcyc₀, hidx₀⟩ := id hU₀
  obtain ⟨J₁, hJ₁, hR₀J₁⟩ := exists_isSylow2In_of_mem_RSet hR₀rs
  have hJ₁J : J₁ = J := Sec6Gen.eq_of_mem_USet hΩ hU₀ hJ₁ hJΩ (hU₀R₀.trans hR₀J₁.1) hU₀J
  rw [hJ₁J] at hR₀J₁
  have hU₀2 : IsPGroup 2 U₀ := hR₀J₁.2.1.to_le hU₀R₀
  obtain ⟨x, hx, hxc⟩ := AscAET.exists_conj_centralized hc2 hJc hMc.1 hU₀2 hU₀J hU₀N
  have hxJ : x ∈ J := hx.1
  have hxM : x ∈ Subgroup.normalizer (M : Set G) := hx.2
  have hR₁ : IsSylow2In (conjSub x R₀) J := by
    have := hR₀J₁.conj x
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hU₁R₁ : conjSub x U₀ ≤ conjSub x R₀ := conjSub_mono hU₀R₀
  have hcard₁ : Nat.card (conjSub x R₀) = 2 * Nat.card (conjSub x U₀) := by
    rw [natCard_conjSub, natCard_conjSub]
    have h1 := Subgroup.relIndex_mul_card U₀ R₀
    rw [inf_eq_left.mpr hU₀R₀, hidx₀] at h1
    omega
  have hrel₁ : (conjSub x U₀).relIndex (conjSub x R₀) = 2 :=
    AscAET.relIndex_eq_two_of_card hU₁R₁ hcard₁
  have hcyc₁ : IsCyclic ↥(conjSub x U₀) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U₀ (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective)).mp hcyc₀
  obtain ⟨P, hPJ', hU₁P, hPc⟩ :=
    AscAET.exists_sylow_centralized_over hc2 hJc hR₁ hU₁R₁ hrel₁ hxc
  have hPJc : IsSylow2In P (tightCore (J ⊓ C)) := by
    obtain ⟨-, -, -, hS, -⟩ := member_data hΩ hJΩ hPJ' hPc
    exact hS
  have hcardP : Nat.card P = 2 * Nat.card (conjSub x U₀) := by
    rw [hPJ'.natCard_eq hR₁]
    exact hcard₁
  have hrelP : (conjSub x U₀).relIndex P = 2 := AscAET.relIndex_eq_two_of_card hU₁P hcardP
  have hUΛ : (conjSub x U₀).subgroupOf C ∈ USet (omegaAFam Ω C) :=
    AscAET.mem_USet_restrict_of_sylow hJmem0 hJY hPJc hU₁P hcyc₁ hrelP
  have hUJ : (conjSub x U₀).subgroupOf C ≤ (tightCore (J ⊓ C)).subgroupOf C :=
    Subgroup.subgroupOf_mono _ (hU₁P.trans hPJc.1)
  have hUN : (conjSub x U₀).subgroupOf C ≤
      Subgroup.normalizer (((tightCore (M ⊓ C)).subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro u hu
    have hu1 : (u : G) ∈ conjSub x U₀ := Subgroup.mem_subgroupOf.mp hu
    have hN : (u : G) ∈ Subgroup.normalizer (M : Set G) := by
      have h0 : x⁻¹ * (u : G) * x ∈ U₀ := mem_conjSub_iff.mp hu1
      have e : (u : G) = x * (x⁻¹ * (u : G) * x) * x⁻¹ := by group
      rw [e]
      exact (Subgroup.normalizer (M : Set G)).mul_mem
        ((Subgroup.normalizer (M : Set G)).mul_mem hxM (hU₀N h0))
        ((Subgroup.normalizer (M : Set G)).inv_mem hxM)
    refine (mem_normalizer_subgroupOf_iff hKY).mp ?_
    have huC : (u : G) ∈ C := hxc hu1
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hconj : conjSub (u : G) (tightCore (M ⊓ C)) = tightCore (M ⊓ C) := by
      rw [conjSub_tightCore]
      congr 1
      ext w
      simp only [mem_conjSub_iff, Subgroup.mem_inf]
      have hMn : ∀ w : G, (u : G)⁻¹ * w * (u : G) ∈ M ↔ w ∈ M := fun w => by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (M : Set G)).inv_mem hN) w)
        simpa using this.symm
      have hCn : ∀ w : G, (u : G)⁻¹ * w * (u : G) ∈ C ↔ w ∈ C := fun w => by
        constructor
        · intro h
          have := C.mul_mem (C.mul_mem huC h) (C.inv_mem huC)
          simpa [mul_assoc] using this
        · intro h
          exact C.mul_mem (C.mul_mem (C.inv_mem huC) h) huC
      rw [hMn w, hCn w]
    constructor
    · intro hy
      have h1 : (u : G) * y * (u : G)⁻¹ ∈ conjSub (u : G) (tightCore (M ⊓ C)) :=
        conj_mem_conjSub hy
      rwa [hconj] at h1
    · intro hy
      have h1 := conj_mem_conjSub (n := (u : G)⁻¹) hy
      have hconj' : conjSub ((u : G)⁻¹) (tightCore (M ⊓ C)) = tightCore (M ⊓ C) := by
        have := congrArg (conjSub ((u : G)⁻¹)) hconj
        rw [conjSub_inv_conjSub] at this
        exact this.symm
      rw [hconj'] at h1
      simpa [mul_assoc] using h1
  have hnot : (tightCore (J ⊓ C)).subgroupOf C ∉
      omegaNbr (omegaAFam Ω C) ((tightCore (M ⊓ C)).subgroupOf C) := by
    rintro ⟨-, -, R', hR', hR'J, hR'N⟩
    have hR'syl : IsSylow2In R' ((tightCore (J ⊓ C)).subgroupOf C) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΛ hJmem hR' hR'J
    have hmap : IsSylow2In (R'.map C.subtype) (tightCore (J ⊓ C)) := by
      have h1 := isSylow2In_map_subtype_iff.mpr hR'syl
      rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at h1
    have hRN : R'.map C.subtype ≤ Subgroup.normalizer ((tightCore (M ⊓ C) : Subgroup G) : Set G) := by
      have h1 := map_le_normalizer_map hR'N
      rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
    have hRz : R'.map C.subtype ≤ Subgroup.centralizer ({zM} : Set G) :=
      T3.le_centralizer_of_le_normalizer' hzM hRN
    have hRJ : IsSylow2In (R'.map C.subtype) J := isSylow2In_of_core hΩ hJΩ hPJ hPJC hmap
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJΩ hRJ)
    have hRM : R'.map C.subtype ≤ Subgroup.normalizer (M : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hM hJΩ hv.ne.symm hv.hzK hRJ.1 hRJ.2.1
        (by omega) hRz
    exact hv.not_nbr ⟨hJΩ, hv.ne, _, mem_RSet_of_isSylow2In hJΩ hRJ, hRJ.1, hRM⟩
  have hnoc : ∀ g ∈ pairNormalizers ((tightCore (M ⊓ C)).subgroupOf C)
      ((tightCore (J ⊓ C)).subgroupOf C) ⟨zM, hKY hzM.mem⟩ ⟨zJ, hJY hzJ.mem⟩,
      conjSub g ((tightCore (M ⊓ C)).subgroupOf C) ≠ (tightCore (J ⊓ C)).subgroupOf C := by
    intro g hg hgK
    have hgG : (g : G) ∈ pairNormalizers M J zM zJ := by
      have h1 := T3Core.map_pairNormalizers_subgroupOf_le hKY hJY ⟨zM, hKY hzM.mem⟩
        ⟨zJ, hJY hzJ.mem⟩ ⟨g, hg, rfl⟩
      exact AscAET.pairNormalizers_mono ((tightCore_le _).trans inf_le_left)
        ((tightCore_le _).trans inf_le_left) h1
    have hgC : (g : G) ∈ C := g.2
    have hCn : conjSub (g : G) C = C := conjSub_eq_self_of_mem hgC
    have hinf : ∀ L : Subgroup G, conjSub (g : G) (L ⊓ C) = conjSub (g : G) L ⊓ C := by
      intro L
      ext y
      simp only [mem_conjSub_iff, Subgroup.mem_inf]
      have : ∀ y : G, (g : G)⁻¹ * y * (g : G) ∈ C ↔ y ∈ C := fun y => by
        constructor
        · intro h
          have := C.mul_mem (C.mul_mem hgC h) (C.inv_mem hgC)
          simpa [mul_assoc] using this
        · intro h
          exact C.mul_mem (C.mul_mem (C.inv_mem hgC) h) hgC
      rw [this y]
    have hcgY : conjSub (g : G) (tightCore (M ⊓ C)) ≤ C := by
      have := conjSub_mono (n := (g : G)) hKY
      rwa [hCn] at this
    have h2 : conjSub (g : G) (tightCore (M ⊓ C)) = tightCore (J ⊓ C) := by
      have h3 : (conjSub (g : G) (tightCore (M ⊓ C))).subgroupOf C =
          (tightCore (J ⊓ C)).subgroupOf C := by
        rw [← conjSub_subgroupOf]
        exact hgK
      have h4 := Subgroup.subgroupOf_inj.mp h3
      rwa [inf_eq_left.mpr hcgY, inf_eq_left.mpr hJY] at h4
    rw [conjSub_tightCore, hinf] at h2
    have hgM : conjSub (g : G) M ∈ Ω := hΩ.conjInvariant _ M hM
    have hgP : IsSylow2In (conjSub (g : G) PM) (conjSub (g : G) M) :=
      Sec6Gen.isSylow2In_conjSub hPM _
    have hgPC : conjSub (g : G) PM ≤ C := by
      have := conjSub_mono (n := (g : G)) hPMC
      rwa [hCn] at this
    have heq : conjSub (g : G) M = J := by
      by_contra hne'
      exact core_ne_of_ne hΩ hgM hJΩ hgP hgPC (Ne.symm hne') h2.symm
    exact hv.no_conj g hgG heq
  exact ⟨⟨zM, hKY hzM.mem⟩, ⟨zJ, hJY hzJ.mem⟩,
    { star := ⟨hJmem, subgroupOf_ne_of_ne hKY hJY hne, _, hUΛ, hUJ, hUN⟩
      not_nbr := hnot
      hzK := isUniqueInvolution_subgroupOf hzM hKY
      hzJ := isUniqueInvolution_subgroupOf hzJ hJY
      no_conj := hnoc }⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
