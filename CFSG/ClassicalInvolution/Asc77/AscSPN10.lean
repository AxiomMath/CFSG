module

public import CFSG.ClassicalInvolution.Asc77.AscSPN9
public import CFSG.ClassicalInvolution.Asc77.AscSPN8
public import CFSG.ClassicalInvolution.Asc77.AscT7PE
public import CFSG.ClassicalInvolution.Asc77.AscT7W13

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.T7P
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped commutatorElement

namespace SPN

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}


@[expose] def SpinGenOn (t : StatedLieTag) (M : CFSG.LieType.Universal.LieUniversal) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K),
    TwinPairOn t M ψ R R' x x' → ∀ s ∈ Subgroup.normalizer (ψ.range : Set H), s * s = 1 →
      (∀ r ∈ R, s * ψ r = ψ r * s) → (∀ r ∈ R', s * ψ r = ψ r * s) →
      (∀ y ∈ ψ.range, s * y = y * s) ∨
      (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x}))

variable (p) in
@[expose] def SpinGen : Prop :=
  p ≠ 2 → ∀ (t : StatedLieTag) (n e : ℕ), SpinTag t n → StatedLieAdmissible t n p e →
    5 ≤ p ^ e → SpinGenOn t (modelUniv t n p e Fact.out)

theorem exactLayer_le_sigmaNorm_of_gen (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hzC : z ∈ Subgroup.centralizer ({u} : Set G)) (htC : t ∈ Subgroup.centralizer ({u} : Set G))
    (A : Subgroup (OddQuot u)) (τ : OddQuot u) (hτ : τ = oddQuotMk u ⟨t, htC⟩)
    (hA : (layerToOddQuot (exactFamily Ω u) u).range = A)
    (hgen : ∀ q ∈ A, q ∈ Subgroup.closure
      ({q | q ∈ A ∧ oddQuotMk u ⟨z, hzC⟩ * q = q * oddQuotMk u ⟨z, hzC⟩} ∪
        {q | q ∈ A ∧ τ * q = q * τ})) :
    exactLayer Ω u ≤ sigmaNorm Ω K := by
  subst hτ
  have hst := h.std.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hz2 : z * z = 1 := h.std.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have hN : NormalizesLayer (exactFamily Ω u) u := normalizesLayer_exactFamily hΩ.conjInvariant
  have hzN : z ∈ Subgroup.normalizer ((centLayer (exactFamily Ω u) u : Subgroup G) : Set G) :=
    hN z hzC
  have htN : t ∈ Subgroup.normalizer ((centLayer (exactFamily Ω u) u : Subgroup G) : Set G) :=
    hN t htC
  have hker : (layerToOddQuot (exactFamily Ω u) u).ker =
      classicalInvolutionOddCore ↥(centLayer (exactFamily Ω u) u) :=
    ker_layerToOddQuot_of_normalizes hN
  have hodd : Odd (Nat.card (layerToOddQuot (exactFamily Ω u) u).ker) := by
    rw [hker]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hact : ∀ (c : G) (hcC : c ∈ Subgroup.centralizer ({u} : Set G))
      (hcN : c ∈ Subgroup.normalizer ((centLayer (exactFamily Ω u) u : Subgroup G) : Set G))
      (y : ↥(centLayer (exactFamily Ω u) u)),
      layerToOddQuot (exactFamily Ω u) u (conjOn (centLayer (exactFamily Ω u) u) c hcN y) =
        oddQuotMk u ⟨c, hcC⟩ * layerToOddQuot (exactFamily Ω u) u y * (oddQuotMk u ⟨c, hcC⟩)⁻¹ := by
    intro c hcC hcN y
    have e : (⟨((conjOn (centLayer (exactFamily Ω u) u) c hcN y : ↥(centLayer (exactFamily Ω u) u))
        : G), centLayer_le_centralizer (exactFamily Ω u) u
          (conjOn (centLayer (exactFamily Ω u) u) c hcN y).2⟩ :
          ↥(Subgroup.centralizer ({u} : Set G))) =
        ⟨c, hcC⟩ * ⟨y, centLayer_le_centralizer (exactFamily Ω u) u y.2⟩ * ⟨c, hcC⟩⁻¹ := rfl
    rw [layerToOddQuot_apply, layerToOddQuot_apply, e, map_mul, map_mul, map_inv]
  have hYr : rLayer Ω u = centLayer (exactFamily Ω u) u := rLayer_eq_exactLayer hp hq hΩ h.hu2
  have hlift : ∀ (c : G) (hcC : c ∈ Subgroup.centralizer ({u} : Set G)), c * c = 1 →
      Subgroup.centralizer ({c} : Set G) ≤ sigmaNorm Ω K → ∀ q ∈ A,
      oddQuotMk u ⟨c, hcC⟩ * q = q * oddQuotMk u ⟨c, hcC⟩ →
        ∃ y : ↥(centLayer (exactFamily Ω u) u),
          layerToOddQuot (exactFamily Ω u) u y = q ∧ (y : G) ∈ sigmaNorm Ω K := by
    intro c hcC hc2 hcS q hq' hcomm
    have hqs : oddQuotMk u ⟨c, hcC⟩ * q * (oddQuotMk u ⟨c, hcC⟩)⁻¹ = q := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
    obtain ⟨y, hy1, hy2⟩ := exists_fixed_lift (centLayer (exactFamily Ω u) u)
      (layerToOddQuot (exactFamily Ω u) u) hodd c (hN c hcC) hc2 (oddQuotMk u ⟨c, hcC⟩)
      (hact c hcC (hN c hcC)) (by rw [hA]; exact hq') hqs
    exact ⟨y, hy1, hcS (Subgroup.mem_centralizer_singleton_iff.mpr hy2.symm)⟩
  refine le_of_closure (centLayer (exactFamily Ω u) u) (layerToOddQuot (exactFamily Ω u) u)
    (sigmaNorm Ω K) (oddQuotMk u ⟨z, hzC⟩) (oddQuotMk u ⟨t, htC⟩) ?_ ?_ ?_ ?_
  · intro q hq' hcomm
    exact hlift z hzC hz2 (centralizer_z_le_sigmaNorm h) q (by rw [← hA]; exact hq') hcomm
  · intro q hq' hcomm
    exact hlift t htC ht2 (centralizer_t_le_sigmaNorm h) q (by rw [← hA]; exact hq') hcomm
  · intro n hn
    rw [hker] at hn
    have hnO : (n : G) ∈ oddCoreOf (rLayer Ω u) := by
      rw [hYr]
      exact ⟨n, hn, rfl⟩
    exact oddCore_rLayer_le_sigmaNorm h hα hnO
  · intro q hq'
    rw [hA] at hq' ⊢
    exact hgen q hq'

theorem spinTrivial_of_spinGen (hG : SpinGen p) (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hne : dComp Ω K ≠ dstarComp Ω K) (hspin : T7P.SpinSection p f Ω u) :
    (∀ y ∈ rLayer Ω u, z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) ∨
      (∀ y ∈ rLayer Ω u, (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) := by
  have hs : TwinFrameSetting p f Ω K K' J z u t := TwinFrameSetting.of_hyp21 p f h
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hz := hd.hz
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hBab := twinFrame_isElemAbelian hp hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hc : UCoset z u t u := Or.inl rfl
  have hcc : u * u = 1 := hd.hu2
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hcc
  obtain ⟨J', hJ'tw, hJ'ne⟩ := hs.exists_twin_J
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJt : IsUniqueInvolution J t := hd.ht
  have hJ't : IsUniqueInvolution J' t := by
    obtain ⟨t', hJt', hJ't'⟩ := hJ'tw.2
    have : t' = t := hJt'.eq hJt
    rwa [this] at hJ't'
  have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hJt
  have hcJ' : IsClassicalMember p f J' t := isClassicalMember_of_twin hΩ hJ'Ω hJ't
  have hMJ : J ∈ tqMembers Ω u := ⟨hJΩ, hs.tq_uc hc hJΩ hJt⟩
  have hMJ' : J' ∈ tqMembers Ω u := ⟨hJ'Ω, hs.tq_uc hc hJ'Ω hJ't⟩
  obtain ⟨D, hcard, j, hspinj⟩ := hspin
  have hs' : SecData p f u (exactFamily Ω u) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨J, hMJ⟩
  obtain ⟨hbY, hKJ, hKJ', hneKJ, hzKJ, hzKJ'⟩ :=
    secFam_twin hp hq hΩ hc2 hMJ hMJ' hcJ hcJ' hJ'ne
  let hDl : OmegaLie p f (secFam Ω u) := LieSystemData.toOmegaLie D (omegaGen_secFam hs')
  have hsurj : Function.Surjective (D.hom j) :=
    hDl.hom_surjective_of_gen hcard (omegaGen_secFam hs') j
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hrange : ψ.range = memberJoin (exactFamily Ω u) u := by
    rw [← range_sectionQuotientHom (normalizesLayer_exactFamily hΩ.conjInvariant)]
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨D.hom j k, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := hsurj q
      exact ⟨k, rfl⟩
  have hMj : modOdd u (exactCore u J) ≤ ψ.range := by
    rw [hrange]
    exact modOdd_le_exactJoin (exactCore_mem_exactFamily hMJ)
  have hM'j : modOdd u (exactCore u J') ≤ ψ.range := by
    rw [hrange]
    exact modOdd_le_exactJoin (exactCore_mem_exactFamily hMJ')
  have hG2 : D.tag j ≠ .G2 := by
    rcases hspinj with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hD4 : D.tag j ≠ .trialityD4 := by
    rcases hspinj with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  obtain ⟨htC, R, R', x₁, x₁', hpair, hshape, hRM, hR'M, hψx₁⟩ :=
    T7S2R.vertexTwin' hp hq hΩ hc2 hBab huB (b := t) htB hMJ hMJ' hcJ hcJ' hJ'ne D j hMj hM'j
      hG2 hD4
  have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
  have hzC : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hBab huB hzB
  obtain ⟨RK, RK', hRK, hRK', hcommK, hRKt, hRK't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
  have hxy_c : x * y = y * x := hcommK x hx y hy
  have hxu : x * u = u * x := by
    rw [← hxy]
    calc x * (x * y) = x * (y * x) := by rw [hxy_c]
      _ = (x * y) * x := by group
  have hxC : x ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxu
  have hxJ : x ∈ trivialOnQuot J :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJΩ hz hJt hd.t_ne_z.symm hRK hRKt hx
  have hxJ' : x ∈ trivialOnQuot J' :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJ'Ω hz hJ't hd.t_ne_z.symm hRK hRKt hx
  have hqs : ∀ R₀ : Subgroup (compModel D j).K,
      R₀ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D →
        CFSG.Open.IsQuasisimple ↥(R₀.map ψ) := fun R₀ hR₀ =>
    isQuasisimple_map_of_ker_le_center ψ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (by omega) R₀ hR₀)
  have hqJ : CFSG.Open.IsQuasisimple ↥(modOdd u (exactCore u J)) := by
    rw [← hRM]
    exact hqs R hpair.mem
  have hqJ' : CFSG.Open.IsQuasisimple ↥(modOdd u (exactCore u J')) := by
    rw [← hR'M]
    exact hqs R' hpair.mem'
  have hcommJ := oddQuotMk_centralizes_modOdd_exactCore hcJ hc2 hMJ.2 hxJ hxC hqJ
  have hcommJ' := oddQuotMk_centralizes_modOdd_exactCore hcJ' hc2 hMJ'.2 hxJ' hxC hqJ'
  have hNormal : (ψ.range).Normal := by
    rw [hrange]
    exact memberJoin_normal_of_normalizes (normalizesLayer_exactFamily hΩ.conjInvariant)
  have hxn : oddQuotMk u ⟨x, hxC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
    have := hNormal
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hxx : oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ = oddQuotMk u ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hx2
  have hzn : oddQuotMk u ⟨z, hzC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
    rw [← hxx]
    exact Subgroup.mul_mem _ hxn hxn
  have hzz : oddQuotMk u ⟨z, hzC⟩ * oddQuotMk u ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = 1 :=
      Subtype.ext hz.sq
    rw [this, map_one]
  have htt : oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨t, htC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = 1 :=
      Subtype.ext hJt.sq
    rw [this, map_one]
  have hzR : ∀ r ∈ R, oddQuotMk u ⟨z, hzC⟩ * ψ r = ψ r * oddQuotMk u ⟨z, hzC⟩ := by
    intro r hr
    have hr' : ψ r ∈ modOdd u (exactCore u J) := hRM ▸ Subgroup.mem_map_of_mem ψ hr
    have h1 := hcommJ (ψ r) hr'
    rw [← hxx]
    calc oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ * ψ r
        = oddQuotMk u ⟨x, hxC⟩ * (oddQuotMk u ⟨x, hxC⟩ * ψ r) := mul_assoc _ _ _
      _ = oddQuotMk u ⟨x, hxC⟩ * (ψ r * oddQuotMk u ⟨x, hxC⟩) := by rw [h1]
      _ = oddQuotMk u ⟨x, hxC⟩ * ψ r * oddQuotMk u ⟨x, hxC⟩ := (mul_assoc _ _ _).symm
      _ = ψ r * oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ := by rw [h1]
      _ = ψ r * (oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩) := mul_assoc _ _ _
  have hzR' : ∀ r ∈ R', oddQuotMk u ⟨z, hzC⟩ * ψ r = ψ r * oddQuotMk u ⟨z, hzC⟩ := by
    intro r hr
    have hr' : ψ r ∈ modOdd u (exactCore u J') := hR'M ▸ Subgroup.mem_map_of_mem ψ hr
    have h1 := hcommJ' (ψ r) hr'
    rw [← hxx]
    calc oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ * ψ r
        = oddQuotMk u ⟨x, hxC⟩ * (oddQuotMk u ⟨x, hxC⟩ * ψ r) := mul_assoc _ _ _
      _ = oddQuotMk u ⟨x, hxC⟩ * (ψ r * oddQuotMk u ⟨x, hxC⟩) := by rw [h1]
      _ = oddQuotMk u ⟨x, hxC⟩ * ψ r * oddQuotMk u ⟨x, hxC⟩ := (mul_assoc _ _ _).symm
      _ = ψ r * oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ := by rw [h1]
      _ = ψ r * (oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩) := mul_assoc _ _ _
  have hMG : SpinGenOn (D.tag j) (compModel D j) :=
    hG hp (D.tag j) (D.rank j) (D.exp j) hspinj (D.admissible j) hq'
  rcases hMG (OddQuot u) ψ R R' x₁ x₁' hpair (oddQuotMk u ⟨z, hzC⟩) hzn hzz hzR hzR' with
    hc1 | hc2' | hc3
  ·
    left
    exact T7S2R.htriv_of_comm_join hp hq hΩ hcc hzC fun y hy' =>
      hc1 y (by rw [hrange]; exact hy')
  ·
    right
    have htzC : t * z ∈ Subgroup.centralizer ({u} : Set G) := Subgroup.mul_mem _ htC hzC
    have hmul : oddQuotMk u ⟨t * z, htzC⟩ = oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨z, hzC⟩ :=
      map_mul (oddQuotMk u) (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) ⟨z, hzC⟩
    have hcomm : ∀ y ∈ memberJoin (exactFamily Ω u) u,
        oddQuotMk u ⟨t * z, htzC⟩ * y = y * oddQuotMk u ⟨t * z, htzC⟩ := by
      intro y hy'
      have hyr : y ∈ ψ.range := by rw [hrange]; exact hy'
      have h1 := hc2' y hyr
      rw [hψx₁] at h1
      rw [hmul]
      have h2 : oddQuotMk u ⟨z, hzC⟩ * y = oddQuotMk u ⟨t, htC⟩ * y * (oddQuotMk u ⟨t, htC⟩)⁻¹ *
          oddQuotMk u ⟨z, hzC⟩ := by
        rw [← h1]
        group
      have hti : (oddQuotMk u ⟨t, htC⟩)⁻¹ = oddQuotMk u ⟨t, htC⟩ := inv_eq_of_mul_eq_one_right htt
      calc oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨z, hzC⟩ * y
          = oddQuotMk u ⟨t, htC⟩ * (oddQuotMk u ⟨z, hzC⟩ * y) := mul_assoc _ _ _
        _ = oddQuotMk u ⟨t, htC⟩ * (oddQuotMk u ⟨t, htC⟩ * y * (oddQuotMk u ⟨t, htC⟩)⁻¹ *
              oddQuotMk u ⟨z, hzC⟩) := by rw [h2]
        _ = (oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨t, htC⟩) * y * (oddQuotMk u ⟨t, htC⟩)⁻¹ *
              oddQuotMk u ⟨z, hzC⟩ := by group
        _ = y * (oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨z, hzC⟩) := by
          rw [htt, hti, one_mul, mul_assoc]
    exact T7S2R.htriv_of_comm_join hp hq hΩ hcc htzC hcomm
  ·
    exfalso
    obtain ⟨r, hrY, hrS⟩ := exists_r_not_sigmaNorm h hne
    refine hrS (exactLayer_le_sigmaNorm_of_gen h hα hzC htC ψ.range (oddQuotMk u ⟨t, htC⟩) rfl
      ?_ ?_ ?_)
    · rw [range_layerToOddQuot_eq, hrange]
    · intro q hq'
      have := hc3 q hq'
      rw [hψx₁] at this
      exact this
    · rw [rLayer_eq_exactLayer hp hq hΩ hcc] at hrY
      exact hrY


theorem spinSectionConn_of_spinGen (hG : SpinGen p) : T7P.SpinSectionConn p f := by
  intro G _ _ _ Ω K K' z u J t W h huW hα hne hconn hspin
  have hC3 : C21_3 p f := c21_3_of_hyp51 (twinFrameHyp51t_proved (twinSmallInner_rows_proved p))
    (twinFrameHyp51u_proved (twinSmallOuter_rows_proved p))
  rcases spinTrivial_of_spinGen hG h hα hne hspin with htriv | htriv
  · left
    exact h.rLayer_u_le_sigmaGen_of_trivial hα (c₀ := z) (Or.inl rfl) htriv
      fun R hR hRz => h.rSet_le_sigmaGen_of_le_centralizer hR hRz
  · right
    have hY := h.rLayer_u_le_centralizer_tz_of_trivial hC3 hα htriv
    refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
    have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR (le_iSup_of_le hRc le_rfl)
    exact le_iSup₂_of_le R hR (le_iSup_of_le (hRY.trans hY) le_rfl)

end SPN

end CFSG.ClassicalInvolution.Asc77
