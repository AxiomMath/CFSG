module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfExt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfSplit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentSingular
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Abstract

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {q : QuadraticForm (ZMod 2) W}

theorem exists_order_three_of_totSing (hq : (polarBilin q).Nondegenerate) {c : ℕ} (hc : 3 ≤ c)
    (hdim : finrank (ZMod 2) W = 2 * c)
    (hT : ∃ T : Submodule (ZMod 2) W, 3 ≤ finrank (ZMod 2) T ∧ ∀ y ∈ T, q y = 0) :
    Group.IsPerfect (elementaryGroup q) ∧ ∃ ρ ∈ elementaryGroup q, orderOf ρ = 3 := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := exists_three_hypPairs hq hT3 hTs
  refine ⟨⟨commutator_elementaryGroup_eq_top h12 h13 h23 hq⟩, ?_⟩
  obtain ⟨P, -, -⟩ := exists_aniso_pair_of_two_le (W := ⊤) (polarNondegOn_top hq) (c := c)
    (by omega) (by rw [finrank_top]; exact hdim)
  have hmem : P.rot ∈ elementaryGroup q :=
    mem_elementaryGroup_of_pow_three hq (by omega) h12 P.rot_mem P.rot_pow_three
  refine ⟨P.rot, hmem, orderOf_eq_prime P.rot_pow_three fun h1 => P.rot_a_ne ?_⟩
  rw [h1]
  rfl

theorem exists_totSing_or_three_planes (hq : (polarBilin q).Nondegenerate) {c : ℕ} (hc : 3 ≤ c)
    (hdim : finrank (ZMod 2) W = 2 * c) :
    (∃ T : Submodule (ZMod 2) W, 3 ≤ finrank (ZMod 2) T ∧ ∀ y ∈ T, q y = 0) ∨
      (c = 3 ∧ ∃ Ps : List (AnisoPair q), Ps.Pairwise AnisoPair.Orth ∧ Ps.length = 3) := by
  obtain ⟨Ps, hpw, -, hcases⟩ := exists_aniso_pairs_nondeg c (⊤ : Submodule (ZMod 2) W)
    (by rw [finrank_top]; exact hdim) (polarNondegOn_top hq)
  rcases hcases with hlen | ⟨hlen, e, -, he0, heQ, heP⟩
  · by_cases hc4 : 4 ≤ c
    · left
      obtain ⟨T, hT, hle⟩ := exists_totSing_of_pairs Ps ⊥
        (fun y hy => by rw [Submodule.mem_bot] at hy; rw [hy]; exact QuadraticMap.map_zero q)
        hpw (fun y hy P _ => by rw [Submodule.mem_bot] at hy; rw [hy]; simp)
      exact ⟨T, by rw [finrank_bot] at hle; omega, hT⟩
    · right
      exact ⟨by omega, Ps, hpw, by omega⟩
  · left
    obtain ⟨T, hT, hle⟩ := exists_totSing_of_pairs Ps (Submodule.span (ZMod 2) {e})
      (fun y hy => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rw [QuadraticMap.map_smul, heQ, smul_zero]) hpw
      (fun y hy P hP => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        exact ⟨by rw [polar_smul_right_eq, (heP P hP).1, mul_zero],
          by rw [polar_smul_right_eq, (heP P hP).2, mul_zero]⟩)
    rw [finrank_span_singleton he0] at hle
    exact ⟨T, by omega, hT⟩

end Abstract

section Fixed

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

@[expose] noncomputable def fixProj (hx3 : ∀ v, x (x (x v)) = v) :
    V →ₗ[ZMod 2] ↥(fixSpace x) :=
  Submodule.projectionOnto (fixSpace x) (moveSpace x) (isCompl_fix_move hx3)

theorem fixProj_comp_subtype (hx3 : ∀ v, x (x (x v)) = v) :
    fixProj hx3 ∘ₗ (fixSpace x).subtype = LinearMap.id :=
  Submodule.projectionOnto_comp_subtype _

theorem fixProj_ker (hx3 : ∀ v, x (x (x v)) = v) : LinearMap.ker (fixProj hx3) = moveSpace x :=
  Submodule.ker_projectionOnto _

theorem add_fixProj_mem_move (hx3 : ∀ v, x (x (x v)) = v) (v : V) :
    v + (fixSpace x).subtype (fixProj hx3 v) ∈ moveSpace x := by
  rw [← fixProj_ker hx3, LinearMap.mem_ker, map_add]
  have h : fixProj hx3 ((fixSpace x).subtype (fixProj hx3 v)) = fixProj hx3 v :=
    LinearMap.congr_fun (fixProj_comp_subtype hx3) (fixProj hx3 v)
  rw [h]
  exact add_self_eq_zero' _

theorem fixProj_apply_apply (hx3 : ∀ v, x (x (x v)) = v) (v : V) :
    fixProj hx3 (x v) = fixProj hx3 v := by
  have hu := add_fixProj_mem_move hx3 v
  have hxu := apply_mem_moveSpace hx3 hu
  rw [← fixProj_ker hx3, LinearMap.mem_ker] at hxu
  have hfix : x ((fixSpace x).subtype (fixProj hx3 v)) = (fixSpace x).subtype (fixProj hx3 v) :=
    mem_fixSpace.1 (fixProj hx3 v).2
  rw [map_add, hfix] at hxu
  have h : fixProj hx3 ((fixSpace x).subtype (fixProj hx3 v)) = fixProj hx3 v :=
    LinearMap.congr_fun (fixProj_comp_subtype hx3) (fixProj hx3 v)
  rw [map_add, h] at hxu
  exact eq_of_add_eq_zero' hxu

theorem exists_perfect_fix [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) {c : ℕ}
    (hc : 3 ≤ c) (hCdim : finrank (ZMod 2) (fixSpace x) = 2 * c)
    (hT : ∃ T : Submodule (ZMod 2) ↥(fixSpace x), 3 ≤ finrank (ZMod 2) T ∧
      ∀ y ∈ T, (Q.restrict (fixSpace x)) y = 0) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  set C := fixSpace x with hCdef
  have hq : (polarBilin (Q.restrict C)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fix hQ hx hx3)
  obtain ⟨hperf, ρ, hρE, hρ3⟩ := exists_order_three_of_totSing hq hc hCdim hT
  have hcψ := fixProj_comp_subtype hx3
  have hort : ∀ v a, polar Q (v + C.subtype (fixProj hx3 v)) (C.subtype a) = 0 := fun v a => by
    rw [polar_comm]
    exact polar_fix_move hx a.2 (add_fixProj_mem_move hx3 v)
  have hinj : Function.Injective (extHom hcψ) := by
    intro S T hST
    apply LinearEquiv.ext
    intro a
    have h := LinearEquiv.congr_fun hST (C.subtype a)
    rw [extHom_apply, extHom_apply, extEquiv_apply', extEquiv_apply'] at h
    have hc1 : fixProj hx3 (C.subtype a) = a := LinearMap.congr_fun hcψ a
    rw [hc1, add_self_eq_zero', zero_add, zero_add] at h
    exact Subtype.ext h
  have := hperf
  refine ⟨(elementaryGroup (Q.restrict C)).map (extHom hcψ), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨T, hT', rfl⟩
    refine extEquiv_mem_orthogonalGroup hcψ hort fun a => ?_
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (elementaryGroup_le_orthogonalGroup (Q.restrict C) hT') a
    exact this
  · rintro _ ⟨T, hT', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact extEquiv_commute hcψ (τ := LinearEquiv.refl (ZMod 2) ↥C) (T := T)
      (fun a => mem_fixSpace.1 a.2) (fun v => fixProj_apply_apply hx3 v) (fun a => rfl)
  · exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.map (extHom hcψ))
  · rw [Subgroup.card_map_of_injective hinj]
    have := orderOf_dvd_natCard (⟨ρ, hρE⟩ : elementaryGroup (Q.restrict C))
    rwa [Subgroup.orderOf_mk, hρ3] at this

theorem exists_perfect_of_small [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 6 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hws : ∀ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) → finrank (ZMod 2) T ≤ m - 1)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v)
    {PsM : List (AnisoPair Q)} (hlen : PsM.length ≤ 3) (hMpw : PsM.Pairwise AnisoPair.Orth)
    (hMmem : ∀ P ∈ PsM, P.a ∈ moveSpace x ∧ P.b = x P.a)
    (hCdim : finrank (ZMod 2) (fixSpace x) = 2 * (m - PsM.length)) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hc : 3 ≤ m - PsM.length := by omega
  have hq : (polarBilin (Q.restrict (fixSpace x))).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fix hQ hx hx3)
  rcases exists_totSing_or_three_planes hq hc hCdim with hT | ⟨hc3, Ps, hpw, hPs⟩
  · exact exists_perfect_fix hQ hx hx3 hc hCdim hT
  · exfalso
    have hPsM : PsM.length = 3 := by omega
    have hmeq : m = 6 := by omega
    have hpwV : (PsM ++ Ps.map AnisoPair.ofRestrict).Pairwise AnisoPair.Orth := by
      rw [List.pairwise_append]
      refine ⟨hMpw, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hpw.imp fun h => h.ofRestrict
      · intro P hP P' hP'
        obtain ⟨P'', -, rfl⟩ := List.mem_map.1 hP'
        exact orth_of_split hx hx3 (hMmem P hP) ⟨P''.a.2, P''.b.2⟩
    obtain ⟨T, hT, hle⟩ := exists_totSing_of_pairs (PsM ++ Ps.map AnisoPair.ofRestrict) ⊥
      (fun y hy => by rw [Submodule.mem_bot] at hy; rw [hy]; exact QuadraticMap.map_zero Q)
      hpwV (fun y hy P _ => by rw [Submodule.mem_bot] at hy; rw [hy]; simp)
    have h1 := hws T hT
    rw [finrank_bot, List.length_append, List.length_map] at hle
    omega

end Fixed

end CFSG.AGLEmbedding.OmegaMinusPerf
