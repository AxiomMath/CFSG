module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwo

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

section
open scoped commutatorElement

private lemma commutatorElement_mul_center_eq {G : Type*} [Group G] {p a q b : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G) :
    ⁅p * a, q * b⁆ = ⁅p, q⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    Commute.commutator_eq (Subgroup.mem_center_iff.mp ha (q * b)).symm,
    commutatorElement_mul_right_eq_mul_conj,
    Commute.commutator_eq (Subgroup.mem_center_iff.mp hb p)]
  group

end

private theorem slTwoOver_of_mulEquiv {q : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : HarrisLit.IsSLTwoOver q A) : HarrisLit.IsSLTwoOver q B := by
  obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := h
  exact ⟨F, hF, hFt, hFq, ⟨e.symm.trans eA⟩⟩

theorem exists_sl2_cover (hGA : TBLit.GriessMultipliersOdd) {M G : Type} [Group M] [Group G]
    [Finite M] (φ : M →* G) (hker : φ.ker ≤ center M) (hZ : IsPGroup 2 ↥(center M))
    {N : Subgroup G} (hN : N ≤ φ.range) {q₀ : ℕ} (hq : Odd q₀) (h5 : 5 ≤ q₀)
    (hSL : HarrisLit.IsSLTwoOver q₀ ↥N) :
    ∃ P : Subgroup M, ⁅P, P⁆ = P ∧ HarrisLit.IsSLTwoOver q₀ ↥P ∧ P.map φ = N ∧
      Function.Injective (φ.comp P.subtype) := by
  classical
  have hNperf : Group.IsPerfect ↥N := isPerfect_of_isSLTwoOver h5 hSL
  have hNN : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hNperf
  set P₀ : Subgroup M := N.comap φ with hP₀def
  set P : Subgroup M := ⁅P₀, P₀⁆ with hPdef
  have hP₀map : P₀.map φ = N := by
    rw [hP₀def, Subgroup.map_comap_eq, inf_eq_right.mpr hN]
  have hPmap : P.map φ = N := by
    rw [hPdef, Subgroup.map_commutator, hP₀map, hNN]
  have hPcomm : ⁅P, P⁆ = P := by
    refine le_antisymm (by simpa using Subgroup.commutator_le_sup P P) ?_
    rw [hPdef]
    refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    obtain ⟨p, hp, hpφ⟩ : ∃ p ∈ P, φ p = φ x := by
      refine Subgroup.mem_map.mp ?_
      rw [hPmap]
      exact hP₀map ▸ Subgroup.mem_map_of_mem φ hx
    obtain ⟨q, hq', hqφ⟩ : ∃ q ∈ P, φ q = φ y := by
      refine Subgroup.mem_map.mp ?_
      rw [hPmap]
      exact hP₀map ▸ Subgroup.mem_map_of_mem φ hy
    have ha : p⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpφ, inv_mul_cancel]
    have hb : q⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqφ, inv_mul_cancel]
    have hxeq : x = p * (p⁻¹ * x) := by group
    have hyeq : y = q * (q⁻¹ * y) := by group
    rw [hxeq, hyeq, commutatorElement_mul_center_eq (hker ha) (hker hb)]
    have hmem := Subgroup.commutator_mem_commutator hp hq'
    rwa [hPdef] at hmem
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPcomm
  have hrange : ∀ x : P, φ (x : M) ∈ N := fun x => by
    rw [← hPmap]
    exact Subgroup.mem_map_of_mem φ x.2
  set ρ : P →* N := (φ.comp P.subtype).codRestrict N hrange with hρdef
  have hρker : ρ.ker = (φ.ker).comap P.subtype := by
    rw [hρdef]
    exact (MonoidHom.ker_codRestrict (φ.comp P.subtype) N hrange).trans
      (MonoidHom.comap_ker φ P.subtype).symm
  have hρker_center : ρ.ker ≤ center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxker : (x : M) ∈ φ.ker := by
      have hx' : x ∈ (φ.ker).comap P.subtype := hρker ▸ hx
      exact Subgroup.mem_comap.mp hx'
    show (y : M) * (x : M) = (x : M) * (y : M)
    exact Subgroup.mem_center_iff.mp (hker hxker) (y : M)
  have hρker2 : IsPGroup 2 ↥ρ.ker := by
    have hA2 : IsPGroup 2 ↥(φ.ker) := hZ.to_le hker
    have h' : IsPGroup 2 ↥((φ.ker).comap P.subtype) := hA2.comap_subtype (K := P)
    rwa [hρker]
  have hρsurj : Function.Surjective ρ := by
    intro n
    have hn : (n : G) ∈ P.map φ := by
      rw [hPmap]
      exact n.2
    obtain ⟨p, hp, hpφ⟩ := Subgroup.mem_map.mp hn
    exact ⟨⟨p, hp⟩, Subtype.ext hpφ⟩
  have hSLquot : HarrisLit.IsSLTwoOver q₀ (↥P ⧸ ρ.ker) :=
    slTwoOver_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).symm hSL
  obtain ⟨hPsl, hρkerbot⟩ :=
    isSLTwoOver_of_perfect_central_extension (E := ↥P) (A := ρ.ker) hGA hq h5 hPperf
      hρker_center hρker2 hSLquot
  refine ⟨P, hPcomm, hPsl, hPmap, ?_⟩
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hρkerbot
  intro p q hpq
  apply hρinj
  exact Subtype.ext hpq

end CFSG.OddStandard.SmallF3.HypA2
