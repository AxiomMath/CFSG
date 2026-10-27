module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Core
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.SectionRank.OddCover Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem factorization_card_GL_three (hK : Nat.card K % 3 = 1) :
    (Nat.card (GL (Fin 3) K)).factorization 3 = 3 * (Nat.card K - 1).factorization 3 + 1 := by
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have h3q : ¬ 3 ∣ q := by omega
  have h3q1 : ¬ 3 ∣ q + 1 := by omega
  have hd : 3 ∣ q - 1 := by omega
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq]
  rw [← hq]
  have hprod : ∏ j ∈ Finset.Icc 1 3, (q ^ j - 1) =
      (q - 1) * ((q - 1) * (q + 1)) * ((q - 1) * (q ^ 2 + q + 1)) := by
    rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
      ring
    have e3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
      zify [Nat.one_le_pow 3 q (by omega), (by omega : 1 ≤ q)]
      ring
    rw [e2, e3, pow_one]
    ring
  rw [hprod]
  have h1 : q - 1 ≠ 0 := by omega
  have h2 : q + 1 ≠ 0 := by omega
  have h4 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have hq0 : q ≠ 0 := by omega
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul h1 h2, Nat.factorization_mul h1 h4, Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_eq_zero_of_not_dvd h3q, Nat.factorization_eq_zero_of_not_dvd h3q1,
    factorization_sq_add_add_one Nat.prime_three (by omega) hd,
    Nat.Prime.factorization_self Nat.prime_three]
  ring

theorem scalar_mem_center' (c : Kˣ) (g : GL (Fin 3) K) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) c = Matrix.GeneralLinearGroup.scalar (Fin 3) c * g := by
  have h : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 h g

theorem relIndex_le_nine_of_isPGroup (hK : Nat.card K % 3 = 1) {S N : Subgroup (GL (Fin 3) K)}
    (hS : IsPGroup 3 S) (hNS : N ≤ S)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ N) (hcube : ∀ x ∈ S, x ^ 3 ∈ N)
    (hZ : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S →
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ N) :
    N.relIndex S ≤ 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨M0⟩ : Nonempty (Sylow 3 Kˣ) := inferInstance
  set M : Subgroup Kˣ := (M0 : Subgroup Kˣ) with hMdef
  have hM : Nat.card M = 3 ^ (Nat.card Kˣ).factorization 3 := Sylow.card_eq_multiplicity M0
  set Sy := torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K) with hSy
  have hSycard : Nat.card Sy = 3 ^ (Nat.card (GL (Fin 3) K)).factorization 3 := by
    rw [hSy, card_torusF_sup_cyc, hM, factorization_card_GL_three hK, card_units_eq]
    ring
  let P0 : Sylow 3 (GL (Fin 3) K) := Sylow.ofCard Sy hSycard
  have hP0 : (P0 : Subgroup (GL (Fin 3) K)) = Sy := rfl
  obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) K) P0 Q
  let φ : GL (Fin 3) K →* GL (Fin 3) K := (MulAut.conj g⁻¹).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  have hSy' : S.map φ ≤ Sy := by
    rintro _ ⟨y, hy, rfl⟩
    have hyQ : y ∈ ((g • P0 : Sylow 3 (GL (Fin 3) K)) : Subgroup (GL (Fin 3) K)) := hg ▸ hSQ hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
    exact hyQ
  have hφscalar : ∀ c : Kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro c
    show g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * g⁻¹⁻¹ = _
    rw [scalar_mem_center' c g⁻¹]
    group
  have key := relIndex_le_nine_of_le_monomial M (S := S.map φ) (N := N.map φ)
    (Subgroup.map_mono hNS) hSy'
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨⁅a, b⁆, hcomm a ha b hb, map_commutatorElement φ a b⟩)
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a ^ 3, hcube a ha, map_pow φ a 3⟩)
    (by
      intro c hc
      obtain ⟨a, ha, hac⟩ := hc
      have : a = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
        apply hφinj
        rw [hac, hφscalar]
      subst this
      exact ⟨_, hZ c ha, hφscalar c⟩)
  rw [Subgroup.relIndex_map_map_of_injective N S hφinj] at key
  exact key

theorem relIndex_le_nine_of_hom (hK : Nat.card K % 3 = 1) {A : Type*} [Group A]
    (G : Subgroup (GL (Fin 3) K)) (c : G →* A)
    (hc : ∀ g : G, (∃ c0 : Kˣ, (g : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c0) →
      c g = 1)
    {H0 N0 : Subgroup A} (hH0 : H0 ≤ c.range) (h3 : IsPGroup 3 H0) (hN : N0 ≤ H0)
    (hcomm : ∀ x ∈ H0, ∀ y ∈ H0, ⁅x, y⁆ ∈ N0) (hcube : ∀ x ∈ H0, x ^ 3 ∈ N0) :
    N0.relIndex H0 ≤ 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Hh : Subgroup G := H0.comap c with hHh
  obtain ⟨R⟩ : Nonempty (Sylow 3 Hh) := inferInstance
  let ρ : Hh →* H0 := (c.comp Hh.subtype).codRestrict H0 (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro h
    obtain ⟨g, hg⟩ := hH0 h.2
    exact ⟨⟨g, by show c g ∈ H0; rw [hg]; exact h.2⟩, Subtype.ext hg⟩
  have hR : (R : Subgroup Hh).map ρ = ⊤ := by
    have hTop : IsPGroup 3 (⊤ : Subgroup H0) := fun g => by
      obtain ⟨k, hk⟩ := h3 g.1
      exact ⟨k, Subtype.ext hk⟩
    have := (R.mapSurjective hρ).is_maximal' hTop le_top
    exact this.symm
  let ι : Hh →* GL (Fin 3) K := G.subtype.comp Hh.subtype
  have hι : Function.Injective ι := G.subtype_injective.comp Hh.subtype_injective
  let Nh : Subgroup Hh := (N0.comap (c.comp Hh.subtype)) ⊓ R
  have hNhR : Nh ≤ (R : Subgroup Hh) := inf_le_right
  let S : Subgroup (GL (Fin 3) K) := (R : Subgroup Hh).map ι
  let N : Subgroup (GL (Fin 3) K) := Nh.map ι
  have hS3 : IsPGroup 3 S := R.2.map ι
  let ρR : (R : Subgroup Hh) →* H0 := ρ.comp (R : Subgroup Hh).subtype
  have hρR : Function.Surjective ρR := by
    intro h
    have hh : h ∈ (R : Subgroup Hh).map ρ := by rw [hR]; trivial
    obtain ⟨r, hr, hrh⟩ := hh
    exact ⟨⟨r, hr⟩, hrh⟩
  have hidx : N.relIndex S = N0.relIndex H0 := by
    rw [Subgroup.relIndex_map_map_of_injective Nh (R : Subgroup Hh) hι]
    unfold Subgroup.relIndex
    have e : Nh.subgroupOf (R : Subgroup Hh) = (N0.subgroupOf H0).comap ρR := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, x.2⟩
    rw [e, Subgroup.index_comap_of_surjective _ hρR]
  have hmemH : ∀ a : Hh, c a.1 ∈ H0 := fun a => a.2
  have key := relIndex_le_nine_of_isPGroup hK hS3 (N := N)
    (Subgroup.map_mono hNhR)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine ⟨⁅a, b⁆, ⟨?_, ?_⟩, map_commutatorElement ι a b⟩
      · show c (⁅a.1, b.1⁆) ∈ N0
        rw [map_commutatorElement]
        exact hcomm _ (hmemH a) _ (hmemH b)
      · rw [commutatorElement_def]
        exact (R : Subgroup Hh).mul_mem ((R : Subgroup Hh).mul_mem
          ((R : Subgroup Hh).mul_mem ha hb) ((R : Subgroup Hh).inv_mem ha))
          ((R : Subgroup Hh).inv_mem hb))
    (by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨a ^ 3, ⟨?_, ?_⟩, map_pow ι a 3⟩
      · show c (a.1 ^ 3) ∈ N0
        rw [map_pow]
        exact hcube _ (hmemH a)
      · exact (R : Subgroup Hh).pow_mem ha 3)
    (by
      rintro c0 ⟨a, ha, hac⟩
      have hcA : c a.1 = 1 := hc a.1 ⟨c0, hac.symm ▸ rfl⟩
      exact ⟨a, ⟨by show c a.1 ∈ N0; rw [hcA]; exact N0.one_mem, ha⟩, hac⟩)
  rw [hidx] at key
  exact key

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
