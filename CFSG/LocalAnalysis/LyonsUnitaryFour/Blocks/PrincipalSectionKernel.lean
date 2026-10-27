module

public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.CentralizerNorm
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrimaryUniqueness

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes
open scoped BigOperators Classical

variable {G : Type*} [Group G]

theorem commute_of_mem_centralizer_zpowers (u : G)
    (h : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : Commute u (h : G) :=
  (Subgroup.mem_centralizer_iff.mp h.property u (Subgroup.mem_zpowers u))

theorem mem_centralizer_zpowers_of_commute {u g : G} (h : Commute u g) :
    g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (h.zpow_left k).eq

theorem inv_mem_inverseSection (p : ℕ) (u : G)
    (r : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hr : Nat.Coprime p (orderOf r)) :
    (centralizerSelf u * r)⁻¹ ∈ inverseSection p u := by
  change Nat.Coprime p (orderOf (centralizerSelf u * (centralizerSelf u * r)⁻¹))
  have hc := centralizerSelf_commute u r
  have heq : centralizerSelf u * (centralizerSelf u * r)⁻¹ = r⁻¹ := by
    calc centralizerSelf u * (centralizerSelf u * r)⁻¹ = centralizerSelf u * r⁻¹ *
        (centralizerSelf u)⁻¹ := by group
      _ = r⁻¹ * centralizerSelf u * (centralizerSelf u)⁻¹ := by rw [(hc.inv_right).eq]
      _ = r⁻¹ := by group
  rw [heq, orderOf_inv]
  exact hr

theorem mask_conjugatorCount_eq_local [Fintype G] (p : ℕ) [Fact p.Prime] (u : G) (e : ℕ)
    (hu : orderOf u ∣ p ^ e) (y : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (ry : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hyr : y = centralizerSelf u * ry)
    (hry : Nat.Coprime p (orderOf ry)) :
    characterFunctionMask (inverseSection p u)
        (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          conjugatorCount (y : G)⁻¹ h.val) =
      conjugatorCount y⁻¹ := by
  funext h
  have hryG : Commute u (ry : G) := commute_of_mem_centralizer_zpowers u ry
  have hyG : (y : G) = u * ry := by rw [hyr]; rfl
  have hyinvG : (y : G)⁻¹ = u⁻¹ * (ry : G)⁻¹ := by
    rw [hyG, mul_inv_rev, (hryG.inv_inv).eq]
  have hyinvC : y⁻¹ = (centralizerSelf u)⁻¹ * ry⁻¹ := by
    rw [hyr, mul_inv_rev, ((centralizerSelf_commute u ry).inv_inv).eq]
  have hmemD : ∀ c : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      c * y⁻¹ * c⁻¹ ∈ inverseSection p u := by
    intro c
    change Nat.Coprime p (orderOf (centralizerSelf u * (c * y⁻¹ * c⁻¹)))
    have hcc := centralizerSelf_commute u c
    have h1 : centralizerSelf u * (c * y⁻¹ * c⁻¹) = c * ry⁻¹ * c⁻¹ := by
      rw [hyinvC]
      calc centralizerSelf u * (c * ((centralizerSelf u)⁻¹ * ry⁻¹) * c⁻¹) =
          (centralizerSelf u * c) * (centralizerSelf u)⁻¹ * ry⁻¹ * c⁻¹ := by group
        _ = (c * centralizerSelf u) * (centralizerSelf u)⁻¹ * ry⁻¹ * c⁻¹ := by rw [hcc.eq]
        _ = c * ry⁻¹ * c⁻¹ := by group
    rw [h1]
    have := (MulAut.conj c).orderOf_eq ry⁻¹
    change orderOf (c * ry⁻¹ * c⁻¹) = orderOf ry⁻¹ at this
    rw [this, orderOf_inv]
    exact hry
  unfold characterFunctionMask
  by_cases hD : h ∈ inverseSection p u
  · rw [ite_eq_left hD]
    have hconjC : ∀ g : G, g * (y : G)⁻¹ * g⁻¹ = h →
        g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
      intro g hg
      have hDh : Nat.Coprime p (orderOf (u * (h : G))) := by
        have := hD
        change Nat.Coprime p (orderOf (centralizerSelf u * h)) at this
        rw [← Subgroup.orderOf_coe] at this
        exact this
      have hhu : Commute u (h : G) := commute_of_mem_centralizer_zpowers u h
      have hfac1 : (h : G) = (g * u⁻¹ * g⁻¹) * (g * (ry : G)⁻¹ * g⁻¹) := by
        rw [← hg, hyinvG]
        group
      have hfac2 : (h : G) = u⁻¹ * (u * h) := by group
      have hord1 : orderOf (g * u⁻¹ * g⁻¹) ∣ p ^ e := by
        have := (MulAut.conj g).orderOf_eq u⁻¹
        change orderOf (g * u⁻¹ * g⁻¹) = orderOf u⁻¹ at this
        rw [this, orderOf_inv]
        exact hu
      have hord2 : Nat.Coprime p (orderOf (g * (ry : G)⁻¹ * g⁻¹)) := by
        have := (MulAut.conj g).orderOf_eq (ry : G)⁻¹
        change orderOf (g * (ry : G)⁻¹ * g⁻¹) = orderOf (ry : G)⁻¹ at this
        rw [this, orderOf_inv, Subgroup.orderOf_coe]
        exact hry
      have hcomm1 : Commute (g * u⁻¹ * g⁻¹) (g * (ry : G)⁻¹ * g⁻¹) := by
        have := (hryG.inv_inv).map (MulAut.conj g).toMonoidHom
        simpa using this
      have hcomm2 : Commute u⁻¹ (u * h) := (Commute.refl u).inv_left.mul_right hhu.inv_left
      have huinv : orderOf u⁻¹ ∣ p ^ e := by rw [orderOf_inv]; exact hu
      obtain ⟨hpart, -⟩ := primary_factorization_unique hord1 hord2 hcomm1 huinv hDh hcomm2
        (hfac1.symm.trans hfac2)
      apply mem_centralizer_zpowers_of_commute
      have hgu : g * u⁻¹ = u⁻¹ * g := by
        calc g * u⁻¹ = (g * u⁻¹ * g⁻¹) * g := by group
          _ = u⁻¹ * g := by rw [hpart]
      exact Commute.inv_left_iff.mp (show Commute u⁻¹ g from hgu.symm)
    unfold conjugatorCount
    dsimp only
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun g : G => g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G))]
    have hzero : ∑ g : {g : G // ¬ g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G)},
        (if (g : G) * (y : G)⁻¹ * (g : G)⁻¹ = h then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro g _
      apply ite_eq_right
      intro hg
      exact g.property (hconjC g hg)
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro c _
    have hiff : (c : G) * (y : G)⁻¹ * (c : G)⁻¹ = (h : G) ↔
        (⟨c, c.property⟩ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) * y⁻¹ *
          (⟨c, c.property⟩ : Subgroup.centralizer (Subgroup.zpowers u : Set G))⁻¹ = h := by
      rw [Subtype.ext_iff]
      rfl
    by_cases hc : (c : G) * (y : G)⁻¹ * (c : G)⁻¹ = (h : G)
    · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (hiff.mpr h'))]
  · rw [ite_eq_right hD]
    unfold conjugatorCount
    symm
    apply Finset.sum_eq_zero
    intro c _
    apply ite_eq_right
    intro hc
    exact hD (hc ▸ hmemD c)

theorem principal_section_kernel_inverse [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (u : G) (e : ℕ)
    (hu : orderOf u ∣ p ^ e)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (rx ry : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hrx : Nat.Coprime p (orderOf rx)) (hry : Nat.Coprime p (orderOf ry)) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character ((centralizerSelf u * ry : _) : G) *
          (basis.representation label).character ((centralizerSelf u * rx : _) : G)⁻¹ =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character (centralizerSelf u * ry) *
          (localBasis.representation label).character (centralizerSelf u * rx)⁻¹ := by
  have hreg : Nat.Coprime p (orderOf (rx : G)) := by rwa [Subgroup.orderOf_coe]
  have hlocal := principal_local_section_projection basis ideal p principal hprincipal u
    e hu localBasis localPrincipal hlocalPrincipal rx hreg
    (conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹)
    (conjugatorCount_conjugation ((centralizerSelf u * ry : _) : G)⁻¹)
  have hpt : ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * rx)⁻¹ =
      (centralizerSelf u * rx)⁻¹ := rfl
  rw [hpt] at hlocal
  have hambient : characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹)
      (((centralizerSelf u * rx)⁻¹ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G) =
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character ((centralizerSelf u * ry : _) : G) *
          (basis.representation label).character ((centralizerSelf u * rx : _) : G)⁻¹ := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    rw [conjugatorCount_pairing, inv_inv, Subgroup.coe_inv]
  have hmask := congrFun (coefficientBlock_section_mask_commute localBasis ideal p
    localPrincipal (inverseSection p u) (inverseSection_primeSectionUnion p u e hu)
    (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
      conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)) (centralizerSelf u * rx)⁻¹
  have hmem := inv_mem_inverseSection p u rx hrx
  have hunmask : characterFunctionMask (inverseSection p u)
      (characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
        fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)
        (centralizerSelf u * rx)⁻¹ =
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
        (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)
        (centralizerSelf u * rx)⁻¹ := by
    unfold characterFunctionMask
    rw [ite_eq_left hmem]
  rw [hunmask, mask_conjugatorCount_eq_local p u e hu (centralizerSelf u * ry) ry rfl hry]
    at hmask
  have hlocalValue : characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (conjugatorCount (centralizerSelf u * ry)⁻¹) (centralizerSelf u * rx)⁻¹ =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character (centralizerSelf u * ry) *
          (localBasis.representation label).character (centralizerSelf u * rx)⁻¹ := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    rw [conjugatorCount_pairing, inv_inv]
  rw [hlocalValue] at hmask
  rw [← hambient, ← hlocal, hmask]

theorem brauer_principal_section_kernel [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (u : G) (e : ℕ)
    (hu : orderOf u ∣ p ^ e)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (x y : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hx : ∃ r : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      x = centralizerSelf u * r ∧ Nat.Coprime p (orderOf r))
    (hy : ∃ r : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      y = centralizerSelf u * r ∧ Nat.Coprime p (orderOf r)) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character (x : G) *
          starRingEnd ℂ ((basis.representation label).character (y : G)) =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character x *
          starRingEnd ℂ ((localBasis.representation label).character y) := by
  obtain ⟨rx, rfl, hrx⟩ := hx
  obtain ⟨ry, rfl, hry⟩ := hy
  simp_rw [finite_character_conjugate_inverse]
  rw [← Subgroup.coe_inv]
  exact principal_section_kernel_inverse basis ideal p principal hprincipal u e hu localBasis
    localPrincipal hlocalPrincipal ry rx hry hrx

end CFSG.LyonsUnitaryFour
