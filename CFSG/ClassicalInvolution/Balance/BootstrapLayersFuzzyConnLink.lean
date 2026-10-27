module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyEdge
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyFrames

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect)
open CFSG.ClassicalInvolution.Balance.Theorem5 (FuzzyFrameOn fuzzyVertices)
open scoped commutatorElement MatrixGroups

section Involutions

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {M : Subgroup G} {a : G}
    (hM : IsClassicalMember p f M a) {x : G} (hx : x ∈ M) (hx2 : x * x = 1) : x = 1 ∨ x = a := by
  obtain ⟨e⟩ := hM.nonempty_equiv
  have hodd := odd_natCard_galoisField hp2 hq
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥M)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥M
  set ρ : ↥M →* ↥M ⧸ classicalInvolutionOddCore ↥M := QuotientGroup.mk' _ with hρ
  set x' : ↥M := ⟨x, hx⟩ with hx'
  set a' : ↥M := ⟨a, hM.mem⟩ with ha'
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have ha'2 : orderOf a' = 2 := by rw [ha', Subgroup.orderOf_mk]; exact hM.orderOf_eq_two
  have hcen : ∀ l : ↥M, l * a' = a' * l := fun l => Subtype.ext (hM.isCentralInvolution.central
    l.1 l.2).symm
  have hsq : ∀ y : ↥M, y * y = 1 → y ∈ classicalInvolutionOddCore ↥M → y = 1 := by
    intro y hy hyO
    have h1 : Odd (orderOf y) := hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hyO)
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
    have h3 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd h1 (by decide)
    exact orderOf_eq_one_iff.mp h3
  by_cases hρ1 : ρ x' = 1
  · left
    exact congrArg Subtype.val (hsq x' hx'2 ((QuotientGroup.eq_one_iff _).mp hρ1))
  · right
    have hρ2 : ρ x' * ρ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have h2 : orderOf (ρ x') = 2 := by
      have hd : orderOf (ρ x') ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hρ2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hρ1
      · exact h
    have hρx := (orderOf_eq_two_iff_of_equiv_sl2 hodd e (ρ x')).mp h2
    have hρa := (orderOf_eq_two_iff_of_equiv_sl2 hodd e (ρ a')).mp
      (CFSG.ClassicalInvolution.Generic.orderOf_mk_oddCore_eq_two ha'2)
    have h3 : x'⁻¹ * a' ∈ classicalInvolutionOddCore ↥M := by
      apply (QuotientGroup.eq_one_iff _).mp
      show ρ (x'⁻¹ * a') = 1
      rw [map_mul, map_inv, hρx, hρa, inv_mul_cancel]
    have hcomm : Commute x' a'⁻¹ := (Commute.inv_right (show Commute x' a' from hcen x'))
    have ha'sq : a' * a' = 1 := by rw [← sq, ← ha'2]; exact pow_orderOf_eq_one a'
    have h4 : (x'⁻¹ * a') * (x'⁻¹ * a') = 1 := by
      have hxi : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
      rw [hxi]
      calc x' * a' * (x' * a') = (x' * x') * (a' * a') := by
            rw [Commute.mul_mul_mul_comm (show Commute a' x' from (hcen x').symm)]
        _ = 1 := by rw [hx'2, ha'sq, mul_one]
    have h5 := hsq _ h4 h3
    have hxi : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    rw [hxi] at h5
    have : x' = a'⁻¹ := (mul_eq_one_iff_eq_inv.mp h5)
    have ha'i : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'sq
    exact congrArg Subtype.val (this.trans ha'i)

end Involutions

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

@[expose] def linkFamily (p f : ℕ) [Fact p.Prime] (𝒞 : Set (Subgroup G)) (a : G) :
    Set (Subgroup G) :=
  residualFamily a (𝒞 ∩ linkMembers p f a)

theorem secData_linkFamily (hinv : ConjInvariant 𝒞) {M : Subgroup G} (hM𝒞 : M ∈ 𝒞)
    (hM : IsClassicalMember p f M a) : SecData p f a (linkFamily p f 𝒞 a) := by
  have cM := isCentralInvolution_of_isClassicalMember hM
  have hMl : M ∈ 𝒞 ∩ linkMembers p f a :=
    ⟨hM𝒞, ⟨a, hM⟩, mem_trivialOnQuot_of_centralizes fun j hj => cM.central j hj⟩
  exact secData_residualFamily cM.sq ⟨M, hMl⟩ (fun J hJ => hJ.2.1) (fun J hJ => hJ.2.2)
    fun n hn J hJ => ⟨hinv n J hJ.1, conjSub_mem_linkMembers hn hJ.2⟩

theorem triangleResidual_mem_linkFamily {J : Subgroup G} {t : G} (hJ𝒞 : J ∈ 𝒞)
    (hJ : IsClassicalMember p f J t) (haJ : a ∈ trivialOnQuot J) :
    triangleResidual J a ∈ linkFamily p f 𝒞 a :=
  ⟨J, ⟨hJ𝒞, ⟨t, hJ⟩, haJ⟩, rfl⟩

theorem mem_linkFamily_of_isClassicalMember {M : Subgroup G} (hM𝒞 : M ∈ 𝒞)
    (hM : IsClassicalMember p f M a) : M ∈ linkFamily p f 𝒞 a := by
  have cM := isCentralInvolution_of_isClassicalMember hM
  have h := triangleResidual_mem_linkFamily (a := a) hM𝒞 hM
    (mem_trivialOnQuot_of_centralizes fun j hj => cM.central j hj)
  rwa [triangleResidual_eq_self hM] at h

variable (hs : SecData p f a (linkFamily p f 𝒞 a))
  (D' : LieDecomposition (memberImages (linkFamily p f 𝒞 a) a) (memberJoin (linkFamily p f 𝒞 a) a))

include hs in
theorem modOdd_eq_comp (hq : 5 ≤ p ^ f) {M : Subgroup G} (hM𝒞 : M ∈ 𝒞)
    (hM : IsClassicalMember p f M a) : ∃ m, modOdd a M = D'.Q m := by
  have := memberJoin_normal_of_normalizes hs.normalizes
  have hcomp := isComponentOf_modOdd hM hq
  rcases D'.eq_or_commutes_of_isComponentOf hcomp with ⟨i, hi⟩ | hcomm
  · exact ⟨i, hi⟩
  · exfalso
    have hMΦ := mem_linkFamily_of_isClassicalMember hM𝒞 hM
    have hjoin : modOdd a M ≤ memberJoin (linkFamily p f 𝒞 a) a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers (linkFamily p f 𝒞 a) a) =>
        modOdd a K) M ⟨hMΦ, hs.le M hMΦ⟩
    exact not_commutes_self_of_isQuasisimple hcomp.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem not_modOdd_le_comp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {M : Subgroup G}
    (hM : IsClassicalMember p f M a) (hcan : IsCanonical M a) {m : D'.ι}
    (hm : modOdd a M = D'.Q m) {J : Subgroup G} {t : G} (hJ : IsClassicalMember p f J t)
    (haJ : a ∈ trivialOnQuot J) (hta : t ≠ a) :
    ¬ modOdd a (triangleResidual J a) ≤ D'.Q m := by
  intro hle
  have hsec := isSectionMember_triangleResidual hJ (isCentralInvolution_of_isClassicalMember hM).sq
    haJ
  rw [← hm] at hle
  have h1 : triangleResidual J a ≤ M ⊔ involutionOddCore a :=
    le_sup_involutionOddCore_of_modOdd_le hsec.le hle
  have h2 : triangleResidual J a ≤ perfectResidualOf (M ⊔ involutionOddCore a) :=
    le_perfectResidualOf_of_perfect h1 hsec.perfect
  have hcan' : perfectResidualOf (M ⊔ involutionOddCore a) = M := hcan
  rw [hcan'] at h2
  rcases eq_one_or_eq_of_isClassicalMember hp2 hq hM (h2 hsec.mem) hsec.sq with h | h
  · exact hsec.isCentralInvolution.ne_one h
  · exact hta h

include hs D' in
theorem mem_trivialOnQuot_of_linkVertex (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {M : Subgroup G}
    (hM𝒞 : M ∈ 𝒞) (hM : IsClassicalMember p f M a) (hcan : IsCanonical M a) {J : Subgroup G}
    {t : G} (hJ𝒞 : J ∈ 𝒞) (hJ : IsClassicalMember p f J t) (haJ : a ∈ trivialOnQuot J)
    (hta : t ≠ a) (htC : t ∈ Subgroup.centralizer ({a} : Set G)) : t ∈ trivialOnQuot M := by
  obtain ⟨m, hm⟩ := modOdd_eq_comp hs D' hq hM𝒞 hM
  have hKΦ := triangleResidual_mem_linkFamily hJ𝒞 hJ haJ
  have hsec := isSectionMember_triangleResidual hJ (isCentralInvolution_of_isClassicalMember hM).sq
    haJ
  obtain ⟨c, hc⟩ := D'.exists_le (modOdd a (triangleResidual J a))
    ⟨triangleResidual J a, ⟨hKΦ, hs.le _ hKΦ⟩, rfl⟩
  have hcm : c ≠ m := fun h => not_modOdd_le_comp D' hp2 hq hM hcan hm hJ haJ hta (h ▸ hc)
  rw [mem_trivialOnQuot_iff_centralizes_modOdd hM hq hcan htC]
  intro y hy
  rw [hm] at hy
  exact D'.commute c m hcm _ (hc (oddQuotMk_mem_modOdd hsec.mem htC)) y hy

end Family

section Classes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_zpowers_conj_eq_of_involution {t n : G} (ht : t * t = 1) (htn : t * n * (t * n) = 1)
    (hn : Odd (orderOf n)) : ∃ y ∈ Subgroup.zpowers n, y * t * y⁻¹ = t * n := by
  obtain ⟨k, hk⟩ := hn
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * n * t = n⁻¹ := by
    have : (t * n * t) * n = 1 := by
      calc (t * n * t) * n = t * n * (t * n) := by group
        _ = 1 := htn
    exact eq_inv_of_mul_eq_one_left this
  have htnt : t * n = n⁻¹ * t := by
    calc t * n = t * n * t * t⁻¹ := by group
      _ = n⁻¹ * t⁻¹ := by rw [h1]
      _ = n⁻¹ * t := by rw [hti]
  have hconj : t * n ^ k * t = (n ^ k)⁻¹ := by
    have h := map_pow (MulAut.conj t) n k
    simp only [MulAut.conj_apply, hti] at h
    rw [h, h1, inv_pow]
  have hpow : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
  have hn2 : n ^ (2 * k) = n⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hpow)
  refine ⟨n ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers n) _, ?_⟩
  have h3 : t * (n ^ k)⁻¹ * t = n ^ k := by
    have := congrArg (fun x => x⁻¹) hconj
    simpa [mul_inv_rev, hti, mul_assoc] using this
  have h2 : t * (n ^ k)⁻¹ = n ^ k * t := by
    calc t * (n ^ k)⁻¹ = t * (n ^ k)⁻¹ * t * t⁻¹ := by group
      _ = n ^ k * t⁻¹ := by rw [h3]
      _ = n ^ k * t := by rw [hti]
  calc n ^ k * t * (n ^ k)⁻¹ = n ^ k * (t * (n ^ k)⁻¹) := by group
    _ = n ^ k * (n ^ k * t) := by rw [h2]
    _ = n ^ (2 * k) * t := by rw [two_mul, pow_add, mul_assoc]
    _ = n⁻¹ * t := by rw [hn2]
    _ = t * n := htnt.symm

end Classes

section ClassesFinite

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_mem_oddCoreIn_conj_eq {X : Subgroup G} {x x' : G} (hx2 : x * x = 1)
    (hx'2 : x' * x' = 1) (h : x⁻¹ * x' ∈ oddCoreIn X) : ∃ y ∈ oddCoreIn X, y * x * y⁻¹ = x' := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hx' : x' = x * (x⁻¹ * x') := by group
  have htn : x * (x⁻¹ * x') * (x * (x⁻¹ * x')) = 1 := by rw [← hx']; exact hx'2
  have hodd : Odd (orderOf (x⁻¹ * x')) :=
    (odd_card_oddCoreIn X).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ h)
  obtain ⟨y, hy, hyc⟩ := exists_zpowers_conj_eq_of_involution hx2 htn hodd
  exact ⟨y, (Subgroup.zpowers_le.mpr h) hy, by rw [hyc, ← hx']⟩

@[expose] def SameClass (a t u : G) : Prop :=
  ∃ n ∈ involutionOddCore a, u = t * n ∨ u = a * t * n

omit [Finite G] in
theorem conj_notMem_of_not_sameClass {a t u : G} (htC : t ∈ Subgroup.centralizer ({a} : Set G))
    (hua : u ≠ a) (h : ¬ SameClass a t u) :
    ∀ x ∈ involutionOddCore a, x * u * x⁻¹ ∉ ({a, t, a * t} : Set G) := by
  intro x hx hmem
  rw [involutionOddCore_eq_oddCoreIn] at hx
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx
  have hax : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hn : t⁻¹ * x⁻¹ * t * x ∈ involutionOddCore a := by
    rw [involutionOddCore_eq_oddCoreIn]
    have h1 : t⁻¹ * x⁻¹ * t⁻¹⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
      conj_mem_oddCoreIn (inv_mem htC) (inv_mem hx)
    rw [inv_inv] at h1
    exact mul_mem h1 hx
  have hu : u = x⁻¹ * (x * u * x⁻¹) * x := by group
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h2 | h3
  · apply hua
    rw [hu, h1]
    calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
      _ = x⁻¹ * (x * a) := by rw [hax]
      _ = a := by group
  · apply h
    refine ⟨_, hn, Or.inl ?_⟩
    rw [hu, h2]
    group
  · apply h
    refine ⟨_, hn, Or.inr ?_⟩
    have hxi : x⁻¹ * a = a * x⁻¹ := by
      calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * a) * x⁻¹ := by rw [hax]
        _ = a * x⁻¹ := by group
    rw [hu, h3]
    calc x⁻¹ * (a * t) * x = (x⁻¹ * a) * t * x := by group
      _ = a * x⁻¹ * t * x := by rw [hxi]
      _ = a * t * (t⁻¹ * x⁻¹ * t * x) := by group

theorem isCanonical_of_mem_canonicalMembers (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {J : Subgroup G}
    {t : G} (hJ𝒞 : J ∈ canonicalMembers p f G) (hJ : IsClassicalMember p f J t) :
    IsCanonical J t := by
  obtain ⟨z, hz, hcan⟩ := hJ𝒞
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have : t = z := hz.eq_of_isCentralInvolution hp2 hf hJ.isCentralInvolution
  rw [this]
  exact hcan

end ClassesFinite

section Cross

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}
  (hs : SecData p f a (linkFamily p f 𝒞 a))
  (D' : LieDecomposition (memberImages (linkFamily p f 𝒞 a) a) (memberJoin (linkFamily p f 𝒞 a) a))

include hs D' in
theorem exists_fuzzyFrame_of_link_vertices (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hinv : ConjInvariant 𝒞) (hcan : 𝒞 ⊆ canonicalMembers p f G) {M : Subgroup G}
    (hM𝒞 : M ∈ 𝒞) (hM : IsClassicalMember p f M a) {J : Subgroup G} {t : G} (hJ𝒞 : J ∈ 𝒞)
    (hJ : IsClassicalMember p f J t) (haJ : a ∈ trivialOnQuot J) (hta : t ≠ a)
    {N : Subgroup G} {u : G} (hN𝒞 : N ∈ 𝒞) (hN : IsClassicalMember p f N u)
    (haN : a ∈ trivialOnQuot N) (hua : u ≠ a) {i j : D'.ι} (hij : i ≠ j)
    (hi : modOdd a (triangleResidual J a) ≤ D'.Q i)
    (hj : modOdd a (triangleResidual N a) ≤ D'.Q j) (hclass : ¬ SameClass a t u) :
    ∃ x ∈ involutionOddCore a, FuzzyFrameOn p f 𝒞 (triangleAxis a t (x * u * x⁻¹)) ∧
      a ∈ fuzzyVertices p f 𝒞 (triangleAxis a t (x * u * x⁻¹)) ∧
      Subgroup.closure ({a, t} : Set G) ≤ triangleAxis a t (x * u * x⁻¹) ∧
      conjSub x (Subgroup.closure ({a, u} : Set G)) ≤ triangleAxis a t (x * u * x⁻¹) := by
  have hMcan : IsCanonical M a := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hM𝒞) hM
  have hJcan := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hJ𝒞) hJ
  have hNcan := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hN𝒞) hN
  have ha2 := (isCentralInvolution_of_isClassicalMember hM).sq
  have hsJ := isSectionMember_triangleResidual hJ ha2 haJ
  have hsN := isSectionMember_triangleResidual hN ha2 haN
  have htC : t ∈ Subgroup.centralizer ({a} : Set G) := hsJ.le hsJ.mem
  have huC : u ∈ Subgroup.centralizer ({a} : Set G) := hsN.le hsN.mem
  have htM := mem_trivialOnQuot_of_linkVertex hs D' hp2 hq hM𝒞 hM hMcan hJ𝒞 hJ haJ hta htC
  have huM := mem_trivialOnQuot_of_linkVertex hs D' hp2 hq hM𝒞 hM hMcan hN𝒞 hN haN hua huC
  have hJN := hs.commutator_mem_oddCore D' (triangleResidual_mem_linkFamily hJ𝒞 hJ haJ)
    (triangleResidual_mem_linkFamily hN𝒞 hN haN) hij hi hj
  exact exists_fuzzyFrame_of_residuals_commute hinv hM𝒞 hJ𝒞 hN𝒞 hM hJ hN hq hJcan hNcan htM huM
    haJ haN hJN (Ne.symm hta) (conj_notMem_of_not_sameClass htC hua hclass)

end Cross

end CFSG.ClassicalInvolution.Balance.Bootstrap
