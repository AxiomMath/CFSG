module

public import CFSG.RankThree.PartOne.TCX.Tri.TorusCentral
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.RankThree.PartOne.TCX.Tri.PlaneSplit

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution CFSG.RankThree.PartOne.TCX.Tri
open CFSG.ComponentClassification

set_option linter.unusedSectionVars false

theorem zpowMatrix_cartan_mem_compatSubgroup {K : Type} [Field K] {σ : K →+* K}
    {c : Fin TwistTag.E6.tag.rank → Kˣ} (hc : c ∈ compatSubgroup (t := TwistTag.E6) σ) :
    zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c ∈ compatSubgroup (t := TwistTag.E6) σ := by
  intro j
  simp only [zpowMatrix_apply, map_prod, map_zpow]
  rw [← Equiv.prod_comp TwistTag.E6.perm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hc i, TwistTag.cartan_perm]

theorem exists_compat_zpowMatrix_eq {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q)
    (h3 : Nat.gcd 3 (q + 1) = 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : b ∈ compatSubgroup (t := TwistTag.E6) σ) :
    ∃ c ∈ compatSubgroup (t := TwistTag.E6) σ,
      zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c = b := by
  set S := compatSubgroup (t := TwistTag.E6) (K := K) σ with hS
  set Z := zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan with hZ
  have hker : Nat.card ↥(S ⊓ Z.ker) = 1 := by
    rw [hS, hZ, card_compat_inf_ker_E6_of_card hK hσ, h3]
  have hker' : S ⊓ Z.ker = ⊥ := Subgroup.card_eq_one.1 hker
  have hinj : Function.Injective (Z.domRestrict S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx0 : Z (x : Fin TwistTag.E6.tag.rank → Kˣ) = 1 := hx
    have hx1 : (x : Fin TwistTag.E6.tag.rank → Kˣ) ∈ S ⊓ Z.ker := ⟨x.2, hx0⟩
    rw [hker'] at hx1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx1))
  have hle : S.map Z ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    exact zpowMatrix_cartan_mem_compatSubgroup hc
  have hcard : Nat.card ↥(S.map Z) = Nat.card S := by
    have h1 : (Z.domRestrict S).range = S.map Z := MonoidHom.domRestrict_range _ _
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfin : Finite S := inferInstance
  have heq : S.map Z = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  have hb' : b ∈ S.map Z := by rw [heq]; exact hb
  obtain ⟨c, hc, hcb⟩ := hb'
  exact ⟨c, hc, hcb⟩

theorem rootDiagUnit_compatDiag_mem_graphFixedRootGroup {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q)
    (h3 : Nat.gcd 3 (q + 1) = 1)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  obtain ⟨c, hc, hcb⟩ := exists_compat_zpowMatrix_eq hK (σ := σ.toRingHom) hσ h3
    (fun i => compatDiag_perm u i)
  have hT : (torusCoordHom TwistTag.E6.tag K c : ModGL TwistTag.E6.tag K) ∈
      compatTorus (t := TwistTag.E6) σ.toRingHom :=
    (mem_compatTorus σ.toRingHom).2 ⟨c, hc, rfl⟩
  have h := compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) σ.toRingHom hT
  rwa [torusCoordHom_eq_rootDiagUnit, hcb] at h

theorem compatDiagAutHom_mem_inner {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q)
    (h3 : Nat.gcd 3 (q + 1) = 1)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ twistedE6Inn K σ := by
  refine ⟨⟨_, rootDiagUnit_compatDiag_mem_graphFixedRootGroup hK hσ h3 u⟩, ?_⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_compatDiagAutHom]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_inner_of_mem_inn_sup_diag {ℓ f p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hpg : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1))
    (hcube : ∀ a : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
      (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ), a ^ 3 = 1)
    {β : MulAut (twistedE6RootGroup K σ)} (hβ : β ^ p = 1)
    (hmem : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : β ∈ twistedE6Inn K σ := by
  by_cases h3 : Nat.gcd 3 (ℓ ^ f + 1) = 1
  · have hΔ : twistedE6Diag K σ ≤ twistedE6Inn K σ := by
      rintro _ ⟨u, rfl⟩
      exact compatDiagAutHom_mem_inner hK hσ h3 u
    rw [sup_eq_left.2 hΔ] at hmem
    exact hmem
  · have hg3 : Nat.gcd 3 (ℓ ^ f + 1) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (ℓ ^ f + 1))).resolve_left h3
    have hp3 : p ≠ 3 := fun h => hpg (by rw [hg3, h])
    set H := twistedE6Inn K σ ⊔ twistedE6Diag K σ
    set a := QuotientGroup.mk' ((twistedE6Inn K σ).subgroupOf H) (⟨β, hmem⟩ : H) with ha
    have hxp : (⟨β, hmem⟩ : H) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hβ)
    have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp, map_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
    have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hap) (orderOf_dvd_of_pow_eq_one (hcube a))))
    have h2 := (QuotientGroup.eq_one_iff (N := (twistedE6Inn K σ).subgroupOf H) _).1 ha1
    rw [Subgroup.mem_subgroupOf] at h2
    exact h2

end CFSG.HardMathSupport.Lang.Coordinator
