module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndN
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21Rel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoverExclusion
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndOne
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_coreActionKernel_of_ne {N B M : Subgroup G} (hBN : B ≤ N) (hMN : M ≤ N)
    (hB : IsPComponent 2 (B.subgroupOf N)) (hM : IsPComponent 2 (M.subgroupOf N))
    (hne : B ≠ M) : B ≤ coreActionKernel M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : B.subgroupOf N ≠ M.subgroupOf N := fun h1 => hne (by
    have h2 := subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hBN, inf_eq_left.mpr hMN] at h2)
  obtain ⟨-, hBM, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hB hM).2 hne'
  set eM : ↥(M.subgroupOf N) ≃* ↥M := subgroupOfEquivOfLe hMN with heM
  have hO : ∀ y : ↥(M.subgroupOf N), y ∈ pPrimeCore 2 ↥(M.subgroupOf N) →
      (eM y : G) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    intro y hy
    refine ⟨eM y, ?_, rfl⟩
    rw [← CFSG.pPrimeCore_map_iso 2 eM]
    exact mem_map_of_mem _ hy
  intro b hb
  refine mem_coreActionKernel.mpr ⟨mem_normalizer_of_subgroupOf hMN
    (hBM (show (⟨b, hBN hb⟩ : N) ∈ B.subgroupOf N from hb)), fun m hm => ?_⟩
  have h1 : ⁅(⟨m, hMN hm⟩ : N)⁻¹, (⟨b, hBN hb⟩ : N)⁻¹⁆ ∈ ⁅B.subgroupOf N, M.subgroupOf N⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (inv_mem (show (⟨m, hMN hm⟩ : N) ∈ M.subgroupOf N from hm))
      (inv_mem (show (⟨b, hBN hb⟩ : N) ∈ B.subgroupOf N from hb))
  have h2 := (hcomm h1).2
  obtain ⟨y, hy, hyc⟩ := mem_map.mp h2
  have h3 := hO y hy
  have h4 : (eM y : G) = m⁻¹ * b⁻¹ * m * b := by
    have := congrArg Subtype.val hyc
    simp only [subtype_apply, commutatorElement_def, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    rw [← this, heM, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [← h4]
  exact h3

theorem factorization_card_eq_of_equiv {L B : Subgroup G}
    (e : L ⧸ pPrimeCore 2 L ≃* B ⧸ pPrimeCore 2 B) :
    (Nat.card L).factorization 2 = (Nat.card B).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ X : Subgroup G, (Nat.card (pPrimeCore 2 ↥X)).factorization 2 = 0 := fun X =>
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  have hne : ∀ X : Subgroup G, Nat.card (pPrimeCore 2 ↥X) ≠ 0 := fun X => Nat.card_pos.ne'
  have hne' : ∀ X : Subgroup G, Nat.card (↥X ⧸ pPrimeCore 2 ↥X) ≠ 0 := fun X => Nat.card_pos.ne'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B),
    Nat.factorization_mul (hne' L) (hne L), Nat.factorization_mul (hne' B) (hne B),
    Finsupp.add_apply, Finsupp.add_apply, hodd L, hodd B, Nat.card_congr e.toEquiv]

omit [Finite G] in
theorem exists_mem_mul_centralizer_of_mem {z g : G} (hz : z * z = 1) {N : Subgroup G}
    (hNodd : Odd (Nat.card N)) (hg : g * z * g⁻¹ * z⁻¹ ∈ N) :
    ∃ k ∈ N, k⁻¹ * g ∈ centralizer ({z} : Set G) := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set m := g * z * g⁻¹ * z⁻¹ with hm
  have hmz : m * z = g * z * g⁻¹ := by rw [hm]; group
  have h1 : m * z * (m * z) = 1 := by
    rw [hmz, show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz]
    group
  have hmz' : z * m * z⁻¹ = m⁻¹ := by
    rw [hzinv]
    calc z * m * z = m⁻¹ * (m * z * (m * z)) := by group
      _ = m⁻¹ := by rw [h1, mul_one]
  have ho : Odd (orderOf m) := Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hg)
  set k := m ^ ((orderOf m + 1) / 2) with hk
  have hkN : k ∈ N := pow_mem hg _
  have hk2 : k * k = m := by
    rw [hk, ← pow_add, ← two_mul, two_mul_half_succ_of_odd ho, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hkz : z * k * z⁻¹ = k⁻¹ := by
    rw [hk, ← conj_pow, hmz', inv_pow]
  refine ⟨k, hkN, mem_centralizer_singleton_iff.mpr ?_⟩
  have hzk : z * k⁻¹ = k * z := by
    have h3 : z * k⁻¹ * z⁻¹ = k := by
      rw [show z * k⁻¹ * z⁻¹ = (z * k * z⁻¹)⁻¹ by group, hkz, inv_inv]
    calc z * k⁻¹ = z * k⁻¹ * z⁻¹ * z := by group
      _ = k * z := by rw [h3]
  have h2 : k * z * k⁻¹ = g * z * g⁻¹ := by
    calc k * z * k⁻¹ = k * (z * k⁻¹) := by group
      _ = k * k * z := by rw [hzk, ← mul_assoc]
      _ = g * z * g⁻¹ := by rw [hk2, hmz]
  calc k⁻¹ * g * z = k⁻¹ * (g * z * g⁻¹) * g := by group
    _ = k⁻¹ * (k * z * k⁻¹) * g := by rw [h2]
    _ = z * (k⁻¹ * g) := by group

theorem nonempty_equiv_of_mem_coreActionKernel {N B L : Subgroup G} {z : G} (hz : z * z = 1)
    (hBN : B ≤ N) (hB : IsPComponent 2 (B.subgroupOf N)) (hLB : L ≤ B)
    (hLz : L ≤ centralizer ({z} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({z} : Set G))))
    (hzB : z ∈ coreActionKernel B) : Nonempty (L ⧸ pPrimeCore 2 L ≃* B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := B ⊓ centralizer ({z} : Set G) with hC
  set ψ := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hψ
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hCtop : (C.subgroupOf B).map ψ = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥B) y
    have hm : (g : G) * z * (g : G)⁻¹ * z⁻¹ ∈ oddCoreIn B := by
      have h1 := (mem_coreActionKernel.mp hzB).2 _ (inv_mem g.2)
      rw [inv_inv, hzinv] at h1
      rwa [hzinv]
    obtain ⟨k, hk, hkg⟩ := exists_mem_mul_centralizer_of_mem hz (odd_card_oddCoreIn B) hm
    obtain ⟨k', hk', hkk'⟩ := mem_map.mp hk
    refine ⟨k'⁻¹ * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      refine mem_inf.mpr ⟨(k'⁻¹ * g).2, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((k' : B) : G) = k from hkk']
      exact hkg
    · rw [map_mul, map_inv, hψ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k').mpr hk',
        inv_one, one_mul]
  set LB := L.subgroupOf B with hLBdef
  have hLC : L ≤ C := le_inf hLB hLz
  have hLCpc : IsPComponent 2 (L.subgroupOf C) :=
    isPComponent_subgroupOf_of_le hLC inf_le_right hL
  have hLBX : LB ≤ C.subgroupOf B := fun x hx => mem_subgroupOf.mpr (hLC (mem_subgroupOf.mp hx))
  have hLBpc : IsPComponent 2 (LB.subgroupOf (C.subgroupOf B)) :=
    (isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mpr hLCpc
  have hker := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥B)
  have h1 := GSThmB.OddQuot.isPComponent_map ψ hker hLBX hLBpc
  rw [hCtop] at h1
  have h2 : IsPComponent 2 (LB.map ψ) := isPComponent_subgroupOf_top_iff'.mp h1
  have htop := TBLit.isPComponent_top_coreQuotient hBN hB
  have h3 : LB.map ψ = ⊤ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ h2 htop).1 le_top
  obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv ψ hker LB
  have hO : pPrimeCore 2 (↥B ⧸ pPrimeCore 2 ↥B) = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two
  let e₂ : ↥(LB.map ψ) ≃* (↥B ⧸ pPrimeCore 2 ↥B) :=
    (MulEquiv.subgroupCongr h3).trans Subgroup.topEquiv
  let e₃ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₂
  let e₄ : (↥B ⧸ pPrimeCore 2 ↥B) ⧸ pPrimeCore 2 (↥B ⧸ pPrimeCore 2 ↥B) ≃* ↥B ⧸ pPrimeCore 2 ↥B :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  let e₀ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hLB).symm
  exact ⟨e₀.trans (e₁.trans (e₃.trans e₄))⟩

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem isTwoComponentAt_conjugate : IsTwoComponentAt t (conjugate L s) := by
  have h1 := isTwoComponentAt_map_mulEquiv (MulAut.conj s⁻¹) H.sec5.zL
  rwa [MulAut.conj_apply, inv_inv, H.conj_s_inv_z] at h1

theorem z_mem_twoLayerIn {N : Subgroup G} (hCt : centralizer ({t} : Set G) ≤ N) :
    z ∈ twoLayerIn N := by
  obtain ⟨ht2, hLsC, hLspc⟩ := H.isTwoComponentAt_conjugate
  have htN : t ∈ N := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have hNC : N ⊓ centralizer ({t} : Set G) = centralizer ({t} : Set G) := inf_eq_right.mpr hCt
  obtain ⟨B, hBN, hB, hLsB, -⟩ := foote_lemma_2_1_iv_subgroup htN ht2
    (le_inf (hLsC.trans hCt) hLsC) (by rw [hNC]; exact hLspc)
  have h1 : B ≤ twoLayerIn N := le_twoLayerIn_of_isTwoComponentIn ⟨hBN, hB⟩
  have h2 : conjugate B t ≤ twoLayerIn N := le_twoLayerIn_of_isTwoComponentIn
    ⟨conjugate_le_of_mem hBN htN, isPComponent_conjugate_subgroupOf htN hB⟩
  have hzLs : z ∈ conjugate L s := by rw [mem_conjugate_iff, H.conj_s_z]; exact H.sec5.tL
  exact sup_le h1 h2 (hLsB hzLs)

theorem exists_component {N : Subgroup G} (hCz : centralizer ({z} : Set G) ≤ N)
    (hCt : centralizer ({t} : Set G) ≤ N) :
    ∃ B : Subgroup G, B ≤ N ∧ IsPComponent 2 (B.subgroupOf N) ∧ L ≤ B ∧ conjugate B z = B ∧
      conjClosure L (twoLayerIn N) = B := by
  obtain ⟨hz2, hLC, hLpc⟩ := H.sec5.zL
  have hzN : z ∈ N := hCz (mem_centralizer_singleton_iff.mpr rfl)
  have hNC : N ⊓ centralizer ({z} : Set G) = centralizer ({z} : Set G) := inf_eq_right.mpr hCz
  obtain ⟨B, hBN, hB, hLB, hcl, -⟩ := foote_lemma_2_1_iv_subgroup hzN hz2
    (le_inf (hLC.trans hCz) hLC) (by rw [hNC]; exact hLpc)
  have hBz : conjugate B z = B := CFSG.conjugate_eq_self_of_mem_normalizer
    (twoLayerIn_le_normalizer hBN hB (H.z_mem_twoLayerIn hCt))
  refine ⟨B, hBN, hB, ?_, hBz, ?_⟩
  · rw [hBz, sup_idem] at hLB
    exact hLB
  · rw [hcl, hBz, sup_idem]

theorem false_of_equiv (h3 : Asc76.Asc76Theorem3Large) {N B : Subgroup G}
    (hCt : centralizer ({t} : Set G) ≤ N) (hNtop : N ≠ ⊤) (hBN : B ≤ N)
    (hB : IsPComponent 2 (B.subgroupOf N)) (hLB : L ≤ B)
    (e : L ⧸ pPrimeCore 2 L ≃* B ⧸ pPrimeCore 2 B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := H.sec5.sec4.simple
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have : IsSimpleGroup (B ⧸ pPrimeCore 2 B) := e.symm.isSimpleGroup
  have hna : ∃ a b : B ⧸ pPrimeCore 2 B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := H.sec5.quotient_nonabelian
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hdih : GorensteinWalter.HasDihedralSylowTwo (B ⧸ pPrimeCore 2 B) :=
    OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e.symm H.sec5.hasDihedralSylowTwo_quotient
  have htB : t ∈ B := hLB H.sec5.tL
  have hcen : center (B ⧸ pPrimeCore 2 B) = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hCtB : centralizer ({t} : Set G) ≤ normalizer (B : Set G) := by
    intro x hx
    have hxN := hCt hx
    by_contra hxB
    have hne : conjugate B x ≠ B := fun h => hxB (mem_normalizer_iff.mpr fun y => by
      rw [← mem_conjugate_iff, h])
    have hle := le_coreActionKernel_of_ne (conjugate_le_of_mem hBN hxN) hBN
      (isPComponent_conjugate_subgroupOf hxN hB) hB hne
    have htBx : t ∈ conjugate B x := by
      have hxt : x * t * x⁻¹ = t := by
        rw [show x * t = t * x from mem_centralizer_singleton_iff.mp hx]
        group
      rw [mem_conjugate_iff, hxt]
      exact htB
    exact center_ne_bot_of_mem_coreActionKernel htB H.sec5.t2 (hle htBx) hcen
  have hTE := tightlyEmbedded_of_centralizer_le hna hdih htB H.sec5.t2 hCtB
  have hR : IsSylowOf 2 (S ⊓ L) B := by
    refine isSylowOf_of_card (inf_le_right.trans hLB) ?_
    rw [H.sec5.R_sylow.card_eq, factorization_card_eq_of_equiv e]
  obtain ⟨a, -, b, -, hab⟩ := H.nonab
  have hB1 : B ≠ ⊥ := fun h => H.t_ne_one (by rw [h] at htB; exact mem_bot.mp htB)
  have hBtop : B ≠ ⊤ := fun h => hNtop (eq_top_iff.mpr (h ▸ hBN))
  exact false_of_tightlyEmbedded h3 hab hTE hB1 hBtop hR H.isDihedralTwoGroup_R H.four_lt_card_R

theorem conjugate_s_eq (h3 : Asc76.Asc76Theorem3Large) {N B : Subgroup G}
    (hCt : centralizer ({t} : Set G) ≤ N) (hNtop : N ≠ ⊤) (hsN : s ∈ N) (hBN : B ≤ N)
    (hB : IsPComponent 2 (B.subgroupOf N)) (hLB : L ≤ B) : conjugate B s = B := by
  by_contra hne
  have hle := le_coreActionKernel_of_ne (conjugate_le_of_mem hBN hsN) hBN
    (isPComponent_conjugate_subgroupOf hsN hB) hB hne
  have hzBs : z ∈ conjugate B s := by rw [mem_conjugate_iff, H.conj_s_z]; exact hLB H.sec5.tL
  obtain ⟨-, hLC, hLpc⟩ := H.sec5.zL
  obtain ⟨e⟩ := nonempty_equiv_of_mem_coreActionKernel H.mul_self_z hBN hB hLB hLC hLpc
    (hle hzBs)
  exact H.false_of_equiv h3 hCt hNtop hBN hB hLB e

end Hyp

end CFSG.ComponentClassification.Sol78.F514
