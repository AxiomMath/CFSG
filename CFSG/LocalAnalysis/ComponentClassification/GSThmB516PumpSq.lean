module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Over
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftGomi

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Pump516

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_normalizer_inf {A B : Subgroup Y} {g : Y} (hA : g ∈ normalizer (A : Set Y))
    (hB : g ∈ normalizer (B : Set Y)) : g ∈ normalizer ((A ⊓ B : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  exact and_congr (hA h) (hB h)

omit [Finite Y] in
theorem centralizer_le_centralizer_sq (β : Y) :
    centralizer ({β} : Set Y) ≤ centralizer ({β ^ 2} : Set Y) := fun x hx => by
  have hc : Commute x β := mem_centralizer_singleton_iff.mp hx
  exact mem_centralizer_singleton_iff.mpr (hc.pow_right 2).eq

theorem fixedLayer_sq_data {L J JB : Subgroup Y} {β t : Y} (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1)
    (hN : β ∈ normalizer (L : Set Y)) (hβt : β ∈ centralizer ({t} : Set Y))
    (hJLC : J ≤ L ⊓ centralizer ({t} : Set Y))
    (hJ : IsPComponent 2 (J.subgroupOf (L ⊓ centralizer ({t} : Set Y))))
    (hβJ : β ∈ coreActionKernel J) (hJBJ : JB ≤ J) (hJBβ : JB ≤ centralizer ({β} : Set Y))
    (hJBp : ⁅JB, JB⁆ = JB) (hJsup : J ≤ JB ⊔ oddCoreIn J) :
    GSLit.fixedLayer J (zpowers (β ^ 2)) ≤
        (L ⊓ centralizer ({β ^ 2} : Set Y)) ⊓ centralizer ({t} : Set Y) ∧
      IsPComponent 2 ((GSLit.fixedLayer J (zpowers (β ^ 2))).subgroupOf
        ((L ⊓ centralizer ({β ^ 2} : Set Y)) ⊓ centralizer ({t} : Set Y))) ∧
      JB ≤ GSLit.fixedLayer J (zpowers (β ^ 2)) ∧
      GSLit.fixedLayer J (zpowers (β ^ 2)) ≤
        JB ⊔ oddCoreIn (GSLit.fixedLayer J (zpowers (β ^ 2))) ∧
      β ∈ coreActionKernel (GSLit.fixedLayer J (zpowers (β ^ 2))) ∧
      Nonempty (↥(GSLit.fixedLayer J (zpowers (β ^ 2))) ⧸
        pPrimeCore 2 ↥(GSLit.fixedLayer J (zpowers (β ^ 2))) ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := L ⊓ centralizer ({t} : Set Y) with hC
  set J' := GSLit.fixedLayer J (zpowers (β ^ 2)) with hJ'
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJLC).mp hJ).2.2
  have hE2 := isPGroup_zpowers_of_pow hβ
  have hβE : zpowers β ≤ coreActionKernel J := zpowers_le.mpr hβJ
  have hγβ : zpowers (β ^ 2) ≤ zpowers β := zpowers_le.mpr (pow_mem (mem_zpowers β) 2)
  have hγE := hγβ.trans hβE
  have hγ2 := hE2.to_le hγβ
  set XJ := C ⊔ zpowers β with hXJ
  have hβC : β ∈ normalizer (C : Set Y) := mem_normalizer_inf hN (le_normalizer hβt)
  have hCXJ : C ≤ XJ := le_sup_left
  have hCn : (C.subgroupOf XJ).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCXJ).mpr (sup_le le_normalizer (zpowers_le.mpr hβC))
  have hJXJ : IsPComponent 2 (J.subgroupOf XJ) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJLC hCXJ hCn.isSubnormal).mpr
      hJ
  have hJs : (J.subgroupOf XJ).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J XJ (hJLC.trans hCXJ)).mp hJXJ).1
  have hJ'1 := GSLit.fixedLayer_isPComponent (hJLC.trans hCXJ) hJs
    (hγβ.trans le_sup_right) hγE hγ2 hJq
  have hJ'le : J' ≤ J ⊓ centralizer ({β ^ 2} : Set Y) := by
    have h1 := GSLit.fixedLayer_le_inf J (zpowers (β ^ 2))
    rwa [centralizer_zpowers_eq] at h1
  have hJ'D : J' ≤ (L ⊓ centralizer ({β ^ 2} : Set Y)) ⊓ centralizer ({t} : Set Y) :=
    fun x hx => by
      obtain ⟨hxJ, hxγ⟩ := mem_inf.mp (hJ'le hx)
      obtain ⟨hxL, hxt⟩ := mem_inf.mp (hJLC hxJ)
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxL, hxγ⟩, hxt⟩
  have hDle : (L ⊓ centralizer ({β ^ 2} : Set Y)) ⊓ centralizer ({t} : Set Y) ≤
      XJ ⊓ centralizer ((zpowers (β ^ 2) : Subgroup Y) : Set Y) := by
    rw [centralizer_zpowers_eq]
    intro x hx
    obtain ⟨hx1, hxt⟩ := mem_inf.mp hx
    obtain ⟨hxL, hxγ⟩ := mem_inf.mp hx1
    exact mem_inf.mpr ⟨hCXJ (mem_inf.mpr ⟨hxL, hxt⟩), hxγ⟩
  have hJ'2 := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJ'D hDle hJ'1
  have hJBJ' : JB ≤ J' := by
    refine (SeitzReduction.F4Pilot.le_closure_two_pow_of_perfect hJBp).trans ?_
    rw [hJ', GSLit.fixedLayer_eq_closure hJq hγE hγ2]
    refine closure_mono fun x ⟨hxJB, k, hk⟩ => ⟨mem_inf.mpr ⟨hJBJ hxJB, ?_⟩, ?_⟩
    · rw [centralizer_zpowers_eq]
      exact centralizer_le_centralizer_sq β (hJBβ hxJB)
    · obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
      exact ⟨m, hm⟩
  obtain ⟨hJ'sup, hJ'O⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hγE hγ2
  refine ⟨hJ'D, hJ'2, hJBJ', ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxJ : x ∈ J := (mem_inf.mp (hJ'le hx)).1
    have hJBN : JB ≤ normalizer (oddCoreIn J : Set Y) := fun y hy =>
      Over516.normalizer_le_normalizer_oddCoreIn J (le_normalizer (hJBJ hy))
    have h1 : x ∈ ((JB ⊔ oddCoreIn J : Subgroup Y) : Set Y) := hJsup hxJ
    rw [coe_mul_of_left_le_normalizer_right _ _ hJBN] at h1
    obtain ⟨y, hy, o, ho, rfl⟩ := Set.mem_mul.mp h1
    have hoJ' : o ∈ J' := by
      have := mul_mem (inv_mem (hJBJ' hy)) hx
      rwa [inv_mul_cancel_left] at this
    have hoO : o ∈ oddCoreIn J' := by
      show o ∈ (pPrimeCore 2 ↥J').map J'.subtype
      rw [hJ'O]
      exact mem_inf.mpr ⟨hoJ', ho⟩
    exact mul_mem (mem_sup_left hy) (mem_sup_right hoO)
  ·
    have hβz : β ∈ normalizer ((zpowers (β ^ 2) : Subgroup Y) : Set Y) :=
      centralizer_le_normalizer _ (by
        rw [centralizer_zpowers_eq]
        exact mem_centralizer_singleton_iff.mpr (Commute.self_pow β 2).eq)
    have hβN : β ∈ normalizer (J' : Set Y) :=
      GSLit.mem_normalizer_fixedLayer (mem_coreActionKernel.mp hβJ).1 hβz
    refine mem_coreActionKernel.mpr ⟨hβN, fun j hj => ?_⟩
    rw [hJ'O]
    refine mem_inf.mpr ⟨?_, (mem_coreActionKernel.mp hβJ).2 j (mem_inf.mp (hJ'le hj)).1⟩
    have h1 : β⁻¹ * j * β ∈ J' := by
      have := (mem_normalizer_iff.mp (inv_mem hβN) j).mp hj
      rwa [inv_inv] at this
    rw [show j⁻¹ * β⁻¹ * j * β = j⁻¹ * (β⁻¹ * j * β) by group]
    exact mul_mem (inv_mem hj) h1
  · obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv (hJ'le.trans inf_le_left) hJ'sup
    exact ⟨e⟩

end Pump516

end CFSG.ComponentClassification.GSThmB
