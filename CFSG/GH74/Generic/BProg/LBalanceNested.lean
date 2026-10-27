module

public import CFSG.GH74.GLS.Basic
import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic
import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74.GLS Subgroup

variable {G : Type} [Group G]

theorem centralizer_sup_zpowers (S : Subgroup G) (x : G) :
    centralizer ((S ⊔ zpowers x : Subgroup G) : Set G) =
      centralizer (S : Set G) ⊓ centralizer ({x} : Set G) := by
  have h : (S ⊔ zpowers x : Subgroup G) = Subgroup.closure ((S : Set G) ∪ {x}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← zpowers_eq_closure]
  rw [h, Subgroup.centralizer_closure]
  ext z
  simp [Subgroup.mem_centralizer_iff, and_comm]

theorem centralizer_zpowers_eq (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, Subgroup.centralizer_closure]

theorem isPGroup_two_zpowers {x : G} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    IsPGroup 2 ↥(zpowers x) := by
  obtain ⟨n, hn⟩ := hx
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]

variable [Finite G]

private theorem pLayerOf_eq_lBalancePLayer (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    pLayerOf p H = Open.lBalancePLayer p H := by
  rw [Stage2.Signalizer.L52Two.I1.pLayerOf_eq_map_pLayer,
    ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map]

theorem pLayerOf_le_of_normal (p : ℕ) [Fact p.Prime] {Y M : Subgroup G} (hYM : Y ≤ M)
    [(Y.subgroupOf M).Normal] : pLayerOf p Y ≤ pLayerOf p M := by
  rw [pLayerOf_eq_lBalancePLayer, pLayerOf_eq_lBalancePLayer]
  exact ComponentClassification.LBalance.pLayer_relative_normal_mono p Y M hYM

theorem pLayerOf_sup_zpowers_le (p : ℕ) [Fact p.Prime] {Y : Subgroup G} {x : G}
    (hx : x ∈ normalizer (Y : Set G)) : pLayerOf p (Y ⊔ zpowers x) ≤ pLayerOf p Y := by
  have hYM : Y ≤ Y ⊔ zpowers x := le_sup_left
  have hMN : Y ⊔ zpowers x ≤ normalizer (Y : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr hx)
  have : (Y.subgroupOf (Y ⊔ zpowers x)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  rw [pLayerOf_eq_lBalancePLayer, pLayerOf_eq_lBalancePLayer]
  refine ComponentClassification.LBalance.Asm.pLayer_le_of_pComponents_le p _ _ hYM fun L hL => ?_
  have : Group.IsPerfect L := ComponentClassification.LBalance.pComponent_perfect p _ L hL
  exact ComponentClassification.LBalance.Asm.le_of_perfect_le_sup_zpowers hx
    (ComponentClassification.LBalance.subnormal_le hL.1)

theorem pLayerOf_centralizer_sup_zpowers_le {S : Subgroup G} {x : G}
    (hxS : x ∈ normalizer (S : Set G)) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    pLayerOf 2 (centralizer ((S ⊔ zpowers x : Subgroup G) : Set G)) ≤
      pLayerOf 2 (centralizer (S : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY := ComponentClassification.LBalance.Asm.mem_normalizer_centralizer hxS
  have hYM : centralizer (S : Set G) ≤ centralizer (S : Set G) ⊔ zpowers x := le_sup_left
  have hxM : x ∈ centralizer (S : Set G) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hMN : centralizer (S : Set G) ⊔ zpowers x ≤ normalizer (centralizer (S : Set G) : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr hxY)
  rw [centralizer_sup_zpowers]
  have : ((centralizer (S : Set G) ⊓ centralizer ({x} : Set G)).subgroupOf
      ((centralizer (S : Set G) ⊔ zpowers x) ⊓ centralizer ({x} : Set G))).Normal := by
    refine (normal_subgroupOf_iff (inf_le_inf_right _ hYM)).mpr fun z c hz hc =>
      mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMN (mem_inf.mp hc).1) z).mp (mem_inf.mp hz).1
    · exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hz).2) (inv_mem (mem_inf.mp hc).2)
  have h1 := pLayerOf_le_of_normal 2 (inf_le_inf_right (centralizer ({x} : Set G)) hYM)
  have h2 : pLayerOf 2 ((centralizer (S : Set G) ⊔ zpowers x) ⊓ centralizer ({x} : Set G)) ≤
      pLayerOf 2 (centralizer (S : Set G) ⊔ zpowers x) := by
    have h := Stage2.Signalizer.L52Two.I1.pLayerOf_inf_centralizer_le (zpowers_le.mpr hxM)
      (isPGroup_two_zpowers hx2)
    rwa [centralizer_zpowers_eq] at h
  exact h1.trans (h2.trans (pLayerOf_sup_zpowers_le 2 hxY))

theorem exists_mem_normalizer_not_mem {S R : Subgroup G} (hSR : S < R) (hR : IsPGroup 2 ↥R) :
    ∃ x ∈ R, x ∈ normalizer (S : Set G) ∧ x ∉ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  have hlt : S.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun h => hSR.not_ge h
  obtain ⟨y, hy, hyS⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (S.subgroupOf R) hlt)
  refine ⟨y, y.2, ?_, hyS⟩
  rw [mem_normalizer_iff] at hy ⊢
  intro h
  constructor
  · intro hh
    exact (hy ⟨h, hSR.le hh⟩).mp hh
  · intro hh
    have hhR : h ∈ R := by
      have := R.mul_mem (R.mul_mem (R.inv_mem y.2) (hSR.le hh)) y.2
      simpa [mul_assoc] using this
    exact (hy ⟨h, hhR⟩).mpr hh

theorem pLayerOf_centralizer_le_of_le {S R : Subgroup G} (hSR : S ≤ R) (hR : IsPGroup 2 ↥R) :
    pLayerOf 2 (centralizer (R : Set G)) ≤ pLayerOf 2 (centralizer (S : Set G)) := by
  revert hSR
  induction S using WellFoundedGT.induction with
  | _ S ih =>
  intro hSR
  by_cases hSeq : S = R
  · subst hSeq
    exact le_rfl
  obtain ⟨x, hxR, hxN, hxS⟩ := exists_mem_normalizer_not_mem (lt_of_le_of_ne hSR hSeq) hR
  have hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hT : S < S ⊔ zpowers x :=
    lt_of_le_of_ne le_sup_left fun h => hxS (h ▸ mem_sup_right (mem_zpowers x))
  exact (ih _ hT (sup_le hSR (zpowers_le.mpr hxR))).trans
    (pLayerOf_centralizer_sup_zpowers_le hxN hx2)

theorem pLayerOf_centralizer_le_inf_centralizer_of_mem {R : Subgroup G} (hR : IsPGroup 2 ↥R)
    {d e : G} (hd : d ∈ R) (he : e ∈ R) :
    pLayerOf 2 (centralizer (R : Set G)) ≤
      pLayerOf 2 (centralizer ({d} : Set G) ⊓ centralizer ({e} : Set G)) := by
  have h := pLayerOf_centralizer_le_of_le (S := zpowers d ⊔ zpowers e)
    (sup_le (zpowers_le.mpr hd) (zpowers_le.mpr he)) hR
  rwa [centralizer_sup_zpowers, centralizer_zpowers_eq] at h

end CFSG.GH74.Generic.BProg
