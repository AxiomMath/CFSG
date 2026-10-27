module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem map_subgroupOf_normalizerMonoidHom_eq {P V : Subgroup G} {a : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    (V.subgroupOf P).map (P.normalizerMonoidHom ⟨a, haP⟩ : ↥P →* ↥P) = V.subgroupOf P := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    have hq'V : (q' : G) ∈ V := (Subgroup.mem_subgroupOf).mp hq'
    change (a * (q' : G) * a⁻¹) ∈ V
    exact (haV _).mp hq'V
  · intro hq
    have hqV : (q : G) ∈ V := (Subgroup.mem_subgroupOf).mp hq
    have hq1 : a⁻¹ * (q : G) * a ∈ P := by
      have := (Subgroup.inv_mem _ haP (q : G)).mp q.2
      simpa using this
    refine ⟨⟨a⁻¹ * q * a, hq1⟩, ?_, ?_⟩
    · refine (Subgroup.mem_subgroupOf).mpr ?_
      have := (Subgroup.inv_mem _ haV (q : G)).mp hqV
      simpa using this
    · apply Subtype.ext
      show a * (a⁻¹ * (q : G) * a) * a⁻¹ = q
      group

@[expose] noncomputable def conjQuotAut {P V : Subgroup G} [(V.subgroupOf P).Normal] {a : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    MulAut (↥P ⧸ V.subgroupOf P) :=
  QuotientGroup.congr (V.subgroupOf P) (V.subgroupOf P)
    (P.normalizerMonoidHom ⟨a, haP⟩) (map_subgroupOf_normalizerMonoidHom_eq haP haV)

@[simp] theorem conjQuotAut_mk {P V : Subgroup G} [(V.subgroupOf P).Normal] {a : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G))
    (x : ↥P) :
    conjQuotAut haP haV (x : ↥P ⧸ V.subgroupOf P) =
      ((⟨a * x * a⁻¹, (haP x).mp x.2⟩ : ↥P) : ↥P ⧸ V.subgroupOf P) := rfl

@[expose] noncomputable def conjQuotHom {L P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* MulAut (↥P ⧸ V.subgroupOf P) where
  toFun l := conjQuotAut (hLP l.2) (hLV l.2)
  map_one' := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [conjQuotAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show (1 : G) * x * 1⁻¹ = x
    group
  map_mul' a b := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, conjQuotAut_mk, conjQuotAut_mk, conjQuotAut_mk]
    congr 1
    apply Subtype.ext
    show (a : G) * b * x * ((a : G) * b)⁻¹ =
      a * (b * x * (b : G)⁻¹) * (a : G)⁻¹
    group

@[simp] theorem conjQuotHom_apply {L P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (l : ↥L) : conjQuotHom hLP hLV l = conjQuotAut (hLP l.2) (hLV l.2) := rfl

end CFSG.GroupTheory
