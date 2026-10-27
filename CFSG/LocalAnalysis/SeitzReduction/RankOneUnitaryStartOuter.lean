module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem inner_iff_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T) :
    (∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) ↔ x ∈ szT₁ L T ⊔ zpowers t := by
  obtain ⟨-, -, -, -, -, -, hinner⟩ := h.start_of_card_sylow hS2
  refine ⟨fun ⟨l, hl, hxl⟩ => hinner x hxT l hl hxl, fun hx => ?_⟩
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hx
  refine ⟨a, szT₁_le_right L T ha, fun y hy => ?_⟩
  have hzy : y * z = z * y := commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem y hy)
  calc a * z * y * (a * z)⁻¹ = a * (z * y) * z⁻¹ * a⁻¹ := by group
    _ = a * y * a⁻¹ := by rw [← hzy]; group

theorem finite_mulAut (L : Subgroup G) : Finite (MulAut L) :=
  Finite.of_injective (fun φ : MulAut L => (φ : L → L)) DFunLike.coe_injective

theorem exists_outHom_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ φ : T →* Outer L, (∀ x : T, φ x = 1 ↔ (x : G) ∈ szT₁ L T ⊔ zpowers t) ∧
      IsCyclic φ.range := by
  have : Finite (MulAut L) := finite_mulAut L
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : T →* Outer L := (QuotientGroup.mk' (inner L)).comp
    (L.normalizerMonoidHom.comp (inclusion h.le_normalizer)) with hφ
  refine ⟨φ, fun x => ?_, ?_⟩
  · rw [← h.inner_iff_mem_of_card_sylow hS2 x.2, hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, g.2, fun y hy => ?_⟩
      have := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hg
      simp only [MulAut.conj_apply, coe_mul, coe_inv, MonoidHom.comp_apply] at this
      rw [this, normalizerMonoidHom_apply_apply_coe]
      rfl
    · rintro ⟨l, hl, hxl⟩
      refine ⟨⟨l, hl⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
      rw [MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe]
      simp only [MulAut.conj_apply, coe_mul, coe_inv]
      exact (hxl y y.2).symm
  · have hp : IsPGroup 2 φ.range :=
      h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 h.two_le h.model
    have := hB.isCyclic_sylow_outer S
    exact isCyclic_of_injective (inclusion hS) (inclusion_injective hS)

theorem isCyclic_quotient_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    [((szT₁ L T ⊔ zpowers t).subgroupOf T).Normal] :
    IsCyclic (T ⧸ (szT₁ L T ⊔ zpowers t).subgroupOf T) := by
  obtain ⟨φ, hker, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
  have hk : φ.ker = (szT₁ L T ⊔ zpowers t).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, hker, mem_subgroupOf]
  exact ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).isCyclic.mpr hcyc

theorem mul_mem_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x x' : G} (hx : x ∈ T)
    (hx' : x' ∈ T) (hx2 : x ^ 2 = 1) (hx'2 : x' ^ 2 = 1) (hxS : x ∉ szT₁ L T ⊔ zpowers t)
    (hx'S : x' ∉ szT₁ L T ⊔ zpowers t) : x * x' ∈ szT₁ L T ⊔ zpowers t := by
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨φ, hker, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
  have hord : ∀ {y : G} (hy : y ∈ T), y ^ 2 = 1 → y ∉ szT₁ L T ⊔ zpowers t →
      orderOf (φ ⟨y, hy⟩) = 2 := by
    intro y hy hy2 hyS
    refine orderOf_eq_prime ?_ fun h1 => hyS ((hker ⟨y, hy⟩).mp h1)
    rw [← map_pow]
    have : (⟨y, hy⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
    rw [this, map_one]
  have heq := CFSG.LocalAnalysis.eq_of_orderOf_eq_two_of_isCyclic_subgroup hcyc
    (⟨⟨x, hx⟩, rfl⟩ : φ ⟨x, hx⟩ ∈ φ.range) (⟨⟨x', hx'⟩, rfl⟩ : φ ⟨x', hx'⟩ ∈ φ.range)
    (hord hx hx2 hxS) (hord hx' hx'2 hx'S)
  have h1 : φ (⟨x, hx⟩ * ⟨x', hx'⟩) = 1 := by
    rw [map_mul, ← heq, ← sq, ← map_pow]
    have : (⟨x, hx⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    rw [this, map_one]
  exact (hker _).mp h1

theorem commutator_le_szT₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ⁅T, T⁆ ≤ szT₁ L T := by
  obtain ⟨htT, -, -, hTN₁, -, hMn, -⟩ := h.start_of_card_sylow hS2
  set N₁ := (szT₁ L T).subgroupOf T with hN₁def
  set M := (szT₁ L T ⊔ zpowers t).subgroupOf T with hMdef
  have hN₁ : N₁.Normal := (normal_subgroupOf_iff_le_normalizer (szT₁_le_left L T)).mpr hTN₁
  have := hMn
  have := h.isCyclic_quotient_of_card_sylow hS2
  have hle : N₁ ≤ M.comap (MonoidHom.id T) := fun x hx => by
    rw [comap_id, hMdef, mem_subgroupOf]
    exact mem_sup_left (mem_subgroupOf.mp hx)
  set φ : T ⧸ N₁ →* T ⧸ M := QuotientGroup.map N₁ M (MonoidHom.id T) hle with hφ
  have hkerZ : φ.ker ≤ center (T ⧸ N₁) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.map_mk, MonoidHom.id_apply,
      QuotientGroup.eq_one_iff, hMdef, mem_subgroupOf] at hq
    obtain ⟨a, ha, z, hz, hxaz⟩ :=
      exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hq
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hcz : ∀ y : T, y * ⟨z, hzT⟩ = ⟨z, hzT⟩ * y := fun y => Subtype.ext
      (commute_of_mem_zpowers hz (mem_centralizer_singleton_iff.mp (h.le y.2)))
    have hx' : (QuotientGroup.mk x : T ⧸ N₁) = QuotientGroup.mk ⟨z, hzT⟩ := by
      rw [QuotientGroup.eq, hN₁def, mem_subgroupOf]
      have haz : a * z = z * a :=
        commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ a ha)
      have e : ((x⁻¹ * ⟨z, hzT⟩ : T) : G) = a⁻¹ := by
        rw [coe_mul, coe_inv, ← hxaz, haz]
        group
      rw [e]
      exact inv_mem ha
    rw [hx', mem_center_iff]
    intro p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcz y]
  have hcomm := φ.isMulCommutative_of_isCyclic_of_ker_le_center hkerZ
  rw [commutator_le]
  intro x hx y hy
  have e := hcomm.is_comm.comm (QuotientGroup.mk ⟨x, hx⟩ : T ⧸ N₁) (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN₁def,
    mem_subgroupOf] at e
  have e' : ((⟨x, hx⟩ * ⟨y, hy⟩ : T)⁻¹ * (⟨y, hy⟩ * ⟨x, hx⟩) : T) = (x * y)⁻¹ * (y * x) := by
    simp
  rw [e'] at e
  have h1 := (mem_normalizer_iff.mp (hTN₁ (mul_mem hx hy)) _).mp (inv_mem e)
  rw [commutatorElement_def]
  convert h1 using 1
  group

end U3Start

end CFSG.SeitzReduction.RankOne
