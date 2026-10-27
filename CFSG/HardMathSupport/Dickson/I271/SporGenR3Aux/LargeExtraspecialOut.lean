module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialOut

open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

@[expose] noncomputable def actQuot (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
  (autCenterQuot ↥J).comp J.normalizerMonoidHom

theorem ker_actQuot {J : Subgroup G} (hperf : commutator ↥J = ⊤) :
    (actQuot J).ker =
      (Subgroup.centralizer (J : Set G)).subgroupOf (Subgroup.normalizer (J : Set G)) := by
  rw [← Subgroup.normalizerMonoidHom_ker (H := J)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    exact (map_eq_one_iff _ (autCenterQuot_injective_of_perfect hperf)).1 h
  · intro h
    show autCenterQuot ↥J (J.normalizerMonoidHom x) = 1
    rw [h, map_one]

theorem autCenterQuot_conj' {Y : Type*} [Group Y] (y : Y) :
    autCenterQuot Y (MulAut.conj y) = MulAut.conj (y : Y ⧸ Subgroup.center Y) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [autCenterQuot_mk, MulAut.conj_apply, MulAut.conj_apply]
    rfl

theorem actQuot_of_mem {J : Subgroup G} {k : G} (hk : k ∈ J) :
    actQuot J ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj ((⟨k, hk⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) := by
  have h1 : J.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (⟨k, hk⟩ : ↥J) := by
    ext x
    rfl
  show autCenterQuot ↥J (J.normalizerMonoidHom _) = _
  rw [h1]
  exact autCenterQuot_conj' _

theorem exists_mem_of_actQuot_mem_inner {J : Subgroup G} (hperf : commutator ↥J = ⊤) {b : G}
    (hb : b ∈ Subgroup.normalizer (J : Set G))
    (h : actQuot J ⟨b, hb⟩ ∈ inner (↥J ⧸ Subgroup.center ↥J)) :
    ∃ k ∈ J, k⁻¹ * b ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
  have h2 : actQuot J ⟨(k : G), Subgroup.le_normalizer k.2⟩ = actQuot J ⟨b, hb⟩ := by
    rw [actQuot_of_mem k.2]
    exact ht
  have h3 : actQuot J ((⟨(k : G), Subgroup.le_normalizer k.2⟩ :
      ↥(Subgroup.normalizer (J : Set G)))⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  rw [← MonoidHom.mem_ker, ker_actQuot hperf, Subgroup.mem_subgroupOf] at h3
  exact ⟨k, k.2, h3⟩

theorem pow_dvd_card_mulAut {p k : ℕ} (hp : 0 < p) {w : G} (hw : orderOf w = p)
    {X J : Subgroup G} [Finite X] (hperf : commutator ↥J = ⊤)
    (hXN : X ≤ Subgroup.normalizer (J : Set G))
    (hC : X ⊓ Subgroup.centralizer (J : Set G) = Subgroup.zpowers w)
    (hX : p ^ (k + 1) ∣ Nat.card X) :
    p ^ k ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) := by
  let φ : X →* MulAut (↥J ⧸ Subgroup.center ↥J) := (actQuot J).comp (Subgroup.inclusion hXN)
  have hker : φ.ker.map X.subtype = Subgroup.zpowers w := by
    rw [← hC]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have h1 : actQuot J ⟨(x : G), hXN x.2⟩ = 1 := hx
      rw [← MonoidHom.mem_ker, ker_actQuot hperf, Subgroup.mem_subgroupOf] at h1
      exact h1
    · rintro ⟨hyX, hyC⟩
      refine ⟨⟨y, hyX⟩, ?_, rfl⟩
      show actQuot J ⟨y, hXN hyX⟩ = 1
      rw [← MonoidHom.mem_ker, ker_actQuot hperf, Subgroup.mem_subgroupOf]
      exact hyC
  have hkerc : Nat.card φ.ker = p := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, hker, Nat.card_zpowers, hw]
  have h1 : Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hkerc] at h1
  have h2 : p ^ k ∣ Nat.card φ.range := by
    have : p * p ^ k ∣ p * Nat.card φ.range := by
      rw [← h1, ← pow_succ']
      exact hX
    exact Nat.dvd_of_mul_dvd_mul_left hp this
  exact h2.trans (Subgroup.card_subgroup_dvd_card φ.range)

theorem pow_dvd_card_quot {p k : ℕ} (hp : 0 < p) {J : Subgroup G}
    (hZ : Nat.card (Subgroup.center ↥J) = p) (hJ : p ^ (k + 1) ∣ Nat.card J) :
    p ^ k ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
  rw [hZ] at h1
  rw [h1, pow_succ] at hJ
  exact Nat.dvd_of_mul_dvd_mul_right hp hJ

end CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialOut
