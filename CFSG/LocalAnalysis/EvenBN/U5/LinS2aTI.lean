module

public import CFSG.LocalAnalysis.EvenBN.U5.LinTorus
public import CFSG.LocalAnalysis.EvenBN.U5.LinModelSylow
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineSylow

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

theorem lins2a_pow_two_pow_add {M : Type*} [Group M] {x : M} {n : ℕ} (h : x ^ 2 ^ n = 1)
    (k : ℕ) : x ^ 2 ^ (n + k) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

theorem lins2a_eq_of_inv_mul_mem {M : Type} [Group M] [Finite M] {K : Subgroup M}
    (hK : Odd (Nat.card K)) (hcen : ∀ k ∈ K, ∀ x : M, x * k = k * x) {r q : M} {a b : ℕ}
    (hr : r ^ 2 ^ a = 1) (hq : q ^ 2 ^ b = 1) (hrq : r⁻¹ * q ∈ K) : q = r := by
  have hrk : Commute r (r⁻¹ * q) := hcen _ hrq r
  have hc : Commute r⁻¹ q := by
    have h1 : Commute r (r * (r⁻¹ * q)) := (Commute.refl r).mul_right hrk
    rw [mul_inv_cancel_left] at h1
    exact h1.inv_left
  have h1 : (r⁻¹) ^ 2 ^ (a + b) = 1 := by
    rw [inv_pow, lins2a_pow_two_pow_add hr b, inv_one]
  have h2 : q ^ 2 ^ (a + b) = 1 := by
    rw [add_comm]
    exact lins2a_pow_two_pow_add hq a
  have hk : (r⁻¹ * q) ^ 2 ^ (a + b) = 1 := by
    rw [hc.mul_pow, h1, h2, one_mul]
  exact (inv_mul_eq_one.1 (eq_one_of_mem_of_pow_two_pow hK hrq hk)).symm

theorem lins2a_core {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ]
    (π : M →* Λ) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker))
    (hcen : ∀ k ∈ π.ker, ∀ x : M, x * k = k * x)
    (hΛ : ∀ P P' : Subgroup Λ, IsSylowOf 2 P ⊤ → IsSylowOf 2 P' ⊤ → P ≠ P' →
      ∀ x ∈ P ⊓ P', x * x = 1)
    {R Q : Subgroup M} (hR : IsSylowOf 2 R ⊤) (hQ : IsPGroup 2 Q) {z : M} (hzQ : z ∈ Q)
    (hzR : z ∈ R) (hz : z * z ≠ 1) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  have hS : IsSylowOf 2 (T : Subgroup M) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  have hEq : R.map π = (T : Subgroup M).map π := by
    by_contra hne
    have hx := hΛ _ _ (LinCase.linto_isSylowOf_map π hπ hker hR)
      (LinCase.linto_isSylowOf_map π hπ hker hS) hne (π z)
      ⟨Subgroup.mem_map_of_mem π hzR, Subgroup.mem_map_of_mem π (hQT hzQ)⟩
    apply hz
    have hk : z * z ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hx
    obtain ⟨n, hn⟩ := hR.isPGroup ⟨z * z, mul_mem hzR hzR⟩
    have hn' : (z * z) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact eq_one_of_mem_of_pow_two_pow hker hk hn'
  intro q hq
  have hπq : π q ∈ R.map π := by
    rw [hEq]
    exact Subgroup.mem_map_of_mem π (hQT hq)
  obtain ⟨r, hrR, hπr⟩ := Subgroup.mem_map.1 hπq
  have hrq : r⁻¹ * q ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπr, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hR.isPGroup ⟨r, hrR⟩
  obtain ⟨b, hb⟩ := hQ ⟨q, hq⟩
  have ha' : r ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : q ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  rw [lins2a_eq_of_inv_mul_mem hker hcen ha' hb' hrq]
  exact hrR

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lins2a_ker_central (hl : d.LinCtx) :
    ∀ k ∈ (linπ hl).ker, ∀ x : d.M₂, x * k = k * x := by
  intro k hk x
  rw [MonoidHom.mem_ker] at hk
  have hmem : (⟨(k : G), lin_M₂_le_H hl k.2⟩ : ↥d.s38dH) ∈ d.s38dO := by
    have h2 := congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hk' : (k : G) ∈ (s39a1O d).map (s39a1H d).subtype :=
    Subgroup.mem_map.2 ⟨⟨(k : G), lin_M₂_le_H hl k.2⟩, hmem, rfl⟩
  apply Subtype.ext
  exact (hl.toCaseHyp.s39a1_odd (k : G) hk' (x : G) x.2).symm

theorem lin_ti_lift (hl : d.LinCtx) {R Q : Subgroup G} (hR : IsSylowOf 2 R d.M₂) (hQM : Q ≤ d.M₂)
    (hQ : IsPGroup 2 Q) {z : G} (hzQ : z ∈ Q) (hzR : z ∈ R) (hz : z * z ≠ 1) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  have hzM : z ∈ d.M₂ := hQM hzQ
  have hR₀ : IsSylowOf 2 (R.subgroupOf d.M₂) (⊤ : Subgroup ↥d.M₂) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hR.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hR).2.2
  have hΛ : ∀ P P' : Subgroup ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)), IsSylowOf 2 P ⊤ →
      IsSylowOf 2 P' ⊤ → P ≠ P' → ∀ x ∈ P ⊓ P', x * x = 1 :=
    LinCase.l3SylowInt (2 * f) (by omega) _ (lin_layer_facts hl).2.1
  have hzQ₀ : (⟨z, hzM⟩ : ↥d.M₂) ∈ Q.subgroupOf d.M₂ := Subgroup.mem_subgroupOf.2 hzQ
  have hzR₀ : (⟨z, hzM⟩ : ↥d.M₂) ∈ R.subgroupOf d.M₂ := Subgroup.mem_subgroupOf.2 hzR
  have hz₀ : (⟨z, hzM⟩ : ↥d.M₂) * ⟨z, hzM⟩ ≠ 1 :=
    fun e => hz (by simpa using congrArg Subtype.val e)
  have hle := lins2a_core (linπ hl) (lin_π_surjective hl) (lin_π_ker_odd hl)
    (lins2a_ker_central hl) hΛ hR₀ (hQ.comap_subtype (K := d.M₂)) hzQ₀ hzR₀ hz₀
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 hx :
    (⟨x, hQM hx⟩ : ↥d.M₂) ∈ Q.subgroupOf d.M₂))

theorem lin_ti_lift₅ (hl : d.LinCtx) {R Q : Subgroup G} (hR : IsSylowOf 2 R d.M₅) (hQM : Q ≤ d.M₅)
    (hQ : IsPGroup 2 Q) {z : G} (hzQ : z ∈ Q) (hzR : z ∈ R) (hz : z * z ≠ 1) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM₅, -, -⟩ := hl.hyp.s39a1_conj_r
  have hc : Function.Injective (MulAut.conj d.r⁻¹).toMonoidHom := (MulAut.conj d.r⁻¹).injective
  have hM : d.M₅.map (MulAut.conj d.r⁻¹).toMonoidHom = d.M₂ := by
    rw [hM₅, s39a1_ti_lift₅_map_conj_inv]
  have hR' : IsSylowOf 2 (R.map (MulAut.conj d.r⁻¹).toMonoidHom) d.M₂ := by
    rw [← hM]
    refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono hR.le) ?_
    rw [Subgroup.card_map_of_injective hc, Subgroup.card_map_of_injective hc]
    exact hR.card_eq
  have hQM' : Q.map (MulAut.conj d.r⁻¹).toMonoidHom ≤ d.M₂ := by
    rw [← hM]
    exact Subgroup.map_mono hQM
  have hz' : (MulAut.conj d.r⁻¹).toMonoidHom z * (MulAut.conj d.r⁻¹).toMonoidHom z ≠ 1 := by
    rw [← map_mul]
    exact fun h1 => hz ((map_eq_one_iff _ hc).1 h1)
  have hle := lin_ti_lift hl hR' hQM' (hQ.map _)
    (Subgroup.mem_map_of_mem (MulAut.conj d.r⁻¹).toMonoidHom hzQ)
    (Subgroup.mem_map_of_mem (MulAut.conj d.r⁻¹).toMonoidHom hzR) hz'
  exact (Subgroup.map_le_map_iff_of_injective hc).1 hle

end Data

end CFSG.LocalAnalysis.EvenBN.U5
