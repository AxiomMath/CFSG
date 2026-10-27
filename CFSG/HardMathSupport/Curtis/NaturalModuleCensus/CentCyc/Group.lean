module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open Subgroup
open scoped Pointwise

theorem exists_cover_of_cyclic_image {Γ H : Type*} [Group Γ] [Finite Γ] [Group H]
    (ρ : Γ →* H) {E : Subgroup Γ} (h : IsCyclic (E.map ρ)) :
    ∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ ρ.ker := by
  obtain ⟨⟨g, hg⟩, hgen⟩ := h
  obtain ⟨u, huE, rfl⟩ := Subgroup.mem_map.mp hg
  refine ⟨u, huE, fun e he => ?_⟩
  have hmem : ρ e ∈ E.map ρ := Subgroup.mem_map_of_mem ρ he
  obtain ⟨m, hm⟩ := hgen ⟨ρ e, hmem⟩
  have hm' : (ρ u) ^ m = ρ e := congrArg Subtype.val hm
  have hn : 0 < orderOf u := orderOf_pos u
  refine ⟨(m % (orderOf u : ℤ)).toNat, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, mul_inv_eq_one]
  have h0 : 0 ≤ m % (orderOf u : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have h1 : ((m % (orderOf u : ℤ)).toNat : ℤ) = m % (orderOf u : ℤ) := Int.toNat_of_nonneg h0
  have h2 : u ^ ((m % (orderOf u : ℤ)).toNat) = u ^ m := by
    rw [← zpow_natCast, h1, zpow_mod_orderOf]
  rw [← map_pow, h2, map_zpow]
  exact hm'.symm

theorem mem_zpowers_of_orderOf_eq {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {a b : G} (h : orderOf a = orderOf b) : b ∈ zpowers a := by
  have : zpowers a = zpowers b := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, h]
  rw [this]
  exact mem_zpowers b

theorem exists_conj_mem_sylow {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p D) {y : D} (hy : y ∈ (Q : Subgroup D)) :
    ∃ g : D, g⁻¹ * y * g ∈ (P : Subgroup D) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P Q
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨g, ?_⟩
  simpa [MulAut.smul_def, mul_assoc] using hz

theorem normal_pPrime_of_cycSylow {D : Type*} [Group D] [Finite D] {p : ℕ} (hp : p.Prime)
    (hcyc : ∀ A : Subgroup D, IsPGroup p A → IsCyclic A) {N : Subgroup D} [N.Normal]
    {x : D} (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxN : x ∉ N) : ¬ p ∣ Nat.card N := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨⟨y, hyN⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
  have hyD : orderOf y = p := by simpa using hy
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxP : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  have hyP : IsPGroup p (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hyD, pow_one])
  obtain ⟨P, hxP'⟩ := hxP.exists_le_sylow
  obtain ⟨Q, hyQ⟩ := hyP.exists_le_sylow
  have hxP'' : x ∈ (P : Subgroup D) := hxP' (mem_zpowers x)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P Q (hyQ (mem_zpowers y))
  have : IsCyclic (P : Subgroup D) := hcyc _ P.isPGroup'
  have hord : orderOf (⟨g⁻¹ * y * g, hg⟩ : (P : Subgroup D)) =
      orderOf (⟨x, hxP''⟩ : (P : Subgroup D)) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxo, ← hyD]
    have : g⁻¹ * y * g = (MulAut.conj g⁻¹) y := by simp
    rw [this]
    exact MulEquiv.orderOf_eq _ y
  have hmem := mem_zpowers_of_orderOf_eq hord
  have hmem' : x ∈ zpowers (g⁻¹ * y * g) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    exact congrArg Subtype.val hk
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
  apply hxN
  rw [← hk]
  exact zpow_mem (by simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance y hyN g⁻¹) k

theorem cyc_of_sylow_dvd {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {Dh : Subgroup K} (hcyc : ∀ A ≤ Dh, IsPGroup p A → IsCyclic A)
    (hdvd : ∀ k, p ^ k ∣ Nat.card K → p ^ k ∣ Nat.card Dh) :
    ∀ A : Subgroup K, IsPGroup p A → IsCyclic A := by
  have : Fact p.Prime := ⟨hp⟩
  intro A hA
  obtain ⟨P'⟩ : Nonempty (Sylow p Dh) := inferInstance
  set R : Subgroup K := (P' : Subgroup Dh).map Dh.subtype with hR
  have hle1 : (Nat.card K).factorization p ≤ (Nat.card Dh).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (hdvd _ (Nat.ordProj_dvd _ _))
  have hle2 : (Nat.card Dh).factorization p ≤ (Nat.card K).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
      ((Nat.ordProj_dvd _ _).trans Dh.card_subgroup_dvd_card)
  have hRcard : Nat.card R = p ^ (Nat.card K).factorization p := by
    rw [hR, Subgroup.card_subtype, P'.card_eq_multiplicity, le_antisymm hle2 hle1]
  let S : Sylow p K := Sylow.ofCard R hRcard
  have hSR : (S : Subgroup K) = R := rfl
  have hRle : R ≤ Dh := Subgroup.map_subtype_le _
  have hRcyc : IsCyclic R := hcyc R hRle (by
    have : IsPGroup p (P' : Subgroup Dh) := P'.isPGroup'
    exact (this.map Dh.subtype))
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S Q
  have hQ : (Q : Subgroup K) = MulAut.conj g • R := by
    rw [← hg, Sylow.coe_subgroup_smul, hSR]
  have hQcyc : IsCyclic (Q : Subgroup K) := by
    rw [hQ]
    exact isCyclic_of_surjective _ (Subgroup.equivSMul (MulAut.conj g) R).surjective
  exact Subgroup.isCyclic_of_le hAQ

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
