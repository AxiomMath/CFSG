module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G] {p : ℕ}

theorem IsSylowOf.exists_mem_conj [Finite G] [Fact p.Prime] {P P' K : Subgroup G}
    (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ K := by
      rw [hx]
      exact K.mul_mem (K.mul_mem g.2 z.2) (K.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

section Cores

variable {H : Type*} [Group H]

theorem isPConstrained_of_centralizer_le [Finite H] [Fact p.Prime] {P : Subgroup H}
    (hP : IsSylowOf p P (Op_p'p p H)) (hC : centralizer (P : Set H) ≤ Op_p'p p H) :
    IsPConstrained p H := by
  intro P' hP' x hx
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'
  have hxc : k⁻¹ * x * k ∈ centralizer (P : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : k * y * k⁻¹ ∈ P' := by
      rw [hconj]
      have : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rw [this]
      exact hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hx) _ hy'
    calc y * (k⁻¹ * x * k) = k⁻¹ * ((k * y * k⁻¹) * x) * k := by group
      _ = k⁻¹ * (x * (k * y * k⁻¹)) * k := by rw [h1]
      _ = k⁻¹ * x * k * y := by group
  have h2 := hC hxc
  have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  rw [this]
  exact (Op_p'p p H).mul_mem ((Op_p'p p H).mul_mem hk h2) ((Op_p'p p H).inv_mem hk)

instance Op_p'p_characteristic : (Op_p'p p H).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  have hM : (pPrimeCore p H).map φ.toMonoidHom = pPrimeCore p H :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  let φ' : H ⧸ pPrimeCore p H ≃* H ⧸ pPrimeCore p H :=
    QuotientGroup.congr (pPrimeCore p H) (pPrimeCore p H) φ hM
  have hcore := pCore_map_iso p φ'
  change QuotientGroup.mk' (pPrimeCore p H) (φ x) ∈ pCore p (H ⧸ pPrimeCore p H)
  rw [← hcore]
  refine ⟨QuotientGroup.mk' (pPrimeCore p H) x, hx, ?_⟩
  change φ' (QuotientGroup.mk x) = QuotientGroup.mk (φ x)
  exact QuotientGroup.congr_mk _ _ φ hM x

theorem pPrimeCore_map_subtype_eq_inf [Finite H] [Fact p.Prime] {N : Subgroup H}
    (hN : N.Normal) : (pPrimeCore p N).map N.subtype = N ⊓ pPrimeCore p H := by
  rw [pPrimeCore_eq_piCore, pPrimeCore_eq_piCore]
  exact LocalCores.prime_set_core_normal_intersection _ hN

theorem exists_pow_mem_pPrimeCore_of_mem_Op_p'p {x : H} (hx : x ∈ Op_p'p p H) :
    ∃ k : ℕ, x ^ p ^ k ∈ pPrimeCore p H := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (G := H ⧸ pPrimeCore p H) (p := p)) ⟨_, hx⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

theorem le_Op_p'p_of_normal {X : Subgroup H} (hX : X.Normal)
    (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ pPrimeCore p H) : X ≤ Op_p'p p H := by
  have hmap : (X.map (QuotientGroup.mk' (pPrimeCore p H))).Normal :=
    hX.map _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup p (X.map (QuotientGroup.mk' (pPrimeCore p H))) := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hpow x hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hle : X.map (QuotientGroup.mk' (pPrimeCore p H)) ≤ pCore p (H ⧸ pPrimeCore p H) :=
    le_sSup (show X.map (QuotientGroup.mk' (pPrimeCore p H)) ∈
      {K : Subgroup (H ⧸ pPrimeCore p H) | K.Normal ∧ IsPGroup p K} from ⟨hmap, hp⟩)
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem Op_p'p_map_subtype_eq_inf [Finite H] [Fact p.Prime] {N : Subgroup H}
    (hN : N.Normal) : (Op_p'p p N).map N.subtype = N ⊓ Op_p'p p H := by
  have hM := pPrimeCore_map_subtype_eq_inf (p := p) hN
  apply le_antisymm
  · refine le_inf (Subgroup.map_subtype_le _) ?_
    have hnormal : ((Op_p'p p N).map N.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    apply le_Op_p'p_of_normal hnormal
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_of_mem_Op_p'p hy
    refine ⟨k, ?_⟩
    have := Subgroup.mem_map_of_mem N.subtype hk
    rw [hM] at this
    simpa using this.2
  · have hnormal : ((N ⊓ Op_p'p p H).subgroupOf N).Normal := Subgroup.normal_subgroupOf
    have hle : (N ⊓ Op_p'p p H).subgroupOf N ≤ Op_p'p p N := by
      apply le_Op_p'p_of_normal hnormal
      intro y hy
      obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_of_mem_Op_p'p hy.2
      refine ⟨k, ?_⟩
      have hmem : ((y ^ p ^ k : N) : H) ∈ N ⊓ pPrimeCore p H := ⟨(y ^ p ^ k).2, by simpa using hk⟩
      rw [← hM] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      have : z = y ^ p ^ k := Subtype.ext hzy
      rw [← this]
      exact hz
    intro x hx
    exact ⟨⟨x, hx.1⟩, hle hx, rfl⟩

end Cores

end CFSG.ABGLocalTools
