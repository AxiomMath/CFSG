module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.GroupTheory.ABGLocalTools.PStabilityFrattini

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.ABGLocalTools

universe u

variable {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem isPStable_of_quadratic_quotients (hOp : pCore p H ≠ ⊥)
    (hquot : ∀ (L : Subgroup H) [L.Normal] (V : Type u) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V] (ρ : H ⧸ L →* LinearMap.GeneralLinearGroup (ZMod p) V),
      Function.Injective ρ → ∀ x : H, (∃ k : ℕ, x ^ p ^ k = 1) →
      ((ρ (x : H ⧸ L) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 →
      ρ.rangeRestrict (x : H ⧸ L) ∈ CFSG.pCore p ρ.range) :
    IsPStable p H := by
  refine ⟨hOp, fun P A _ hP hn hA hAN hcomm => ?_⟩
  apply le_normalizerPCoreModCentralizer_of_chief hP hAN
  intro W₁ W₂ hW₁P hchief
  have hW : (W₂.subgroupOf W₁).Normal := hchief.normal
  have hE : IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁) := hchief.isElementaryAbelian
  set N := normalizer (P : Set H) with hNdef
  obtain ⟨ρN, hρN⟩ : ∃ ρN : N →* LinearMap.GeneralLinearGroup (ZMod p)
      (Additive (W₁ ⧸ W₂.subgroupOf W₁)), ρN = chiefRep (p := p) hchief.2.1 hchief.2.2.1 :=
    ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup H, K = ρN.ker.map N.subtype := ⟨_, rfl⟩
  have hKN : K ≤ N := hKdef ▸ map_subtype_le _
  have hKsub : K.subgroupOf N = ρN.ker := by
    rw [hKdef, subgroupOf, comap_map_eq_self_of_injective N.subtype_injective]
  have hKn : N ≤ normalizer (K : Set H) := by
    rw [hKdef]
    exact le_normalizer_map_subtype N ρN.ker
  have hNO : N ⊓ pPrimeCore p H ≤ K := by
    rintro x ⟨hxN, hxO⟩
    have hxC := normalizer_inf_pPrimeCore_le_centralizer hP ⟨hxN, hxO⟩
    rw [hKdef]
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hρN, chiefRep_eq_one_iff]
    intro w hw
    have : ⁅w, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (mem_centralizer_iff.mp hxC w (hW₁P hw))
    rw [this]
    exact one_mem _
  have hLn : (K ⊔ pPrimeCore p H).Normal :=
    sup_pPrimeCore_normal hKn (pPrimeCore_sup_normalizer_eq_top hP hn)
  have : (K.subgroupOf N).Normal := by
    rw [hKsub]
    exact MonoidHom.normal_ker ρN
  set e := normalizerQuotientEquiv hP hn hKN hNO with he
  set ρbar : N ⧸ K.subgroupOf N →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive (W₁ ⧸ W₂.subgroupOf W₁)) :=
    QuotientGroup.lift (K.subgroupOf N) ρN (by rw [hKsub]) with hρbar
  have hρbar_inj : Function.Injective ρbar := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, hρbar, QuotientGroup.lift_mk] at hy
    rw [mem_bot, QuotientGroup.eq_one_iff, hKsub]
    exact hy
  set ρ := ρbar.comp e.symm.toMonoidHom with hρdef
  have hρ_inj : Function.Injective ρ := hρbar_inj.comp e.symm.injective
  have hρa : ∀ n : N, ρ ((n : H) : H ⧸ (K ⊔ pPrimeCore p H)) = ρN n := by
    intro n
    have h1 : e.symm ((n : H) : H ⧸ (K ⊔ pPrimeCore p H)) = (n : N ⧸ K.subgroupOf N) := by
      rw [MulEquiv.symm_apply_eq, he, normalizerQuotientEquiv_apply]
    rw [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, hρbar, QuotientGroup.lift_mk]
  have : Finite (Additive (W₁ ⧸ W₂.subgroupOf W₁)) :=
    inferInstanceAs (Finite (W₁ ⧸ W₂.subgroupOf W₁))
  have : FiniteDimensional (ZMod p) (Additive (W₁ ⧸ W₂.subgroupOf W₁)) :=
    Module.Finite.of_finite
  have : Nontrivial (Additive (W₁ ⧸ W₂.subgroupOf W₁)) := by
    obtain ⟨w, hw₁, hw₂⟩ := IsConcreteLE.exists_of_lt hchief.1
    refine ⟨⟨Additive.ofMul ((⟨w, hw₁⟩ : W₁) : W₁ ⧸ W₂.subgroupOf W₁), 0, fun h => hw₂ ?_⟩⟩
    have h1 : ((⟨w, hw₁⟩ : W₁) : W₁ ⧸ W₂.subgroupOf W₁) = 1 := congrArg Additive.toMul h
    exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hirr : ∀ U : Submodule (ZMod p) (Additive (W₁ ⧸ W₂.subgroupOf W₁)),
      (∀ g : H ⧸ (K ⊔ pPrimeCore p H), ∀ v ∈ U, (ρ g).val v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    apply chiefRep_irreducible hchief U
    intro n v hv
    have := hU ((n : H) : H ⧸ _) v hv
    rwa [hρa, hρN] at this
  have hOp1 := pCore_range_eq_bot_of_irreducible ρ hirr
  rw [commutator_le]
  intro w hw a ha
  have hquad : ((ρ ((a : H) : H ⧸ (K ⊔ pPrimeCore p H))).val - 1) ^ 2 = 0 := by
    rw [show (a : H) = ((⟨a, hAN ha⟩ : N) : H) from rfl, hρa, hρN]
    refine chiefRep_quadratic _ _ ⟨a, hAN ha⟩ fun u hu => ?_
    have := commutator_mem_commutator (commutator_mem_commutator (hW₁P hu) ha) ha
    rwa [hcomm, mem_bot] at this
  have hpe : ∃ k : ℕ, a ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmem := hquot (K ⊔ pPrimeCore p H) (Additive (W₁ ⧸ W₂.subgroupOf W₁)) ρ hρ_inj a hpe hquad
  rw [hOp1, mem_bot] at hmem
  have hρ1 : ρ ((a : H) : H ⧸ (K ⊔ pPrimeCore p H)) = 1 := by
    have := congrArg Subtype.val hmem
    simpa using this
  rw [show (a : H) = ((⟨a, hAN ha⟩ : N) : H) from rfl, hρa, hρN] at hρ1
  exact (chiefRep_eq_one_iff _ _ ⟨a, hAN ha⟩).mp hρ1 w hw

end CFSG.ABGLocalTools
