module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem pPrimeCore_two_quotient_oddCore_eq_bot (H : Type*) [Group H] [Finite H] :
    pPrimeCore 2 (H ⧸ oddCore H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (N : Subgroup H) [N.Normal], N = pPrimeCore 2 H → pPrimeCore 2 (H ⧸ N) = ⊥ := by
    intro N _ hN
    subst hN
    exact pPrimeCore_quotient_eq_bot Nat.prime_two
  exact key _ ((oddCore_eq_piCore H).trans (pPrimeCore_eq_piCore H 2).symm)

section Components

variable {Y : Type*} [Group Y]

theorem normal_of_isComponent_of_standard [Finite Y] {D : Subgroup Y} (hD : IsComponent D)
    (hstd : CFSG.Open.standardComponentIsStandard D) : D.Normal := by
  have hconj : ∀ g : Y, D.map (MulAut.conj g).toMonoidHom = D := fun g =>
    (CFSG.LocalCores.distinct_components_commute
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hD) hD).resolve_right
      (by rw [commutator_comm]; exact hstd.2.2.2.2 g)
  refine ⟨fun n hn g => ?_⟩
  have h : g * n * g⁻¹ ∈ D.map (MulAut.conj g).toMonoidHom := ⟨n, hn, by simp⟩
  rwa [hconj g] at h

theorem eq_of_isComponent_subgroupOf [Finite Y] {D K : Subgroup Y} (hK : IsQuasisimple K)
    (hDK : D ≤ K) (hD : IsComponent (D.subgroupOf K)) : D = K := by
  have htop : IsComponent (⊤ : Subgroup K) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hK, IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hD htop with h | h
  · exact le_antisymm hDK (subgroupOf_eq_top.mp h)
  · exfalso
    have hperf : ⁅D.subgroupOf K, D.subgroupOf K⁆ = D.subgroupOf K := isPerfect_iff.mp hD.1.1
    have hbot : D.subgroupOf K = ⊥ := by
      rw [← hperf, eq_bot_iff, ← h]
      exact commutator_mono le_rfl le_top
    have hne := CFSG.LocalCores.isQuasisimple_nontrivial hD.1
    rw [nontrivial_iff_ne_bot] at hne
    exact hne hbot

end Components

section Induced

variable {Y : Type*} [Group Y] (K : Subgroup Y) {s : Y} (hsN : s ∈ normalizer (K : Set Y))

include hsN in
theorem coe_normalizerMonoidHom_mk_apply (k : K) :
    ((K.normalizerMonoidHom ⟨s, hsN⟩ k : K) : Y) = s * k * s⁻¹ :=
  normalizerMonoidHom_apply_apply_coe K ⟨s, hsN⟩ k

theorem fixedSubgroup_normalizerMonoidHom :
    fixedSubgroup (K.normalizerMonoidHom ⟨s, hsN⟩) = (centralizer ({s} : Set Y)).subgroupOf K := by
  ext k
  rw [mem_subgroupOf, mem_centralizer_singleton_iff]
  change K.normalizerMonoidHom ⟨s, hsN⟩ k = k ↔ _
  rw [← Subtype.coe_inj, coe_normalizerMonoidHom_mk_apply, mul_inv_eq_iff_eq_mul, eq_comm]

theorem map_fixedSubgroup_normalizerMonoidHom :
    (fixedSubgroup (K.normalizerMonoidHom ⟨s, hsN⟩)).map K.subtype =
      K ⊓ centralizer ({s} : Set Y) := by
  rw [fixedSubgroup_normalizerMonoidHom, subgroupOf_map_subtype, inf_comm]

theorem normalizerMonoidHom_sq_eq_one (hs : s ^ 2 = 1) :
    K.normalizerMonoidHom ⟨s, hsN⟩ ^ 2 = 1 := by
  have h1 : (⟨s, hsN⟩ : normalizer (K : Set Y)) ^ 2 = 1 := Subtype.ext (by simpa using hs)
  rw [← map_pow, h1, map_one]

theorem normalizerMonoidHom_mem_range_conj (hsK : s ∈ K) :
    K.normalizerMonoidHom ⟨s, hsN⟩ ∈ (MulAut.conj : K →* MulAut K).range := by
  refine ⟨⟨s, hsK⟩, ?_⟩
  ext k
  rw [coe_normalizerMonoidHom_mk_apply, MulAut.conj_apply]
  rfl

theorem le_centralizer_of_normalizerMonoidHom_eq_one
    (h1 : K.normalizerMonoidHom ⟨s, hsN⟩ = 1) : K ≤ centralizer ({s} : Set Y) := by
  intro k hk
  have h := congrArg (fun τ : MulAut K => ((τ ⟨k, hk⟩ : K) : Y)) h1
  simp only [coe_normalizerMonoidHom_mk_apply, MulAut.one_apply] at h
  rw [mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem orderOf_normalizerMonoidHom_eq_two (hs : s ^ 2 = 1)
    (hK : ¬ K ≤ centralizer ({s} : Set Y)) : orderOf (K.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (normalizerMonoidHom_sq_eq_one K hsN hs)
    fun h1 => hK (le_centralizer_of_normalizerMonoidHom_eq_one K hsN h1)

end Induced

section Transport

variable {Y : Type*} [Group Y]

theorem isComponent_subgroupOf_subgroupOf {B D K : Subgroup Y} {B' : Subgroup K}
    (hB' : B'.map K.subtype = B) (hD : IsComponent (D.subgroupOf B)) :
    IsComponent ((D.subgroupOf K).subgroupOf B') := by
  let ψ : B' ≃* B := (B'.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hB')
  have hψ : ∀ x : B', ((ψ x : B) : Y) = ((x : K) : Y) := fun x => rfl
  have hmap : (D.subgroupOf B).map ψ.symm.toMonoidHom = (D.subgroupOf K).subgroupOf B' := by
    ext x
    rw [mem_map_equiv, MulEquiv.symm_symm, mem_subgroupOf, mem_subgroupOf, mem_subgroupOf, hψ]
  rw [← hmap]
  exact CFSG.LocalCores.isComponent_map_mulEquiv ψ.symm hD

noncomputable def subgroupOfSubgroupOfEquiv {D K : Subgroup Y} {B' : Subgroup K}
    (hDK : D ≤ K) (hDB : D.subgroupOf K ≤ B') : (D.subgroupOf K).subgroupOf B' ≃* D :=
  (subgroupOfEquivOfLe hDB).trans (subgroupOfEquivOfLe hDK)

end Transport

section TwoFree

variable {Y : Type} [Group Y] [Finite Y]

private theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two' {s y : Y} (hs : orderOf s = 2)
    (hy : y ∈ zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
  rw [← pow_mod_orderOf, hs]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact Or.inl (pow_zero s)
  · exact Or.inr (pow_one s)

theorem fixedCentralizerTwoFree_of_card_le_two {K D : Subgroup Y} {s : Y}
    (hsN : s ∈ normalizer (K : Set Y)) (hs : orderOf s = 2) (hsK : s ∉ K)
    (hDs : D ≤ centralizer ({s} : Set Y)) (hDK : D ≤ K)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (D' : Subgroup (fixedSubgroup (K.normalizerMonoidHom ⟨s, hsN⟩)))
    (hD' : D'.map (fixedSubgroup (K.normalizerMonoidHom ⟨s, hsN⟩)).subtype = D.subgroupOf K) :
    FixedCentralizerTwoFree (K.normalizerMonoidHom ⟨s, hsN⟩) D' := by
  intro U hU hUD hUfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hD'] at hUD
  set U' : Subgroup Y := U.map K.subtype with hU'
  have hU'p : IsPGroup 2 U' := hU.map _
  have hU'D : U' ≤ centralizer (D : Set Y) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have h := mem_centralizer_iff.mp (hUD hu) ⟨d, hDK hd⟩ (mem_subgroupOf.mpr hd)
    exact congrArg Subtype.val h
  have hU's : U' ≤ centralizer ({s} : Set Y) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUfix hu
    rw [fixedSubgroup_normalizerMonoidHom, mem_subgroupOf] at h
    exact h
  have hsD : s ∈ centralizer (D : Set Y) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hDs hd)
  have hzp : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hU'N : U' ≤ normalizer ((zpowers s : Subgroup Y) : Set Y) := by
    intro u hu
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp (hU's hu)).symm k).eq
  have hVp : IsPGroup 2 (U' ⊔ zpowers s : Subgroup Y) := hU'p.to_sup_of_normal_right' hzp hU'N
  have hVD : U' ⊔ zpowers s ≤ centralizer (D : Set Y) :=
    sup_le hU'D ((zpowers_le (G := Y)).mpr hsD)
  have hV2 := hsyl _ hVp hVD
  have hVeq : zpowers s = U' ⊔ zpowers s :=
    eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, hs]; exact hV2)
  rw [eq_bot_iff]
  intro u hu
  have hu' : (u : Y) ∈ zpowers s := hVeq ▸ mem_sup_left ⟨u, hu, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two' hs hu' with h | h
  · exact (mem_bot).mpr (Subtype.ext h)
  · exact absurd (h ▸ u.2) hsK

end TwoFree

theorem catalog_center_quotient_of_kProper {G : Type} [Group G]
    (hKP : CFSG.Assembly.KProper Catalog G) {H : Subgroup G} (hH : H ≠ ⊤) {N : Subgroup H}
    [N.Normal] {Kc : Subgroup (H ⧸ N)} (hKc : IsQuasisimple Kc) : Catalog (Kc ⧸ center Kc) := by
  have : IsSimpleGroup (Kc ⧸ center Kc) := hKc.2.1
  set π := QuotientGroup.mk' N with hπ
  set M : Subgroup G := (Kc.comap π).map H.subtype with hM
  have hMH : M ≤ H := map_subtype_le _
  have hMtop : M ≠ ⊤ := fun h => hH (top_unique (h ▸ hMH))
  have hmem : ∀ m : M, (π.comp (Subgroup.inclusion hMH)) m ∈ Kc := by
    rintro ⟨_, h, hh, rfl⟩
    exact hh
  let ψ : M →* Kc := (π.comp (Subgroup.inclusion hMH)).codRestrict Kc hmem
  let φ : M →* Kc ⧸ center Kc := (QuotientGroup.mk' (center Kc)).comp ψ
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center Kc) z
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective N (k : H ⧸ N)
    have hhK : h ∈ Kc.comap π := by
      rw [mem_comap]
      change QuotientGroup.mk' N h ∈ Kc
      rw [hh]
      exact k.2
    refine ⟨⟨(h : G), h, hhK, rfl⟩, ?_⟩
    change QuotientGroup.mk' (center Kc) (ψ _) = QuotientGroup.mk' (center Kc) k
    congr 1
    exact Subtype.ext hh
  exact EvenSmallLie.CatalogOrders.catalog_of_kProper_of_surjective hKP M hMtop _ hKc.2.2 φ hφ

theorem nonempty_mulEquiv_map_of_isSimpleGroup {A B : Type*} [Group A] [Group B] (φ : A →* B)
    {D : Subgroup A} (hD : IsSimpleGroup D) (hne : D.map φ ≠ ⊥) : Nonempty (D ≃* D.map φ) := by
  let ψ : D →* D.map φ := (φ.comp D.subtype).codRestrict (D.map φ) fun d => ⟨d, d.2, rfl⟩
  have hsurj : Function.Surjective ψ := by
    rintro ⟨_, d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  have hinj : Function.Injective ψ := by
    rcases hD.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨d, hd, rfl⟩
      have h1 : (⟨d, hd⟩ : D) ∈ ψ.ker := h ▸ mem_top _
      rw [MonoidHom.mem_ker] at h1
      exact (mem_bot).mpr (congrArg Subtype.val h1)
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

end CFSG.SeitzReduction.F4Pilot
