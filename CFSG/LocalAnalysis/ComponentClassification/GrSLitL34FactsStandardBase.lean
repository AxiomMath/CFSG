
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolic

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem jq_surjective (J : Subgroup G) : Function.Surjective (jq J) :=
  QuotientGroup.mk'_surjective _

theorem betaHat_betaHat (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) (e : Jhat J) : betaHat J hx (betaHat J hx e) = e := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, betaHat_jq]
  congr 1
  apply Subtype.ext
  rw [coe_conjJ, coe_conjJ, inv_eq_of_mul_eq_one_right hx2]
  calc x * (x * ↑j * x) * x = (x * x) * ↑j * (x * x) := by group
    _ = ↑j := by rw [hx2]; group

theorem mulEquiv_mem_center_iff {E : Type*} [Group E] (β : E ≃* E) (e : E) :
    β e ∈ center E ↔ e ∈ center E := by
  simp only [mem_center_iff]
  constructor
  · intro h g
    apply β.injective
    rw [map_mul, map_mul]
    exact h (β g)
  · intro h g
    obtain ⟨g', rfl⟩ := β.surjective g
    rw [← map_mul, ← map_mul, h g']

theorem inv_mul_conj_eq_one_iff {X : Type*} [Group X] (y r : X) :
    y⁻¹ * (r * y * r⁻¹) = 1 ↔ y * r = r * y := by
  rw [inv_mul_eq_one, eq_mul_inv_iff_mul_eq, eq_comm]

theorem mem_withKernel_of_realization {J : Subgroup G} (hJ : ⁅J, J⁆ = J) {x : G}
    (hxN : x ∈ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqker : q.ker = center (Jhat J)) {e₀ : Jhat J}
    (h : ∀ e, q (betaHat J hxN e) = q e₀ * q e * (q e₀)⁻¹) : x ∈ withKernel J := by
  have hext : (betaHat J hxN).toMonoidHom = (MulAut.conj e₀).toMonoidHom := by
    apply hom_ext_of_central (commutator_jhat hJ) q (hqker ▸ le_refl _)
    refine MonoidHom.ext fun e => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    exact h e
  have hβ : ∀ e, betaHat J hxN e = e₀ * e * e₀⁻¹ := fun e => by
    have := DFunLike.congr_fun hext e
    simpa using this
  obtain ⟨j₀, rfl⟩ := jq_surjective J e₀
  have hg : x * j₀ ∈ coreActionKernel J := by
    refine ⟨mul_mem hxN (le_normalizer j₀.2), fun j hj => ?_⟩
    have hmem : j⁻¹ * (x * j₀)⁻¹ * j * (x * j₀) ∈ J := by
      have := conj_mem_of_mem_normalizer hxN hj
      have e1 : j⁻¹ * (x * j₀)⁻¹ * j * (x * j₀) =
          j⁻¹ * ((j₀ : G)⁻¹ * (x⁻¹ * j * x) * j₀) := by group
      rw [e1]
      exact J.mul_mem (J.inv_mem hj) (J.mul_mem (J.mul_mem (J.inv_mem j₀.2) this) j₀.2)
    show _ ∈ oddIn J
    rw [mem_oddIn_iff hmem]
    have e1 : (⟨j⁻¹ * (x * ↑j₀)⁻¹ * j * (x * ↑j₀), hmem⟩ : J) =
        (⟨j, hj⟩ : J)⁻¹ * (j₀⁻¹ * conjJ J hxN ⟨j, hj⟩ * j₀) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← betaHat_jq, hβ]
    group
  have hx : x = x * j₀ * (j₀ : G)⁻¹ := by group
  rw [hx]
  exact mul_mem (mem_sup_right hg) (mem_sup_left (inv_mem j₀.2))

theorem card_centralizer_of_realization [Finite G] {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {r : Equiv.Perm (Fin 42)} (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹)
    (hcard : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} =
      72 * Nat.card (zStarIn J)) :
    Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := by
  set φ : ↥J →* Equiv.Perm (Fin 42) := q.comp (jq J) with hφ
  set C := centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S with hC
  have hCφ : C ≤ φ.range := by
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, he⟩
  have h1 := card_comap_eq φ C hCφ
  have hker : Nat.card φ.ker = Nat.card (zStarIn J) := by
    have hk : φ.ker = Open.fusionZStar J := by
      ext j
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hqker,
        ← mem_zStarIn_iff j.2, zStarIn, mem_map]
      constructor
      · rintro ⟨j', hj', hjj⟩
        rwa [Subtype.ext hjj] at hj'
      · intro hj
        exact ⟨j, hj, rfl⟩
    rw [hk, zStarIn, Subgroup.card_map_of_injective Subtype.val_injective]
  have hset : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = Nat.card (C.comap φ) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun j => ?_
    have hmem : (j : G)⁻¹ * x⁻¹ * j * x ∈ J := by
      have := conj_mem_of_mem_normalizer hxN j.2
      have e1 : (j : G)⁻¹ * x⁻¹ * j * x = (j : G)⁻¹ * (x⁻¹ * j * x) := by group
      rw [e1]
      exact J.mul_mem (J.inv_mem j.2) this
    rw [mem_zStarIn_iff hmem]
    have e1 : (⟨(j : G)⁻¹ * x⁻¹ * j * x, hmem⟩ : J) = j⁻¹ * conjJ J hxN j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, ← hqker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, ← betaHat_jq, hr,
      mem_comap, hC, mem_inf, mem_centralizer_singleton_iff, inv_mul_conj_eq_one_iff]
    simp only [hφ, MonoidHom.comp_apply]
    exact ⟨fun h => ⟨h, hqS _⟩, fun h => h.1⟩
  rw [hset, h1, hker] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard

theorem exists_unitary_realization [Finite G] {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {x : G} (hx : IsL34Unitary J x) :
    ∃ q : Jhat J →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧
      q.ker = center (Jhat J) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      ∀ e, q (betaHat J hx.1 e) = r₄ * q e * r₄⁻¹ := by
  obtain ⟨hxN, hx2, hxK, hxC⟩ := hx
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hxN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have h1 := hr (betaHat J hxN e)
      rw [betaHat_betaHat J hxN hx2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  have hrS : r ∉ S := by
    intro hrS
    obtain ⟨e₀, he₀⟩ := hqsurj r hrS
    exact hxK (mem_withKernel_of_realization hJ hxN hqker (e₀ := e₀) fun e => by
      rw [hr e, he₀])
  have hcard := card_centralizer_of_realization hxN hqS hqsurj hqker hr hxC
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  have hconj : ∃ c ∈ R, r = c * r₄ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · have h1 := card_centralizer_S_of_isConj h
      have h2 : Nat.card C₂ = 168 := card_C₂
      rw [C₂] at h2
      rw [hcard] at h1
      exact absurd (h1.trans h2) (by norm_num)
    · have h1 := card_centralizer_S_of_isConj h
      have h2 : Nat.card C₃ = 60 := card_C₃
      rw [C₃] at h2
      rw [hcard] at h1
      exact absurd (h1.trans h2) (by norm_num)
    · exact eq_conj_of_isConj h
  obtain ⟨c, hcR, hc⟩ := hconj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q, hS', hsurj', by rw [hker', hqker],
    by rw [hker']; exact h3, fun e => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr e, hc]
  group

theorem mem_smul_sylowT0_iff
    [Fact (Nat.Prime 2)] (g y : S) :
    y ∈ ((g • sylowT0 : Sylow 2 S) : Subgroup S) ↔
      (g : Equiv.Perm (Fin 42))⁻¹ * y * g ∈ T0 := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, coe_sylowT0]
  constructor
  · rintro ⟨b, hb, hby⟩
    have hval : (g : Equiv.Perm (Fin 42)) * b * (g : Equiv.Perm (Fin 42))⁻¹ = y := by
      have := congrArg Subtype.val hby
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hval]
    have e : (g : Equiv.Perm (Fin 42))⁻¹ * ((g : Equiv.Perm (Fin 42)) * b *
        (g : Equiv.Perm (Fin 42))⁻¹) * g = b := by group
    rw [e]
    exact mem_subgroupOf.mp hb
  · intro hy
    refine ⟨g⁻¹ * y * g, mem_subgroupOf.mpr (by simpa using hy), Subtype.ext ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group

end CFSG.ComponentClassification.GrSLit.L34Facts
