module

public import CFSG.Quasithin.SteinbergBSAlternatingFivePoints
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.GroupTheory.AlternatingFive

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open

theorem orderOf_eq_one_or_prime_of_odd (σ : Equiv.Perm (Fin 5)) (hσ : Odd (orderOf σ)) :
    σ = 1 ∨ (orderOf σ).Prime := by
  rcases CFSG.Quasithin.F53.perm5_odd_order hσ with h | h
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h3
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · exact Or.inr (by rw [h3]; exact Nat.prime_three)
  · rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h5
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · exact Or.inr (by rw [h5]; exact Nat.prime_five)

theorem exists_three_cycle_moving_swaps (p : Fin 5) :
    ∃ c : Equiv.Perm (Fin 5), c ^ 3 = 1 ∧ c ≠ 1 ∧ c p = p ∧
      ∀ τ : Equiv.Perm (Fin 5), τ ^ 2 = 1 → τ p = p → τ ∉ alternatingGroup (Fin 5) →
        (τ * (c⁻¹ * τ * c)) ^ 3 = 1 ∧ τ * (c⁻¹ * τ * c) ≠ 1 := by
  fin_cases p
  · exact ⟨swap 1 2 * swap 1 3, by decide, by decide, by decide, by
      simp only [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  · exact ⟨swap 0 2 * swap 0 3, by decide, by decide, by decide, by
      simp only [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  · exact ⟨swap 0 1 * swap 0 3, by decide, by decide, by decide, by
      simp only [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  · exact ⟨swap 0 1 * swap 0 2, by decide, by decide, by decide, by
      simp only [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  · exact ⟨swap 0 1 * swap 0 2, by decide, by decide, by decide, by
      simp only [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

theorem isSylowOf_alternatingGroup_of_card_four {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : P ≤ alternatingGroup (Fin 5)) (hcP : Nat.card P = 4) :
    CFSG.ABGLocalTools.IsSylowOf 2 P (alternatingGroup (Fin 5)) := by
  have hfac : (Nat.factorization 60) 2 = 2 := by
    rw [show 60 = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by decide), Nat.factorization_pow,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  refine CFSG.ABGLocalTools.isSylowOf_of_card hP ?_
  rw [hcP, CFSG.Quasithin.SteinbergCB.nat_card_alternating_five, hfac]
  norm_num

theorem inf_normalizer_eq_bot_of_card_four {P P' : Subgroup (Equiv.Perm (Fin 5))}
    (hP : P ≤ alternatingGroup (Fin 5)) (hP' : P' ≤ alternatingGroup (Fin 5))
    (hcP : Nat.card P = 4) (hcP' : Nat.card P' = 4) (hne : P ≠ P') :
    P ⊓ Subgroup.normalizer (P' : Set (Equiv.Perm (Fin 5))) = ⊥ := by
  have hPis := isSylowOf_alternatingGroup_of_card_four hP hcP
  have hP'is := isSylowOf_alternatingGroup_of_card_four hP' hcP'
  obtain ⟨α, -, hfixP, -, hleP, -, -⟩ :=
    CFSG.Quasithin.SteinbergBS.sylow_alternating_five_fixed hPis
  obtain ⟨α', -, -, -, hleP', hNP', -⟩ :=
    CFSG.Quasithin.SteinbergBS.sylow_alternating_five_fixed hP'is
  have hαα' : α ≠ α' := by
    intro h
    apply hne
    refine CFSG.Quasithin.SteinbergBS.sylow_eq_of_fixed hPis hP'is
      (hleP.trans inf_le_right) ?_
    rw [h]
    exact hleP'.trans inf_le_right
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  obtain ⟨hσP, hσN⟩ := Subgroup.mem_inf.mp hσ
  have hσA : σ ∈ alternatingGroup (Fin 5) := hP hσP
  have hσα : σ • α = α := (hleP hσP).2
  have hσα' : σ • α' = α' := by
    have hmem : σ ∈ alternatingGroup (Fin 5) ⊓
        Subgroup.normalizer (P' : Set (Equiv.Perm (Fin 5))) := ⟨hσA, hσN⟩
    rw [hNP'] at hmem
    exact hmem.2
  by_contra hσ1
  have hfix := hfixP σ hσP hσ1 α' (by simpa [Equiv.Perm.smul_def] using hσα')
  exact hαα' hfix.symm

theorem exists_conjSubgroup_ne_of_card_four {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : P ≤ alternatingGroup (Fin 5)) (hcP : Nat.card P = 4) :
    ∃ σ ∈ alternatingGroup (Fin 5), conjSubgroup P σ ≠ P := by
  by_contra h
  have hconj : ∀ σ ∈ alternatingGroup (Fin 5), conjSubgroup P σ = P := by
    intro σ hσ
    by_contra hne
    exact h ⟨σ, hσ, hne⟩
  have hnorm : alternatingGroup (Fin 5) ≤
      Subgroup.normalizer (P : Set (Equiv.Perm (Fin 5))) :=
    fun σ hσ => conjSubgroup_eq_iff_mem_normalizer.mp (hconj σ hσ)
  have hPn : (P.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mpr hnorm
  have hcard : Nat.card (P.subgroupOf (alternatingGroup (Fin 5))) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _
      alternatingGroup.isSimpleGroup_five (P.subgroupOf (alternatingGroup (Fin 5))) hPn with
    hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    omega
  · rw [ht, Subgroup.card_top, CFSG.Quasithin.SteinbergCB.nat_card_alternating_five,
      hcP] at hcard
    omega

theorem exists_hom_perm_five {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hsh : Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* Equiv.Perm (Fin 5))) :
    ∃ ψ : ↥H →* Equiv.Perm (Fin 5), ψ.ker = (pCoreOf 2 H).subgroupOf H ∧
      (ψ.range = alternatingGroup (Fin 5) ∨ ψ.range = ⊤) := by
  rcases hsh with hsh | hsh
  · obtain ⟨e⟩ := hsh
    refine ⟨(alternatingGroup (Fin 5)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' _)), ?_, Or.inl ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 5)).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
      exact (CFSG.openPCoreOf_subgroupOf 2 H).symm
    · rw [MonoidHom.range_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.map_top,
        MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top, Subgroup.range_subtype]
  · obtain ⟨e⟩ := hsh
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, Or.inr ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
      exact (CFSG.openPCoreOf_subgroupOf 2 H).symm
    · rw [MonoidHom.range_eq_top]
      exact e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem card_map_subgroupOf_eq_two_pow {G K : Type*} [Group G] [Finite G] [Group K]
    {H A : Subgroup G} (ψ : ↥H →* K) (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H)
    (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    Nat.card ((A.subgroupOf H).map ψ) = 2 ^ E3.mQuot A (A ⊓ pCoreOf 2 H) := by
  rw [← Subgroup.relIndex_ker (A.subgroupOf H) ψ, hker,
    Subgroup.relIndex_subgroupOf hAH, ← Subgroup.inf_relIndex_right (H := pCoreOf 2 H) (K := A),
    inf_comm (pCoreOf 2 H) A]
  exact E3.relIndex_eq_two_pow hA (A ⊓ pCoreOf 2 H)

theorem twoResidual_le_map_comap_alternatingGroup {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (ψ : ↥H →* Equiv.Perm (Fin 5)) :
    twoResidual H ≤ ((alternatingGroup (Fin 5)).comap ψ).map H.subtype := by
  set K : Subgroup ↥H := (alternatingGroup (Fin 5)).comap ψ with hK
  set N : Subgroup G := K.map H.subtype with hN
  have hNK : N.subgroupOf H = K := by
    rw [hN, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hKnormal : K.Normal := by
    rw [hK]
    infer_instance
  have hNH : N ≤ H := Subgroup.map_subtype_le K
  refine twoResidual_le_of_isTwoQuotient hNH ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp (hNK ▸ hKnormal)
  · intro y hy
    refine ⟨1, ?_⟩
    have hsq : ψ ⟨y, hy⟩ ^ 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_pow_two]
    have hy2 : y ^ 2 ∈ N := by
      refine ⟨(⟨y, hy⟩ : ↥H) ^ 2, ?_, rfl⟩
      change ψ ((⟨y, hy⟩ : ↥H) ^ 2) ∈ alternatingGroup (Fin 5)
      rw [map_pow]
      exact hsq
    simpa using hy2

theorem eq_one_or_prime_of_hom_perm_five {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (ψ : ↥H →* Equiv.Perm (Fin 5)) (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H) {x : G}
    (hx : x ∈ H) (hodd : Odd (orderOf x)) : x = 1 ∨ (orderOf x).Prime := by
  have hodd' : Odd (orderOf (⟨x, hx⟩ : ↥H)) := by
    rwa [Subgroup.orderOf_mk]
  have hker2 : IsPGroup 2 ψ.ker := by
    rw [hker, CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_isPGroup
  have horder : orderOf (ψ ⟨x, hx⟩) = orderOf x := by
    rw [CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.orderOf_map_eq_of_odd ψ hker2 hodd',
      Subgroup.orderOf_mk]
  rcases orderOf_eq_one_or_prime_of_odd (ψ ⟨x, hx⟩) (horder.symm ▸ hodd) with h1 | hp
  · left
    have hx'ker : (⟨x, hx⟩ : ↥H) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, h1]
    rw [hker, CFSG.openPCoreOf_subgroupOf] at hx'ker
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥H) (p := 2)).exists_card_eq
    have hdvd : orderOf (⟨x, hx⟩ : ↥H) ∣ Nat.card (CFSG.pCore 2 ↥H) :=
      Subgroup.orderOf_dvd_natCard _ hx'ker
    rw [hn] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      have heven : Even (orderOf (⟨x, hx⟩ : ↥H)) := by
        rw [hk]
        exact even_iff_two_dvd.mpr h2dvd
      exact (Nat.not_even_iff_odd.mpr hodd') heven
    rw [hk0, pow_zero] at hk
    have hx1 : (⟨x, hx⟩ : ↥H) = 1 := orderOf_eq_one_iff.mp hk
    simpa using congrArg Subtype.val hx1
  · right
    rwa [horder] at hp

end CFSG.GroupTheory.AlternatingFive
