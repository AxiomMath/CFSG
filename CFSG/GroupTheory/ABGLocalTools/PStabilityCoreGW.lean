module

public import CFSG.LinearAlgebra.LinearGroups.QuadraticPCoreImages
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup

public section

open Subgroup

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def TwoSectionsCyclic (G : Type*) [Group G] : Prop :=
  ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
    (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E)

theorem mem_pCore_of_injective {M : Type*} [Group M] {p : ℕ} (ρ : G →* M)
    (hρ : Function.Injective ρ) {x : G} (hx : ρ.rangeRestrict x ∈ pCore p ρ.range) :
    x ∈ pCore p G := by
  rw [← pCore_map_iso p (MonoidHom.ofInjective hρ).symm]
  refine ⟨ρ.rangeRestrict x, hx, ?_⟩
  change (MonoidHom.ofInjective hρ).symm (ρ.rangeRestrict x) = x
  rw [MulEquiv.symm_apply_eq]
  ext
  rw [MonoidHom.ofInjective_apply, MonoidHom.coe_rangeRestrict]

theorem mem_pCore_of_twoSectionsCyclic [Finite G] (hsec : TwoSectionsCyclic G) {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) (x : G) (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) :
    x ∈ pCore p G := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have h := CFSG.LinearGroups.cyclic_unique_involution_two_sections_give_quadratic_p_core_images
    hsec ⊤ (Fact.out : p.Prime) hodd (ρ.comp (⊤ : Subgroup G).subtype) ⟨x, trivial⟩ hx
  have h2 := mem_pCore_of_injective (ρ.comp (⊤ : Subgroup G).subtype)
    (hρ.comp (subtype_injective _)) h
  have hn : (⊤ : Subgroup G).subtype.range.Normal := by
    rw [range_subtype]
    infer_instance
  exact map_pCore_le_of_injective_of_normal _ (⊤ : Subgroup G).subtype_injective hn ⟨_, h2, rfl⟩

theorem twoSectionsCyclic_of_isCyclic (h : ∀ D : Subgroup G, IsPGroup 2 D → IsCyclic D) :
    TwoSectionsCyclic G := by
  intro D hD E _ _
  have := h D hD
  exact isCyclic_of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)

theorem eq_of_orderOf_eq_two_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Z) ⊆ Finset.univ.filter (fun x : Z => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [← ha]; exact pow_orderOf_eq_one x
    · rw [← hb]; exact pow_orderOf_eq_one x
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num at hb
  have hcard : ({1, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

@[expose] def CyclicModInvolutions (T : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≤ T ∧ IsCyclic C ∧ ∀ t ∈ T, t ∉ C → t ^ 2 = 1

theorem CyclicModInvolutions.mono {T T' : Subgroup G} (h : CyclicModInvolutions T)
    (hT : T' ≤ T) : CyclicModInvolutions T' := by
  obtain ⟨C, -, hC, hout⟩ := h
  exact ⟨C ⊓ T', inf_le_right, isCyclic_of_le inf_le_left,
    fun t ht htC => hout t (hT ht) fun h => htC ⟨h, ht⟩⟩

theorem CyclicModInvolutions.map {M : Type*} [Group M] {T : Subgroup G}
    (h : CyclicModInvolutions T) (f : G →* M) : CyclicModInvolutions (T.map f) := by
  obtain ⟨C, hCT, hC, hout⟩ := h
  refine ⟨C.map f, map_mono hCT,
    isCyclic_of_surjective (f.subgroupMap C) (f.subgroupMap_surjective C), ?_⟩
  rintro _ ⟨t, ht, rfl⟩ htC
  rw [← map_pow, hout t ht (fun h => htC ⟨t, h, rfl⟩), map_one]

theorem CyclicModInvolutions.top_of_le {T D : Subgroup G} (h : CyclicModInvolutions T)
    (hD : D ≤ T) : CyclicModInvolutions (⊤ : Subgroup D) := by
  obtain ⟨C, hCD, hC, hout⟩ := h.mono hD
  refine ⟨C.subgroupOf D, le_top, ?_, fun t _ htC => ?_⟩
  · exact isCyclic_of_surjective (subgroupOfEquivOfLe hCD).symm.toMonoidHom
      (subgroupOfEquivOfLe hCD).symm.surjective
  · have := hout t t.2 (fun h => htC (mem_subgroupOf.mpr h))
    exact Subtype.ext (by simpa using this)

theorem isCyclic_of_cyclicModInvolutions {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (h : CyclicModInvolutions (⊤ : Subgroup Q))
    (huniq : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u = v) : IsCyclic Q := by
  obtain ⟨C, -, hC, hout⟩ := h
  by_cases hCtop : C = ⊤
  · subst hCtop
    exact isCyclic_of_surjective (⊤ : Subgroup Q).subtype fun q => ⟨⟨q, trivial⟩, rfl⟩
  obtain ⟨t, htC⟩ : ∃ t, t ∉ C := by
    by_contra hcon
    exact hCtop (eq_top_iff.mpr fun x _ => by_contra fun hx => hcon ⟨x, hx⟩)
  have ht2 : t ^ 2 = 1 := hout t trivial htC
  have ht1 : t ≠ 1 := fun h => htC (h ▸ C.one_mem)
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hCbot : C = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (card_eq_one.mp (by simpa using hn))
    have h2 : 2 ∣ Nat.card C := by rw [hn]; exact dvd_pow_self 2 hn0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have : (c : Q) = t := huniq c t (by rw [orderOf_coe]; exact hc) hto
    exact htC (this ▸ c.2)
  refine ⟨⟨t, fun u => ?_⟩⟩
  by_cases hu : u = 1
  · exact ⟨0, by simp [hu]⟩
  · have hu2 : u ^ 2 = 1 := hout u trivial (by rw [hCbot]; exact fun h => hu (mem_bot.mp h))
    exact ⟨1, by simp [huniq u t (orderOf_eq_prime hu2 hu) hto]⟩

theorem twoSectionsCyclic_of_cyclicModInvolutions [Finite G]
    (h : ∀ D : Subgroup G, IsPGroup 2 D → CyclicModInvolutions D) : TwoSectionsCyclic G := by
  intro D hD E _ huniq
  have h1 : CyclicModInvolutions (⊤ : Subgroup D) := (h D hD).top_of_le le_rfl
  have h2 : CyclicModInvolutions (⊤ : Subgroup (D ⧸ E)) := by
    have := h1.map (QuotientGroup.mk' E)
    rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective E)] at this
  exact isCyclic_of_cyclicModInvolutions (hD.to_quotient E) h2 huniq

theorem twoSectionsCyclic_of_sylow [Finite G] (P : Sylow 2 G)
    (hP : CyclicModInvolutions (P : Subgroup G)) : TwoSectionsCyclic G := by
  refine twoSectionsCyclic_of_cyclicModInvolutions fun D hD => ?_
  obtain ⟨Q, hDQ⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have : CyclicModInvolutions (Q : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, pointwise_smul_def]
    exact hP.map _
  exact this.mono hDQ

end CFSG.ABGLocalTools
