module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem alt_nonabelian_of_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h : 4 ≤ Nat.card Ω) :
    ∃ a b : alternatingGroup Ω, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hZ : center (alternatingGroup Ω) = ⊤ :=
    eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => hc b a
  rw [alternatingGroup.center_eq_bot h] at hZ
  have : Nontrivial (alternatingGroup Ω) := alternatingGroup.nontrivial_of_three_le_card (by omega)
  exact bot_ne_top hZ

theorem exists_even_involution {n k : ℕ} (hk : k + 4 ≤ n) (h4 : 4 ∣ n - k) :
    ∃ τ : Perm (Fin n), τ ∈ alternatingGroup (Fin n) ∧ orderOf τ = 2 ∧
      τ.support.card = n - k := by
  classical
  obtain ⟨r, hr⟩ := h4
  obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr
    (show (Multiset.replicate (2 * r) 2).sum ≤ Fintype.card (Fin n) ∧
      ∀ a ∈ Multiset.replicate (2 * r) 2, 2 ≤ a from ⟨by
        rw [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]; omega,
        fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩)
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hg,
      Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
      show 2 * r * 2 + 2 * r = 2 * (3 * r) by ring, pow_mul]
    simp
  · rw [← Equiv.Perm.lcm_cycleType, hg]
    apply Nat.dvd_antisymm
    · exact Multiset.lcm_dvd.mpr fun b hb => by rw [Multiset.eq_of_mem_replicate hb]
    · exact Multiset.dvd_lcm (Multiset.mem_replicate.mpr ⟨by omega, rfl⟩)
  · rw [← Equiv.Perm.sum_cycleType, hg, Multiset.sum_replicate, smul_eq_mul]
    omega

variable {n : ℕ}

@[expose] noncomputable def fixAlt (τ : Perm (Fin n)) : Subgroup (alternatingGroup (Fin n)) :=
  (alternatingGroup.ofSubtype τ.supportᶜ).range

theorem mem_fixAlt {τ : Perm (Fin n)} {k : alternatingGroup (Fin n)} :
    k ∈ fixAlt τ ↔ (k : Perm (Fin n)).support ⊆ τ.supportᶜ :=
  alternatingGroup.mem_range_ofSubtype_iff _ k

noncomputable def fixAltEquiv (τ : Perm (Fin n)) :
    alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)) ≃* fixAlt τ :=
  MonoidHom.ofInjective alternatingGroup.ofSubtype_injective

theorem fixAlt_le_centralizer {τ : Perm (Fin n)} (hτ : τ ∈ alternatingGroup (Fin n)) :
    fixAlt τ ≤ centralizer ({⟨τ, hτ⟩} : Set (alternatingGroup (Fin n))) := by
  intro k hk
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hd : (k : Perm (Fin n)).Disjoint τ := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Disjoint.mono_left (mem_fixAlt.mp hk) disjoint_compl_left
  exact hd.commute.eq

theorem conj_mem_fixAlt {τ : Perm (Fin n)} {g k : alternatingGroup (Fin n)}
    (hg : (g : Perm (Fin n)) * τ = τ * g) (hk : k ∈ fixAlt τ) : g * k * g⁻¹ ∈ fixAlt τ := by
  rw [mem_fixAlt] at hk ⊢
  have hc : ((g * k * g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      (g : Perm (Fin n)) * k * (g : Perm (Fin n))⁻¹ := rfl
  rw [hc, Equiv.Perm.support_conj]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
  have h1 := hk hz
  rw [Finset.mem_compl, Equiv.Perm.notMem_support] at h1 ⊢
  change τ ((g : Perm (Fin n)) z) = (g : Perm (Fin n)) z
  rw [← Perm.mul_apply, ← hg, Perm.mul_apply, h1]

theorem isComponent_fixAlt {τ : Perm (Fin n)} (hτ : τ ∈ alternatingGroup (Fin n))
    (h5 : 5 ≤ n - τ.support.card) :
    IsComponent ((fixAlt τ).subgroupOf
      (centralizer ({⟨τ, hτ⟩} : Set (alternatingGroup (Fin n))))) := by
  classical
  set C := centralizer ({⟨τ, hτ⟩} : Set (alternatingGroup (Fin n))) with hC
  have hle := fixAlt_le_centralizer hτ
  have hcard : 5 ≤ Nat.card ↥(τ.supportᶜ : Finset (Fin n)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    exact h5
  have : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))) :=
    alternatingGroup.isSimpleGroup hcard
  have hq := (LocalCores.isQuasisimple_of_isSimpleGroup
    (alt_nonabelian_of_card (Ω := ↥(τ.supportᶜ : Finset (Fin n))) (by omega))).1
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    ((fixAltEquiv τ).trans (subgroupOfEquivOfLe hle).symm) hq, ?_⟩
  refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc => ?_)
  have hc' : (c : Perm (Fin n)) * τ = τ * c :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
  rw [mem_normalizer_iff]
  intro k
  constructor
  · exact conj_mem_fixAlt hc'
  · intro hk
    have hci : ((c⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) * τ = τ * (c⁻¹ :) := by
      have h1 : (c : Perm (Fin n))⁻¹ * τ = τ * (c : Perm (Fin n))⁻¹ := by
        calc (c : Perm (Fin n))⁻¹ * τ = (c : Perm (Fin n))⁻¹ * (τ * c) * (c : Perm (Fin n))⁻¹ := by
              group
          _ = (c : Perm (Fin n))⁻¹ * (c * τ) * (c : Perm (Fin n))⁻¹ := by rw [hc']
          _ = τ * (c : Perm (Fin n))⁻¹ := by group
      exact h1
    have h2 := conj_mem_fixAlt hci hk
    rwa [show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at h2

theorem exists_component_of_mulEquiv_alt {X : Type} [Group X] {m k : ℕ}
    (e : X ≃* alternatingGroup (Fin m)) (hk5 : 5 ≤ k) (hk : k + 4 ≤ m) (h4 : 4 ∣ m - k) :
    ∃ t : X, orderOf t = 2 ∧ ∃ B : Subgroup (centralizer ({t} : Set X)), IsComponent B ∧
      Nonempty (↥B ≃* alternatingGroup (Fin k)) := by
  classical
  obtain ⟨τ, hτ, hτ2, hτs⟩ := exists_even_involution hk h4
  set t₀ : alternatingGroup (Fin m) := ⟨τ, hτ⟩ with ht₀def
  have ht₀ : orderOf t₀ = 2 := by rw [ht₀def, Subgroup.orderOf_mk]; exact hτ2
  set C := centralizer ({t₀} : Set (alternatingGroup (Fin m))) with hC
  have hB₀ := isComponent_fixAlt hτ (by omega)
  set B₀ := (fixAlt τ).subgroupOf C with hB₀def
  have hcardk : Fintype.card ↥(τ.supportᶜ : Finset (Fin m)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτs]
    omega
  let eB₀ : ↥B₀ ≃* alternatingGroup (Fin k) :=
    ((subgroupOfEquivOfLe (fixAlt_le_centralizer hτ)).trans (fixAltEquiv τ).symm).trans
      (Fintype.equivFinOfCardEq hcardk).altCongrHom
  set φ := RestrictedStd.Spor.centralizerEquiv e.symm t₀ with hφ
  refine ⟨e.symm t₀, by rw [MulEquiv.orderOf_eq]; exact ht₀, B₀.map φ.toMonoidHom,
    CatLeaf.isComponent_map_mulEquiv φ hB₀, ⟨?_⟩⟩
  exact (B₀.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB₀

end CFSG.ComponentClassification.SolMax
