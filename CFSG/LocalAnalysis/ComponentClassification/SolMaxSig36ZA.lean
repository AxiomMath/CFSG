module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem map_conj_centralizer_singleton (g x : X) :
    (centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set X) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    change g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hz
    rw [mem_centralizer_singleton_iff] at hz
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [hz]
        _ = x * (g⁻¹ * z * g) := by group
    · change g * (g⁻¹ * z * g) * g⁻¹ = z
      group

theorem isPComponent_map_conj [Finite X] {Y L : Subgroup X} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) (g : X) :
    IsPComponent 2 ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (Y.map (MulAut.conj g).toMonoidHom)) := by
  let f : ↥Y ≃* ↥(Y.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap Y
  have h1 := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    f).1 (L.subgroupOf Y)).mp hL
  have h2 : (L.subgroupOf Y).map f.toMonoidHom =
      (L.map (MulAut.conj g).toMonoidHom).subgroupOf (Y.map (MulAut.conj g).toMonoidHom) := by
    apply Subgroup.map_injective (Y.map (MulAut.conj g).toMonoidHom).subtype_injective
    rw [map_subgroupOf_eq_of_le (map_mono hLY), Subgroup.map_map]
    have h3 : (Y.map (MulAut.conj g).toMonoidHom).subtype.comp f.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp Y.subtype := by
      ext y
      rfl
    rw [h3, ← Subgroup.map_map, map_subgroupOf_eq_of_le hLY]
  rwa [h2] at h1

theorem exists_four_of_fix {n : ℕ} (σ : Perm (Fin n)) (h4 : 4 ≤ n - σ.support.card) :
    ∃ δ : Perm (Fin n), δ ∈ alternatingGroup (Fin n) ∧ δ * δ = 1 ∧ δ.support.card = 4 ∧
      δ.support ⊆ σ.supportᶜ ∧ δ * σ = σ * δ := by
  classical
  have hF : 4 ≤ (σ.supportᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact h4
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (σ.supportᶜ).card)
  obtain ⟨b, hb, hbn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a}) (t := σ.supportᶜ) (by rw [Finset.card_singleton]; omega)
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, b}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨d, hd, hdn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, b, c}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn hcn hdn
  have hab : a ≠ b := Ne.symm hbn
  have hac : a ≠ c := Ne.symm hcn.1
  have hbc : b ≠ c := Ne.symm hcn.2
  have had : a ≠ d := Ne.symm hdn.1
  have hbd : b ≠ d := Ne.symm hdn.2.1
  have hcd : c ≠ d := Ne.symm hdn.2.2
  have hδ2 := swap_mul_swap_mul_self hac had hbc hbd
  have hδ4 := card_support_swap_mul_swap hab hcd hac had hbc hbd
  have hsub : (swap a b * swap c d).support ⊆ σ.supportᶜ := by
    intro ω hω
    have h1 := Perm.support_mul_le (swap a b) (swap c d) hω
    rw [Finset.sup_eq_union, Finset.mem_union, Perm.support_swap hab, Perm.support_swap hcd,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with (rfl | rfl) | (rfl | rfl)
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hdisj : (swap a b * swap c d).Disjoint σ :=
    Perm.disjoint_iff_disjoint_support.mpr (Finset.disjoint_of_subset_left hsub disjoint_compl_left)
  exact ⟨_, mem_alternatingGroup_of_four hδ2 hδ4, hδ2, hδ4, hsub, hdisj.commute.eq⟩

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_involution_lift (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r)
    {x : X} (hxN : x ∈ normalizer (M : Set X)) (hx2 : x * x = 1) {δ : Perm (Fin r)}
    (hδA : δ ∈ alternatingGroup (Fin r)) (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1)
    (hδx : δ * ρ ⟨x, hxN⟩ = ρ ⟨x, hxN⟩ * δ) :
    ∃ (y : X) (hy : y ∈ M), y ∈ centralizer ({x} : Set X) ∧ y * y = 1 ∧
      ρ ⟨y, le_normalizer hy⟩ = δ := by
  classical
  obtain ⟨w, hwx, hw⟩ := hρ.exists_lift hxN hx2 (b := ⟨δ, hδA⟩) hδx
  have hO : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hw2 : ((w : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ^ 2 = 1 := by
    apply θ.injective
    rw [map_pow, hw, map_one, sq]
    exact Subtype.ext hδ2
  have hw1 : ((w : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ≠ 1 := by
    intro h
    rw [h, map_one] at hw
    exact hδ1 (congrArg Subtype.val hw).symm
  obtain ⟨k, hk2, hkw⟩ := exists_involution_of_mk hO hw2 hw1
  refine ⟨((w ^ k : ↥M) : X), (w ^ k).2, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem hwx k
  · have h1 : (w ^ k) ^ 2 = 1 := by rw [← hk2]; exact pow_orderOf_eq_one _
    have h2 := congrArg Subtype.val h1
    rw [sq] at h2
    exact h2
  · rw [hρ.apply_of_mem hr (w ^ k), hkw, hw]

theorem IsPermAction.card_support_eq_four_of_not_mem_oddGen (hρ : IsPermAction θ ρ) [Finite X]
    (hr : 4 ≤ r) {v : X} (hvM : v ∈ M) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvo : v ∉ oddGen (centralizer ({v} : Set X))) :
    (ρ ⟨v, le_normalizer hvM⟩).support.card = 4 := by
  classical
  have hkerM : ∀ g ∈ M, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) :=
    fun g hg hgK => odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ hr hg hgK)
  have hσ2 : ρ ⟨v, le_normalizer hvM⟩ * ρ ⟨v, le_normalizer hvM⟩ = 1 := by
    rw [← map_mul, show (⟨v, le_normalizer hvM⟩ : ↥(normalizer (M : Set X))) *
      ⟨v, le_normalizer hvM⟩ = 1 from Subtype.ext hv2, map_one]
  have hA : ρ ⟨v, le_normalizer hvM⟩ ∈ alternatingGroup (Fin r) := by
    rw [hρ.apply_of_mem hr ⟨v, hvM⟩]
    exact (θ ((⟨v, hvM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M)).2
  have hdvd := four_dvd_card_support_of_mem_alternating hσ2 hA
  by_cases h8 : 8 ≤ (ρ ⟨v, le_normalizer hvM⟩).support.card
  · exact absurd (hρ.mem_oddGen_of_eight hr le_rfl hkerM (le_normalizer hvM) hvM hv2 hA h8) hvo
  · rcases (show (ρ ⟨v, le_normalizer hvM⟩).support.card = 0 ∨
        (ρ ⟨v, le_normalizer hvM⟩).support.card = 4 by omega) with h0 | h4
    · exfalso
      rw [Finset.card_eq_zero, Perm.support_eq_empty_iff] at h0
      have hodd := hkerM v hvM (hρ.mem_coreActionKernel (le_normalizer hvM) h0)
      have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hv2)
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact hv1 (orderOf_eq_one_iff.mp h)
      · rw [h] at hodd
        exact absurd hodd (by decide)
    · exact h4

end CFSG.ComponentClassification.SolMax
