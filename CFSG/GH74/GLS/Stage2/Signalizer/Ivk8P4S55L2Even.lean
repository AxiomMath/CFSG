module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2Pair

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG
open scoped commutatorElement

theorem commutator_mul_zpow {G : Type*} [Group G] {c κ κ' : G} (i j : ℤ) (h1 : Commute c κ)
    (h2 : Commute c κ') : ⁅c ^ i * κ, c ^ j * κ'⁆ = ⁅κ, κ'⁆ := by
  have ha : Commute (c ^ i) κ := h1.zpow_left i
  have ha' : Commute (c ^ i) κ' := h2.zpow_left i
  have hb : Commute (c ^ j) κ := h1.zpow_left j
  have hb' : Commute (c ^ j) κ' := h2.zpow_left j
  have hab : Commute (c ^ i) (c ^ j) := Commute.zpow_zpow_self c i j
  generalize c ^ i = a at ha ha' hab
  generalize c ^ j = b at hb hb' hab
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : a * κ * (b * κ') * (a * κ)⁻¹ = κ * (b * κ') * κ⁻¹ := by
    have hc : Commute a (κ * (b * κ') * κ⁻¹) :=
      (ha.mul_right (hab.mul_right ha')).mul_right ha.inv_right
    calc a * κ * (b * κ') * (a * κ)⁻¹ = a * (κ * (b * κ') * κ⁻¹) * a⁻¹ := by group
      _ = κ * (b * κ') * κ⁻¹ := by rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [e1]
  have hc2 : Commute b (κ * κ' * κ⁻¹ * κ'⁻¹) :=
    ((hb.mul_right hb').mul_right hb.inv_right).mul_right hb'.inv_right
  calc κ * (b * κ') * κ⁻¹ * (b * κ')⁻¹ = (κ * b) * κ' * κ⁻¹ * κ'⁻¹ * b⁻¹ := by group
    _ = (b * κ) * κ' * κ⁻¹ * κ'⁻¹ * b⁻¹ := by rw [← hb.eq]
    _ = b * (κ * κ' * κ⁻¹ * κ'⁻¹) * b⁻¹ := by group
    _ = κ * κ' * κ⁻¹ * κ'⁻¹ := by rw [hc2.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem pair_le_sup {Γ : Type} [Group Γ] {K : Subgroup Γ} {yh c k : Γ} (hyh : yh ∈ K)
    (hc : c ∈ centralizer (K : Set Γ)) (hk : k ∈ K) :
    Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ) ≤ K ⊔ zpowers c := by
  have hcK : ∀ x ∈ K, x * c = c * x := fun x hx => (Subgroup.mem_centralizer_iff.mp hc x hx)
  rw [Subgroup.closure_le]
  have h1 : yh * c ∈ K ⊔ zpowers c :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hyh) (Subgroup.mem_sup_right (mem_zpowers c))
  have h2 : k * (yh * c) * k⁻¹ = (k * yh * k⁻¹) * c := by
    have : k * c * k⁻¹ = c := by rw [hcK k hk]; group
    calc k * (yh * c) * k⁻¹ = k * yh * (k⁻¹ * k) * c * k⁻¹ := by group
      _ = k * yh * k⁻¹ * (k * c * k⁻¹) := by group
      _ = (k * yh * k⁻¹) * c := by rw [this]
  rintro _ (rfl | rfl)
  · exact h1
  · rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hk hyh) (Subgroup.inv_mem _ hk)))
      (Subgroup.mem_sup_right (mem_zpowers c))

theorem pair_commutator_mem {Γ : Type} [Group Γ] {K : Subgroup Γ} {yh c k : Γ} (hyh : yh ∈ K)
    (hc : c ∈ centralizer (K : Set Γ)) (hk : k ∈ K) {u v : Γ}
    (hu : u ∈ Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ))
    (hv : v ∈ Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ)) : ⁅u, v⁆ ∈ K := by
  have hcN : c ∈ normalizer (K : Set Γ) := Subgroup.centralizer_le_normalizer (K : Set Γ) hc
  obtain ⟨i, κ, hκ, rfl⟩ := mem_sup_zpowers_decomp hcN (pair_le_sup hyh hc hk hu)
  obtain ⟨j, κ', hκ', rfl⟩ := mem_sup_zpowers_decomp hcN (pair_le_sup hyh hc hk hv)
  rw [commutator_mul_zpow i j ((Subgroup.mem_centralizer_iff.mp hc κ hκ).symm)
    ((Subgroup.mem_centralizer_iff.mp hc κ' hκ').symm)]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hκ hκ') (Subgroup.inv_mem _ hκ))
    (Subgroup.inv_mem _ hκ')

theorem even_center_of_pair {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ} {yh c k : Γ}
    (hyh : yh ∈ K) (hc : c ∈ centralizer (K : Set Γ)) (hk : k ∈ K) {J : Subgroup Γ}
    (hJ : J = Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ))
    (N : Subgroup ↥J) [N.Normal] {F' : Type} [Field F'] [Finite F']
    (e' : (↥J ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) F')
    (h5 : Nat.card F' = 5) (hY : Nat.card (↥K ⧸ center ↥K) = 60) :
    2 ∣ Nat.card (center ↥K) := by
  classical
  let q : ↥J →* Matrix.SpecialLinearGroup (Fin 2) F' := e'.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective N)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F') := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    have := Fintype.ofFinite F'
    have : (4 : ℕ) ≤ (Finset.univ : Finset F').card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h5]
      omega
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq this
    exact ⟨s, hs⟩
  let D : Subgroup ↥J := ⁅(⊤ : Subgroup ↥J), ⊤⁆
  have hDq : D.map q = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective q hq]
    exact hperf.commutator_eq_top
  have hsurj : Function.Surjective (q.domRestrict D) := by
    intro s
    have : s ∈ D.map q := by rw [hDq]; trivial
    obtain ⟨d, hd, hds⟩ := this
    exact ⟨⟨d, hd⟩, hds⟩
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F') ∣ Nat.card ↥D :=
    Subgroup.card_dvd_of_surjective hsurj
  have hDK : ∀ d : ↥J, d ∈ D → (d : Γ) ∈ K := by
    intro d hd
    have hle : D ≤ K.comap J.subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      show ((⁅g₁, g₂⁆ : ↥J) : Γ) ∈ K
      exact pair_commutator_mem hyh hc hk (hJ ▸ g₁.2) (hJ ▸ g₂.2)
    exact hle hd
  let εD : ↥D →* ↥K := ((J.subtype).comp D.subtype).codRestrict K (fun d => hDK d d.2)
  have hεinj : Function.Injective εD := by
    intro d d' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥K => (x : Γ)) h
  have h2 : Nat.card ↥D ∣ Nat.card ↥K := Subgroup.card_dvd_of_injective εD hεinj
  have h3 : Nat.card ↥K = Nat.card (↥K ⧸ center ↥K) * Nat.card (center ↥K) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K)
    exact this
  have h4 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F') = 120 := by
    rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two, h5]
    norm_num
  rw [h4] at h1
  have h6 := h1.trans h2
  rw [h3, hY] at h6
  have : 60 * 2 ∣ 60 * Nat.card (center ↥K) := by simpa using h6
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
