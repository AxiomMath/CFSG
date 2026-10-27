module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)

@[expose] def e7Frame : Fin 4 → List (Fin Tag.E7.rank → ℤ) :=
  ![oddDerivE7YFrame, oddDerivE7ZFrame, oddDerivE7UFrame, oddDerivE7VFrame]

@[expose] def e7CentList : Fin 4 → List (Fin Tag.E7.rank → ℤ) :=
  ![
    [![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 0, 0],
      ![1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 0],
      ![0, 1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 1],
      ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0, 0],
      ![1, 0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 1],
      ![0, 1, 1, 2, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0],
      ![1, 1, 1, 2, 1, 0, 0], ![0, 1, 1, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0],
      ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 0, 0]],
    [![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 0],
      ![0, 0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
      ![0, 0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0, 0],
      ![1, 1, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 0],
      ![1, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 0],
      ![0, 1, 1, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0], ![1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 0, 0], ![0, 1, 1, 2, 2, 1, 1],
      ![1, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1, 0],
      ![0, 1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 1],
      ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1]],
    [![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 0, 0],
      ![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0, 0],
      ![1, 0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 2, 1, 1, 0], ![0, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 1, 1, 1],
      ![0, 1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 1],
      ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1],
      ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1],
      ![1, 2, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1]],
    [![0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0],
      ![0, 0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1, 1],
      ![0, 1, 1, 2, 1, 0, 0], ![1, 0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 2, 1, 1, 0], ![0, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 1, 1, 1],
      ![0, 1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 1],
      ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1],
      ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1],
      ![1, 2, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1],
      ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
      ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]
  ]

theorem e7CentList_check (κ : Fin 4) :
    (e7CentList κ).Nodup ∧ (∀ γ ∈ e7CentList κ, oddDerivIsRootB .E7 γ = true ∧ 0 < height γ) ∧
      (∀ γ ∈ e7CentList κ, ∀ σ ∈ e7Frame κ,
        γ = σ ∨ (γ ≠ -σ ∧ oddDerivNotRootB .E7 (γ + σ) = true)) ∧
      (∀ σ ∈ e7Frame κ, oddDerivIsRootB .E7 σ = true) ∧ (e7CentList κ).length = 33 := by
  revert κ
  decide +kernel


section Bounds

variable {K : Type} [Field K]

theorem commute_pinnedX_e7Frame (κ : Fin 4) {γ : Fin Tag.E7.rank → ℤ}
    (hγ : γ ∈ e7CentList κ) (c : K) :
    Commute (pinnedX .E7 K γ c) (((e7Frame κ).map fun σ => pinnedX .E7 K σ 1).prod) := by
  obtain ⟨-, hroot, hcomm, hframe, -⟩ := e7CentList_check κ
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
  have hσr : IsRoot .E7 σ := isRoot_of_oddDerivIsRootB (hframe σ hσ)
  refine E6Pilot.commute_pinnedX_of_eq_or_not_isRoot (Or.inr (Or.inr (Or.inl rfl)))
    (isRoot_of_oddDerivIsRootB (hroot γ hγ).1) hσr ?_ c 1
  rcases hcomm γ hγ σ hσ with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, not_isRoot_of_oddDerivNotRootB h2⟩

variable [Finite K]

theorem pow_dvd_card_centralizer_e7Frame {f : ℕ} (hK : Nat.card K = 2 ^ f) (κ : Fin 4) :
    2 ^ (f * 33) ∣ Nat.card (centralizer ({(⟨((e7Frame κ).map fun σ => pinnedX .E7 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E7 K)} :
        Set (adjointGroup .E7 K))) := by
  obtain ⟨hnodup, hroot, -, -, hlen⟩ := e7CentList_check κ
  have hinj : Function.Injective (e7CentList κ).get := List.nodup_iff_injective_get.1 hnodup
  have hpos : ∀ i, IsRoot .E7 ((e7CentList κ).get i) ∧ 0 < height ((e7CentList κ).get i) :=
    fun i => ⟨isRoot_of_oddDerivIsRootB (hroot _ (List.get_mem _ _)).1,
      (hroot _ (List.get_mem _ _)).2⟩
  obtain ⟨hU, hψ⟩ := positive_root_product_injectivity .E7 K _ hinj hpos
  refine E6Pilot.pow_dvd_card_centralizer_of_injective Nat.prime_two hK _
    (X := Fin (e7CentList κ).length → K) ?_ _ hψ hU fun c => ?_
  · rw [Nat.card_fun, Nat.card_fin, hK, ← pow_mul, hlen]
  · refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact commute_pinnedX_e7Frame κ (List.get_mem _ _) (c i)

theorem pow_dvd_card_centralizer_highRoot_E7 {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    2 ^ (f * 63) ∣ Nat.card (centralizer ({(⟨pinnedX .E7 K (highRoot .E7) 1,
      pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E7 K)} : Set (adjointGroup .E7 K))) := by
  have : Finite (ModGL Tag.E7 K) := finite_modGL
  refine E6Pilot.pow_dvd_card_centralizer_of_injective Nat.prime_two hK _
    (X := posUnipotent .E7 K) ?_ (fun u => (u : ModGL .E7 K)) Subtype.val_injective
    (fun u => u.2) fun u => ?_
  · rw [card_posUnipotent, hK, ← pow_mul, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7]
  · exact mem_centralizer_singleton_iff.1
      (E8Pilot.posUnipotent_le_centralizer_pinnedX_highRoot 1 u.2)

theorem two_pow_dvd_card_centralizer_E7 {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {w : adjointGroup .E7 K} (hw : orderOf w = 2) :
    2 ^ (33 * f) ∣ Nat.card (centralizer ({w} : Set (adjointGroup .E7 K))) := by
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hw2 : w ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE7 hw2 hw1
  have hcard : ∀ v : adjointGroup .E7 K, g * w * g⁻¹ = v →
      Nat.card (centralizer ({w} : Set (adjointGroup .E7 K))) =
        Nat.card (centralizer ({v} : Set (adjointGroup .E7 K))) := by
    rintro v rfl
    have hmap : (centralizer ({w} : Set (adjointGroup .E7 K))).map (MulAut.conj g).toMonoidHom =
        centralizer ({g * w * g⁻¹} : Set (adjointGroup .E7 K)) := by
      ext x
      simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
          _ = g * (w * y) * g⁻¹ := by rw [hy]
          _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by group⟩
        calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
          _ = w * (g⁻¹ * x * g) := by group
    rw [← hmap, card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h | h
  · rw [hcard _ h]
    exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_highRoot_E7 hK)
  · rw [hcard _ h]
    exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_e7Frame hK 0)
  · rw [hcard _ h]
    exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_e7Frame hK 1)
  · rw [hcard _ h]
    exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_e7Frame hK 2)
  · rw [hcard _ h]
    exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_e7Frame hK 3)

end Bounds

section TwoParts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem factorization_card_le_of_le_centralizer_E7 (hL : standardComponentIsStandard L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) :
    (Nat.card X).factorization 2 ≤ 63 * f + 2 + f.factorization 2 := by
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have h1 := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer hL e ht hKt hXt
  have h2 := E6Pilot.card_mulAut_dvd_card_mul_card_outer (adjointGroup .E7 K)
  have h3 := (ordinary_E_outer_order_Cartan_divisor Tag.E7 (Or.inr (Or.inl rfl)) Nat.prime_two hf
    K hK 2 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))).1
  rw [mul_one] at h3
  have h4 : Nat.card X ∣ 2 * (Nat.card (adjointGroup .E7 K) * (2 * f)) :=
    h1.trans (Nat.mul_dvd_mul_left 2 (h2.trans (Nat.mul_dvd_mul_left _ h3)))
  have hC0 : Nat.card (adjointGroup .E7 K) ≠ 0 := Nat.card_pos.ne'
  have hf0 : f ≠ 0 := by omega
  have h6 : (2 * f : ℕ) ≠ 0 := by positivity
  have hN0 : Nat.card (adjointGroup .E7 K) * (2 * f) ≠ 0 := mul_ne_zero hC0 h6
  have h5 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (mul_ne_zero two_ne_zero hN0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hN0, Finsupp.add_apply, Nat.factorization_mul hC0 h6,
    Finsupp.add_apply, Nat.factorization_mul two_ne_zero hf0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    E6Pilot.factorization_card_adjointGroup hK,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7] at h5
  omega

end TwoParts

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_exists_inner_E7_field (hset : StandardSetting G L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E7 K₂) :
    ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  refine E6Pilot.not_exists_inner_of_two_pow_dvd_centralizer ht eM
    (center_adjointGroup_eq_bot_field _ K₂)
    (E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E7) (Pi.single (0 : Fin 7) 1))
    (a := 33 * (2 * f)) (fun w hw => two_pow_dvd_card_centralizer_E7 hK₂ hw) fun hdvd => ?_
  have hb := factorization_card_le_of_le_centralizer_E7 hset.standard hK e ht hKt
    (le_refl (centralizer ({t} : Set G)))
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega

theorem not_mem_E7_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E7 K₂) :
    t ∉ M :=
  fun htM => not_exists_inner_E7_field hset hK e ht hKt hK₂ eM ⟨t, htM, fun _ _ => rfl⟩

end Inner

end CFSG.SeitzReduction.E7Pilot
