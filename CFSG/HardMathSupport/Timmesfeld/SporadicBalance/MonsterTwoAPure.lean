module

public import CFSG.Monster.Existence.Defs
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.Existence CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Blueprint CFSG.Open

variable {K : Type} [Group K]

theorem orderOf_eq_of_isConj'' {a b : K} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem exists_orderOf_nineteen_of_twoPointShape_one [Finite K]
    (hE6 : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → 19 ∣ Nat.card X)
    {H : Subgroup K} (h : TwoPointShape H 1) : ∃ x ∈ H, orderOf x = 19 := by
  obtain ⟨N, hN, -, -, hL⟩ := h
  have h1 := hE6 _ hL
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h19 : 19 ∣ Nat.card H := by rw [h2]; exact Dvd.dvd.mul_right h1 _
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 19 h19
  exact ⟨x, x.2, by rw [← Subgroup.orderOf_coe] at hx; exact hx⟩

theorem image_of_twoA_pair {X : Type*} [Group X] [Finite K]
    (hE6 : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → 19 ∣ Nat.card X)
    {a : K} {c : Fin 9 → K} (hc1 : IsConj a (c 1))
    (hshape : ∀ (α β : K) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i)
    {α δ : K} (hα : IsConj a α) (hδ : IsConj a δ) (hαδ : IsConj a (α * δ))
    (hcomm : α * δ = δ * α) (hα2 : orderOf α = 2) (hδ2 : orderOf δ = 2) (π : cent α →* X)
    (hker : ∀ x : cent α, π x = 1 ↔ (x : K) = 1 ∨ (x : K) = α) :
    orderOf (π ⟨δ, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩) = 2 ∧
      19 ∣ Nat.card (Subgroup.centralizer
        ({π ⟨δ, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩} : Set X)) := by
  set δ' : cent α := ⟨δ, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩ with hδ'
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hshape1 := hshape α δ 1 hα hδ (hαδ.symm.trans hc1)
  obtain ⟨x, hxH, hx19⟩ := exists_orderOf_nineteen_of_twoPointShape_one hE6 hshape1
  have hxα : x ∈ cent α := (Subgroup.mem_inf.1 hxH).1
  have hxδ : x ∈ cent δ := (Subgroup.mem_inf.1 hxH).2
  set x' : cent α := ⟨x, hxα⟩
  have hπδ1 : π δ' ≠ 1 := by
    intro h1
    rcases (hker δ').1 h1 with h | h
    · rw [show (δ' : K) = δ from rfl] at h
      rw [h, orderOf_one] at hδ2
      exact absurd hδ2 (by norm_num)
    · rw [show (δ' : K) = δ from rfl] at h
      have h2 := orderOf_eq_of_isConj'' hαδ
      have h3 := orderOf_eq_of_isConj'' hα
      rw [h, ← pow_two, ← hα2, pow_orderOf_eq_one, orderOf_one] at h2
      rw [h2, hα2] at h3
      exact absurd h3 (by norm_num)
  have hπδ2 : orderOf (π δ') = 2 := by
    refine orderOf_eq_prime ?_ hπδ1
    rw [← map_pow]
    have : δ' ^ 2 = 1 := Subtype.ext (by
      show δ ^ 2 = 1
      rw [← hδ2]
      exact pow_orderOf_eq_one δ)
    rw [this, map_one]
  have hπx : orderOf (π x') = 19 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow]
      have : x' ^ 19 = 1 := Subtype.ext (by
        show x ^ 19 = 1
        rw [← hx19]
        exact pow_orderOf_eq_one x)
      rw [this, map_one]
    · rcases (hker x').1 h1 with h | h
      · rw [show (x' : K) = x from rfl] at h
        rw [h, orderOf_one] at hx19
        exact absurd hx19 (by norm_num)
      · rw [show (x' : K) = x from rfl] at h
        rw [h, hα2] at hx19
        exact absurd hx19 (by norm_num)
  have hxc : π x' * π δ' = π δ' * π x' := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show x * δ = δ * x
    exact Subgroup.mem_centralizer_singleton_iff.1 hxδ
  refine ⟨hπδ2, ?_⟩
  have hmem : π x' ∈ Subgroup.centralizer ({π δ'} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxc
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [hπx] at this

theorem babyInv_zero_of_nineteen (hT3 : BabyTableIII) {t : B} (h2 : orderOf t = 2)
    (h19 : 19 ∣ Nat.card (Subgroup.centralizer ({t} : Set B))) : BabyInv 0 t := by
  obtain ⟨k, hk⟩ := hT3.1 t h2
  have hk0 : k = 0 := by
    rw [hk.2] at h19
    fin_cases k
    · rfl
    all_goals (exfalso; revert h19; norm_num [babyCentOrder])
  rw [hk0] at hk
  exact hk

theorem quotient_ker_iff {X : Type*} [Group X] {α : K} (hα2 : orderOf α = 2)
    (hZ : (Subgroup.center (cent α)).map (cent α).subtype = Subgroup.zpowers α)
    (e : cent α ⧸ Subgroup.center (cent α) ≃* X) (x : cent α) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (cent α)))) x = 1 ↔
      (x : K) = 1 ∨ (x : K) = α := by
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    have hmem : (x : K) ∈ (Subgroup.center (cent α)).map (cent α).subtype := ⟨x, hx, rfl⟩
    rw [hZ] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h := zpow_mod_orderOf α k
    rw [hα2] at h
    push_cast at h
    rw [← hk, ← h]
    rcases Int.emod_two_eq_zero_or_one k with h2 | h2
    · left; rw [h2, zpow_zero]
    · right; rw [h2, zpow_one]
  · intro hx
    have hmem : (x : K) ∈ Subgroup.zpowers α := by
      rcases hx with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers α
    rw [← hZ] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem exists_hom_ker_iff {X : Type*} [Group X] {α : K} (hα2 : orderOf α = 2)
    (hZ : (Subgroup.center (cent α)).map (cent α).subtype = Subgroup.zpowers α)
    (e : cent α ⧸ Subgroup.center (cent α) ≃* X) :
    ∃ π : cent α →* X, ∀ x : cent α, π x = 1 ↔ (x : K) = 1 ∨ (x : K) = α :=
  ⟨_, quotient_ker_iff hα2 hZ e⟩

theorem not_twoA_pure_eight [Finite K] (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hE6 : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → 19 ∣ Nat.card X)
    {a : K} (ha2 : orderOf a = 2) (hA : ∀ t : K, IsConj a t → IsTwoACentralizer t)
    {c : Fin 9 → K} (hc1 : IsConj a (c 1))
    (hshape : ∀ (α β : K) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i)
    {α β γ : K} (hab : α * β = β * α) (hac : α * γ = γ * α) (hbc : β * γ = γ * β)
    (hα : IsConj a α) (hβ : IsConj a β) (hγ : IsConj a γ) (hαβ : IsConj a (α * β))
    (hαγ : IsConj a (α * γ)) (hβγ : IsConj a (β * γ)) (hαβγ : IsConj a (α * (β * γ))) : False := by
  have hord : ∀ t, IsConj a t → orderOf t = 2 := fun t ht => (orderOf_eq_of_isConj'' ht).symm.trans ha2
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA α hα
  obtain ⟨π, hker⟩ := @exists_hom_ker_iff K _ B Units.instGroup α (hord α hα) hZ e
  have hcβγ : α * (β * γ) = β * γ * α := by
    rw [← mul_assoc, hab, mul_assoc, hac, ← mul_assoc]
  obtain ⟨hr2, hr19⟩ := image_of_twoA_pair hE6 hc1 hshape hα hβ hαβ hab (hord α hα) (hord β hβ) π
    hker
  obtain ⟨hs2, hs19⟩ := image_of_twoA_pair hE6 hc1 hshape hα hγ hαγ hac (hord α hα) (hord γ hγ) π
    hker
  obtain ⟨hu2, hu19⟩ := image_of_twoA_pair hE6 hc1 hshape hα hβγ hαβγ hcβγ (hord α hα)
    (hord _ hβγ) π hker
  set β' : cent α := ⟨β, Subgroup.mem_centralizer_singleton_iff.2 hab.symm⟩
  set γ' : cent α := ⟨γ, Subgroup.mem_centralizer_singleton_iff.2 hac.symm⟩
  have hprod : (⟨β * γ, Subgroup.mem_centralizer_singleton_iff.2 hcβγ.symm⟩ : cent α) = β' * γ' :=
    rfl
  rw [hprod] at hu2 hu19
  have hr := babyInv_zero_of_nineteen hT3 hr2 hr19
  have hs := babyInv_zero_of_nineteen hT3 hs2 hs19
  have hu := babyInv_zero_of_nineteen hT3 hu2 hu19
  have hne : π γ' ≠ π β' := by
    intro h
    have h1 : π (β'⁻¹ * γ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rcases (hker _).1 h1 with h2 | h2
    · have h3 : β = γ := by
        have : (β : K)⁻¹ * γ = 1 := h2
        exact (inv_mul_eq_one.1 this)
      have h4 := hord _ hβγ
      have h5 : β * γ = 1 := by
        rw [← h3, ← pow_two, ← hord β hβ, pow_orderOf_eq_one]
      rw [h5, orderOf_one] at h4
      exact absurd h4 (by norm_num)
    · have h3 : γ = β * α := by
        have : (β : K)⁻¹ * γ = α := h2
        rw [← this, mul_inv_cancel_left]
      have h4 := hord _ hαβγ
      have h5 : α * (β * γ) = 1 := by
        rw [h3, ← mul_assoc β, ← pow_two, ← hord β hβ, pow_orderOf_eq_one, one_mul, ← pow_two,
          ← hord α hα, pow_orderOf_eq_one]
      rw [h5, orderOf_one] at h4
      exact absurd h4 (by norm_num)
  obtain ⟨k, hk⟩ := (hT4 _ hr).1 _ hs hne
  rw [map_mul] at hu
  fin_cases k
  · obtain ⟨-, h1⟩ := hk
    rw [hu.2] at h1
    revert h1
    norm_num [babyCentOrder]
  · obtain ⟨-, h1⟩ := hk
    rw [hu.2] at h1
    revert h1
    norm_num [babyCentOrder]
  · have h1 : orderOf (π β' * π γ') = 3 := hk
    rw [hu.1] at h1
    exact absurd h1 (by norm_num)
  · have h1 : orderOf (π β' * π γ') = 4 := hk.1
    rw [hu.1] at h1
    exact absurd h1 (by norm_num)

theorem exists_mem_not_mem_of_ncard_lt {A : Subgroup K} {S : Set K} [Finite K]
    (h : S.ncard < Nat.card A) : ∃ x ∈ A, x ∉ S := by
  by_contra hc
  push Not at hc
  have hle : (A : Set K) ⊆ S := fun x hx => hc x hx
  have h1 := Set.ncard_le_ncard hle (Set.toFinite S)
  rw [← Nat.card_coe_set_eq] at h1
  exact absurd h (not_lt.2 h1)

theorem exists_twoB_of_elemAbelian [Finite K] (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hE6 : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → 19 ∣ Nat.card X)
    {a z : K} (ha2 : orderOf a = 2) (hA : ∀ t : K, IsConj a t → IsTwoACentralizer t)
    {c : Fin 9 → K} (hc1 : IsConj a (c 1))
    (hshape : ∀ (α β : K) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i)
    (hcls : ∀ u : K, orderOf u = 2 → IsConj a u ∨ IsConj z u)
    (A : Subgroup K) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAe : ∀ x ∈ A, x ^ 2 = 1)
    (h8 : 8 ≤ Nat.card A) : ∃ u ∈ A, IsConj z u := by
  by_contra hno
  push Not at hno
  have h2A : ∀ u ∈ A, u ≠ 1 → IsConj a u := by
    intro u hu hu1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hcls u (orderOf_eq_prime (hAe u hu) hu1) with h | h
    · exact h
    · exact absurd h (hno u hu)
  have inv_eq : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hAe x hx)
  obtain ⟨α, hα, hα1⟩ := exists_mem_not_mem_of_ncard_lt (A := A) (S := {1})
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨β, hβ, hβS⟩ := exists_mem_not_mem_of_ncard_lt (A := A) (S := {1, α})
    (lt_of_le_of_lt (Set.ncard_insert_le _ _) (by rw [Set.ncard_singleton]; omega))
  obtain ⟨γ, hγ, hγS⟩ := exists_mem_not_mem_of_ncard_lt (A := A) (S := {1, α, β, α * β})
    (lt_of_le_of_lt (Set.ncard_insert_le _ _) (by
      have := Set.ncard_insert_le α ({β, α * β} : Set K)
      have := Set.ncard_insert_le β ({α * β} : Set K)
      rw [Set.ncard_singleton] at this
      omega))
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, not_or] at hα1 hβS hγS
  obtain ⟨hβ1, hβα⟩ := hβS
  obtain ⟨hγ1, hγα, hγβ, hγαβ⟩ := hγS
  have hab := hAc α hα β hβ
  have hac := hAc α hα γ hγ
  have hbc := hAc β hβ γ hγ
  have ne1 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x * y ≠ 1 := by
    intro x hx y hy hxy h
    apply hxy
    have := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq y hy]
  refine not_twoA_pure_eight hT3 hT4 hE6 ha2 hA hc1 hshape hab hac hbc (h2A α hα hα1)
    (h2A β hβ hβ1) (h2A γ hγ hγ1) (h2A _ (A.mul_mem hα hβ) (ne1 α hα β hβ (Ne.symm hβα)))
    (h2A _ (A.mul_mem hα hγ) (ne1 α hα γ hγ (Ne.symm hγα)))
    (h2A _ (A.mul_mem hβ hγ) (ne1 β hβ γ hγ (Ne.symm hγβ)))
    (h2A _ (A.mul_mem hα (A.mul_mem hβ hγ)) ?_)
  rw [← mul_assoc]
  exact ne1 _ (A.mul_mem hα hβ) γ hγ (Ne.symm hγαβ)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
