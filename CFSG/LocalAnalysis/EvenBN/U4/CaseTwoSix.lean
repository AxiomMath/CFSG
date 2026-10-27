module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoFive

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G] {M : Subgroup G} {k : Type*} [Field k] [Finite k]

theorem card_le_card_inf_prodFactorTwo_mul (ψ : M ≃* SL(2, k) × SL(2, k)) {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {V : Subgroup G} (hVM : V ≤ M)
    (hV : IsPGroup 2 V) : Nat.card V ≤ Nat.card (V ⊓ prodFactorTwo ψ : Subgroup G) *
      Nat.card k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : V →* SL(2, k) :=
    (MonoidHom.fst _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hVM))
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ Nat.card k :=
    card_le_of_isPGroup_of_sl2 (MulEquiv.refl _) hk hm
      (hV.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  have hker : Nat.card φ.ker = Nat.card (V ⊓ prodFactorTwo ψ : Subgroup G) := by
    have e : φ.ker.map V.subtype = V ⊓ prodFactorTwo ψ := by
      ext g
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact mem_inf.2 ⟨w.2, (Common.mem_prodFactorTwo_iff ψ).2 ⟨hVM w.2, hw⟩⟩
      · intro hg
        obtain ⟨hgV, hg2⟩ := mem_inf.1 hg
        obtain ⟨hgM, hg1⟩ := (Common.mem_prodFactorTwo_iff ψ).1 hg2
        exact ⟨⟨g, hgV⟩, hg1, rfl⟩
    rw [← e, card_map_of_injective V.subtype_injective]
  rw [← h1, hker]
  exact Nat.mul_le_mul_left _ hrange

theorem card_le_card_inf_prodFactorOne_mul (ψ : M ≃* SL(2, k) × SL(2, k)) {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {V : Subgroup G} (hVM : V ≤ M)
    (hV : IsPGroup 2 V) : Nat.card V ≤ Nat.card (V ⊓ prodFactorOne ψ : Subgroup G) *
      Nat.card k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : V →* SL(2, k) :=
    (MonoidHom.snd _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hVM))
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ Nat.card k :=
    card_le_of_isPGroup_of_sl2 (MulEquiv.refl _) hk hm
      (hV.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  have hker : Nat.card φ.ker = Nat.card (V ⊓ prodFactorOne ψ : Subgroup G) := by
    have e : φ.ker.map V.subtype = V ⊓ prodFactorOne ψ := by
      ext g
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact mem_inf.2 ⟨w.2, (Common.mem_prodFactorOne_iff ψ).2 ⟨hVM w.2, hw⟩⟩
      · intro hg
        obtain ⟨hgV, hg2⟩ := mem_inf.1 hg
        obtain ⟨hgM, hg1⟩ := (Common.mem_prodFactorOne_iff ψ).1 hg2
        exact ⟨⟨g, hgV⟩, hg1, rfl⟩
    rw [← e, card_map_of_injective V.subtype_injective]
  rw [← h1, hker]
  exact Nat.mul_le_mul_left _ hrange

omit [Finite k] in
theorem map_conj_prodFactorOne_of_swap {S : Type*} [Group S] (ψ : M ≃* S × S) {t : G}
    (ht : t ∈ normalizer (M : Set G)) (htt : t * t = 1)
    (hswap : ∀ (x y : M) (y₁ y₂ : S), (y : G) = t⁻¹ * x * t → ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (prodFactorOne ψ) = prodFactorTwo ψ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine le_antisymm ?_ fun x hx =>
    ⟨t⁻¹ * x * t, Common.conj_mem_prodFactorOne_of_swap ψ ht hswap hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := Common.conj_mem_prodFactorTwo_of_swap ψ ht hswap hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hti] at this ⊢
    exact this
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem eq_one_of_commute_of_torus {f : ℕ} {k₂ : Type} [Field k₂] [Fintype k₂] [CharP k₂ 2]
    (hf : 1 ≤ f)
    (hk₂ : Fintype.card k₂ = 2 ^ f) {g x y : SL(2, k₂)} (hg1 : g ≠ 1)
    (hgpow : g ^ (Nat.card k₂ - 1) = 1) (hxg : x * g = g * x) (hx1 : x ≠ 1)
    (hyx : y * x = x * y) {n : ℕ} (hy : orderOf y ∣ 2 ^ n) : y = 1 := by
  have hcard : Nat.card k₂ - 1 = 2 ^ f - 1 := by rw [Nat.card_eq_fintype_card, hk₂]
  have hxC : x ∈ centralizer (zpowers g : Set SL(2, k₂)) := by
    rw [Common.centralizer_zpowers, mem_centralizer_singleton_iff]
    exact hxg
  have hxpow : x ^ (Nat.card k₂ - 1) = 1 := by
    have h1 := Common.card_centralizer_zpowers (MulEquiv.refl _) hg1 hgpow
    have h2 : (⟨x, hxC⟩ : centralizer (zpowers g : Set SL(2, k₂))) ^
        Nat.card (centralizer (zpowers g : Set SL(2, k₂))) = 1 := pow_card_eq_one'
    rw [h1] at h2
    simpa using congrArg Subtype.val h2
  have hyC : y ∈ centralizer (zpowers x : Set SL(2, k₂)) := by
    rw [Common.centralizer_zpowers, mem_centralizer_singleton_iff]
    exact hyx
  have hypow : orderOf y ∣ 2 ^ f - 1 := by
    have h1 := Common.card_centralizer_zpowers (MulEquiv.refl _) hx1 hxpow
    have h2 : (⟨y, hyC⟩ : centralizer (zpowers x : Set SL(2, k₂))) ^
        Nat.card (centralizer (zpowers x : Set SL(2, k₂))) = 1 := pow_card_eq_one'
    rw [h1, hcard] at h2
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val h2)
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hcop : Nat.Coprime (2 ^ n) (2 ^ f - 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hy hcop)
    hypow)

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚


theorem exists_torus_coord (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a)) :
    ∃ g : SL(2, k₂), g ≠ 1 ∧ g ^ (Nat.card k₂ - 1) = 1 ∧
      ∀ (j : miyamotoM2G h L η t Q), (j : G) ∈ centralizer (miyamotoIN2G h L η : Set G) →
        (ψ₂ j).1 * g = g * (ψ₂ j).1 ∧ (ψ₂ j).2 * g = g * (ψ₂ j).2 := by
  obtain ⟨-, -, hNM, -, -, -, -, -⟩ := hS.sec3_12_two
  obtain ⟨d, hd⟩ := (isCyclic_miyamotoIN2G h L η).exists_generator
  have hdM : (d : G) ∈ miyamotoM2G h L η t Q := hNM (mem_inf.1 d.2).2
  have hq4 := hS.four_le
  set g := α₂ ⟨d, (mem_inf.1 d.2).2⟩ with hg
  have hψd : ψ₂ ⟨d, hdM⟩ = (g, g) := hψα₂ ⟨d, (mem_inf.1 d.2).2⟩ ⟨d, hdM⟩ rfl
  have hd1 : d ≠ 1 := by
    intro e
    have hall : ∀ x : miyamotoIN2G h L η, x = 1 := fun x => by
      obtain ⟨n, hn⟩ := hd x
      rw [← hn]
      simp [e]
    have : Nat.card (miyamotoIN2G h L η) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
    have := card_miyamotoIN2G h L η
    omega
  refine ⟨g, ?_, ?_, fun j hj => ?_⟩
  · intro e
    apply hd1
    have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) = 1 := by
      rw [← map_one α₂] at e
      exact α₂.injective e
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  · have hdpow : (d : G) ^ (2 ^ f - 1) = 1 := by
      have e : d ^ Nat.card (miyamotoIN2G h L η) = 1 := pow_card_eq_one'
      rw [card_miyamotoIN2G] at e
      simpa using congrArg Subtype.val e
    rw [Nat.card_eq_fintype_card, hk₂, hg, ← map_pow]
    have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) ^ (2 ^ f - 1) = 1 :=
      Subtype.ext (by simpa using hdpow)
    rw [this, map_one]
  · have hc : j * ⟨d, hdM⟩ = ⟨d, hdM⟩ * j :=
      Subtype.ext (mem_centralizer_iff.1 hj d d.2).symm
    have := congrArg ψ₂ hc
    rw [map_mul, map_mul, hψd] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only [Prod.fst_mul, Prod.snd_mul] at h1 h2
    exact ⟨h1, h2⟩


theorem le_Wt_of_fpf [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {S : Subgroup G} (hSR : S ≤ miyamotoRG h L η t Q) {j : G}
    (hjS : j ∈ normalizer (S : Set G)) (hfp : S ⊓ centralizer ({j} : Set G) = ⊥)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) :
    S ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' := by
  refine fun a ha => hS.RG_inf_centralizer_K1'_le hk hψA hψt hZ (mem_inf.2 ⟨hSR ha, ?_⟩)
  obtain ⟨b, hb, rfl⟩ := exists_eq_inv_mul_conj_of_inf_centralizer_eq_bot hjS hfp ha
  have hbN : b⁻¹ ∈ normalizer (centralizer ((𝓚 : Subgroup G) : Set G) : Set G) :=
    mem_normalizer_centralizer (inv_mem (hS.RG_le_normalizer_K1' hk hψA hψt hZ (hSR hb)))
  have h1 : b⁻¹ * j * b⁻¹⁻¹ ∈ centralizer ((𝓚 : Subgroup G) : Set G) :=
    (mem_normalizer_iff.1 hbN j).1 hjC
  rw [inv_inv] at h1
  rw [show b⁻¹ * (j * b * j⁻¹) = b⁻¹ * j * b * j⁻¹ by group]
  exact mul_mem h1 (inv_mem hjC)

theorem V2_inf_Y1_inf_centralizer (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a)) {j : G} (hj : j ∈ miyamotoJ2G h L η t Q)
    (hx : (ψ₂ ⟨j, (mem_inf.1 hj).1⟩).1 ≠ 1) :
    (𝓥 ⊓ prodFactorOne ψ₂) ⊓ centralizer ({j} : Set G) = ⊥ := by
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := f) hk₂
  obtain ⟨g, hg1, hgpow, hcomm⟩ := hS.exists_torus_coord hk₂ hψα₂
  have hxg := (hcomm ⟨j, (mem_inf.1 hj).1⟩ (mem_inf.1 hj).2).1
  refine eq_bot_iff.2 fun s hs => ?_
  obtain ⟨⟨hsV, hsY⟩, hsj⟩ := And.intro (mem_inf.1 (mem_inf.1 hs).1) (mem_inf.1 hs).2
  obtain ⟨hsM, hs2⟩ := (Common.mem_prodFactorOne_iff ψ₂).1 hsY
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hS.isPGroup_V2) ⟨s, hsV⟩
  have hsj' : (⟨s, hsM⟩ : miyamotoM2G h L η t Q) * ⟨j, (mem_inf.1 hj).1⟩ =
      ⟨j, (mem_inf.1 hj).1⟩ * ⟨s, hsM⟩ := Subtype.ext (mem_centralizer_singleton_iff.1 hsj)
  have hu := congrArg (fun m => (ψ₂ m).1) hsj'
  simp only [map_mul, Prod.fst_mul] at hu
  have hord : orderOf (ψ₂ ⟨s, hsM⟩).1 ∣ 2 ^ n := by
    have h1 : orderOf (ψ₂ ⟨s, hsM⟩).1 ∣ orderOf (ψ₂ ⟨s, hsM⟩) := by
      rw [Prod.orderOf]
      exact Nat.dvd_lcm_left _ _
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
    rw [← hn, Subgroup.orderOf_mk]
    exact h1
  have hu1 := eq_one_of_commute_of_torus (by have := hS.two_le; omega) hk₂ hg1 hgpow hxg hx hu
    hord
  have hψs : ψ₂ ⟨s, hsM⟩ = 1 := Prod.ext hu1 hs2
  have : (⟨s, hsM⟩ : miyamotoM2G h L η t Q) = 1 := by
    rw [← map_one ψ₂] at hψs
    exact ψ₂.injective hψs
  rw [mem_bot]
  exact congrArg Subtype.val this

theorem V2_inf_Y2_inf_centralizer (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a)) {j : G} (hj : j ∈ miyamotoJ2G h L η t Q)
    (hx : (ψ₂ ⟨j, (mem_inf.1 hj).1⟩).2 ≠ 1) :
    (𝓥 ⊓ prodFactorTwo ψ₂) ⊓ centralizer ({j} : Set G) = ⊥ := by
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := f) hk₂
  obtain ⟨g, hg1, hgpow, hcomm⟩ := hS.exists_torus_coord hk₂ hψα₂
  have hxg := (hcomm ⟨j, (mem_inf.1 hj).1⟩ (mem_inf.1 hj).2).2
  refine eq_bot_iff.2 fun s hs => ?_
  obtain ⟨⟨hsV, hsY⟩, hsj⟩ := And.intro (mem_inf.1 (mem_inf.1 hs).1) (mem_inf.1 hs).2
  obtain ⟨hsM, hs1⟩ := (Common.mem_prodFactorTwo_iff ψ₂).1 hsY
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hS.isPGroup_V2) ⟨s, hsV⟩
  have hsj' : (⟨s, hsM⟩ : miyamotoM2G h L η t Q) * ⟨j, (mem_inf.1 hj).1⟩ =
      ⟨j, (mem_inf.1 hj).1⟩ * ⟨s, hsM⟩ := Subtype.ext (mem_centralizer_singleton_iff.1 hsj)
  have hu := congrArg (fun m => (ψ₂ m).2) hsj'
  simp only [map_mul, Prod.snd_mul] at hu
  have hord : orderOf (ψ₂ ⟨s, hsM⟩).2 ∣ 2 ^ n := by
    have h1 : orderOf (ψ₂ ⟨s, hsM⟩).2 ∣ orderOf (ψ₂ ⟨s, hsM⟩) := by
      rw [Prod.orderOf]
      exact Nat.dvd_lcm_right _ _
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
    rw [← hn, Subgroup.orderOf_mk]
    exact h1
  have hu1 := eq_one_of_commute_of_torus (by have := hS.two_le; omega) hk₂ hg1 hgpow hxg hx hu
    hord
  have hψs : ψ₂ ⟨s, hsM⟩ = 1 := Prod.ext hs1 hu1
  have : (⟨s, hsM⟩ : miyamotoM2G h L η t Q) = 1 := by
    rw [← map_one ψ₂] at hψs
    exact ψ₂.injective hψs
  rw [mem_bot]
  exact congrArg Subtype.val this

theorem map_conj_t_Y1 (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (prodFactorOne ψ₂) =
      prodFactorTwo ψ₂ :=
  map_conj_prodFactorOne_of_swap ψ₂ (hS.sec3_12_two.2.1 hS.t_mem_H2) hS.t_mul_t hψt₂

theorem mem_prodFactor_of_mem_J2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) :
    j ∈ prodFactorOne ψ₂ ∨ j ∈ prodFactorTwo ψ₂ := by
  obtain ⟨-, hJV, -⟩ := hS.J2_two hk₂ hψα₂
  obtain ⟨-, -, -, -, hVM, -, -, -⟩ := hS.sec3_12_two
  by_cases h2 : (ψ₂ ⟨j, (mem_inf.1 hj).1⟩).2 = 1
  · exact Or.inl ((Common.mem_prodFactorOne_iff ψ₂).2 ⟨_, h2⟩)
  by_cases h1 : (ψ₂ ⟨j, (mem_inf.1 hj).1⟩).1 = 1
  · exact Or.inr ((Common.mem_prodFactorTwo_iff ψ₂).2 ⟨_, h1⟩)
  exfalso
  have hV2R : (𝓥 : Subgroup G) ≤ miyamotoRG h L η t Q := inf_le_left
  have hjN1 : j ∈ normalizer ((𝓥 ⊓ prodFactorOne ψ₂ : Subgroup G) : Set G) :=
    mem_normalizer_inf (hJV hj) (Common.le_normalizer_prodFactorOne ψ₂ (mem_inf.1 hj).1)
  have hjN2 : j ∈ normalizer ((𝓥 ⊓ prodFactorTwo ψ₂ : Subgroup G) : Set G) :=
    mem_normalizer_inf (hJV hj) (Common.le_normalizer_prodFactorTwo ψ₂ (mem_inf.1 hj).1)
  have hS1 := hS.le_Wt_of_fpf hk hψA hψt hZ (inf_le_left.trans hV2R) hjN1
    (hS.V2_inf_Y1_inf_centralizer hk₂ hψα₂ hj h1) hjC
  have hS2 := hS.le_Wt_of_fpf hk hψA hψt hZ (inf_le_left.trans hV2R) hjN2
    (hS.V2_inf_Y2_inf_centralizer hk₂ hψα₂ hj h2) hjC
  have hV : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓥 : Subgroup G) = 𝓥 :=
    mem_normalizer_iff_map_conj_eq.1 hS.t_mem_normalizer_V2
  have hSt : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓥 ⊓ prodFactorOne ψ₂) =
      𝓥 ⊓ prodFactorTwo ψ₂ := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, hV, hS.map_conj_t_Y1 hψt₂]
  have hS2W : 𝓥 ⊓ prodFactorTwo ψ₂ ≤ 𝓦' := by
    rw [← hSt, ← map_conj_map_conj_of_mul_self hS.t_mul_t 𝓦']
    exact map_mono hS1
  have hbot : 𝓥 ⊓ prodFactorTwo ψ₂ = ⊥ := by
    rw [eq_bot_iff, ← (hS.sec5_2_one hk hψA hψt hZ).2.2.1]
    exact le_inf hS2W hS2
  have hk₂' : Nat.card k₂ = 2 ^ f := by rw [Nat.card_eq_fintype_card, hk₂]
  have hcard := card_le_card_inf_prodFactorTwo_mul ψ₂ hk₂' (by have := hS.two_le; omega) hVM
    hS.isPGroup_V2
  rw [hbot, card_bot, one_mul, hS.card_V2, hk₂'] at hcard
  have := hS.four_le
  nlinarith

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
