module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Conj

variable {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] (e : Y₁ ≃* Y₂) {b : MulAut Y₁} {β : MulAut Y₂}

theorem congr_eq_of_conj (hb : ∀ y, e (b y) = β (e y)) : MulAut.congr e b = β := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact hb x

theorem HHObsAt.of_conj {p r : ℕ} (hb : ∀ y, e (b y) = β (e y)) (h : HHObsAt p r Y₁ b) :
    HHObsAt p r Y₂ β := by
  obtain ⟨hr, hrp, E, hE, hab, hinv, x, hx, hbx⟩ := h
  refine ⟨hr, hrp, E.map e.toMonoidHom, hE.map _, ?_, ?_, e x, ⟨x, hx, rfl⟩, ?_⟩
  · rintro h2 _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hab h2 u hu v hv]
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨b u, hinv u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    exact hb u
  · intro h1
    apply hbx
    apply e.injective
    rw [hb]
    exact h1

end Conj

theorem bAut_eq_actYHom {Γ : Type} [Group Γ] {K : Subgroup Γ} [hK : K.Normal] (a : Γ) :
    bAut hK a = actYHom (K := K) a := by
  ext w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  rw [bAut_mk, actYHom_mk]
  congr 1

section Bar

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {M : Type} [Group M]

theorem isFourSubgroup_map_barIn {A : Subgroup G} (hA : IVK.IsFourSubgroup A) (hAH : A ≤ H)
    {f : HBar H →* M} (hf : Function.Injective f) : IVK.IsFourSubgroup ((barIn H A).map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA.1
  have := IsElementaryAbelian.subgroupOf (p := 2) hAH
  have : IsElementaryAbelian 2 ↥(barIn H A) :=
    IsElementaryAbelian.map (QuotientGroup.mk' (pPrimeCore 2 ↥H))
  refine ⟨IsElementaryAbelian.map f, ?_⟩
  rw [Subgroup.card_map_of_injective hf,
    L52Two.card_barIn (IsElementaryAbelian.isPGroup 2 ↥A) hAH, hA.2]

omit [Finite G] in
theorem commutator_map_barIn {A : Subgroup G} (hAH : A ≤ H) (hA : ⁅A, A⁆ = A) (f : HBar H →* M) :
    ⁅(barIn H A).map f, (barIn H A).map f⁆ = (barIn H A).map f := by
  have h1 : ⁅A.subgroupOf H, A.subgroupOf H⁆ = A.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAH, hA]
  rw [← Subgroup.map_commutator, barIn, ← Subgroup.map_commutator, h1]

theorem barIn_inf_eq_bot {A B : Subgroup G} (hA : IVK.IsFourSubgroup A)
    (hB : IVK.IsFourSubgroup B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    barIn H A ⊓ barIn H B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA.1
  have := hB.1
  rw [eq_bot_iff]
  rintro x ⟨⟨u, hu, rfl⟩, ⟨w, hw, hwu⟩⟩
  have huA : (u : G) ∈ A := hu
  have hwB : (w : G) ∈ B := hw
  have hc : u⁻¹ * w ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact hwu.symm
  have hcomm : (u : G) * w = w * u := hAB _ huA _ hwB
  have hu2 : (u : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (u : G) huA
  have hw2 : (w : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (w : G) hwB
  have hsq : (u⁻¹ * w) ^ 2 = 1 := by
    apply Subtype.ext
    have hcw : Commute ((u : G)⁻¹) (w : G) := Commute.inv_left hcomm
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hcw.mul_pow, inv_pow, hu2, hw2, inv_one, one_mul]
  have hodd : Odd (orderOf (u⁻¹ * w)) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.orderOf_dvd_natCard _ hc)
  have h1 : u⁻¹ * w = 1 := by
    have hdvd : orderOf (u⁻¹ * w) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have huw : u = w := by
    rw [inv_mul_eq_one] at h1
    exact h1
  have hu1 : (u : G) = 1 := by
    have : (u : G) ∈ A ⊓ B := ⟨huA, huw ▸ hwB⟩
    rw [hinf] at this
    exact this
  have : u = 1 := Subtype.ext hu1
  rw [this, map_one]
  exact Subgroup.one_mem _

end Bar

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
