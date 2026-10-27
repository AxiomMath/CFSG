module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilpDef
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Burnside

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.Stage2.Local

namespace L29TwoNilp

section Helpers

variable {D E : Type} [Group D] [Group E]

theorem card_comap_eq (f : D →* E) (N : Subgroup E) :
    Nat.card ↥(N.comap f) = Nat.card ↥(f.range ⊓ N) * Nat.card f.ker := by
  have h1 := Subgroup.relIndex_mul_card f.ker (N.comap f)
  rw [inf_of_le_left (f.ker_le_comap N), Subgroup.relIndex_ker, Subgroup.map_comap_eq] at h1
  exact h1.symm

theorem odd_card_comap (f : D →* E) (N : Subgroup E) (hk : Odd (Nat.card f.ker))
    (hN : Odd (Nat.card N)) : Odd (Nat.card ↥(N.comap f)) := by
  rw [card_comap_eq]
  exact Nat.odd_mul.mpr ⟨Odd.of_dvd_nat hN (Subgroup.card_dvd_of_le inf_le_right), hk⟩

theorem exists_index_comap_two (f : D →* E) (N : Subgroup E) [N.Normal]
    (hN : ∃ a : ℕ, N.index = 2 ^ a) : ∃ b : ℕ, (N.comap f).index = 2 ^ b := by
  obtain ⟨a, ha⟩ := hN
  have h2 : (N.comap f).index ∣ 2 ^ a := by
    rw [Subgroup.index_comap, ← ha]
    exact Subgroup.relIndex_dvd_index_of_normal N f.range
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact ⟨b, hb⟩

end Helpers

end L29TwoNilp

section Basic

theorem hasNormal2Compl_iff_twoNilp {G : Type} [Group G] (X : Subgroup G) :
    HasNormal2Compl X ↔ TwoNilp ↥X := by
  constructor
  · rintro ⟨N, hNX, hn, hodd, a, ha⟩
    refine ⟨N.subgroupOf X, hn, ?_, a, ha⟩
    rwa [← Subgroup.card_map_of_injective X.subtype_injective (K := N.subgroupOf X),
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hNX]
  · rintro ⟨N, hn, hodd, a, ha⟩
    have hsub : (N.map X.subtype).subgroupOf X = N :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective N
    refine ⟨N.map X.subtype, Subgroup.map_subtype_le N, ?_, ?_, a, ?_⟩
    · rw [hsub]
      exact hn
    · rwa [Subgroup.card_map_of_injective X.subtype_injective]
    · rwa [hsub]

theorem twoNilp_of_isPGroup {D : Type} [Group D] [Finite D] (h : IsPGroup 2 D) : TwoNilp D := by
  obtain ⟨a, ha⟩ := h.exists_card_eq
  exact ⟨⊥, inferInstance, by simp, a, by rw [Subgroup.index_bot, ha]⟩

end Basic

section Extensions

theorem twoNilp_of_odd_ker {D E : Type} [Group D] [Group E] [Finite D] [Finite E] (f : D →* E)
    (hk : Odd (Nat.card f.ker)) (h : TwoNilp E) : TwoNilp D := by
  obtain ⟨N, hN, hodd, hidx⟩ := h
  exact ⟨N.comap f, inferInstance, L29TwoNilp.odd_card_comap f N hk hodd,
    L29TwoNilp.exists_index_comap_two f N hidx⟩

theorem twoNilp_of_injective {D E : Type} [Group D] [Group E] [Finite E] (f : D →* E)
    (hf : Function.Injective f) (h : TwoNilp E) : TwoNilp D := by
  have : Finite D := Finite.of_injective f hf
  refine twoNilp_of_odd_ker f ?_ h
  rw [(MonoidHom.ker_eq_bot_iff f).mpr hf, Subgroup.card_bot]
  exact odd_one

theorem twoNilp_of_normal_two_index {D : Type} [Group D] [Finite D] (D₀ : Subgroup D) [D₀.Normal]
    (hD₀ : TwoNilp ↥D₀) (hq : ∃ a : ℕ, D₀.index = 2 ^ a) : TwoNilp D := by
  obtain ⟨N, hN, hodd, b, hb⟩ := hD₀
  obtain ⟨a, ha⟩ := hq
  have hqp : IsPGroup 2 (↥D₀ ⧸ N) := IsPGroup.of_card hb
  have hnorm := L29Burnside.normal_map_subtype_of_odd D₀ N hqp hodd
  refine ⟨N.map D₀.subtype, hnorm, ?_, b + a, ?_⟩
  · rwa [Subgroup.card_map_of_injective D₀.subtype_injective]
  · rw [Subgroup.index_map_subtype, hb, ha, pow_add]

theorem twoNilp_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : TwoNilp A) (hB : TwoNilp B) : TwoNilp (A × B) := by
  obtain ⟨N, hN, hNo, a, ha⟩ := hA
  obtain ⟨M, hM, hMo, b, hb⟩ := hB
  refine ⟨N.prod M, inferInstance, ?_, a + b, ?_⟩
  · have hc : Nat.card (N.prod M) = Nat.card N * Nat.card M := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (Subgroup.prodEquiv N M).toEquiv
    rw [hc]
    exact Nat.odd_mul.mpr ⟨hNo, hMo⟩
  · rw [Subgroup.index_prod, ha, hb, pow_add]

end Extensions

section Central

namespace L29TwoNilp

theorem twoNilp_of_central_odd_index {P : Type} [Group P] [Finite P] (K : Subgroup P)
    (hKc : K ≤ Subgroup.center P) (hK : IsPGroup 2 ↥K) (hi : Odd K.index) : TwoNilp P := by
  have hcen : ∀ k ∈ K, ∀ x : P, k * x * k⁻¹ = x := fun k hk x => by
    rw [← Subgroup.mem_center_iff.mp (hKc hk) x, mul_inv_cancel_right]
  have hKn : K.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hKc hn) g, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨j, hj⟩ := hK.exists_card_eq
  have hcop : Nat.Coprime (Nat.card K) K.index := by
    rw [hj]
    exact Nat.Coprime.pow_left j (Nat.coprime_comm.mp hi.coprime_two_right)
  obtain ⟨M, hM⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdecomp : ∀ g : P, ∃ k ∈ K, ∃ m ∈ M, g = k * m := fun g => by
    obtain ⟨⟨k, m⟩, hg⟩ := hM.2 g
    exact ⟨k, k.2, m, m.2, hg.symm⟩
  have hMn : M.Normal := ⟨fun m hm g => by
    obtain ⟨k, hk, m', hm', rfl⟩ := hdecomp g
    have e : k * m' * m * (k * m')⁻¹ = k * (m' * m * m'⁻¹) * k⁻¹ := by group
    rw [e, hcen k hk]
    exact M.mul_mem (M.mul_mem hm' hm) (M.inv_mem hm')⟩
  refine ⟨M, hMn, ?_, j, ?_⟩
  · rw [← hM.symm.index_eq_card]
    exact hi
  · rw [hM.index_eq_card, hj]

theorem twoNilp_comap_of_central_ker {D E : Type} [Group D] [Group E] [Finite D] [Finite E]
    (f : D →* E) (hk : IsPGroup 2 f.ker) (hkc : f.ker ≤ Subgroup.center D) (N : Subgroup E)
    (hodd : Odd (Nat.card N)) : TwoNilp ↥(N.comap f) := by
  have hker : f.ker ≤ N.comap f := f.ker_le_comap N
  have hKc : f.ker.subgroupOf (N.comap f) ≤ Subgroup.center ↥(N.comap f) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hkc (Subgroup.mem_subgroupOf.mp hx)) y.1)
  have hK2 : IsPGroup 2 ↥(f.ker.subgroupOf (N.comap f)) :=
    hk.of_injective (Subgroup.subgroupOfEquivOfLe hker).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hker).injective
  have hKi : Odd (f.ker.subgroupOf (N.comap f)).index := by
    have h1 : (f.ker.subgroupOf (N.comap f)).index = Nat.card ((N.comap f).map f) :=
      Subgroup.relIndex_ker (N.comap f) f
    rw [h1, Subgroup.map_comap_eq]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
  exact twoNilp_of_central_odd_index _ hKc hK2 hKi

end L29TwoNilp

theorem twoNilp_of_central_two_ker {D E : Type} [Group D] [Group E] [Finite D] [Finite E]
    (f : D →* E) (hk : IsPGroup 2 f.ker) (hkc : f.ker ≤ Subgroup.center D) (h : TwoNilp E) :
    TwoNilp D := by
  obtain ⟨N, hN, hodd, hidx⟩ := h
  exact twoNilp_of_normal_two_index (N.comap f)
    (L29TwoNilp.twoNilp_comap_of_central_ker f hk hkc N hodd)
    (L29TwoNilp.exists_index_comap_two f N hidx)

end Central

section Actions

theorem twoNilp_of_two_actions {D B₁ B₂ : Type} [Group D] [Group B₁] [Group B₂] [Finite D]
    [Finite B₁] [Finite B₂] (θ₁ : D →* B₁) (θ₂ : D →* B₂) (A₁ : Subgroup B₁) (A₂ : Subgroup B₂)
    (hA₁ : ∀ d, θ₁ d ∈ A₁) (hA₂ : ∀ d, θ₂ d ∈ A₂) (h₁ : TwoNilp ↥A₁) (h₂ : TwoNilp ↥A₂)
    (hk : IsPGroup 2 ↥(θ₁.ker ⊓ θ₂.ker)) (hkc : θ₁.ker ⊓ θ₂.ker ≤ Subgroup.center D) :
    TwoNilp D := by
  let φ : D →* ↥A₁ × ↥A₂ := (θ₁.codRestrict A₁ hA₁).prod (θ₂.codRestrict A₂ hA₂)
  have hker : φ.ker = θ₁.ker ⊓ θ₂.ker := by
    ext d
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_inf, Prod.ext_iff, Subtype.ext_iff]
  rw [← hker] at hk hkc
  exact twoNilp_of_central_two_ker φ hk hkc (twoNilp_prod h₁ h₂)

end Actions

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
