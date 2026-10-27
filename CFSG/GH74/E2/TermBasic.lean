module

public import CFSG.GH74.AS16.Standard
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.Local
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

section Dihedral

theorem dihedral_cases {G : Type*} [Group G] [Finite G] {t y : G} (ht : t * t = 1)
    (hy : y * y = 1) :
    (∃ g ∈ Subgroup.zpowers (t * y), g⁻¹ * t * g = y) ∨
    (∃ z ∈ Subgroup.zpowers (t * y), z * z = 1 ∧ z ≠ 1 ∧ z * t = t * z ∧ z * y = y * z) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  obtain ⟨s, hs⟩ : ∃ s, s = t * y := ⟨_, rfl⟩
  rw [← hs]
  have hsinv : s⁻¹ = y * t := by
    rw [hs, mul_inv_rev, ht', hy']
  have hconj : t * s * t = s⁻¹ := by
    rw [hsinv, hs]
    calc t * (t * y) * t = (t * t) * y * t := by simp only [mul_assoc]
      _ = y * t := by rw [ht, one_mul]
  have hpow : ∀ j : ℕ, t * s ^ j * t = (s⁻¹) ^ j := by
    intro j
    have := conj_pow (a := t) (b := s) (i := j)
    rw [ht', hconj] at this
    exact this.symm
  have hyt : y = t * s := by
    rw [hs, ← mul_assoc, ht, one_mul]
  have hm : 0 < orderOf s := orderOf_pos s
  rcases Nat.even_or_odd' (orderOf s) with ⟨k, hk | hk⟩
  · right
    have hk0 : 0 < k := by omega
    have hsk : s ^ (2 * k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one s
    have hz2 : s ^ k * s ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hsk
    have hzinv : (s ^ k)⁻¹ = s ^ k := inv_eq_of_mul_eq_one_right hz2
    have hzt : s ^ k * t = t * s ^ k := by
      have h1 := hpow k
      rw [inv_pow, hzinv] at h1
      calc s ^ k * t = t * s ^ k * t * t := by rw [h1]
        _ = t * s ^ k := by rw [mul_assoc, ht, mul_one]
    have hzs : s ^ k * s = s * s ^ k := (Commute.pow_left (Commute.refl s) k).eq
    refine ⟨s ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers s) k, hz2, ?_, hzt, ?_⟩
    · exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    · calc s ^ k * y = s ^ k * (t * s) := by rw [← hyt]
        _ = (s ^ k * t) * s := by rw [mul_assoc]
        _ = (t * s ^ k) * s := by rw [hzt]
        _ = t * (s ^ k * s) := by rw [mul_assoc]
        _ = t * (s * s ^ k) := by rw [hzs]
        _ = (t * s) * s ^ k := by rw [mul_assoc]
        _ = y * s ^ k := by rw [← hyt]
  · left
    have hsm : s ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one s
    refine ⟨s ^ (k + 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers s) (k + 1), ?_⟩
    obtain ⟨g, hg⟩ : ∃ g, g = s ^ (k + 1) := ⟨_, rfl⟩
    rw [← hg]
    have hgg : g * g = s := by
      rw [hg, ← pow_add]
      have : k + 1 + (k + 1) = (2 * k + 1) + 1 := by omega
      rw [this, pow_succ, hsm, one_mul]
    have h1 : t * g * t = g⁻¹ := by
      have := hpow (k + 1)
      rw [inv_pow, ← hg] at this
      exact this
    have h2 : t * g = g⁻¹ * t := by
      calc t * g = t * g * t * t := by rw [mul_assoc (t * g) t t, ht, mul_one]
        _ = g⁻¹ * t := by rw [h1]
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g⁻¹ * t) := by rw [h2]
      _ = (g⁻¹ * g⁻¹) * t := by rw [mul_assoc]
      _ = (g * g)⁻¹ * t := by rw [mul_inv_rev]
      _ = s⁻¹ * t := by rw [hgg]
      _ = y * t * t := by rw [hsinv]
      _ = y := by rw [mul_assoc, ht, mul_one]

end Dihedral

section Balance

theorem isSolvable_pPrimeCore_two {X : Type*} [Group X] [Finite X] :
    Group.IsSolvable (CFSG.pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card)

theorem isPComponent_two_of_component {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) : CFSG.IsPComponent 2 K :=
  (CFSG.LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components (H := X) 2
    Nat.prime_two isSolvable_pPrimeCore_two).1 K hK

theorem component_le_layer_of_balance {H : Type} [Group H] [Finite H]
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {x : H} (hx : x * x = 1) {M K : Subgroup H}
    (hM : ∀ m : H, m ∈ M ↔ m * x = x * m) (hKM : K ≤ M)
    (hK : CFSG.IsComponent (K.subgroupOf M)) : K ≤ CFSG.layer H := by
  have hA : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hMA : M = Subgroup.centralizer ((Subgroup.zpowers x : Subgroup H) : Set H) := by
    ext m
    rw [hM m, Subgroup.mem_centralizer_iff]
    constructor
    · intro hm g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hc : Commute m x := hm
      exact (hc.zpow_right k).eq.symm
    · intro h
      exact (h x (Subgroup.mem_zpowers x)).symm
  subst hMA
  have h1 : CFSG.IsPComponent 2 (K.subgroupOf _) := isPComponent_two_of_component hK
  have h2 := CFSG.ClassicalInvolution.l2PrimeBalance H _ hA
  have h3 := (Subgroup.map_mono (le_sSup h1)).trans h2
  rw [Subgroup.map_subgroupOf_eq_of_le hKM,
    CFSG.ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hcore] at h3
  exact h3

end Balance

section CompIn

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf_iff {K M H : Subgroup G} (hMH : M ≤ H) :
    CFSG.IsComponent ((K.subgroupOf H).subgroupOf (M.subgroupOf H)) ↔
      CFSG.IsComponent (K.subgroupOf M) := by
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMH
  have hmap : ((K.subgroupOf H).subgroupOf (M.subgroupOf H)).map e.toMonoidHom =
      K.subgroupOf M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [(CFSG.LocalCores.component_isomorphism e).1, hmap]

theorem isCompIn_mono {A B K : Subgroup G} (h : IsCompIn A K) (hKB : K ≤ B) (hBA : B ≤ A) :
    IsCompIn B K := by
  refine ⟨hKB, ?_⟩
  have h1 : CFSG.IsComponent ((K.subgroupOf A).subgroupOf (B.subgroupOf A)) :=
    CFSG.LocalCores.component_overgroup h.2 (Subgroup.subgroupOf_mono A hKB)
  exact (isComponent_subgroupOf_iff hBA).1 h1

end CompIn

section Unique

variable {G : Type} [Group G]

theorem conjugate_eq_of_unique {y : G} {Ky : Subgroup G} (hKy : IsCompCen y Ky)
    (huniq : ∀ K' : Subgroup G, IsCompCen y K' → K' = Ky) {g : G} (hg : g ∈ Cen y) :
    conjugate Ky g = Ky := by
  have hc : conjugate (Cen y) g = Cen y := by
    rw [AS16.conjugate_centralizer_singleton]
    have : g⁻¹ * y * g = y := by
      have h1 : y * g = g * y := (mem_Cen'.1 hg).symm
      calc g⁻¹ * y * g = g⁻¹ * (y * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * y) := by rw [h1]
        _ = y := by rw [inv_mul_cancel_left]
    rw [this]
  have h := AS16.isCompIn_conj hKy g
  rw [hc] at h
  exact huniq _ h

theorem layer_le_of_unique {y : G} {Ky : Subgroup G} (huniq : ∀ K' : Subgroup G, IsCompCen y K' →
    K' = Ky) : CFSG.layer ↥(Cen y) ≤ Ky.subgroupOf (Cen y) := by
  refine sSup_le fun L hL => ?_
  have hL' : IsCompCen y (L.map (Cen y).subtype) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · have h : (L.map (Cen y).subtype).subgroupOf (Cen y) = L :=
        Subgroup.comap_map_eq_self_of_injective (Cen y).subtype_injective L
      rw [h]
      exact hL
  have h := huniq _ hL'
  have h2 : (L.map (Cen y).subtype).subgroupOf (Cen y) = L :=
    Subgroup.comap_map_eq_self_of_injective (Cen y).subtype_injective L
  rw [← h2, h]

end Unique

end CFSG.GH74.E2
