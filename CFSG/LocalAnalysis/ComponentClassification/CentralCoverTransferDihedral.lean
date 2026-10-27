module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferCocycle
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBComplementLifting
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_central {G : Type*} [Group G] {a₁ a₂ : G} (h₁ : a₁ ∈ center G)
    (h₂ : a₂ ∈ center G) (b₁ b₂ : G) : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅b₁, b₂⁆ := by
  have key : ∀ a ∈ center G, ∀ x : G, a * x * a⁻¹ = x := fun a ha x => by
    rw [← Subgroup.mem_center_iff.1 ha x, mul_inv_cancel_right]
  calc ⁅a₁ * b₁, a₂ * b₂⁆ = a₁ * (b₁ * (a₂ * b₂) * b₁⁻¹) * a₁⁻¹ * (a₂ * b₂)⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = b₁ * a₂ * (b₂ * b₁⁻¹ * b₂⁻¹ * a₂⁻¹) := by
        rw [key a₁ h₁]
        group
    _ = a₂ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by
        rw [Subgroup.mem_center_iff.1 h₂ b₁]
        group
    _ = ⁅b₁, b₂⁆ := by rw [key a₂ h₂, commutatorElement_def]

namespace IsCentralDoubleExt

variable {D E : Type*} [Group D] [Group E] {ρ : E →* D} {z : E} (hρ : IsCentralDoubleExt ρ z)
include hρ

theorem zpowers_normal : (zpowers z).Normal :=
  ⟨fun n hn g => by
    rw [(Subgroup.mem_center_iff.1 (zpowers_le.2 hρ.mem_center hn) g), mul_inv_cancel_right]
    exact hn⟩

theorem eq_one_or_eq_of_mem_zpowers {x : E} (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  have h1 : ρ x = ρ 1 := by
    rw [map_one, ← MonoidHom.mem_ker, hρ.ker_eq]
    exact hx
  rcases hρ.eq_or_eq_mul h1 with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h, mul_one])

theorem splits_of_complement [Group.IsPerfect D] {B : Subgroup E} (hinf : zpowers z ⊓ B = ⊥)
    (hsup : zpowers z ⊔ B = ⊤) :
    commutator E = B ∧ Group.IsPerfect (commutator E) ∧
      (∃ e : commutator E ≃* D, ∀ x, e x = ρ x) ∧
      ∃ φ : zpowers z × commutator E ≃* E, ∀ a b, φ (a, b) = a * b := by
  have hcen : ∀ a ∈ zpowers z, ∀ x : E, x * a = a * x := fun a ha x =>
    Subgroup.mem_center_iff.1 (zpowers_le.2 hρ.mem_center ha) x
  have hmapB : B.map ρ = ⊤ := by
    have h := Subgroup.map_sup (zpowers z) B ρ
    rw [hsup, Subgroup.map_top_of_surjective ρ hρ.surjective,
      (Subgroup.map_eq_bot_iff _).2 (by rw [hρ.ker_eq]), bot_sup_eq] at h
    exact h.symm
  have hdecomp : ∀ x : E, ∃ a ∈ zpowers z, ∃ b ∈ B, x = a * b := by
    intro x
    obtain ⟨b, hb, hbx⟩ := (Subgroup.mem_map.1 (hmapB ▸ Subgroup.mem_top (ρ x)))
    refine ⟨x * b⁻¹, ?_, b, hb, by rw [inv_mul_cancel_right]⟩
    rw [← hρ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hbx, mul_inv_cancel]
  have hinj : Function.Injective (ρ.comp B.subtype) := by
    intro b b' h
    have h' : ρ b = ρ b' := h
    have hmem : (b : E) * (b' : E)⁻¹ ∈ zpowers z ⊓ B :=
      Subgroup.mem_inf.2
        ⟨by rw [← hρ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, h', mul_inv_cancel],
          mul_mem b.2 (inv_mem b'.2)⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact Subtype.ext hmem
  have hsurj : Function.Surjective (ρ.comp B.subtype) := by
    intro d
    obtain ⟨b, hb, hbd⟩ := Subgroup.mem_map.1 (hmapB ▸ Subgroup.mem_top d)
    exact ⟨⟨b, hb⟩, hbd⟩
  let eB : B ≃* D := MulEquiv.ofBijective (ρ.comp B.subtype) ⟨hinj, hsurj⟩
  have hBperf : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom)
    eB.symm.surjective
  have hcomm : commutator E = B := by
    apply le_antisymm
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdecomp g₁
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdecomp g₂
      have hc₁ : a₁ ∈ center E := zpowers_le.2 hρ.mem_center ha₁
      have hc₂ : a₂ ∈ center E := zpowers_le.2 hρ.mem_center ha₂
      rw [commutatorElement_mul_central hc₁ hc₂, commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
    · calc B = ⁅B, B⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(⊤ : Subgroup E), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator E := (_root_.commutator_def E).symm
  subst hcomm
  refine ⟨rfl, hBperf, ⟨eB, fun x => rfl⟩, ?_⟩
  let φ₀ : zpowers z × commutator E →* E :=
    MonoidHom.noncommCoprod (zpowers z).subtype (commutator E).subtype fun a b =>
      (hcen a a.2 b).symm
  have hφinj : Function.Injective φ₀ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    change (a : E) * b = a' * b' at h
    have hmem : (a' : E)⁻¹ * a = b' * (b : E)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h1 : (a' : E)⁻¹ * a ∈ zpowers z ⊓ commutator E :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, hmem ▸ mul_mem b'.2 (inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
    have ha : a = a' := Subtype.ext h1.symm
    subst ha
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
  have hφsurj : Function.Surjective φ₀ := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact ⟨MulEquiv.ofBijective φ₀ ⟨hφinj, hφsurj⟩, fun a b => rfl⟩

end IsCentralDoubleExt

section Dihedral

variable {D E : Type*} [Group D] [Group E] {ρ : E →* D} {z : E}

theorem exists_zpow_of_mem_closure_pair {R S x : E} (hS : S * S = 1) (hRS : S * R * S⁻¹ = R⁻¹)
    (hx : x ∈ closure {R, S}) : ∃ i : ℤ, x = R ^ i ∨ x = R ^ i * S := by
  have hSinv : S⁻¹ = S := inv_eq_of_mul_eq_one_left hS
  have hSR : ∀ j : ℤ, S * R ^ j = R ^ (-j) * S := by
    intro j
    have h := (conj_zpow (a := S) (b := R) (i := j)).symm
    rw [hRS, inv_zpow', zpow_neg, ← inv_zpow] at h
    rw [zpow_neg, ← inv_zpow, ← h, inv_mul_cancel_right]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, Or.inl (zpow_one y).symm⟩
    · exact ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩
  | one => exact ⟨0, Or.inl (zpow_zero R).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨j, rfl | rfl⟩ := hy
    · exact ⟨i + j, Or.inl (zpow_add R i j).symm⟩
    · exact ⟨i + j, Or.inr (by rw [← mul_assoc, ← zpow_add])⟩
    · exact ⟨i - j, Or.inr (by rw [mul_assoc, hSR, ← mul_assoc, ← zpow_add, sub_eq_add_neg])⟩
    · refine ⟨i - j, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc S, hSR, mul_assoc, hS, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv x _ hx =>
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact ⟨-i, Or.inl (zpow_neg R i).symm⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [mul_inv_rev, hSinv, ← zpow_neg, hSR, neg_neg]

theorem splits_of_dihedral_of_odd_index [Finite E] [Group.IsPerfect D] (hρ : IsCentralDoubleExt ρ z)
    (hlift : ∀ x : E, orderOf (ρ x) = 2 → orderOf x = 2) {W : Subgroup D}
    (hWodd : ¬ 2 ∣ W.index) {n : ℕ} {r s : D} (hW : W = closure {r, s})
    (hr : orderOf r = 2 ^ n) (hs : orderOf s = 2) (hsr : s ∉ zpowers r)
    (hrs : s * r * s⁻¹ = r⁻¹) :
    zpowers z ⊓ commutator E = ⊥ ∧ zpowers z ⊔ commutator E = ⊤ ∧
      Group.IsPerfect (commutator E) ∧ (∃ e : commutator E ≃* D, ∀ x, e x = ρ x) ∧
      ∃ φ : zpowers z × commutator E ≃* E, ∀ a b, φ (a, b) = a * b := by
  obtain ⟨R, hRr, hR⟩ : ∃ R : E, ρ R = r ∧ R ^ 2 ^ n = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, ?_, by simp⟩
      rw [map_one, eq_comm, ← orderOf_eq_one_iff, hr, pow_zero]
    · obtain ⟨R, hRr⟩ := hρ.surjective r
      refine ⟨R, hRr, ?_⟩
      have hn' : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hn]
      have hinv : orderOf (ρ (R ^ 2 ^ (n - 1))) = 2 := by
        rw [map_pow, hRr]
        apply orderOf_eq_prime
        · rw [← pow_mul, ← hn', ← hr, pow_orderOf_eq_one]
        · intro h1
          have h2 := orderOf_dvd_of_pow_eq_one h1
          rw [hr, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h2
          omega
      have h3 : (R ^ 2 ^ (n - 1)) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (R ^ 2 ^ (n - 1))
        rwa [hlift _ hinv] at this
      rwa [← pow_mul, ← hn'] at h3
  obtain ⟨S, hSs⟩ := hρ.surjective s
  have hS2 : S * S = 1 := by
    rw [← sq, ← hlift S (by rw [hSs, hs])]
    exact pow_orderOf_eq_one S
  have hrs2 : orderOf (r * s) = 2 := by
    apply orderOf_eq_prime
    · have hs2 : s * s = 1 := by rw [← sq, ← hs]; exact pow_orderOf_eq_one s
      calc (r * s) ^ 2 = r * s * (r * s) := sq _
        _ = r * (s * r * s⁻¹) * (s * s) := by group
        _ = 1 := by rw [hrs, hs2, mul_one, mul_inv_cancel]
    · intro h
      apply hsr
      rw [← mul_eq_one_iff_inv_eq.1 h]
      exact inv_mem (mem_zpowers r)
  have hRS2 : R * S * (R * S) = 1 := by
    rw [← sq, ← hlift (R * S) (by rw [map_mul, hRr, hSs, hrs2])]
    exact pow_orderOf_eq_one _
  have hSRS : S * R * S⁻¹ = R⁻¹ := by
    rw [inv_eq_of_mul_eq_one_left hS2]
    calc S * R * S = R⁻¹ * (R * S * (R * S)) := by group
      _ = R⁻¹ := by rw [hRS2, mul_one]
  have hzK : z ∉ closure ({R, S} : Set E) := by
    intro hz
    obtain ⟨i, h | h⟩ := exists_zpow_of_mem_closure_pair hS2 hSRS hz
    · have h1 : r ^ i = 1 := by rw [← hRr, ← map_zpow, ← h, hρ.map_z]
      obtain ⟨k, rfl⟩ : ((2 ^ n : ℕ) : ℤ) ∣ i := by
        rw [← hr]
        exact orderOf_dvd_iff_zpow_eq_one.2 h1
      apply hρ.ne_one
      rw [h, zpow_mul, zpow_natCast, hR, one_zpow]
    · apply hsr
      have h1 : r ^ i * s = 1 := by rw [← hRr, ← hSs, ← map_zpow, ← map_mul, ← h, hρ.map_z]
      rw [← mul_eq_one_iff_inv_eq.1 h1]
      exact inv_mem (zpow_mem (mem_zpowers r) i)
  have hinfK : zpowers z ⊓ closure ({R, S} : Set E) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rcases hρ.eq_one_or_eq_of_mem_zpowers hx1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hx2 hzK
  have hsupK : zpowers z ⊔ closure ({R, S} : Set E) = W.comap ρ := by
    apply le_antisymm
    · apply sup_le
      · rw [zpowers_le, Subgroup.mem_comap, hρ.map_z]
        exact W.one_mem
      · rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · change ρ x ∈ W
          rw [hRr, hW]
          exact subset_closure (Set.mem_insert _ _)
        · change ρ x ∈ W
          rw [hSs, hW]
          exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · intro x hx
      have hmap : (closure ({R, S} : Set E)).map ρ = W := by
        rw [MonoidHom.map_closure, Set.image_pair, hRr, hSs, hW]
      rw [Subgroup.mem_comap, ← hmap] at hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
      have hxk : x * k⁻¹ ∈ zpowers z := by
        rw [← hρ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hkx, mul_inv_cancel]
      have := Subgroup.mul_mem_sup hxk hk
      rwa [inv_mul_cancel_right] at this
  have := hρ.zpowers_normal
  have hcop : Nat.Coprime (W.comap ρ).index (Nat.card (zpowers z)) := by
    rw [Subgroup.index_comap_of_surjective W hρ.surjective, Nat.card_zpowers, hρ.orderOf_eq]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hWodd).symm
  obtain ⟨B, hBinf, hBsup, -⟩ := abelian_normal_coprime_index_complement_lifting hcop hinfK hsupK
  obtain ⟨hcomm, hperf, he, hφ⟩ := hρ.splits_of_complement hBinf hBsup
  exact ⟨by rw [hcomm]; exact hBinf, by rw [hcomm]; exact hBsup, hperf, he, hφ⟩

theorem central_double_extension_splits_over_dihedral_sylow [Finite D] [Group.IsPerfect D]
    (W : Sylow 2 D) {n : ℕ} {r s : D} (hW : (W : Subgroup D) = closure {r, s})
    (hr : orderOf r = 2 ^ n) (hs : orderOf s = 2) (hsr : s ∉ zpowers r)
    (hrs : s * r * s⁻¹ = r⁻¹) [Finite E] (hρ : IsCentralDoubleExt ρ z)
    (hlift : ∀ x : E, orderOf (ρ x) = 2 → orderOf x = 2) :
    zpowers z ⊓ commutator E = ⊥ ∧ zpowers z ⊔ commutator E = ⊤ ∧
      Group.IsPerfect (commutator E) ∧ (∃ e : commutator E ≃* D, ∀ x, e x = ρ x) ∧
      ∃ φ : zpowers z × commutator E ≃* E, ∀ a b, φ (a, b) = a * b :=
  splits_of_dihedral_of_odd_index hρ hlift W.not_dvd_index hW hr hs hsr hrs

end Dihedral

end CFSG.ComponentClassification.CentralCover
