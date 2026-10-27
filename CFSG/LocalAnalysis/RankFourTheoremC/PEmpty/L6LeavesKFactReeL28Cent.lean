module

public import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28

open Subgroup
open scoped Pointwise

theorem mem_or_mul_mem_of_mem_sup {Γ : Type*} [Group Γ] {t : Γ} (ht : orderOf t = 2)
    {F : Subgroup Γ} (hcomm : ∀ f ∈ F, f * t = t * f) {y : Γ} (hy : y ∈ zpowers t ⊔ F) :
    y ∈ F ∨ y * t ∈ F := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hLE : zpowers t ≤ normalizer (F : Set Γ) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (F : Set Γ)
      (Subgroup.mem_centralizer_iff.mpr hcomm))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) F hLE
  have hy' : y ∈ ((zpowers t : Set Γ) * (F : Set Γ)) := by
    rw [← hmul]
    exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rcases Int.even_or_odd' e with ⟨s, rfl | rfl⟩
  · left
    have : t ^ (2 * s) = 1 := by
      rw [zpow_mul]
      simp [ht2]
    rw [← hab, this, one_mul]
    exact hb
  · right
    have hte : t ^ (2 * s + 1) = t := by
      rw [zpow_add_one, zpow_mul]
      simp [ht2]
    have htt : t * t = 1 := by rw [← pow_two]; exact ht2
    rw [← hab, hte]
    have : t * b * t = b := by
      rw [← hcomm b hb, mul_assoc, htt, mul_one]
    rw [this]
    exact hb

theorem card_inf_eq_four {Γ : Type*} [Group Γ] {t : Γ} (ht : orderOf t = 2)
    {F P : Subgroup Γ} (hcomm : ∀ f ∈ F, f * t = t * f) (htF : t ∉ F) (htP : t ∈ P)
    (hPC : P ≤ zpowers t ⊔ F) (hP8 : Nat.card P = 8) [Finite Γ] :
    Nat.card (P ⊓ F : Subgroup Γ) = 4 := by
  have hindex : F.relIndex P = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htP⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases mem_or_mul_mem_of_mem_sup ht hcomm (hPC b.2) with h | h
    · exact Or.inr ⟨h, fun h' => htF (by simpa using F.mul_mem (F.inv_mem h) h')⟩
    · exact Or.inl ⟨h, fun h' => htF (by simpa using F.mul_mem (F.inv_mem h') h)⟩
  have h := Subgroup.relIndex_mul_card F P
  rw [hindex, inf_comm, hP8] at h
  omega

theorem isKleinFour_inf {Γ : Type*} [Group Γ] [Finite Γ] {t : Γ} (ht : orderOf t = 2)
    {F P : Subgroup Γ} (hcomm : ∀ f ∈ F, f * t = t * f) (htF : t ∉ F) (htP : t ∈ P)
    (hPC : P ≤ zpowers t ⊔ F) (hP8 : Nat.card P = 8) (hPexp : ∀ x ∈ P, x ^ 2 = 1) :
    IsKleinFour (P ⊓ F : Subgroup Γ) := by
  have hcard := card_inf_eq_four ht hcomm htF htP hPC hP8
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (P ⊓ F : Subgroup Γ) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hPexp x x.2.1)
  have h1 : Monoid.exponent (P ⊓ F : Subgroup Γ) ≠ 1 := by
    intro h
    have hall : ∀ x : (P ⊓ F : Subgroup Γ), x = 1 := fun x => by
      simpa [h] using Monoid.pow_exponent_eq_one x
    have : Nat.card (P ⊓ F : Subgroup Γ) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega
  exact ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left h1

theorem centralizer_le_of_isKleinFour {Γ : Type*} [Group Γ] [Finite Γ] {t : Γ} (ht : orderOf t = 2)
    {F P : Subgroup Γ} (hcomm : ∀ f ∈ F, f * t = t * f) (htF : t ∉ F)
    (hCt : Subgroup.centralizer ({t} : Set Γ) = zpowers t ⊔ F) (htP : t ∈ P)
    (hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP8 : Nat.card P = 8)
    (hPexp : ∀ x ∈ P, x ^ 2 = 1)
    (hkl : ∀ V : Subgroup Γ, V ≤ F → IsKleinFour V → F ⊓ Subgroup.centralizer (V : Set Γ) = V)
    {x : Γ} (hx : ∀ s ∈ P, x * s = s * x) : x ∈ P := by
  have hPC : P ≤ zpowers t ⊔ F := by
    rw [← hCt]
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hPcomm s hs t htP
  have hV := isKleinFour_inf ht hcomm htF htP hPC hP8 hPexp
  have htt : t * t = 1 := by rw [← pow_two]; exact hPexp t htP
  have hfP : ∀ f : Γ, f ∈ F → (∀ s ∈ P, f * s = s * f) → f ∈ P := by
    intro f hfF hfc
    have hmem : f ∈ F ⊓ Subgroup.centralizer ((P ⊓ F : Subgroup Γ) : Set Γ) :=
      ⟨hfF, Subgroup.mem_centralizer_iff.mpr fun v hv => (hfc v hv.1).symm⟩
    rw [hkl (P ⊓ F) inf_le_right hV] at hmem
    exact hmem.1
  have hxt : x ∈ zpowers t ⊔ F := by
    rw [← hCt, Subgroup.mem_centralizer_singleton_iff]
    exact hx t htP
  rcases mem_or_mul_mem_of_mem_sup ht hcomm hxt with h | h
  · exact hfP x h hx
  · have hc : ∀ s ∈ P, x * t * s = s * (x * t) := by
      intro s hs
      calc x * t * s = x * (t * s) := by rw [mul_assoc]
        _ = x * (s * t) := by rw [hPcomm t htP s hs]
        _ = (x * s) * t := by rw [mul_assoc]
        _ = (s * x) * t := by rw [hx s hs]
        _ = s * (x * t) := by rw [mul_assoc]
    have := hfP _ h hc
    have e : x = x * t * t := by rw [mul_assoc, htt, mul_one]
    rw [e]
    exact P.mul_mem this htP

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model


theorem reeL28_cent {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∀ (S : Sylow 2 ↥(ReeTag.G2.reeGamma K a)) (x : ↥(ReeTag.G2.reeGamma K a)),
      (∀ s ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)), x * s = s * x) →
        x ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a))) ∧
    ∀ S : Sylow 2 ↥(ReeTag.G2.reeGamma K a),
      Nat.card (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) = 8 := by
  classical
  haveI : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Finite ↥(ReeTag.G2.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hE, hcard, P, hP⟩ := smallRee_E8_sylow hK hw₀
  set J := smallReeJTHyp ha hK with hJ
  have hF := CFSG.Walter.JT.psl2Facts J.F J.iso (by show (3 : ℕ) ≠ 2; decide) J.five_lt
  have htP : J.t ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) := by
    rw [hP]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hPcomm : ∀ x ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)),
      ∀ y ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)), x * y = y * x := by
    intro x hx y hy
    rw [hP] at hx hy
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPexp : ∀ x ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)), x ^ 2 = 1 := by
    intro x hx
    rw [hP] at hx
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hP8 : Nat.card (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) = 8 := by
    rw [hP]
    exact hcard
  have hcommF : ∀ f ∈ J.F, f * J.t = J.t * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mp (J.le_centralizer hf)
  have hCP : ∀ x : ↥(ReeTag.G2.reeGamma K a),
      (∀ s ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)), x * s = s * x) →
        x ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) := fun x hx =>
    centralizer_le_of_isKleinFour J.orderOf_t hcommF J.t_not_mem J.centralizer_eq htP hPcomm hP8
      hPexp hF.kleinFour hx
  refine ⟨fun S x hx => ?_, fun S => ?_⟩
  · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(ReeTag.G2.reeGamma K a) P S
    have hSg : ∀ s, s ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) ↔
        g⁻¹ * s * g ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) := by
      intro s
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have h1 : g⁻¹ * x * g ∈ (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) := by
      apply hCP
      intro s hs
      have hgs : g * s * g⁻¹ ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) := by
        have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
        rw [hSg, e]
        exact hs
      have := hx _ hgs
      calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [this]
        _ = s * (g⁻¹ * x * g) := by group
    exact (hSg x).mpr h1
  · rw [S.card_eq_multiplicity, ← P.card_eq_multiplicity]
    exact hP8

end Ree

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28
