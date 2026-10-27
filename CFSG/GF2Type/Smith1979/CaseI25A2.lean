module

public import CFSG.GF2Type.Smith1979.CaseIClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj)

section Abstract

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

@[expose] def singPerp (Q : QuadraticForm (ZMod 2) W) (a : W) : Set W :=
  {x | polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a}

@[expose] def eichlerFive (Q : QuadraticForm (ZMod 2) W) (a : W) : Set (W ≃ₗ[ZMod 2] W) :=
  eichler Q a '' singPerp Q a

theorem conj_mem_singPerp {a : W} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hga : g a = a) {α : W}
    (hα : α ∈ singPerp Q a) : g α ∈ singPerp Q a := by
  obtain ⟨hp, hq, h0, ha⟩ := hα
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg a α
    rw [hga] at this
    exact this.trans hp
  · exact (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg α).trans hq
  · exact fun h => h0 ((LinearEquiv.map_eq_zero_iff g).mp h)
  · exact fun h => ha (g.injective (h.trans hga.symm))

theorem conj_mem_eichlerFive {a : W} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hga : g a = a) {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ eichlerFive Q a) : g * e * g⁻¹ ∈ eichlerFive Q a := by
  obtain ⟨α, hα, rfl⟩ := he
  refine ⟨g α, conj_mem_singPerp hg hga hα, ?_⟩
  rw [eichler_conj hg, hga]

theorem mem_pointRadical_of_commute (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0)
    (ha : Q a = 0) {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hga : g a = a) (hcomm : ∀ u ∈ pointRadical Q a, g * u * g⁻¹ = u) :
    g ∈ pointRadical Q a := by
  refine ⟨hg, hga, fun x hx => ?_, fun v => ?_⟩
  · have hgx : polar Q a (g x) = 0 := by
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg a x
      rw [hga] at this
      rw [this]
      exact hx
    have h1 := hcomm _ (eichler_mem_pointRadical ha hx)
    rw [eichler_conj hg, hga] at h1
    rcases (CaseIClosure.eichler_eq_iff hQ ha0 ha hgx hx).mp h1 with h2 | h2
    · rw [h2, sub_self]
      exact Submodule.zero_mem _
    · rw [h2, add_sub_cancel_left]
      exact Submodule.mem_span_singleton_self a
  · have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg a v
    rw [hga] at this
    rw [polar_sub_right, this, sub_self]

theorem eichler_ne_one_of_mem_singPerp (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0)
    (ha : Q a = 0) {α : W} (hα : α ∈ singPerp Q a) : eichler Q a α ≠ 1 := by
  intro h
  rcases mem_span_cl_iff.mp ((eichler_eq_one_iff hQ ha0 ha hα.1).mp h) with h0 | h0
  · exact hα.2.2.1 h0
  · exact hα.2.2.2 h0

theorem closure_eichlerFive (hcount : CountSixStmt) (hV : finrank (ZMod 2) W = 6)
    (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0) (ha : Q a = 0)
    (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) :
    closure (eichlerFive Q a) = pointRadical Q a := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  obtain ⟨c, hcΩ, hca, hc5, hc1, hfix⟩ := CaseIClosure.exists_order_five hV hQ ha0 ha h27
  have hcO := omegaGroup_le Q hQ hcΩ
  set P := closure (eichlerFive Q a) with hP
  have hPle : P ≤ pointRadical Q a := by
    rw [hP, closure_le]
    rintro _ ⟨α, hα, rfl⟩
    exact eichler_mem_pointRadical ha hα.1
  have hcP : ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact subset_closure (conj_mem_eichlerFive hcO hca hx)
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul x y _ _ hx hy =>
      have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [this]
      exact mul_mem hx hy
    | inv x _ hx =>
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  have h10 : (singPerp Q a).ncard = 10 := (hcount W Q hV hQ a ha0 ha).2 h27
  obtain ⟨α₀, hα₀⟩ : (singPerp Q a).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), h10]
    norm_num
  have hE0 : eichler Q a α₀ ∈ P := subset_closure ⟨α₀, hα₀, rfl⟩
  have hE1 : eichler Q a α₀ ≠ 1 := eichler_ne_one_of_mem_singPerp hQ ha0 ha hα₀
  have hcard16 : Nat.card (pointRadical Q a) = 16 := by
    rw [card_pointRadical hQ ha0 ha, hV]
    norm_num
  have hdvd : Nat.card P ∣ 16 := hcard16 ▸ Subgroup.card_dvd_of_le hPle
  have h5 : 5 ∣ ((P : Set (W ≃ₗ[ZMod 2] W)) \ {1}).ncard := by
    refine CaseIClosure.five_dvd_ncard (Set.toFinite _) (fun x _ => by rw [hc5]; simp) ?_ ?_
    · rintro x ⟨hx, hx1⟩
      refine ⟨hcP x hx, fun h => hx1 ?_⟩
      have h' : c * x * c⁻¹ = 1 := h
      rw [Set.mem_singleton_iff]
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = 1 := by rw [h']; group
    · rintro x ⟨hx, hx1⟩ hcx
      exact hx1 (hfix x (hPle hx) hcx)
  have hcard : ((P : Set (W ≃ₗ[ZMod 2] W)) \ {1}).ncard + 1 = Nat.card P := by
    rw [Set.ncard_diff_singleton_add_one P.one_mem (Set.toFinite _)]
    exact (Nat.card_coe_set_eq (P : Set (W ≃ₗ[ZMod 2] W))).symm
  have hne1 : Nat.card P ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq P h1
    rw [hbot, Subgroup.mem_bot] at hE0
    exact hE1 hE0
  have hP16 : Nat.card P = 16 := by
    have hle : Nat.card P ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card P = m at hdvd hcard hne1 hle ⊢
    generalize ((P : Set (W ≃ₗ[ZMod 2] W)) \ {1}).ncard = k at hcard h5
    interval_cases m <;> omega
  exact Subgroup.eq_of_le_of_card_ge hPle (by omega)

theorem ncard_eichlerFive (hcount : CountSixStmt) (hV : finrank (ZMod 2) W = 6)
    (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0) (ha : Q a = 0)
    (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) : (eichlerFive Q a).ncard = 5 := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  obtain ⟨c, hcΩ, hca, hc5, hc1, hfix⟩ := CaseIClosure.exists_order_five hV hQ ha0 ha h27
  have hcO := omegaGroup_le Q hQ hcΩ
  have h10 : (singPerp Q a).ncard = 10 := (hcount W Q hV hQ a ha0 ha).2 h27
  have hle : (eichlerFive Q a).ncard ≤ 5 := CaseIClosure.ncard_eichler_image_le ha0 ha h10
  obtain ⟨α₀, hα₀⟩ : (singPerp Q a).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), h10]
    norm_num
  have hpos : 0 < (eichlerFive Q a).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, α₀, hα₀, rfl⟩
  have h5 : 5 ∣ (eichlerFive Q a).ncard := by
    refine CaseIClosure.five_dvd_ncard (Set.toFinite _) (fun x _ => by rw [hc5]; simp)
      (fun x hx => conj_mem_eichlerFive hcO hca hx) (fun x hx hcx => ?_)
    obtain ⟨α, hα, rfl⟩ := hx
    exact eichler_ne_one_of_mem_singPerp hQ ha0 ha hα
      (hfix _ (eichler_mem_pointRadical ha hα.1) hcx)
  omega

@[expose] def omegaStab (Q : QuadraticForm (ZMod 2) W) (hQ : Q.polarBilin.Nondegenerate) (a : W) :
    Subgroup (W ≃ₗ[ZMod 2] W) :=
  (MulAction.stabilizer (omegaGroup Q hQ) a).map (omegaGroup Q hQ).subtype

theorem mem_omegaStab {hQ : Q.polarBilin.Nondegenerate} {a : W} {g : W ≃ₗ[ZMod 2] W} :
    g ∈ omegaStab Q hQ a ↔ g ∈ omegaGroup Q hQ ∧ g a = a := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, MulAction.mem_stabilizer_iff.mp hx⟩
  · rintro ⟨hg, hga⟩
    exact ⟨⟨g, hg⟩, MulAction.mem_stabilizer_iff.mpr hga, rfl⟩

theorem card_omegaStab (hV : finrank (ZMod 2) W = 6) (hQ : Q.polarBilin.Nondegenerate) {a : W}
    (ha0 : a ≠ 0) (ha : Q a = 0) (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) :
    Nat.card (omegaStab Q hQ a) = 960 := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  set Ω := omegaGroup Q hQ with hΩ
  have horb : MulAction.orbit Ω a = {v : W | v ≠ 0 ∧ Q v = 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply ha0
        exact (LinearEquiv.map_eq_zero_iff (x : W ≃ₗ[ZMod 2] W)).mp h
      · have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
          (omegaGroup_le Q hQ x.2) a
        exact this.trans ha
    · rintro ⟨hv0, hv⟩
      obtain ⟨x, hx, hxa⟩ := O62.exists_mem_omegaGroup_apply_eq hQ (by omega) ha0 hv0
        (by rw [ha, hv])
      exact ⟨⟨x, hx⟩, hxa⟩
  have key : Nat.card (MulAction.orbit Ω a) * Nat.card (MulAction.stabilizer Ω a) =
      Nat.card Ω := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Ω a)
  have horbcard : Nat.card (MulAction.orbit Ω a) = 27 := by
    rw [horb, Nat.card_coe_set_eq]
    exact h27
  rw [omegaStab, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  change Nat.card (MulAction.stabilizer Ω a) = 960
  rw [horbcard] at key
  rcases O62.card_omegaGroup hV hQ with h | h <;> rw [h] at key <;> omega

noncomputable instance instFintypeEichlerFive {a : W} : Fintype (eichlerFive Q a) :=
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  Fintype.ofFinite _

theorem pointRadical_le_omegaStab (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0)
    (ha : Q a = 0) : pointRadical Q a ≤ omegaStab Q hQ a := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ ha0 ha).mp hg
  exact mem_omegaStab.mpr ⟨O62.eichler_mem_omegaGroup hQ a u,
    CFSG.ClassicalGroups.Orthogonal.eichler_apply_self a u⟩

end Abstract

end Case25

end CFSG.GF2Type.Smith1979
