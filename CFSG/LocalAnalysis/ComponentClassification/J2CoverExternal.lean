module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalSection
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData

public section

universe u

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
open External

theorem j2LiftOrders : J2LiftOrders.{u} := by
  intro L _ _ hLq t ht hZ π hπ hker
  obtain ⟨h1, h2, h3⟩ := j2_double_cover_involution_lift_orders hLq ht hZ π hπ hker
  refine ⟨fun q hq => ?_, fun v hv h => h2 v hv ?_, fun v hv h => h3 v hv ?_⟩
  · simpa only [Lift.fixedCount_eq_fixCount] using h1 q hq
  · rwa [Lift.fixedCount_eq_fixCount]
  · rwa [Lift.fixedCount_eq_fixCount]

theorem ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section
    {H : Type u} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) (hCL : centralizer (L : Set H) = zpowers (t : H)) :
    (∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 →
      ∃ l : L, (l : H) * x * (l : H)⁻¹ = y) ∧
    ∀ p : H, p ∉ L → orderOf p = 2 → ∀ α : MulAut P,
      (∀ l : L, α (π l) = π (MulAut.conjNormal p l)) →
      Nat.card (fixSub α) = 336 ∧
      ⁅⁅fixSub α, fixSub α⁆, ⁅fixSub α, fixSub α⁆⁆ = ⁅fixSub α, fixSub α⁆ ∧
      Nat.card (⁅fixSub α, fixSub α⁆ : Subgroup P) = 168 ∧
      centralizer ((⁅fixSub α, fixSub α⁆ : Subgroup P) : Set P) ⊓ fixSub α = ⊥ ∧
      zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
        (centralizer {p}).subgroupOf L ∧
      zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
      t ∈ center L ∧
      (∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
          (⁅fixSub α, fixSub α⁆ : Subgroup P), ∀ a, (e a : P) = π a) ∧
      ⁅⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
          ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆⁆ =
        ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ ∧
      Nat.card (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L) = 168 ∧
      center (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L) = ⊥ ∧
      Nat.card (Outer (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L)) ∣ 2 ∧
      ∃ c ∈ fixSub α, c ∉ ⁅fixSub α, fixSub α⁆ ∧ orderOf c = 2 ∧
        Models.fixCount (c : Equiv.Perm (Fin 315)) = 15 ∧
        ∀ v : L, π v = c → v ^ 2 = t ∧ p * (v : H) * p⁻¹ = v * t ∧
          (∀ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
            v * a * v⁻¹ ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆) ∧
          (¬ ∃ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
            ∀ x ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
              v * x * v⁻¹ = a * x * a⁻¹) ∧
          (v : H) * p * (v : H)⁻¹ = t * p :=
  ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section_of_liftOrders
    j2LiftOrders hLq ht hZ π hπ hker hCL

theorem ctss_j2_central_double_cover_external_involution_data_frontier :
    StandardRecognition.ExternalInvolutionData .J2 := by
  intro H _ _ L t hset
  obtain ⟨hLn, hLq, ht, hZ, ⟨e⟩, hCL, -⟩ := hset
  have htL : t ∈ L := by
    have h : t ∈ (center L).map L.subtype := by
      rw [hZ]
      exact mem_zpowers t
    obtain ⟨z, -, rfl⟩ := h
    exact z.2
  let t' : L := ⟨t, htL⟩
  have hZ' : center L = zpowers t' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hCL' : centralizer (L : Set H) = zpowers (t' : H) := hCL
  obtain ⟨eP⟩ : Nonempty (L ⧸ center L ≃* P) :=
    ⟨(e : L ⧸ center L ≃* NativeSporadic.J2).trans nativeEquivP⟩
  let π : L →* P := eP.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = zpowers t' := hkerZ.trans hZ'
  obtain ⟨hconjL, hfix⟩ :=
    ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section hLq ht' hZ' π hπ hker
      hCL'
  refine ⟨fun x y hxL hx hyL hy => ?_, fun p hpL hp => ?_⟩
  · obtain ⟨l, hl⟩ := hconjL x y hxL hx hyL hy
    exact ⟨(l : H)⁻¹, by rw [inv_inv]; exact hl⟩
  have hα := CentralCover.fullAction_apply π hπ hkerZ p
  obtain ⟨-, -, -, -, hsup, hinf, -, -, hperf, hcard, -, hout, -⟩ := hfix p hpL hp _ hα
  have ht2 : t' ^ 2 = 1 := by rw [← ht', pow_orderOf_eq_one]
  have htH : (t' : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ' ht2
  have hmapt : (zpowers t').map L.subtype = zpowers t := by
    rw [MonoidHom.map_zpowers]
    rfl
  let A : Subgroup H :=
    (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L).map L.subtype
  let fA : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃* A :=
    Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective
  refine ⟨A, map_subtype_le _, ?_, ?_, fun a _ => mem_center_iff.mp htH a, ?_, ?_, ?_⟩
  · rw [← hmapt, ← Subgroup.map_sup, hsup, Subgroup.subgroupOf_map_subtype, inf_comm]
  · rw [← hmapt, ← Subgroup.map_inf_eq _ _ L.subtype L.subtype_injective, hinf, Subgroup.map_bot]
  · have : Group.IsPerfect
        (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) :=
      Subgroup.isPerfect_iff.2 hperf
    exact Group.isPerfect_def.1 (Group.IsPerfect.ofSurjective (f := fA.toMonoidHom) fA.surjective)
  · rw [← Nat.card_congr fA.toEquiv, hcard]
    exact ⟨84, rfl⟩
  · rw [← Nat.card_congr (equivalence fA).toEquiv]
    exact fun h3 => absurd (dvd_trans h3 hout) (by norm_num)

end CFSG.ComponentClassification.J2Cover
