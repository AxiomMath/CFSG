module

public import CFSG.LargeExtraspecial.AS62Iso2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.CosetTable AS62.Sem

namespace AS62

variable {G : Type} [Group G] [Finite G]

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

@[expose] def M0 (y : G) : Subgroup G := closure (Set.range ![S.z, g.t, g.e, g.x, y])

omit [Finite G] in
theorem gens_mem_M0 (y : G) (i : Fin 5) : ![S.z, g.t, g.e, g.x, y] i ∈ g.M0 y :=
  subset_closure ⟨i, rfl⟩

theorem M0_le_M (hc : ConfHyp S H) {y : G} (hy : g.IsY y) : g.M0 y ≤ S.M :=
  (closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact g.gens1_mem hc hy i)

@[expose] def Φ10 {y : G} (hy : g.IsY y) : PG 5 rels1 →* ↥(g.M0 y) :=
  Sem.toSubgroup (g.rels1_hold hy) (g.M0 y) (g.gens_mem_M0 y)

omit [Finite G] in
theorem Φ10_of {y : G} (hy : g.IsY y) (i : Fin 5) :
    (g.Φ10 hy (PresentedGroup.of i) : G) = ![S.z, g.t, g.e, g.x, y] i :=
  congrArg Subtype.val (Sem.toSubgroup_of _ _ _ i)

omit [Finite G] in
theorem Φ10_surjective {y : G} (hy : g.IsY y) : Function.Surjective (g.Φ10 hy) := by
  intro m
  have hle : g.M0 y ≤ (g.Φ10 hy).range.map (g.M0 y).subtype :=
    (closure_le _).mpr (by
      rintro _ ⟨i, rfl⟩
      exact ⟨g.Φ10 hy (PresentedGroup.of i), ⟨_, rfl⟩, g.Φ10_of hy i⟩)
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hle m.2
  exact ⟨w, Subtype.ext hw⟩

theorem coe_ΦB_eq (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (w : PG 4 relsB) :
    (g.ΦB hc w : G) = (g.Φ10 hy (ι₁ w) : G) := by
  have h : (S.M ⊓ H).subtype.comp (g.ΦB hc) = (g.M0 y).subtype.comp ((g.Φ10 hy).comp ι₁) := by
    refine PresentedGroup.ext fun i => ?_
    change (g.ΦB hc (PresentedGroup.of i) : G) = (g.Φ10 hy (ι₁ (PresentedGroup.of i)) : G)
    rw [ι₁_of, g.ΦB_of, g.Φ10_of, Frame.gens2_castSucc]
  exact DFunLike.congr_fun h w

theorem inf_le_M0 (hc : ConfHyp S H) {y : G} (hy : g.IsY y) : S.M ⊓ H ≤ g.M0 y := by
  intro b hb
  obtain ⟨w, hw⟩ := g.ΦB_surjective hc ⟨b, hb⟩
  have h := g.coe_ΦB_eq hc hy w
  rw [hw] at h
  rw [show b = (g.Φ10 hy (ι₁ w) : G) from h]
  exact (g.Φ10 hy (ι₁ w)).2

theorem card_M0
    (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (hyH : y ∉ H) :
    Nat.card (g.M0 y) = 576 := by
  have hPG : Nat.card (PG 5 rels1) = 576 := by
    rw [Nat.card_congr (MulEquiv.ofBijective _ Ψ1_bijective).toEquiv, U42.card_P1]
  have h1 : Nat.card (g.M0 y) ∣ 576 := hPG ▸ Subgroup.card_dvd_of_surjective (g.Φ10_surjective hy)
  have h2 : 192 ∣ Nat.card (g.M0 y) := hc.card_M_inf ▸ card_dvd_of_le (g.inf_le_M0 hc hy)
  have h3 : Nat.card (g.M0 y) ≠ 192 := by
    intro h
    have heq : S.M ⊓ H = g.M0 y :=
      eq_of_le_of_card_ge (g.inf_le_M0 hc hy) (by rw [h, hc.card_M_inf])
    exact hyH (heq ▸ g.gens_mem_M0 y 4 : y ∈ S.M ⊓ H).2
  obtain ⟨k, hk⟩ := h2
  rw [hk] at h1 h3 ⊢
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; norm_num at h1)
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 192) (by simpa using h1)
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · exact absurd rfl h3
  · rfl

theorem Φ10_bijective
    (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (hyH : y ∉ H) :
    Function.Bijective (g.Φ10 hy) :=
  (g.Φ10_surjective hy).bijective_of_nat_card_le
    (rels1_card_le.trans (g.card_M0 hc hy hyH).ge)

theorem M0_inf_H (hc : ConfHyp S H) {y : G} (hy : g.IsY y) : g.M0 y ⊓ H = S.M ⊓ H :=
  le_antisymm (inf_le_inf_right H (g.M0_le_M hc hy)) (le_inf (g.inf_le_M0 hc hy) inf_le_right)

@[expose] noncomputable def ΦB0 (hc : ConfHyp S H) {y : G} (hy : g.IsY y) :
    PG 4 relsB →* ↥(g.M0 y ⊓ H) :=
  (MulEquiv.subgroupCongr (g.M0_inf_H hc hy)).symm.toMonoidHom.comp (g.ΦB hc)

theorem coe_ΦB0 (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (w : PG 4 relsB) :
    (g.ΦB0 hc hy w : G) = (g.ΦB hc w : G) := rfl

theorem ΦB0_bijective (hc : ConfHyp S H) {y : G}
    (hy : g.IsY y) : Function.Bijective (g.ΦB0 hc hy) :=
  (MulEquiv.subgroupCongr (g.M0_inf_H hc hy)).symm.bijective.comp (g.ΦB_bijective hc)

theorem inclusion_comp_ΦB0_left (hc : ConfHyp S H) {y : G} (hy : g.IsY y) :
    (Subgroup.inclusion (inf_le_left : g.M0 y ⊓ H ≤ g.M0 y)).comp (g.ΦB0 hc hy) =
      (g.Φ10 hy).comp ι₁ := by
  refine MonoidHom.ext fun w => Subtype.ext ?_
  change (g.ΦB0 hc hy w : G) = (g.Φ10 hy (ι₁ w) : G)
  rw [coe_ΦB0, g.coe_ΦB_eq hc hy w]

theorem inclusion_comp_ΦB0_right (hc : ConfHyp S H) {y : G} (hy : g.IsY y) :
    (Subgroup.inclusion (inf_le_right : g.M0 y ⊓ H ≤ H)).comp (g.ΦB0 hc hy) =
      (g.Φ2 hc).comp ι₂ := by
  refine MonoidHom.ext fun w => Subtype.ext ?_
  change (g.ΦB0 hc hy w : G) = (g.Φ2 hc (ι₂ w) : G)
  rw [coe_ΦB0]
  exact congrArg Subtype.val (DFunLike.congr_fun (g.inclusion_comp_ΦB_right hc) w)

@[expose] noncomputable def iso36
    (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (hyH : y ∉ H) :
    (RankTwoAmalgam.ofSubgroups (g.M0 y) H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2) where
  φ1 := (MulEquiv.ofBijective _ (g.Φ10_bijective hc hy hyH)).symm.trans
    (MulEquiv.ofBijective _ Ψ1_bijective)
  φ12 := (MulEquiv.ofBijective _ (g.ΦB0_bijective hc hy)).symm.trans
    (MulEquiv.ofBijective _ ΨB_bijective)
  φ2 := (MulEquiv.ofBijective _ (g.Φ2_bijective hc)).symm.trans
    (MulEquiv.ofBijective _ Ψ2_bijective)
  comm1 := comm_ofBijective (g.ΦB0_bijective hc hy) ΨB_bijective (g.Φ10_bijective hc hy hyH)
    Ψ1_bijective (g.inclusion_comp_ΦB0_left hc hy) ψ_comm1
  comm2 := comm_ofBijective (g.ΦB0_bijective hc hy) ΨB_bijective (g.Φ2_bijective hc)
    Ψ2_bijective (g.inclusion_comp_ΦB0_right hc hy) ψ_comm2

end Gens

theorem ConfHyp.exists_subAmalgam
    {S : Setting G} {H : Subgroup G} (hc : ConfHyp S H)
    (h36 : Nat.card S.Mbar = 36) :
    ∃ M₀ : Subgroup G, M₀ ≤ S.M ∧ S.M ⊓ H ≤ M₀ ∧ M₀.relIndex S.M = 2 ∧
      Nonempty ((RankTwoAmalgam.ofSubgroups M₀ H).Iso
        (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2)) := by
  obtain ⟨g⟩ := hc.exists_gens
  obtain ⟨y, hy, hyH⟩ := g.exists_isY_not_mem hc (Or.inr h36)
  refine ⟨g.M0 y, g.M0_le_M hc hy, g.inf_le_M0 hc hy, ?_, ⟨g.iso36 hc hy hyH⟩⟩
  have h1 := Setting.card_eq_relIndex_mul S.M (g.M0 y)
  rw [inf_eq_right.mpr (g.M0_le_M hc hy), g.card_M0 hc hy hyH, card_M_eq_card_QG_mul, hc.card_QG,
    h36] at h1
  omega

end AS62

end CFSG.LargeExtraspecial
