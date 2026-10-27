module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParF5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}

theorem Om6Par.main (D : Om6Par Q t) {xg xy : simGroup Q} {c : (ZMod 3)ˣ}
    (hc : IsSimilitude Q (xg : V ≃ₗ[ZMod 3] V) c)
    (hL : ∀ u : OGroup Q, simAct Q xg u ∈ D.L ↔ u ∈ D.L)
    (hR : ∀ u : OGroup Q, simAct Q xg u ∈ D.R ↔ u ∈ D.R)
    (hy : ∀ u ∈ D.L ⊔ D.R, simAct Q xy u = u) (hy2 : xy * xy ∈ piSim Q) (hy1 : xy ∉ piSim Q)
    (hyt : xy * orthToSim Q t ∉ piSim Q) :
    Xor' (∃ u ∈ D.L, ¬ (simAct Q xg⁻¹ u * u⁻¹) ^ 4 = 1)
        (∃ u ∈ D.R, ¬ (simAct Q xg⁻¹ u * u⁻¹) ^ 4 = 1) ↔
      (xy⁻¹ * (xg⁻¹ * xy * xg) ∉ piSim Q ∧
        (xy * orthToSim Q t)⁻¹ * (xg⁻¹ * xy * xg) ∉ piSim Q) := by
  rw [D.lhs_iff hc hL hR, D.rhs_iff hc
    (D.simAct_t (fun u hu => (hL u).mpr hu) (fun u hu => (hR u).mpr hu)) hy hy2 hy1 hyt]
  have h3 : ∀ a : ZMod 3, a ≠ 0 → (a = -1 ↔ a ≠ 1) := by decide
  exact h3 _ c.ne_zero

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {hQ : Q.Nondegenerate}
  {φ : ↥L →* omegaGroup hQ}

theorem om6par_case (hφ : IsCoverMap L φ) (hinj : Function.Injective φ) {z : G} (hzL : z ∈ L)
    (D : Om6Par Q ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ L) (hK₂ : K₂ ≤ L) (h₁ : (K₁.subgroupOf L).map (om6par_embed φ) = D.L)
    (h₂ : (K₂.subgroupOf L).map (om6par_embed φ) = D.R) {g y : G} {xg xy : simGroup Q}
    (hxg : CoverAct L φ g xg) (hgK₁ : CFSG.conjugate K₁ g = K₁) (hgK₂ : CFSG.conjugate K₂ g = K₂)
    (hxy : CoverAct L φ y xy) (hyK : K₁ ⊔ K₂ ≤ centralizer ({y} : Set G))
    (hy2 : y * y ∈ centralizer (L : Set G)) (hy1 : y ∉ centralizer (L : Set G))
    (hyz : y * z ∉ centralizer (L : Set G)) :
    (Xor' (∃ k ∈ K₁, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn K₁)
        (∃ k ∈ K₂, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn K₂) ↔
      (y⁻¹ * (g⁻¹ * y * g) ∉ centralizer (L : Set G) ∧
        (y * z)⁻¹ * (g⁻¹ * y * g) ∉ centralizer (L : Set G))) := by
  have h3 : 3 ≤ Module.finrank (ZMod 3) V := by rw [hφ.finrank_eq]; norm_num
  have hxz := om6par_coverAct_of_mem (φ := φ) hzL
  have hcen := fun {s : G} {x : simGroup Q} (hx : CoverAct L φ s x) =>
    om6par_cent_iff hφ.surjective hinj h3 hx
  obtain ⟨c, hc⟩ := xg.2
  rw [om6par_outer_iff hinj hK₁ (om6par_iso_of_eq hinj hK₁ h₁ D.sec5Pair.iso₁) hxg hgK₁ h₁,
    om6par_outer_iff hinj hK₂ (om6par_iso_of_eq hinj hK₂ h₂ D.sec5Pair.iso₂) hxg hgK₂ h₂,
    om6par_cent_comm hφ.surjective hinj h3 hxy hxg hxy,
    om6par_cent_comm hφ.surjective hinj h3 (om6par_coverAct_mul hxy hxz) hxg hxy]
  exact D.main hc (om6par_normalized hxg hgK₁ h₁) (om6par_normalized hxg hgK₂ h₂)
    (om6par_fix_sup (om6par_fix hxy (le_sup_left.trans hyK) h₁)
      (om6par_fix hxy (le_sup_right.trans hyK) h₂))
    ((hcen (om6par_coverAct_mul hxy hxy)).mp hy2) (mt (hcen hxy).mpr hy1)
    (mt (hcen (om6par_coverAct_mul hxy hxz)).mpr hyz)

theorem asc82FactOm6Par_of (hS : Asc82SchurU43) : Asc82FactOm6Par := by
  intro G _ _ L z K₁ K₂ hL hodd hz2 hK₁ hK₂ hne _ hsup g y hg hgK₁ hgK₂ hy hyK hy2 hy1 hyz
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  letI := i1
  letI := i2
  letI := i3
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq]
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hodd
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hK₁.1)).1
  have hK₁L : K₁ ≤ L := hK₁.2.1.trans inf_le_left
  have hK₂L : K₂ ≤ L := hK₂.2.1.trans inf_le_left
  have hz' : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have htt : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hz', map_one]
    rfl
  let D := Om6Par.mk' hQ hφ.finrank_eq hφ.quadSign_eq htt
    (t5_phi_pocket_invType hφ hL ⟨hz2, K₁, hK₁⟩ hzL)
  obtain ⟨xg, hxg⟩ := t5_exists_coverAct hL hφ hg
  obtain ⟨xy, hxy⟩ := t5_exists_coverAct hL hφ hy
  have hne' : (K₁.subgroupOf L).map (om6par_embed φ) ≠ (K₂.subgroupOf L).map (om6par_embed φ) :=
    fun h => hne (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hK₁L, ← Subgroup.map_subgroupOf_eq_of_le hK₂L,
        Subgroup.map_injective (om6par_embed_injective hinj) h])
  rcases D.pocket_cases (om6par_pocket_map hφ.surjective hinj hzL hK₁)
      (om6par_twoRes_map hinj hzL (le_sup_left.trans hsup.le)) with h₁ | h₁ <;>
    rcases D.pocket_cases (om6par_pocket_map hφ.surjective hinj hzL hK₂)
      (om6par_twoRes_map hinj hzL (le_sup_right.trans hsup.le)) with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne'
  · exact om6par_case hφ hinj hzL D hK₁L hK₂L h₁ h₂ hxg hgK₁ hgK₂ hxy hyK hy2 hy1 hyz
  · exact (Iff.of_eq (_root_.xor_comm _ _)).trans
      (om6par_case hφ hinj hzL D hK₂L hK₁L h₂ h₁ hxg hgK₂ hgK₁ hxy
        ((sup_comm K₂ K₁).le.trans hyK) hy2 hy1 hyz)
  · exact absurd (h₁.trans h₂.symm) hne'

end CFSG.OddStandard.SmallF3.Omega
