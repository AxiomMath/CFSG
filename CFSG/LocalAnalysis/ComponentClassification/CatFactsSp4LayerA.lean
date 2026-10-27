module

public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

section General

variable {G G' : Type*} [Group G] [Group G']

@[expose] def layerOf (X : Subgroup G) : Subgroup G :=
  sSup {M : Subgroup G | M ≤ X ∧ CFSG.IsPComponent 2 (M.subgroupOf X)}

theorem le_layerOf {X M : Subgroup G} (hMX : M ≤ X) (hM : CFSG.IsPComponent 2 (M.subgroupOf X)) :
    M ≤ layerOf X :=
  le_sSup ⟨hMX, hM⟩

theorem map_layerOf (φ : G ≃* G') (X : Subgroup G) :
    (layerOf X).map φ.toMonoidHom = layerOf (X.map φ.toMonoidHom) := by
  have hφ : ∀ M : Subgroup G, (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := fun M => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id M
    ext x
    simp
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M ⟨hMX, hM⟩ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨map_mono hMX, isPComponent_map_subgroupOf 2 φ hMX hM⟩
  · refine sSup_le fun N ⟨hNX, hN⟩ => ?_
    have hNX' : N.map φ.symm.toMonoidHom ≤ X := by
      have := map_mono (f := φ.symm.toMonoidHom) hNX
      rwa [hφ] at this
    have hN' := isPComponent_map_subgroupOf 2 φ.symm hNX hN
    rw [hφ] at hN'
    have hle : N.map φ.symm.toMonoidHom ≤ layerOf X := le_layerOf hNX' hN'
    have h2 := map_mono (f := φ.toMonoidHom) hle
    have h3 : (N.map φ.symm.toMonoidHom).map φ.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x
      simp
    rwa [h3] at h2

theorem layerOf_eq_of_unique {X L₀ : Subgroup G} (hL₀X : L₀ ≤ X)
    (hL₀ : CFSG.IsPComponent 2 (L₀.subgroupOf X))
    (huniq : ∀ M, M ≤ X → CFSG.IsPComponent 2 (M.subgroupOf X) → M = L₀) : layerOf X = L₀ := by
  apply le_antisymm
  · exact sSup_le fun M ⟨hMX, hM⟩ => (huniq M hMX hM).le
  · exact le_layerOf hL₀X hL₀

variable [Finite G]

theorem isPComponent_two_of_quasisimple' {X J : Subgroup G} (hJX : J ≤ X)
    (hJq : CFSG.IsQuasisimple J) (hJs : (J.subgroupOf X).IsSubnormal) (hJe : Even (Nat.card J)) :
    CFSG.IsPComponent 2 (J.subgroupOf X) := by
  have hK : CFSG.IsComponent (J.subgroupOf X) :=
    ⟨(isQuasisimple_congr (subgroupOfEquivOfLe hJX)).mpr hJq, hJs⟩
  refine isPComponent_of_isComponent_of_not_le 2 hK fun hle => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card (J.subgroupOf X) ∣ Nat.card (CFSG.pPrimeCore 2 X) := card_dvd_of_le hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hJX).toEquiv] at hdvd
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 X)) := CFSG.pPrimeCore_coprime_card
  exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd))) hJe

theorem eq_bot_of_simple {E R R₁ : Subgroup G} (hE : IsSimpleGroup E)
    (hEc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hEe : Even (Nat.card E)) (hRE : R ≤ E)
    (hRn : (R.subgroupOf E).Normal) (hR₁R : R₁ ≤ R) (hR₁n : (R₁.subgroupOf R).Normal)
    (hR₁o : Odd (Nat.card R₁)) (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁) : R = ⊥ := by
  rcases hRn.eq_bot_or_eq_top with hb | ht
  · rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRE hr⟩ : E) ∈ R.subgroupOf E := hr
    rw [hb] at this
    exact congrArg Subtype.val ((mem_bot).mp this)
  · exfalso
    have hRE' : E ≤ R := fun x hx => by
      have : (⟨x, hx⟩ : E) ∈ R.subgroupOf E := ht ▸ mem_top _
      exact this
    have hReq : R = E := le_antisymm hRE hRE'
    subst hReq
    rcases hR₁n.eq_bot_or_eq_top with hb | ht'
    ·
      have hR₁bot : R₁ = ⊥ := by
        rw [eq_bot_iff]
        intro r hr
        have : (⟨r, hR₁R hr⟩ : R) ∈ R₁.subgroupOf R := hr
        rw [hb] at this
        exact congrArg Subtype.val ((mem_bot).mp this)
      have hp : IsPGroup 2 R := by
        rintro ⟨r, hr⟩
        obtain ⟨k, hk⟩ := hR2 r hr
        rw [hR₁bot, mem_bot] at hk
        exact ⟨k, Subtype.ext hk⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnt : Nontrivial R := by
        obtain ⟨x, hx, y, hy, hxy⟩ := hEc
        refine ⟨⟨⟨x, hx⟩, 1, fun h => hxy ?_⟩⟩
        have : x = 1 := congrArg Subtype.val h
        rw [this, one_mul, mul_one]
      have hz := hp.center_nontrivial
      rcases (center R).normal_of_characteristic.eq_bot_or_eq_top with hzb | hzt
      · rw [hzb] at hz
        exact not_nontrivial _ hz
      · obtain ⟨x, hx, y, hy, hxy⟩ := hEc
        have hxc : (⟨x, hx⟩ : R) ∈ center R := hzt ▸ mem_top _
        exact hxy (congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y, hy⟩)).symm
    · have hR₁eq : R₁ = R := by
        apply le_antisymm hR₁R
        intro x hx
        have : (⟨x, hx⟩ : R) ∈ R₁.subgroupOf R := ht' ▸ mem_top _
        exact this
      rw [hR₁eq] at hR₁o
      exact (Nat.not_even_iff_odd.mpr hR₁o) hEe

end General

variable {K : Type} [Field K]

theorem map_fixOf_normal (θ : MulAut (StatedSp 2 K)) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g)) :
    (((fixOf θ).map (proj 2 K)).subgroupOf (fixOf α)).Normal := by
  refine ⟨fun x hx c => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨h, hh⟩ := proj_surjective (c : StatedProj (StatedSp 2 K))
  have hs : θ h * h⁻¹ ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα, hh]
    have : α c = c := c.2
    rw [this, mul_inv_cancel]
  have hsc := mem_center_iff.mp (mem_center_of_mem_spScalars hs)
  refine ⟨h * g * h⁻¹, ?_, ?_⟩
  · change θ (h * g * h⁻¹) = h * g * h⁻¹
    have hθh : θ h = θ h * h⁻¹ * h := by group
    have hg' : θ g = g := hg
    rw [map_mul, map_mul, map_inv, hg', hθh]
    calc θ h * h⁻¹ * h * g * (θ h * h⁻¹ * h)⁻¹ =
        (θ h * h⁻¹) * (h * g * h⁻¹) * (θ h * h⁻¹)⁻¹ := by group
      _ = h * g * h⁻¹ := by rw [← hsc, mul_inv_cancel_right]
  · change proj 2 K (h * g * h⁻¹) = ((c * x * c⁻¹ : fixOf α) : StatedProj (StatedSp 2 K))
    rw [map_mul, map_mul, map_inv, hh, hgx]
    rfl

theorem map_isSubnormal_fixOf (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    {M : Subgroup (StatedSp 2 K)} (hM : M ≤ fixOf θ) (hMn : (M.subgroupOf (fixOf θ)).Normal) :
    ((M.map (proj 2 K)).subgroupOf (fixOf α)).IsSubnormal := by
  have hNX := map_fixOf_le θ hθα
  have hMN : M.map (proj 2 K) ≤ (fixOf θ).map (proj 2 K) := map_mono hM
  have h1 : ((M.map (proj 2 K)).subgroupOf ((fixOf θ).map (proj 2 K))).Normal := by
    refine ⟨fun x hx c => ?_⟩
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hdc⟩ := c.2
    refine ⟨d * m * d⁻¹, ?_, ?_⟩
    · have := hMn.conj_mem ⟨m, hM hm⟩ hm ⟨d, hd⟩
      exact this
    · change proj 2 K (d * m * d⁻¹) = ((c * x * c⁻¹ : (fixOf θ).map (proj 2 K)) :
        StatedProj (StatedSp 2 K))
      rw [map_mul, map_mul, map_inv, hdc, hmx]
      rfl
  exact (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hMN hNX
    (map_fixOf_normal θ hθα).isSubnormal).mpr h1.isSubnormal

end CFSG.ComponentClassification.CatFactsSp4
