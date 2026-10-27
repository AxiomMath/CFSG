module

public import CFSG.CGT.M24S.NSOrbit5

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem dotProduct_v₀_v₀ : v₀ ⬝ᵥ v₀ = 1 := by decide

theorem exists_conj_eq_mul_t {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) :
    ∃ s ∈ T, s * x * s⁻¹ = x * t := by
  obtain ⟨s, hs, hsv⟩ := c.exists_vec_eq (Fin.cons 0 v₀)
  refine ⟨s, hs, conj_eq_of_dotProduct_eq_one c hx hs ?_⟩
  rw [hsv, tail_cons_zero, hxv, dotProduct_v₀_v₀]

theorem mem_K_of_commute {x g : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hg : g ∈ H)
    (hgx : g * x = x * g) : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨s, hs, hsx⟩ := exists_conj_eq_mul_t c hx hxv
  have ht : t = x⁻¹ * s * x * s⁻¹ := by
    rw [show x⁻¹ * s * x * s⁻¹ = x⁻¹ * (s * x * s⁻¹) by group, hsx, inv_mul_cancel_left]
  have hs' : g * s * g⁻¹ ∈ T := c.conj_mem hg hs
  have hgxi : g * x⁻¹ * g⁻¹ = x⁻¹ := by
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group, hgx, mul_inv_cancel_right]
  have hgt : g * t * g⁻¹ = x⁻¹ * (g * s * g⁻¹) * x * (g * s * g⁻¹)⁻¹ := by
    have hgx' : g * x * g⁻¹ = x := by rw [hgx, mul_inv_cancel_right]
    calc g * t * g⁻¹ = (g * x⁻¹ * g⁻¹) * (g * s * g⁻¹) * (g * x * g⁻¹) *
          (g * s * g⁻¹)⁻¹ := by rw [ht]; group
      _ = _ := by rw [hgxi, hgx']
  obtain ⟨hm, hv⟩ := vec_commutator c hx hs'
  refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rcases zmod_two_eq_zero_or_one (top (c.mat x) ⬝ᵥ tail (c.vec (g * s * g⁻¹))) with h | h
  · rw [h, zero_smul] at hv
    have h1 := c.eq_of_vec_eq hm T.one_mem (hv.trans c.vec_one.symm)
    rw [← hgt] at h1
    exfalso
    apply c.z_ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [h, one_smul] at hv
    have h1 := c.eq_of_vec_eq hm c.mem (hv.trans c.vec_z.symm)
    rw [← hgt] at h1
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]

theorem stab_of_commute {x g : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hg : g ∈ H)
    (hgx : g * x = x * g) : StabV₀ c g := by
  have hK := mem_K_of_commute c hx hxv hg hgx
  refine ⟨hK, ?_⟩
  have h1 := top_conj c hK hx
  rw [show g * x * g⁻¹ = x by rw [hgx, mul_inv_cancel_right], hxv] at h1
  calc vecMul v₀ (blk (c.mat g)) = vecMul (vecMul v₀ (blk (c.mat g⁻¹))) (blk (c.mat g)) := by
        rw [← h1]
    _ = v₀ := by rw [vecMul_vecMul, blk_inv_mul c hK, vecMul_one]

theorem mem_E_of_commute [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {x g : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1) (hg : g ∈ H)
    (hgx : g * x = x * g) (hmb : mb (blk (c.mat g)) = 1) : g ∈ c.E := by
  have hs := stab_of_commute c hx hxv hg hgx
  obtain ⟨cc, hcc, hB⟩ := isO₂_of_mb_eq_one _ hs.2 hmb
  have hover : Over c v₀ x := ⟨hx, hxv, hx2⟩
  have hd := moves_of_ne_zero c hN hns (by decide) g hs.1 cc hcc hB x hover
  have hT := mem_T_of_fix c hs.1 hx (by rw [hxv]; exact hs.2)
  rw [(disp_eq_zero_iff c hT).2 (Or.inl (by rw [hgx, mul_inv_cancel_right]))] at hd
  rw [← hd, lv_zero] at hB
  exact mem_E_of_blk_eq_one c hs.1 hB

theorem conj_eq_or_of_mem_E {x e : G} (hx : x ∈ c.E) (he : e ∈ c.E) :
    x⁻¹ * (e * x * e⁻¹) = 1 ∨ x⁻¹ * (e * x * e⁻¹) = t := by
  rcases conj_mem_E_eq c he hx with h | h <;> rw [h]
  · exact Or.inl (inv_mul_cancel x)
  · exact Or.inr (inv_mul_cancel_left x t)

theorem vec_zero_of_eq_or {d : G} (hd : d = 1 ∨ d = t) : d ∈ T ∧
    (c.vec d 0 = 0 ↔ d = 1) := by
  rcases hd with rfl | rfl
  · exact ⟨T.one_mem, by simp [c.vec_one]⟩
  · refine ⟨c.mem, ?_⟩
    rw [c.vec_z]
    simp only [e0, Pi.single_eq_same, one_ne_zero, false_iff]
    exact c.z_ne_one

noncomputable def chi (x : G) (hx : x ∈ c.E) : c.E →* Multiplicative (ZMod 2) where
  toFun e := Multiplicative.ofAdd (c.vec (x⁻¹ * ((e : G) * x * (e : G)⁻¹)) 0)
  map_one' := by
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, inv_mul_cancel, c.vec_one,
      Pi.zero_apply, ofAdd_zero]
  map_mul' e₁ e₂ := by
    have h1 := conj_eq_or_of_mem_E c hx e₁.2
    have h2 := conj_eq_or_of_mem_E c hx e₂.2
    have e : x⁻¹ * ((e₁ : G) * e₂ * x * ((e₁ : G) * e₂)⁻¹) = (x⁻¹ * (e₁ * x * (e₁ : G)⁻¹)) *
        (e₁ * (x⁻¹ * (e₂ * x * (e₂ : G)⁻¹)) * (e₁ : G)⁻¹) := by group
    have hc : (e₁ : G) * (x⁻¹ * (e₂ * x * (e₂ : G)⁻¹)) * (e₁ : G)⁻¹ =
        x⁻¹ * (e₂ * x * (e₂ : G)⁻¹) := by
      rcases h2 with h | h <;> rw [h]
      · group
      · rw [commute_t (c.E_le e₁.2), mul_inv_cancel_right]
    rw [Subgroup.coe_mul, e, hc, c.vec_mul (vec_zero_of_eq_or c h1).1 (vec_zero_of_eq_or c h2).1,
      Pi.add_apply, ofAdd_add]

theorem chi_eq_one_iff {x : G} (hx : x ∈ c.E) (e : c.E) :
    chi c x hx e = 1 ↔ (e : G) * x = x * e := by
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one, (vec_zero_of_eq_or c (conj_eq_or_of_mem_E c hx e.2)).2]
  constructor
  · intro h
    calc (e : G) * x = x * (x⁻¹ * ((e : G) * x * (e : G)⁻¹)) * e := by group
      _ = x * e := by rw [h, mul_one]
  · intro h
    rw [h, mul_inv_cancel_right, inv_mul_cancel]

theorem card_centralizer_E {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) :
    Nat.card (c.E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 64 := by
  obtain ⟨s, hs, hsx⟩ := exists_conj_eq_mul_t c hx hxv
  have hsurj : Function.Surjective (chi c x hx) := by
    intro a
    rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd a) with h | h
    · exact ⟨1, by rw [map_one, ← ofAdd_toAdd a, h, ofAdd_zero]⟩
    · refine ⟨⟨s, c.T_le_E hs⟩, ?_⟩
      change Multiplicative.ofAdd _ = a
      rw [hsx, inv_mul_cancel_left, c.vec_z, ← ofAdd_toAdd a, h]
      rfl
  have hker : (chi c x hx).ker =
      (c.E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf c.E := by
    ext e
    rw [MonoidHom.mem_ker, chi_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (chi c x hx).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, c.card_E,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1
  omega

end CFSG.CGT.M24S.NSB
