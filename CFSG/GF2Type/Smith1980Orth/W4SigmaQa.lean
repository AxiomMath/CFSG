module

public import CFSG.GF2Type.Smith1980Orth.S2Coord
public import CFSG.GF2Type.Smith1980Orth.S2Lbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

variable (D : S2Pre S)

private theorem eq_one_or_eq_spTransvection {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt) (hnd : β.Nondegenerate) {a : V}
    (ha : a ≠ 0) {e : V ≃ₗ[ZMod 2] V} (he : e ∈ spPointRadical β a)
    (hfix : ∀ x, β x a = 0 → e x = x) : e = 1 ∨ e = spTransvection β hβ a := by
  obtain ⟨b, hb⟩ : ∃ b, β a b ≠ 0 := by
    by_contra! h
    exact ha (hnd.1 a h)
  have hb1 : β a b = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hb
  have hba : β b a = 1 := by rw [OrthoF2.isAlt_symm hβ, hb1]
  have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp he.1
  set w := e b - b with hw
  have h1 : ∀ x, β x a = 0 → β x w = 0 := by
    intro x hx
    have h := hiso x b
    rw [hfix x hx] at h
    rw [hw, map_sub, h, sub_self]
  have h2 : ∀ x, β x w = β x a * β b w := by
    intro x
    have hx0 : β (x - β x a • b) a = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hba,
        mul_one, sub_self]
    have h := h1 _ hx0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact sub_eq_zero.mp h
  have h3 : w = β b w • a := by
    have h4 : w - β b w • a = 0 := by
      refine hnd.2 _ fun x => ?_
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [h2 x, mul_comm]
      exact sub_self _
    exact sub_eq_zero.mp h4
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (β b w) with hc | hc
  · left
    refine spPointRadical_ext hb1 he (one_mem _) ?_
    rw [hc, zero_smul] at h3
    have h5 : e b = b := by rw [← sub_eq_zero]; exact h3
    rw [h5]
    rfl
  · right
    refine spPointRadical_ext hb1 he (spTransvection_mem_spPointRadical hβ a) ?_
    rw [hc, one_smul] at h3
    rw [spTransvection_apply, hba, one_smul, ← h3, hw]
    abel

private theorem coord_sub_coord (x y u v : Vt S D.g D.t) :
    D.coord (x, y) - D.coord (u, v) = D.coord (x - u, y - v) := by
  rw [← map_sub]
  rfl

private theorem coord_mem_cases {x y : Vt S D.g D.t}
    (h : D.coord (x, y) = 0 ∨ D.coord (x, y) = ((aV D.good.ht : Vt S D.g D.t) : S.Qt)) :
    (x = 0 ∨ x = aV D.good.ht) ∧ y = 0 := by
  rcases h with h | h
  · have h1 := D.coord.injective (h.trans (map_zero D.coord).symm)
    exact ⟨Or.inl (congrArg Prod.fst h1), congrArg Prod.snd h1⟩
  · have h1 := D.coord.injective (h.trans (D.coord_apply_zero_right _).symm)
    exact ⟨Or.inr (congrArg Prod.fst h1), congrArg Prod.snd h1⟩

private theorem apply_sub_cl_mem {e : G} (heQ : e ∈ S.QG) (heQa : e ∈ S.Qa D.g) {ℓ : S.O}
    (hℓ : ℓ ∈ S.Lbar D.g) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) - S.cl e = 0 ∨
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) - S.cl e =
        ((aV D.good.ht : Vt S D.g D.t) : S.Qt) := by
  obtain ⟨y, hyL, rfl⟩ := (mem_Lbar S).mp hℓ
  rw [S.ρ_cl y heQ]
  have hc : (y : G) * e * (y : G)⁻¹ * e⁻¹ = 1 ∨
      (y : G) * e * (y : G)⁻¹ * e⁻¹ = D.g * S.z * D.g⁻¹ :=
    (S.conjBy D.g).commutator_eq_one_or_z hyL.1 heQa
  rcases hc with h | h
  · left
    have h' : (y : G) * e * (y : G)⁻¹ = e := by
      calc (y : G) * e * (y : G)⁻¹ = ((y : G) * e * (y : G)⁻¹ * e⁻¹) * e := by group
        _ = e := by rw [h, one_mul]
    rw [h', sub_self]
  · right
    have h' : (y : G) * e * (y : G)⁻¹ = (D.g * S.z * D.g⁻¹) * e := by
      calc (y : G) * e * (y : G)⁻¹ = ((y : G) * e * (y : G)⁻¹ * e⁻¹) * e := by group
        _ = (D.g * S.z * D.g⁻¹) * e := by rw [h]
    rw [h', S.cl_mul D.good.H.conj_mem heQ, add_sub_cancel_right]
    rfl

private theorem core (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {e : G}
    (heQ : e ∈ S.QG) (heQa : e ∈ S.Qa D.g) {u v : Vt S D.g D.t} (he : S.cl e = D.coord (u, v)) :
    D.betaV u (aV D.good.ht) = 0 ∧ (v = 0 ∨ v = aV D.good.ht) := by
  constructor
  · obtain ⟨d, hd, hdn, hdL⟩ := hP.exists_typeA
    rw [← D.range_resLC] at hdL
    obtain ⟨⟨p, hp⟩, hpe⟩ := hdL
    have h := D.apply_sub_cl_mem heQ heQa hp.1
    rw [he, D.Cbar_apply_coord ⟨p, hp.2⟩ u v] at h
    have hres : D.resC ⟨p, hp.2⟩ = spRho D.betaV_isAlt hd 0 := hpe
    rw [hres, D.coord_sub_coord] at h
    obtain ⟨hx, -⟩ := D.coord_mem_cases h
    have e1 : spRho D.betaV_isAlt hd 0 u - u =
        D.betaV u (aV D.good.ht) • d + D.betaV u d • aV D.good.ht := by
      rw [spRho_apply, zero_mul, add_zero]
      abel
    rw [e1] at hx
    by_contra hβu
    have h1 : D.betaV u (aV D.good.ht) = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hβu
    apply hdn
    have hx' : (D.betaV u (aV D.good.ht) • d + D.betaV u d • aV D.good.ht) ∈
        (ZMod 2) ∙ aV D.good.ht := OrthoF2.mem_span_singleton_iff.mpr hx
    have h2 : d = (D.betaV u (aV D.good.ht) • d + D.betaV u d • aV D.good.ht) -
        D.betaV u d • aV D.good.ht := by
      rw [h1, one_smul]
      abel
    rw [h2]
    exact Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · have h := D.apply_sub_cl_mem heQ heQa D.good.ht
    rw [he, D.t_apply_coord u v, D.coord_sub_coord, add_sub_cancel_left, sub_self] at h
    exact (D.coord_mem_cases (by rwa [D.coord_apply_zero_right] at h ⊢)).1

private theorem finrank_clSub_QG_inf_Qa (hw : S.width = 4) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa D.g)) = 4 := by
  have hzQa : S.z ∈ S.Qa D.g := S.z_mem_Qa_of_mem_QG rfl D.good.H.conj_mem D.good.H.conj_ne
  have hz : S.z ∈ S.QG ⊓ S.Qa D.g := ⟨S.z_mem_QG, hzQa⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa D.g))
  rw [S.clPre_clSub inf_le_left hz, D.good.C.card_QG_inf_Qa, hw, S.card_submodule] at h1
  have h2 : 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa D.g)) = 2 ^ 4 := by
    omega
  exact Nat.pow_right_injective le_rfl h2

private theorem clSub_QG_inf_Qa_eq (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) :
    S.clSub (S.QG ⊓ S.Qa D.g) =
      ((LinearMap.ker (D.betaV (aV D.good.ht))).prod ((ZMod 2) ∙ aV D.good.ht)).map
        (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) := by
  set K0 : Submodule (ZMod 2) (Vt S D.g D.t) := LinearMap.ker (D.betaV (aV D.good.ht)) with hK0
  have hdimV : finrank (ZMod 2) (Vt S D.g D.t) = 4 := by rw [D.finrank_Vt, hw]
  have hker : finrank (ZMod 2) K0 = 3 := by
    have hβ0 : D.betaV (aV D.good.ht) ≠ 0 := fun h0 =>
      aV_ne_zero D.good.H D.good.ht
        (D.betaV_nondegenerate.1 _ fun y => by rw [h0, LinearMap.zero_apply])
    have hrange : LinearMap.range (D.betaV (aV D.good.ht)) = ⊤ := by
      obtain ⟨y, hy⟩ : ∃ y, D.betaV (aV D.good.ht) y ≠ 0 := by
        by_contra h
        push Not at h
        exact hβ0 (LinearMap.ext h)
      have hy1 := OrthoF2.zmod2_eq_one_of_ne_zero hy
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (D.betaV (aV D.good.ht))
    rw [hrange, finrank_top, finrank_self, ← hK0, hdimV] at h1
    omega
  have hK : finrank (ZMod 2) (K0.prod ((ZMod 2) ∙ aV D.good.ht)) = 4 := by
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, hker,
      finrank_span_singleton (aV_ne_zero D.good.H D.good.ht)]
  have hle : S.clSub (S.QG ⊓ S.Qa D.g) ≤
      (K0.prod ((ZMod 2) ∙ aV D.good.ht)).map
        (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) := by
    intro x hx
    obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hx
    obtain ⟨⟨u, v⟩, huv⟩ := D.coord.surjective (S.cl e)
    obtain ⟨h1, h2⟩ := D.core hP heQ he.2 huv.symm
    refine ⟨(u, v), Submodule.mem_prod.mpr ⟨?_, ?_⟩, huv⟩
    · exact LinearMap.mem_ker.mpr ((D.betaV_symm _ _).trans h1)
    · exact OrthoF2.mem_span_singleton_iff.mpr h2
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [D.finrank_clSub_QG_inf_Qa hw, LinearEquiv.finrank_map_eq, hK])

theorem mem_Qa_iff_coord (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {e : G} (heQ : e ∈ S.QG)
    {u v : Vt S D.g D.t} (he : S.cl e = D.coord (u, v)) :
    e ∈ S.Qa D.g ↔ D.betaV u (aV D.good.ht) = 0 ∧ (v = 0 ∨ v = aV D.good.ht) := by
  refine ⟨fun h => D.core hP heQ h he, fun ⟨h1, h2⟩ => ?_⟩
  have hmem : S.cl e ∈ S.clSub (S.QG ⊓ S.Qa D.g) := by
    rw [D.clSub_QG_inf_Qa_eq hw hP, he]
    refine ⟨(u, v), Submodule.mem_prod.mpr ⟨?_, ?_⟩, rfl⟩
    · exact LinearMap.mem_ker.mpr ((D.betaV_symm _ _).trans h1)
    · exact OrthoF2.mem_span_singleton_iff.mpr h2
  obtain ⟨e', he', he'Q, he'c⟩ := S.mem_clSub_iff.mp hmem
  rcases (S.cl_eq_cl_iff he'Q heQ).mp he'c with h | h
  · rw [h]
    exact he'.2
  · rw [h]
    exact (S.Qa D.g).mul_mem he'.2
      (S.z_mem_Qa_of_mem_QG rfl D.good.H.conj_mem D.good.H.conj_ne)

theorem eq_one_or_eq_t_of_forall_fix
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {ℓ : S.O}
    (hℓ : ℓ ∈ S.Lbar D.g)
    (hfix : ∀ u : Vt S D.g D.t, D.betaV u (aV D.good.ht) = 0 →
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt) = u) : ℓ = 1 ∨ ℓ = D.t := by
  obtain ⟨c, hc, hcℓ⟩ := D.exists_eq_mul_of_mem_Lbar hℓ
  have hcfix : ∀ u : Vt S D.g D.t, D.betaV u (aV D.good.ht) = 0 →
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt) = u := by
    intro u hu
    rcases hcℓ with rfl | rfl
    · exact hfix u hu
    · have h := hfix u hu
      rwa [coe_mul_apply, D.t_apply_of_mem (D.Cbar_apply_mem_Vt hc.2 u.2)] at h
  have hmem : D.resLC ⟨c, hc⟩ ∈ spPointRadical D.betaV (aV D.good.ht) :=
    LmodN_le_spPointRadical D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ
      (D.range_resLC ▸ ⟨⟨c, hc⟩, rfl⟩)
  have hc1 : c = 1 := by
    rcases eq_one_or_eq_spTransvection D.betaV_isAlt D.betaV_nondegenerate
        (aV_ne_zero D.good.H D.good.ht) hmem (fun x hx => Subtype.ext (by
          rw [D.coe_resLC_apply]
          exact hcfix x hx)) with h | h
    · have h1 : D.resLC ⟨c, hc⟩ = D.resLC 1 := by rw [h, map_one]
      exact congrArg Subtype.val (D.resLC_injective h1)
    · exfalso
      refine hP.tau_not_mem ?_
      rw [← h, ← D.range_resLC]
      exact ⟨_, rfl⟩
  rcases hcℓ with rfl | rfl
  · exact Or.inl hc1
  · exact Or.inr (by rw [hc1, mul_one])

end S2Pre

end CFSG.GF2Type.Smith1980Orth
