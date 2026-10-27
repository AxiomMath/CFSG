module

public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)


variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem ivk93res_inner_of_diag {α : MulAut (adjointGroup ReeTag.G2.tag F)}
    {g : adjointGroup ReeTag.G2.tag F} {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) = (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
      h * (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹) :
    α ∈ (MulAut.conj : adjointGroup ReeTag.G2.tag F →* MulAut (adjointGroup ReeTag.G2.tag F)).range := by
  obtain ⟨-, hrest⟩ := G2_F4_root_character_diagonals_inner ReeTag.G2.tag (Or.inl rfl) F
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner ReeTag.G2.tag (Or.inl rfl) F).1
  obtain ⟨-, -, hdC, -⟩ := hrest B hB a
  refine ⟨g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hαg h]
  show (((g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩ : adjointGroup ReeTag.G2.tag F) * h *
    (g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩ : adjointGroup ReeTag.G2.tag F)⁻¹ : adjointGroup ReeTag.G2.tag F) : ModGL ReeTag.G2.tag F) = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem ivk93res_g2_quadratic (hF2 : ringChar F ≠ 2) {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hKe : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e))
    (hδ1 : δ ≠ 1) {α : MulAut (adjointGroup ReeTag.G2.tag F)} {g : adjointGroup ReeTag.G2.tag F}
    {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) = (g : ModGL ReeTag.G2.tag F) *
      rootDiagUnit ReeTag.G2.tag a * Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
        (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), K ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧
      Nat.card ↥K = (p ^ e) ^ 6 * ((p ^ e) ^ 6 - 1) * ((p ^ e) ^ 2 - 1) := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 ReeTag.G2.tag
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup ReeTag.G2.tag F).subtype =
      entrywiseFixedGroup ReeTag.G2.tag δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL ReeTag.G2.tag F) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL ReeTag.G2.tag F) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup ReeTag.G2.tag F))) ≃*
      ↥(entrywiseFixedGroup ReeTag.G2.tag δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  let eF := e₁.trans e₂
  obtain ⟨-, -, -, hJΓ, -, -, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup ReeTag.G2.tag F δ
  set N : Subgroup ↥(entrywiseFixedGroup ReeTag.G2.tag δ) :=
    (fixedFieldImage ReeTag.G2.tag δ).subgroupOf (entrywiseFixedGroup ReeTag.G2.tag δ) with hN
  let eN : adjointGroup ReeTag.G2.tag (fixSubfield δ) ≃* ↥N :=
    (fixedFieldImageEquiv δ).trans (Subgroup.subgroupOfEquivOfLe hJΓ).symm
  let K : Subgroup (adjointGroup ReeTag.G2.tag F) :=
    (N.map eF.symm.toMonoidHom).map (α.toMonoidHom.eqLocus (MonoidHom.id _)).subtype
  let eK : adjointGroup ReeTag.G2.tag (fixSubfield δ) ≃* ↥K :=
    eN.trans ((N.equivMapOfInjective eF.symm.toMonoidHom eF.symm.injective).trans
      (Subgroup.equivMapOfInjective _ _ Subtype.val_injective))
  have hkodd : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF2 δ
  obtain ⟨hsimple, ⟨x, y, hxy⟩, -⟩ := odd_pinned_Chevalley_p_components ReeTag.G2.tag (fixSubfield δ) hkodd
  have : Fintype F := Fintype.ofFinite F
  have hδ2 : δ ^ 2 = 1 := by
    ext c
    show δ (δ c) = c
    rw [hδ, hδ, ← pow_mul, ← sq, ← hKe, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hK2 : Nat.card F = p ^ (2 * e) := by rw [hKe, ← pow_mul, mul_comm]
  have hkcard : Nat.card (fixSubfield δ) = p ^ e := by
    have h := (ringEquiv_sq_eq_one_facts hp (by omega : 1 ≤ 2 * e) hK2 hδ2 hδ1).2.2
    rw [Nat.mul_div_cancel_left e (by norm_num : 0 < 2)] at h
    exact h
  refine ⟨K, Subgroup.map_subtype_le _, (MulEquiv.isSimpleGroup_congr eK).1 hsimple, ?_, ?_⟩
  · exact ⟨eK x, eK y, fun h => hxy (eK.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← Nat.card_congr eK.toEquiv]
    have hc := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := fixSubfield δ)
    rw [hkcard] at hc
    exact hc

theorem ivk93res_g2_ree [CharP F ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b)
    (hK : Nat.card F = 3 ^ (2 * b + 1)) {g : adjointGroup ReeTag.G2.tag F}
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F b) ^ 2 = 1) :
    ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F),
      K ≤ (MulAut.conj g * ReeTag.G2.finiteReeAut F b).toMonoidHom.eqLocus (MonoidHom.id _) ∧
      IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧
      Nat.card ↥K = (3 ^ (2 * b + 1)) ^ 3 * (3 ^ (2 * b + 1) - 1) * ((3 ^ (2 * b + 1)) ^ 3 + 1) := by
  classical
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b F hK g hα
  obtain ⟨-, ⟨e, -⟩, -, -⟩ := fixed_centralizer_of_conj_eq hψ
  have hmap : ((ReeTag.G2.finiteReeAut F b).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup ReeTag.G2.tag F).subtype = ReeTag.G2.reeGamma F b := rfl
  let Ψ' : ↥((MulAut.conj g * ReeTag.G2.finiteReeAut F b).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup ReeTag.G2.tag F))) ≃* ↥(ReeTag.G2.reeGamma F b) :=
    e.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap))
  obtain ⟨hDs, ⟨x, y, hxy⟩, -, htop, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b F hK
  have ec : ↥(commutator (ReeTag.G2.reeGamma F b)) ≃* ↥(ReeTag.G2.reeGamma F b) :=
    (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
  have hΓs : IsSimpleGroup ↥(ReeTag.G2.reeGamma F b) := (MulEquiv.isSimpleGroup_congr ec).1 hDs
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max
    (fun w : WeylGroup ReeTag.G2.tag => (coxeterSystem ReeTag.G2.tag).length w)
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓcard, -⟩ :=
    CFSG.LieType.Ree.small_Ree_Borel_coset_Sylow_action b F hK w₀ hw₀
  refine ⟨_, le_rfl, (MulEquiv.isSimpleGroup_congr Ψ').2 hΓs, ?_, ?_⟩
  · exact ⟨Ψ'.symm (ec x), Ψ'.symm (ec y), fun h => hxy (ec.injective (by
      have := congrArg Ψ' h
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      rw [map_mul, map_mul]
      exact this))⟩
  · rw [Nat.card_congr Ψ'.toEquiv]
    exact hΓcard

theorem ivk93res_ineq_quad {x : ℕ} (hx : 3 ≤ x) :
    (x ^ 2 * ((x ^ 2) ^ 2 - 1)) ^ 2 < 2 * (x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1)) := by
  obtain ⟨y, hy⟩ : ∃ y, x ^ 2 = y + 1 :=
    ⟨x ^ 2 - 1, by have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hy8 : 8 ≤ y := by nlinarith
  have h6 : x ^ 6 = (y + 1) ^ 3 := by rw [show x ^ 6 = (x ^ 2) ^ 3 by ring, hy]
  have e1 : (x ^ 2) ^ 2 - 1 = y * (y + 2) := by
    have : (x ^ 2) ^ 2 = y * (y + 2) + 1 := by rw [hy]; ring
    omega
  have e2 : x ^ 6 - 1 = y * (y ^ 2 + 3 * y + 3) := by
    have : x ^ 6 = y * (y ^ 2 + 3 * y + 3) + 1 := by rw [h6]; ring
    omega
  have e3 : x ^ 2 - 1 = y := by omega
  rw [e1, e2, e3, hy, h6]
  have key : (y + 2) ^ 2 < 2 * (y + 1) * (y ^ 2 + 3 * y + 3) := by nlinarith
  calc ((y + 1) * (y * (y + 2))) ^ 2 = ((y + 1) ^ 2 * y ^ 2) * (y + 2) ^ 2 := by ring
    _ < ((y + 1) ^ 2 * y ^ 2) * (2 * (y + 1) * (y ^ 2 + 3 * y + 3)) :=
        Nat.mul_lt_mul_of_pos_left key (by positivity)
    _ = 2 * ((y + 1) ^ 3 * (y * (y ^ 2 + 3 * y + 3)) * y) := by ring

theorem ivk93res_ineq_ree {q : ℕ} (hq : 2 ≤ q) :
    (q * (q ^ 2 - 1)) ^ 2 < 2 * (q ^ 3 * (q - 1) * (q ^ 3 + 1)) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
  have hu : 1 ≤ u := by omega
  have e1 : (u + 1) ^ 2 - 1 = u * (u + 2) := by
    have : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    omega
  rw [e1, Nat.add_sub_cancel]
  have h1 : 0 < u := hu
  have key : u * (u + 2) ^ 2 < 2 * (u + 1) * ((u + 1) ^ 3 + 1) := by
    nlinarith [pow_pos h1 2, pow_pos h1 3, pow_pos h1 4, sq_nonneg u, mul_pos h1 h1]
  calc ((u + 1) * (u * (u + 2))) ^ 2 = ((u + 1) ^ 2 * u) * (u * (u + 2) ^ 2) := by ring
    _ < ((u + 1) ^ 2 * u) * (2 * (u + 1) * ((u + 1) ^ 3 + 1)) :=
        Nat.mul_lt_mul_of_pos_left key (by positivity)
    _ = 2 * ((u + 1) ^ 3 * u * ((u + 1) ^ 3 + 1)) := by ring

theorem ivk93res_g2_outer_involution (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {α : MulAut (adjointGroup ReeTag.G2.tag F)} (hα : α ^ 2 = 1)
    (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →* MulAut (adjointGroup ReeTag.G2.tag F)).range) :
    ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), K ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧
      (Nat.card F * (Nat.card F ^ 2 - 1)) ^ 2 < 2 * Nat.card ↥K := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hodd
  have hF2 : ringChar F ≠ 2 := hchar ▸ hp2
  have h1 : ∀ x : ModGL ReeTag.G2.tag F, Units.map (entrywiseHom (1 : F ≃+* F).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hquad : ∀ {p' e : ℕ}, p'.Prime → 1 ≤ e → Nat.card F = (p' ^ e) ^ 2 → ∀ δ : F ≃+* F,
      (∀ c, δ c = c ^ (p' ^ e)) → ∀ (g : adjointGroup ReeTag.G2.tag F) (a : Fin ReeTag.G2.tag.rank → Fˣ),
      (∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) = (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) * (rootDiagUnit ReeTag.G2.tag a)⁻¹ *
          (g : ModGL ReeTag.G2.tag F)⁻¹) →
      ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), K ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
        IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧
        (Nat.card F * (Nat.card F ^ 2 - 1)) ^ 2 < 2 * Nat.card ↥K := by
    intro p' e hp' he hKe δ hδ g a hαg
    have hδ1 : δ ≠ 1 := by
      intro hδ1
      apply hnot
      refine ivk93res_inner_of_diag (g := g) (a := a) fun h => ?_
      rw [hαg h, hδ1, h1]
    obtain ⟨K, hK, hs, hn, hcardK⟩ := ivk93res_g2_quadratic hF2 hp' he hKe δ hδ hδ1 hαg hα
    refine ⟨K, hK, hs, hn, ?_⟩
    have hx3 : 3 ≤ p' ^ e := by
      by_contra hlt
      have h2 : p' ^ e ≤ 2 := by omega
      have h4 : (p' ^ e) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rw [hcardK, hKe]
    exact ivk93res_ineq_quad hx3
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime := by
      have h := ringChar.charP F
      rw [hchar] at h
      exact h
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with
      ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad Nat.prime_three he hKe δ hδ g a hαg
    · have hb : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        subst hb0'
        simp at hfb
        subst hfb
        simp at hcard
        omega
      have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
      obtain ⟨K, hK, hs, hn, hcardK⟩ := ivk93res_g2_ree hb hK' hα
      refine ⟨K, hK, hs, hn, ?_⟩
      rw [hcardK, hK']
      exact ivk93res_ineq_ree (by have : 5 ≤ 3 ^ (2 * b + 1) := hK' ▸ h5; omega)
  · rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inr ⟨rfl, by rw [hchar]; exact hp3⟩))
        hodd hα with ⟨g, a, hαg⟩ | ⟨p', e, hp', he, hKe, δ, hδ, g, a, hαg⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad hp' he hKe δ hδ g a hαg

end CFSG.GH74.GLS.IVK.Proofs2
