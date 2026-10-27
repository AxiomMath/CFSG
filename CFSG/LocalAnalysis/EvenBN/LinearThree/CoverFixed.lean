module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CentralLift
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover

section Generic

open CFSG.ComponentClassification.RankTwoHypIIY

variable {W : Type*} [Group W]

theorem exists_simple_of_isSimpleGroup {X L : Subgroup W} {t : W} (htX : t ∉ X)
    (ht2 : t ^ 2 = 1) (hLX : L ≤ X) (hLt : L ≤ centralizer ({t} : Set W)) (hL : IsSimpleGroup L)
    {x : W} (hx : x ∈ L) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1)
    (hC : centralizer ({t} : Set W) ⊓ centralizer (L : Set W) ≤ zpowers t) :
    ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({t} : Set W) ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ¬ ∀ a b : L, a * b = b * a := fun hcomm => by
    have hxL : x ∈ centralizer (L : Set W) := mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (hcomm ⟨l, hl⟩ ⟨x, hx⟩)
    rcases eq_one_or_eq_of_mem_zpowers ht2 (hC ⟨hLt hx, hxL⟩) with h | h
    · exact hx1 h
    · exact htX (h ▸ hLX hx)
  refine ⟨L, hLX, hLt, hL, ?_, commutator_eq_self_of_isSimpleGroup hL hnc, x, hx,
    orderOf_eq_prime hx2 hx1⟩
  by_contra h
  exact hnc fun a b => by_contra fun hab => h ⟨a, b, hab⟩

theorem exists_simple_conj {X : Subgroup W} (hX : X.Normal) {t₀ : W} (w : W)
    (h : ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({t₀} : Set W) ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2) :
    ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({w * t₀ * w⁻¹} : Set W) ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  obtain ⟨L, hLX, hLt, hLs, ⟨a, b, hab⟩, hLp, c, hc, hc2⟩ := h
  set e := L.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  refine ⟨L.map (MulAut.conj w).toMonoidHom, ?_, ?_, e.isSimpleGroup_congr.1 hLs,
    ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩, ?_,
    MulAut.conj w c, ⟨c, hc, rfl⟩, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact hX.conj_mem l (hLX hl) w
  · rintro _ ⟨l, hl, rfl⟩
    have hl := hLt hl
    rw [mem_centralizer_singleton_iff] at hl ⊢
    change w * l * w⁻¹ * (w * t₀ * w⁻¹) = w * t₀ * w⁻¹ * (w * l * w⁻¹)
    calc w * l * w⁻¹ * (w * t₀ * w⁻¹) = w * (l * t₀) * w⁻¹ := by group
      _ = w * (t₀ * l) * w⁻¹ := by rw [hl]
      _ = w * t₀ * w⁻¹ * (w * l * w⁻¹) := by group
  · rw [← map_commutator, hLp]
  · rw [MulEquiv.orderOf_eq, hc2]

end Generic

section Canonical

variable {K : Type} [Field K] [Finite K]

open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoHypIIL3
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem exists_simple_fieldAut [CharP K 2] (σ : K ≃+* K)
    (hX : fieldAut 3 K σ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : fieldAut 3 K σ ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {fieldAut 3 K σ} ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  obtain ⟨-, ⟨e, -⟩, hinn, -, hcent, -, hC⟩ :=
    linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  have := isSimpleGroup_projectiveSL_three (fixedField K σ)
  refine exists_simple_of_isSimpleGroup hX h2 hinn hcent e.symm.isSimpleGroup ?_
    conjAut_swapGL_ne_one conjAut_swapGL_sq ?_
  · rw [range_subfieldConj]
    refine ⟨swapGL K, ⟨?_, ?_⟩, rfl⟩
    · exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_swapGL, det_swapMat]; rfl)
    · exact Units.ext (swapMat_map _)
  · rw [hC]
    exact inf_le_right

theorem exists_simple_dualAut {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hX : dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {dualAut 3 K} ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨hinj, hinn, hβ2, -, hcent, -, hrest⟩ :=
    even_linear_canonical_graph_symplectic_centralizers (n := 3) (by omega) hK le_rfl 1
      (Or.inl rfl)
  obtain ⟨hC, -⟩ := hrest (Or.inr ⟨rfl, by decide⟩)
  have hβ : conjAut 3 K 1 * dualAut 3 K = dualAut 3 K := by rw [map_one, one_mul]
  rw [hβ] at hβ2 hcent hC
  set O := FourGroupEvenCanonical.matrixIsometryGroup
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hO
  have hNO : ((conjAut 3 K).comp O.subtype).range = O.map (conjAut 3 K) := by
    rw [MonoidHom.range_comp, range_subtype]
  obtain ⟨eSL⟩ := nonempty_matrixIsometryGroup_one_mulEquiv_SL2 (K := K)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := isSimpleGroup_SL2 h4
  have hsimple : IsSimpleGroup (O.map (conjAut 3 K)) :=
    ((MulEquiv.subgroupCongr hNO).symm.trans
      ((MonoidHom.ofInjective hinj).symm.trans eSL)).isSimpleGroup
  refine exists_simple_of_isSimpleGroup hX hβ2 hinn hcent hsimple (mem_map_of_mem _ ?_)
    conjAut_swapGL_ne_one conjAut_swapGL_sq hC.le
  rw [hO, FourGroupEvenCanonical.mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one,
    coe_swapGL, swapMat_transpose, swapMat_mul_self]

omit [Finite K] in
theorem exists_simple_graphField {e : ℕ} (h : UnitaryFieldData 2 e K) (he : 2 ≤ e)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hX : fieldAut 3 K σ * dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : (fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {fieldAut 3 K σ * dualAut 3 K} ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, -, hC⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσ
  have hq : ((3 : ℕ), 2 ^ e) ≠ (3, 2) := by
    intro hq
    have h2e : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd hq
    have := Nat.pow_right_injective le_rfl h2e
    omega
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 e
    (by rw [h.card, ← pow_mul, mul_comm]) 3 le_rfl hq
  have hsimple := (ι.symm.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num))).isSimpleGroup
  refine exists_simple_of_isSimpleGroup hX h2 hinn hcent hsimple (mem_map_of_mem _ ?_)
    conjAut_swapGL_ne_one conjAut_swapGL_sq ?_
  · rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, coe_swapGL, det_swapMat,
      swapMat_map, swapMat_transpose, swapMat_mul_self]
    exact ⟨rfl, rfl⟩
  · rw [hC]
    exact inf_le_right

end Canonical

section Outer

variable {K : Type} [Field K] [Finite K]

open CFSG.ComponentClassification

theorem exists_simple_inner_of_not_mem {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 2 ^ m)
    {t : MulAut (projectiveSL 3 K)}
    (htX : t ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (ht2 : t ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {t} ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set X := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  have hXn : X.Normal := ⟨fun _ ⟨x, hx⟩ w =>
    ⟨w x, by rw [← hx, SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj]⟩⟩
  have hconj : ∀ {t' w t₀ : MulAut (projectiveSL 3 K)}, t' ∉ X → t' ^ 2 = 1 →
      t' = w * t₀ * w⁻¹ → t₀ ∉ X ∧ t₀ ^ 2 = 1 := by
    intro t' w t₀ h1 h2 h
    subst h
    refine ⟨fun h0 => h1 (hXn.conj_mem t₀ h0 w), ?_⟩
    rwa [conj_pow, conj_eq_one_iff] at h2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 t
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      exfalso
      subst hσ
      rw [map_one, mul_one] at htX ht2
      exact htX (RankTwoL3Even.mem_inner_of_mem_linearAutGroup (conjAut_mem_linearAutGroup A)
        (k := 1) ht2)
    ·
      obtain ⟨-, -, H, hH⟩ :=
        even_linear_field_involution_descent (n := 3) (by omega) hK le_rfl A σ hσ ht2
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_simple_conj hXn _ (exists_simple_fieldAut σ h0X h02)
  ·
    rw [pow_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      rw [map_one, mul_one] at htX ht2 ⊢
      obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (n := 3) (by omega) hK
          le_rfl A ht2
      have hC1 : C = 1 := by
        rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
        · exact Units.ext hC1
        · omega
      subst hC1
      rw [map_one, one_mul] at hH
      obtain ⟨h0X, -⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_simple_conj hXn _ (exists_simple_dualAut (by omega) hK h0X)
    ·
      obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two (by omega) hK le_rfl
          A σ hσ ht2
      have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
      have hσbar : ∀ x, σ x = hud.bar x := fun x => by
        rw [hσx, UnitaryFieldData.bar_apply, show m / 2 = e by omega]
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_simple_conj hXn _ (exists_simple_graphField hud (by omega) σ hσbar h0X h02)

theorem exists_simple_of_not_mem_range {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : y ^ 2 = 1)
    (hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    ∃ D : Subgroup (projectiveSL 3 K), (∀ a ∈ D, y a = a) ∧ IsSimpleGroup D ∧
      (∃ a b : D, a * b ≠ b * a) ∧ ⁅D, D⁆ = D ∧ ∃ c ∈ D, orderOf c = 2 := by
  obtain ⟨L, hLX, hLy, hLs, ⟨a, b, hab⟩, hLp, c, hcL, hc2⟩ :=
    exists_simple_inner_of_not_mem hf hK hout hy
  have hinj := RankTwoL3Even.conj_injective_projectiveSL (F := K)
  set D := L.comap (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) with hD
  have hDL : D.map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) = L :=
    map_comap_eq_self hLX
  let e : D ≃* L := (D.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hDL)
  refine ⟨D, fun a ha => hinj ?_, e.isSimpleGroup_congr.2 hLs,
    ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩,
    map_injective hinj ?_, ?_⟩
  · have h := mem_centralizer_singleton_iff.mp (hLy ha)
    rw [← SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj, ← h, mul_inv_cancel_right]
  · rw [map_commutator, hDL, hLp]
  · obtain ⟨c', rfl⟩ := hLX hcL
    exact ⟨c', hcL, by rw [← orderOf_injective _ hinj, hc2]⟩

end Outer

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_elem_of_mul_self {a : projectiveSL 3 K} (ha : a * a = 1) :
    ∃ E : Subgroup (projectiveSL 3 K), a ∈ E ∧ (∀ u ∈ E, ∀ v ∈ E, u * v = v * u) ∧
      (∀ u ∈ E, u * u = 1) ∧ Nat.card E = Nat.card K ^ 2 := by
  have hR := (radicals_projUnip (K := K)).elem₁
  have hc : ∀ u ∈ projRad K 0, ∀ v ∈ projRad K 0, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h2 : ∀ u ∈ projRad K 0, u * u = 1 := fun u hu => by rw [← sq]; exact hR.2 u hu
  have key : ∀ y : projectiveSL 3 K, ∃ E : Subgroup (projectiveSL 3 K),
      E = (projRad K 0).map (MulAut.conj y).toMonoidHom ∧
        (∀ u ∈ E, ∀ v ∈ E, u * v = v * u) ∧ (∀ u ∈ E, u * u = 1) ∧
        Nat.card E = Nat.card K ^ 2 := by
    intro y
    refine ⟨(projRad K 0).map (MulAut.conj y).toMonoidHom, rfl, ?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hc u hu v hv]
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, h2 u hu, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, radicals_projUnip.card₁]
  by_cases ha1 : a = 1
  · obtain ⟨E, rfl, hE⟩ := key 1
    exact ⟨(projRad K 0).map (MulAut.conj 1).toMonoidHom, by rw [ha1]; exact one_mem _, hE⟩
  · obtain ⟨y, hy⟩ := CFSG.ComponentClassification.RankTwoL3Even.exists_conj_eq_x0 ha ha1
    obtain ⟨E, rfl, hE⟩ := key y⁻¹
    refine ⟨(projRad K 0).map (MulAut.conj y⁻¹).toMonoidHom,
      ⟨CFSG.ComponentClassification.RankTwoL3Even.x0 K, mem_projRad_zero.2 ⟨0, 1, rfl⟩, ?_⟩, hE⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hy]
    group

end Model

section Cover

variable {Y : Type*} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite Y] [Finite K] [CharP K 2] in
theorem center_le_ker_of_cover (π : Y →* projectiveSL 3 K) (hπ : Function.Surjective π) :
    center Y ≤ π.ker := by
  have hinj := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  intro z hz
  rw [MonoidHom.mem_ker]
  apply hinj
  rw [map_one]
  ext p
  obtain ⟨y, rfl⟩ := hπ p
  rw [MulAut.conj_apply, MulAut.one_apply, ← map_inv, ← map_mul, ← map_mul,
    ← mem_center_iff.1 hz y, mul_inv_cancel_right]

omit [Finite Y] in
theorem exists_four_le_of_map_eq_of_isSimpleGroup {P : Type*} [Group P] [Finite P]
    {π : Y →* P} (hker : π.ker ≤ center Y) (hodd : Odd (Nat.card π.ker)) {X : Subgroup Y}
    {D : Subgroup P} (hXD : X.map π = D) (hD : IsSimpleGroup D) (hnc : ∃ a b : D, a * b ≠ b * a) :
    ∃ V : Subgroup Y, V ≤ X ∧ (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧
      Nat.card V = 4 := by
  obtain ⟨VD, hVD, hVD4⟩ := exists_four_group_of_two_le_pRank
    (two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hnc) (by
      rw [center_eq_bot_of_isSimpleGroup hnc, Subgroup.card_bot]
      exact odd_one))
  set VP := VD.map D.subtype with hVP
  have hVPc : ∀ a ∈ VP, ∀ b ∈ VP, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val (hVD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hVP2 : ∀ a ∈ VP, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← sq, hVD.2 a ha, map_one]
  set πX := π.comp X.subtype with hπX
  have hrange : πX.range = D := by rw [hπX, MonoidHom.range_comp, range_subtype, hXD]
  have hkerX : πX.ker ≤ center X := fun x hx => mem_center_iff.2 fun y => Subtype.ext
    (mem_center_iff.1 (hker (show (x : Y) ∈ π.ker from hx)) y)
  have hoddX : Odd (Nat.card πX.ker) := by
    have hle : πX.ker.map X.subtype ≤ π.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    refine Odd.of_dvd_nat hodd ?_
    rw [← Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hVPrange : VP ≤ πX.range := by
    rw [hrange, hVP]
    exact map_subtype_le VD
  obtain ⟨R, hR⟩ := exists_liftSq hkerX hoddX VP hVPc
  refine ⟨R.map X.subtype, map_subtype_le R, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (comm_of_liftSq hkerX hoddX hVPc hR x hx y hy)
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((hR x).1 hx).2
  · rw [Subgroup.card_map_of_injective X.subtype_injective, card_liftSq hoddX hVPrange hVP2 hR,
      hVP, Subgroup.card_map_of_injective D.subtype_injective, hVD4]

theorem exists_fixed_four_of_cover {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f)
    (π : Y →* projectiveSL 3 K) (hπ : Function.Surjective π) (hker : π.ker ≤ center Y)
    (hodd : Odd (Nat.card π.ker)) (α : Y ≃* Y) (hα : ∀ x, α (α x) = x) :
    (∃ E : Subgroup Y, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
        Nat.card E = Nat.card K ^ 2 ∧ ∀ x ∈ E, α x = x) ∨
      ∃ D : Subgroup Y, ⁅D, D⁆ = D ∧ (∃ c ∈ D, orderOf c = 2) ∧
        (∃ V : Subgroup Y, V ≤ D ∧ (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧
          Nat.card V = 4) ∧ ∀ x ∈ D, α x = x := by
  have hinj := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  have hcen := center_le_ker_of_cover π hπ
  have hα0 : ∀ z ∈ π.ker, α z ∈ π.ker := fun z hz => hcen (by
    have hzc := hker hz
    rw [mem_center_iff] at hzc ⊢
    intro g
    obtain ⟨g', rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, hzc g'])
  have hrange : ∀ p, p ∈ π.range := fun p => hπ p
  obtain ⟨β, hβ⟩ := exists_mulAut_comp π hπ α hα0
  have hβ2 : β ^ 2 = 1 := by
    ext p
    obtain ⟨x, rfl⟩ := hπ p
    rw [sq, MulAut.mul_apply, hβ, hβ, hα, MulAut.one_apply]
  by_cases hout : β ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  · left
    obtain ⟨a, ha⟩ := hout
    have ha2 : a * a = 1 := hinj (by rw [map_mul, ha, ← sq, hβ2, map_one])
    obtain ⟨EP, haEP, hEPc, hEP2, hEPcard⟩ := exists_elem_of_mul_self ha2
    have hβE : ∀ u ∈ EP, β u = u := fun u hu => by
      rw [← ha, MulAut.conj_apply, hEPc a haEP u hu, mul_inv_cancel_right]
    obtain ⟨R, hR⟩ := exists_liftSq hker hodd EP hEPc
    refine ⟨R, comm_of_liftSq hker hodd hEPc hR, fun x hx => ((hR x).1 hx).2, ?_, ?_⟩
    · rw [card_liftSq hodd (fun u _ => hrange u) hEP2 hR, hEPcard]
    · intro x hx
      obtain ⟨hxE, hx2⟩ := (hR x).1 hx
      have hπα : π (α x) = π x := by rw [← hβ, hβE _ hxE]
      have hαx : α x ∈ R := (hR _).2 ⟨by rw [hπα]; exact hxE, by rw [← map_mul, hx2, map_one]⟩
      exact eq_of_liftSq hodd hR hαx hx hπα
  · right
    obtain ⟨DP, hDfix, hDs, hDnc, hDperf, c, hcD, hc2⟩ :=
      exists_simple_of_not_mem_range hf hK hβ2 hout
    obtain ⟨X, hXperf, hXmap, hXle⟩ := exists_liftPerfect hker hDperf (fun u _ => hrange u)
    refine ⟨X, hXperf, ?_, exists_four_le_of_map_eq_of_isSimpleGroup hker hodd hXmap hDs hDnc, ?_⟩
    · have h1 : 2 ∣ Nat.card DP := hc2 ▸ Subgroup.orderOf_dvd_natCard DP hcD
      have h2 : Nat.card DP ∣ Nat.card X := hXmap ▸ Subgroup.card_map_dvd X π
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (h1.trans h2)
      exact ⟨c', c'.2, by rw [Subgroup.orderOf_coe, hc']⟩
    · refine forall_apply_eq_of_perfect α.toMonoidHom hXperf fun x hx => ?_
      refine ⟨x⁻¹ * α x, hker ?_, by simp⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hβ, hDfix _ (hXle hx), inv_mul_cancel]

end Cover

section Conj

variable {G : Type*} [Group G]

@[expose] def conjOfMem {X : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G)) : X ≃* X where
  toFun x := ⟨t * x * t⁻¹, (mem_normalizer_iff.1 ht x).1 x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have := (mem_normalizer_iff.1 ht (t⁻¹ * x * t)).2 (by simp [mul_assoc])
    exact this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjOfMem {X : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G)) (x : X) :
    (conjOfMem ht x : G) = t * x * t⁻¹ := rfl

theorem exists_fixed_four_of_mem_normalizer [Finite G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f) {X : Subgroup G}
    (π : X →* projectiveSL 3 K) (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hodd : Odd (Nat.card π.ker)) {t : G} (ht : t ∈ normalizer (X : Set G)) (htt : t * t = 1) :
    (∃ E : Subgroup G, E ≤ X ⊓ centralizer ({t} : Set G) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
        (∀ a ∈ E, a * a = 1) ∧ Nat.card E = Nat.card K ^ 2) ∨
      ∃ D : Subgroup G, D ≤ X ⊓ centralizer ({t} : Set G) ∧ ⁅D, D⁆ = D ∧
        (∃ c ∈ D, orderOf c = 2) ∧
        ∃ V : Subgroup G, V ≤ D ∧ (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧
          Nat.card V = 4 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hα : ∀ x, conjOfMem ht (conjOfMem ht x) = x := fun x => Subtype.ext (by
    rw [coe_conjOfMem, coe_conjOfMem, htinv]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [htt, one_mul, mul_one])
  have hfix : ∀ x : X, conjOfMem ht x = x → (x : G) ∈ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val hx
    rw [coe_conjOfMem] at h
    calc (x : G) * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  rcases exists_fixed_four_of_cover hf hK π hπ hker hodd (conjOfMem ht) hα with
    ⟨E, hEc, hE2, hEcard, hEfix⟩ | ⟨D, hDp, ⟨c, hcD, hc2⟩, ⟨V, hVD, hVc, hV2, hV4⟩, hDfix⟩
  · left
    refine ⟨E.map X.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hfix x (hEfix x hx)⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hEc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hE2 x hx)
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hEcard]
  · right
    refine ⟨D.map X.subtype, ?_, by rw [← map_commutator, hDp], ⟨c, ⟨c, hcD, rfl⟩, ?_⟩,
      V.map X.subtype, map_mono hVD, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hfix x (hDfix x hx)⟩
    · rw [Subgroup.orderOf_coe, hc2]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hVc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hV2 x hx)
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hV4]

end Conj

end CFSG.LocalAnalysis.EvenBN.LinearThree
