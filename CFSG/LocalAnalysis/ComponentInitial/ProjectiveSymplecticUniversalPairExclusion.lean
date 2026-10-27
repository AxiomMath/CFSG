module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryUniversalPairExclusion

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic

open Module Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddProjectivePair

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

namespace SymplecticPair

theorem eq_of_isCompl {A W : Submodule K V} (hAW : IsCompl A W) {x y : sesqUnitaryGroup B}
    (hA : ∀ a ∈ A, spOp x a = spOp y a) (hW : ∀ w ∈ W, spOp x w = spOp y w) : x = y := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (hAW.sup_eq_top ▸ Submodule.mem_top : v ∈ A ⊔ W)
  change spOp x (a + w) = spOp y (a + w)
  rw [map_add, map_add, hA a ha, hW w hw]

theorem det_eq_one_of_isometry {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {C : LinearMap.BilinForm K A} (hC : C.IsAlt) (hCnd : C.Nondegenerate) (hA : finrank K A = 2)
    {y : Module.End K A} (hy : ∀ u v, C (y u) (y v) = C u v) : LinearMap.det y = 1 := by
  let b : Basis (Fin 2) K A := Module.finBasisOfFinrankEq K A hA
  set M := LinearMap.toMatrix b b y with hM
  have hyb : ∀ j, y (b j) = ∑ i, M i j • b i := fun j => by
    rw [hM]
    simp only [LinearMap.toMatrix_apply]
    exact (b.sum_repr (y (b j))).symm
  set c := C (b 0) (b 1) with hcdef
  have h10 : C (b 1) (b 0) = -c := by rw [hcdef, ← hC.neg_eq]
  have hc : c ≠ 0 := by
    intro hc0
    have hzero : ∀ i j, C (b i) (b j) = 0 := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact hC.self_eq_zero _
      · exact hc0
      · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta]
        rw [h10, hc0, neg_zero]
      · exact hC.self_eq_zero _
    have h0 : C = 0 := LinearMap.ext_basis b b fun i j => by rw [hzero]; rfl
    exact b.ne_zero 0 (hCnd.1 (b 0) fun v => by rw [h0]; rfl)
  have h1 := hy (b 0) (b 1)
  rw [hyb, hyb] at h1
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hC.self_eq_zero, h10] at h1
  rw [← LinearMap.det_toMatrix b, ← hM, Matrix.det_fin_two]
  have h2 : (M 0 0 * M 1 1 - M 0 1 * M 1 0 - 1) * c = 0 := by linear_combination h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hc)

theorem neg_of_mem_symplecticSummandSet_of_finrank_eq_two [FiniteDimensional K V]
    (htwo : (2 : K) ≠ 0) (hB : B.IsAlt) {A W : Submodule K V} (hAW : IsCompl A W)
    (hAnd : (B.domRestrict₁₂ A A).Nondegenerate) (hA2 : finrank K A = 2)
    {x : sesqUnitaryGroup B} (hx : x ∈ symplecticSummandSet B A W) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∀ a ∈ A, spOp x a = -a := by
  obtain ⟨hxW, hxA⟩ := hx
  have hxx : spOp x * spOp x = 1 := congrArg spOp hx2
  set xA := (spOp x).restrict hxA with hxAdef
  have hrr : xA * xA = 1 := LinearMap.ext fun a => Subtype.ext (by
    change spOp x (spOp x a) = a
    rw [← Module.End.mul_apply, hxx, Module.End.one_apply])
  have hiso : ∀ u v : A, B.domRestrict₁₂ A A (xA u) (xA v) = B.domRestrict₁₂ A A u v :=
    fun u v => mem_sesqUnitaryGroup.mp x.2 u v
  have hAalt : (B.domRestrict₁₂ A A).IsAlt := fun u => hB u
  have hdet := det_eq_one_of_isometry hAalt hAnd hA2 hiso
  rcases UnitaryPair.end_eq_one_or_neg_one htwo hA2 hrr hdet with h1 | h1
  · exfalso
    refine hx1 (eq_of_isCompl hAW (fun a ha => ?_) fun w hw => ?_)
    · have h2 := congrArg (fun φ : Module.End K A => (φ ⟨a, ha⟩ : V)) h1
      simp only [hxAdef, LinearMap.restrict_apply, Module.End.one_apply] at h2
      exact h2
    · rw [hxW w hw]
      rfl
  · intro a ha
    have h2 := congrArg (fun φ : Module.End K A => (φ ⟨a, ha⟩ : V)) h1
    simpa [hxAdef] using h2

theorem eq_of_mem_symplecticSummandSet_of_finrank_eq_two [FiniteDimensional K V]
    (htwo : (2 : K) ≠ 0) (hB : B.IsAlt) {A W : Submodule K V} (hAW : IsCompl A W)
    (hAnd : (B.domRestrict₁₂ A A).Nondegenerate) (hA2 : finrank K A = 2)
    {x y : sesqUnitaryGroup B} (hx : x ∈ symplecticSummandSet B A W)
    (hy : y ∈ symplecticSummandSet B A W) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y :=
  eq_of_isCompl hAW (fun a ha => by
      rw [neg_of_mem_symplecticSummandSet_of_finrank_eq_two htwo hB hAW hAnd hA2 hx hx2 hx1 a ha,
        neg_of_mem_symplecticSummandSet_of_finrank_eq_two htwo hB hAW hAnd hA2 hy hy2 hy1 a ha])
    fun w hw => by rw [hx.1 w hw, hy.1 w hw]

theorem exists_plane_reflection (hB : B.IsAlt) {e f : V} (hef : B e f = 1) :
    ∃ S : sesqUnitaryGroup B, S * S = 1 ∧
      ∀ v, spOp S v = v - (2 * B v f) • e + (2 * B v e) • f := by
  have hfe : B f e = -1 := by rw [← hB.neg_eq, hef]
  have hee : B e e = 0 := hB.self_eq_zero e
  have hff : B f f = 0 := hB.self_eq_zero f
  let φ : V →ₗ[K] V :=
    { toFun := fun v => v - (2 * B v f) • e + (2 * B v e) • f
      map_add' := fun v w => by
        simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
        abel
      map_smul' := fun c v => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
          smul_sub, smul_smul]
        congr 2 <;> ring_nf }
  have hφ : ∀ v, φ (φ v) = v := fun v => by
    change (v - (2 * B v f) • e + (2 * B v e) • f) -
      (2 * B (v - (2 * B v f) • e + (2 * B v e) • f) f) • e +
        (2 * B (v - (2 * B v f) • e + (2 * B v e) • f) e) • f = v
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hef, hfe, hee, hff]
    module
  let ψ : V ≃ₗ[K] V := LinearEquiv.ofInvolutive φ hφ
  have hψ : ∀ v, ψ v = v - (2 * B v f) • e + (2 * B v e) • f := fun v => rfl
  have hmem : LinearMap.GeneralLinearGroup.ofLinearEquiv ψ ∈ sesqUnitaryGroup B := by
    intro x y
    change B (ψ x) (ψ y) = B x y
    rw [hψ, hψ]
    have hxe : B e x = -B x e := by rw [← hB.neg_eq]
    have hxf : B f x = -B x f := by rw [← hB.neg_eq]
    have hye : B e y = -B y e := by rw [← hB.neg_eq]
    have hyf : B f y = -B y f := by rw [← hB.neg_eq]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hef, hfe, hee, hff, hye, hyf]
    ring
  refine ⟨⟨_, hmem⟩, ?_, hψ⟩
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  change ψ (ψ v) = v
  exact hφ v

theorem exists_transvection (hB : B.IsAlt) (a : V) :
    ∃ g : sesqUnitaryGroup B, ∀ v, spOp g v = v + B v a • a := by
  have haa : B a a = 0 := hB.self_eq_zero a
  let ψ : V ≃ₗ[K] V :=
    { toFun := fun v => v + B v a • a
      invFun := fun v => v - B v a • a
      map_add' := fun v w => by
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
      map_smul' := fun c v => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
          smul_smul]
      left_inv := fun v => by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          haa, mul_zero, add_zero, add_sub_cancel_right]
      right_inv := fun v => by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          haa, mul_zero, sub_zero, sub_add_cancel] }
  have hmem : LinearMap.GeneralLinearGroup.ofLinearEquiv ψ ∈ sesqUnitaryGroup B := by
    intro x y
    change B (x + B x a • a) (y + B y a • a) = B x y
    have hay : B a y = -B y a := by rw [← hB.neg_eq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hay]
    ring
  exact ⟨⟨_, hmem⟩, fun v => rfl⟩

end SymplecticPair

open SymplecticPair

theorem odd_projective_symplectic_commuting_universal_pair_exclusion {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V] {r : ℕ}
    (hr : 1 ≤ r) (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate) :
    ¬ ∃ B₁ B₂ : Subgroup (sesqUnitaryGroup B ⧸ spSigns B),
      CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧ ⁅B₁, B₂⁆ = ⊥ ∧
      (∃ V₁ : Subgroup (sesqUnitaryGroup B ⧸ spSigns B), V₁ ≤ B₁ ∧
        CFSG.IsElementaryAbelian 2 V₁ ∧ Nat.card V₁ = 4) ∧
      (∃ V₂ : Subgroup (sesqUnitaryGroup B ⧸ spSigns B), V₂ ≤ B₂ ∧
        CFSG.IsElementaryAbelian 2 V₂ ∧ Nat.card V₂ = 4) ∧
      (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁
        (centralizer ({t} : Set (sesqUnitaryGroup B ⧸ spSigns B)))) ∧
      (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂
        (centralizer ({s} : Set (sesqUnitaryGroup B ⧸ spSigns B)))) := by
  rintro ⟨B₁, B₂, hq₁, hq₂, hcomm, ⟨V₁, hV₁, hV₁e, hV₁c⟩, ⟨V₂, hV₂, hV₂e, hV₂c⟩, h₁, h₂⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  set π := QuotientGroup.mk' (spSigns B) with hπ
  have hB₁p := commutator_eq_self_of_isQuasisimple hq₁
  have hB₂p := commutator_eq_self_of_isQuasisimple hq₂
  have hB₁ne := ne_bot_of_card_eq_four hV₁ hV₁c
  have hB₂ne := ne_bot_of_card_eq_four hV₂ hV₂c
  have hB₁B₂ : B₁ ≤ centralizer (B₂ : Set (sesqUnitaryGroup B ⧸ spSigns B)) :=
    commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hB₂B₁ : B₂ ≤ centralizer (B₁ : Set (sesqUnitaryGroup B ⧸ spSigns B)) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hcomm)
  set B₁hat := ⁅B₁.comap π, B₁.comap π⁆ with hB₁hat
  have hmk₁ : ∀ g ∈ B₁hat, π g ∈ B₁ := fun g hg => commutator_le_self (B₁.comap π) hg
  obtain ⟨t, htV, -, -, ht1, -, -⟩ := exists_ne_one_ne_one_ne hV₂c
  have ht2 : t ^ 2 = 1 := by
    have := hV₂e
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₂) t htV
  have htB₂ : t ∈ B₂ := hV₂ htV
  obtain ⟨T, hT⟩ := QuotientGroup.mk'_surjective (spSigns B) t
  have hC₁ := h₁ t htB₂ (orderOf_eq_prime ht2 ht1)
  have hBcomp₁ := (isComponentOf_iff_isComponent_subgroupOf hC₁.1).1 hC₁
  have hmap₁ : ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype :
      Subgroup (sesqUnitaryGroup B ⧸ spSigns B)) = B₁ := map_subgroupOf_eq_of_le hC₁.1
  obtain ⟨hTT, hP, hM, horth, hndP, hndM, A, W, hAW, hBhat, ⟨e, he⟩, -⟩ :=
    odd_projective_symplectic_local_component_supported_on_eigenspace hp hp2 hf hK hr hdim hB
      hBnd (orderOf_eq_prime ht2 ht1) hT hBcomp₁ (Q := B₂) (by rw [hmap₁]; exact hB₂B₁) hB₂ne
      hB₂p
  rw [hmap₁] at hBhat
  have hcompl := isCompl_ker_sub_one_ker_add_one htwo hTT
  have hAWc : IsCompl A W := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcompl
    · exact hcompl.symm
  have hA0 : A ≠ ⊥ := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hM
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hM
    · exact hP
  have hAWo : ∀ a ∈ A, ∀ w ∈ W, B a w = 0 := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact horth
    · intro a ha w hw
      rw [← hB.neg_eq, horth w hw a ha, neg_zero]
  have hWAo : ∀ w ∈ W, ∀ a ∈ A, B w a = 0 := fun w hw a ha => by
    rw [← hB.neg_eq, hAWo a ha w hw, neg_zero]
  have hAnd : (B.domRestrict₁₂ A A).Nondegenerate := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hndP
    · exact hndM
  have hsep : ∀ a ∈ A, a ≠ 0 → ∃ y ∈ A, B a y ≠ 0 := by
    intro a ha ha0
    by_contra hcon
    push Not at hcon
    exact ha0 (congrArg Subtype.val (hAnd.1 ⟨a, ha⟩ fun y => hcon y y.2))
  have hmemB : ∀ g : sesqUnitaryGroup B, g ∈ symplecticSummandSet B A W → g ∈ B₁hat :=
    fun g hg => by
      rw [← SetLike.mem_coe, hBhat]
      exact hg
  have hmemB' : ∀ g : sesqUnitaryGroup B, g ∈ B₁hat → g ∈ symplecticSummandSet B A W :=
    fun g hg => by
      rw [← hBhat]
      exact hg
  have hr2 : finrank K A ≠ 2 := by
    intro hr2
    obtain ⟨v, hv, v', hv', hv1, hv'1, hvv'⟩ := exists_ne_one_ne_one_ne hV₁c
    have hsq : ∀ w ∈ V₁, w * w = 1 := fun w hw => by
      have := hV₁e
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₁) w hw
    have hlift : ∀ w ∈ V₁, ∃ x : sesqUnitaryGroup B, x ∈ B₁hat ∧ π x = w ∧ x * x = 1 := by
      intro w hw
      set y : B₁.subgroupOf (centralizer {t}) :=
        ⟨⟨w, hC₁.1 (hV₁ hw)⟩, by rw [mem_subgroupOf]; exact hV₁ hw⟩
      refine ⟨(e.symm y : sesqUnitaryGroup B), ?_, ?_, ?_⟩
      · have hK' : ⁅((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π,
            ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π⁆ =
            B₁hat := by rw [hmap₁]
        exact (Subgroup.ext_iff.1 hK' _).1 (e.symm y).2
      · rw [← he, MulEquiv.apply_symm_apply]
      · have hy : y * y = 1 := Subtype.ext (Subtype.ext (hsq w hw))
        rw [← Subgroup.coe_mul, ← map_mul, hy, map_one, Subgroup.coe_one]
    obtain ⟨x, hxB, hxv, hx2⟩ := hlift v hv
    obtain ⟨x', hx'B, hx'v, hx'2⟩ := hlift v' hv'
    have hx1 : x ≠ 1 := fun h1 => hv1 (by rw [← hxv, h1, map_one])
    have hx'1 : x' ≠ 1 := fun h1 => hv'1 (by rw [← hx'v, h1, map_one])
    apply hvv'
    rw [← hxv, ← hx'v, eq_of_mem_symplecticSummandSet_of_finrank_eq_two htwo hB hAWc hAnd hr2
      (hmemB' x hxB) (hmemB' x' hx'B) hx2 hx'2 hx1 hx'1]
  have hr1 : finrank K A ≠ 1 := by
    intro hr1
    obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
    obtain ⟨y, hy, hy0⟩ := hsep a₀ ha₀ ha₀0
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨a₀, ha₀⟩ : A)
      (fun h0 => ha₀0 (congrArg Subtype.val h0))).1 hr1 ⟨y, hy⟩
    have hc' : c • a₀ = y := congrArg Subtype.val hc
    rw [← hc', map_smul, hB.self_eq_zero, smul_zero] at hy0
    exact hy0 rfl
  have hr0 : finrank K A ≠ 0 := fun h0 => hA0 (Submodule.finrank_eq_zero.1 h0)
  have hr3 : 3 ≤ finrank K A := by omega
  obtain ⟨e₁, he₁, he₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
  obtain ⟨y₁, hy₁, hy₁0⟩ := hsep e₁ he₁ he₁0
  set f₁ := (B e₁ y₁)⁻¹ • y₁ with hf₁def
  have hf₁ : f₁ ∈ A := A.smul_mem _ hy₁
  have hef : B e₁ f₁ = 1 := by rw [hf₁def, map_smul, smul_eq_mul, inv_mul_cancel₀ hy₁0]
  have hfe : B f₁ e₁ = -1 := by rw [← hB.neg_eq, hef]
  set X := Submodule.span K (Set.range ![e₁, f₁]) with hXdef
  obtain ⟨a₀, ha₀, ha₀X⟩ : ∃ a₀ ∈ A, a₀ ∉ X := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ X := fun a ha => hcon a ha
    have h1 := (Submodule.finrank_mono hle).trans (finrank_range_le_card (R := K) ![e₁, f₁])
    rw [Fintype.card_fin] at h1
    omega
  set b := a₀ - (B a₀ f₁ • e₁ - B a₀ e₁ • f₁) with hbdef
  have hbA : b ∈ A := A.sub_mem ha₀ (A.sub_mem (A.smul_mem _ he₁) (A.smul_mem _ hf₁))
  have hbe : B b e₁ = 0 := by
    rw [hbdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hfe]
    ring
  have hbf : B b f₁ = 0 := by
    rw [hbdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hef]
    ring
  have hb0 : b ≠ 0 := by
    intro h0
    apply ha₀X
    have h1 : a₀ = B a₀ f₁ • e₁ - B a₀ e₁ • f₁ := sub_eq_zero.1 h0
    rw [h1]
    exact X.sub_mem (X.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
      (X.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
  obtain ⟨a, haA, hba⟩ := hsep b hbA hb0
  obtain ⟨S, hS2, hSapp⟩ := exists_plane_reflection hB hef
  obtain ⟨g, hgapp⟩ := exists_transvection hB a
  have hSS : S ∈ symplecticSummandSet B A W := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [hSapp, hWAo w hw f₁ hf₁, hWAo w hw e₁ he₁, mul_zero, zero_smul, zero_smul, sub_zero,
        add_zero]
    · rw [hSapp]
      exact A.add_mem (A.sub_mem hv (A.smul_mem _ he₁)) (A.smul_mem _ hf₁)
  have hgS : g ∈ symplecticSummandSet B A W := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [hgapp, hWAo w hw a haA, zero_smul, add_zero]
    · rw [hgapp]
      exact A.add_mem hv (A.smul_mem _ haA)
  have hSmem : S ∈ B₁hat := hmemB S hSS
  have hgmem : g ∈ B₁hat := hmemB g hgS
  have hneg : ∀ v : V, -v = v → v = 0 := by
    intro v hv
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hv]
      exact neg_add_cancel v
    exact (smul_eq_zero.1 h2v).resolve_left htwo
  have hSe : spOp S e₁ = -e₁ := by
    rw [hSapp, hef, hB.self_eq_zero, mul_zero, zero_smul, add_zero, mul_one, two_smul]
    abel
  have hSb : spOp S b = b := by
    rw [hSapp, hbf, hbe, mul_zero, zero_smul, zero_smul, sub_zero, add_zero]
  have hgb : spOp g b ≠ b := by
    rw [hgapp]
    intro h1
    have h2 : B b a • a = 0 := by
      have := congrArg (· - b) h1
      simpa using this
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hba
      exact hba rfl
    exact hba ((smul_eq_zero.1 h2).resolve_right ha0)
  set s := π S with hsdef
  have hsB₁ : s ∈ B₁ := hmk₁ S hSmem
  have hs2 : s ^ 2 = 1 := by rw [hsdef, ← map_pow, sq, hS2, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have hS1 := eq_one_of_mem_spSigns htwo ((QuotientGroup.eq_one_iff S).1 h1) hW0 hSS.1
    have h2 := hSe
    rw [hS1] at h2
    exact he₁0 (hneg _ h2.symm)
  have hC₂ := h₂ s hsB₁ (orderOf_eq_prime hs2 hs1)
  have hBcomp₂ := (isComponentOf_iff_isComponent_subgroupOf hC₂.1).1 hC₂
  have hmap₂ : ((B₂.subgroupOf (centralizer {s})).map (centralizer {s}).subtype :
      Subgroup (sesqUnitaryGroup B ⧸ spSigns B)) = B₂ := map_subgroupOf_eq_of_le hC₂.1
  obtain ⟨-, -, hM', -, -, -, A', W', hA'W', -, -, hfix'⟩ :=
    odd_projective_symplectic_local_component_supported_on_eigenspace hp hp2 hf hK hr hdim hB
      hBnd (orderOf_eq_prime hs2 hs1) hsdef.symm hBcomp₂ (Q := B₁)
      (by rw [hmap₂]; exact hB₁B₂) hB₁ne hB₁p
  rcases hA'W' with ⟨rfl, -⟩ | ⟨rfl, -⟩
  ·
    exact hgb (hfix' g hgmem b (LinearMap.mem_ker.2 (by
      rw [LinearMap.sub_apply, Module.End.one_apply, hSb, sub_self])))
  ·
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM'
    have h1 := hfix' S hSmem v hv
    have h2 := LinearMap.mem_ker.1 hv
    rw [LinearMap.add_apply, Module.End.one_apply, h1] at h2
    exact hv0 ((smul_eq_zero.1 (by rw [two_smul]; exact h2 : (2 : K) • v = 0)).resolve_left htwo)

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
