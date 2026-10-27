module

public import CFSG.CharacterTheory.KleinFourBlocks.FibreOrbit
public import CFSG.CharacterTheory.KleinFourBlocks.LevelBlock

public section

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed CFSG.Wreathed.BlockOrbits CFSG.BlockBasics
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourFiber
  CFSG.Semidihedral.Principal.ControlledDefect CFSG.Semidihedral.Principal.FreeSix

open scoped Classical

namespace CFSG.KleinFourBlocks

variable {G : Type*} [Group G]

@[expose] def AffordsFun {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (ι : X → G) (f : G → ℂ) (n : basis.index) :
    Prop :=
  ∀ x : X, (basis.representation n).character x = f (ι x)

omit [Group G] in
theorem affordsFun_iff_of_labelTransport {X Y : Type*} [Group X] [Fintype X] [Group Y]
    [Fintype Y] (bX : FiniteIrreducibleCharacterBasis X) (bY : FiniteIrreducibleCharacterBasis Y)
    (e : X ≃* Y) (ιX : X → G) (ιY : Y → G) (hι : ∀ x, ιY (e x) = ιX x) (f : G → ℂ)
    {n : bX.index} {n' : bY.index} (h : LabelTransport bX bY e n n') :
    AffordsFun bX ιX f n ↔ AffordsFun bY ιY f n' := by
  constructor
  · intro hn y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [h x, hn x, hι x]
  · intro hn x
    rw [← h x, hn (e x), hι x]

omit [Group G] in
theorem eq_of_affordsFun {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (ι : X → G) (f : G → ℂ) {n n' : basis.index}
    (hn : AffordsFun basis ι f n) (hn' : AffordsFun basis ι f n') : n = n' := by
  apply basis.distinct
  funext x
  exact (hn x).trans (hn' x).symm

section DLevel

variable {G : Type} [Group G] [Fintype G] {V : Subgroup G} {f₀ : G → ℂ}

omit [Fintype G] in
theorem centralizerConjugation_symm_apply (V : Subgroup G) {m : G} (hm : m ∈ mV V) (y : dV V) :
    (((centralizerConjugation V m hm).symm y : dV V) : G) = m⁻¹ * y * m := rfl

omit [Fintype G] in
theorem subgroupOf_map_centralizerConjugation (V : Subgroup G) {m : G} (hm : m ∈ mV V) :
    (V.subgroupOf (dV V)).map (centralizerConjugation V m hm).toMonoidHom =
      V.subgroupOf (dV V) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ V := hy
    show ((centralizerConjugation V m hm y : dV V) : G) ∈ V
    rw [centralizerConjugation_apply]
    exact (Subgroup.mem_normalizer_iff.mp hm (y : G)).mp hy'
  · intro hx
    have hx' : (x : G) ∈ V := hx
    refine ⟨(centralizerConjugation V m hm).symm x, ?_, MulEquiv.apply_symm_apply _ _⟩
    show (((centralizerConjugation V m hm).symm x : dV V) : G) ∈ V
    rw [centralizerConjugation_symm_apply]
    exact inv_conj_mem_V hm hx'

theorem labelTransport_conj_of_affords (basisD : FiniteIrreducibleCharacterBasis (dV V))
    {n₀ ℓ : basisD.index} (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀) {f : G → ℂ} {m : G}
    (hm : m ∈ mV V) (hfm : ∀ g, f g = f₀ (m⁻¹ * g * m))
    (hℓ : AffordsFun basisD (fun x => (x : G)) f ℓ) :
    LabelTransport basisD basisD (centralizerConjugation V m hm) n₀ ℓ := by
  intro x
  have h1 : (basisD.representation ℓ).character (centralizerConjugation V m hm x) =
      f ((centralizerConjugation V m hm x : dV V) : G) := hℓ _
  have h2 : (basisD.representation n₀).character x = f₀ (x : G) := hn₀ x
  rw [h1, h2, hfm, centralizerConjugation_apply]
  congr 1
  group

theorem exists_affords_D (basisD : FiniteIrreducibleCharacterBasis (dV V)) {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀) {f : G → ℂ} (hf : f ∈ fOrbit V f₀) :
    ∃ ℓ, AffordsFun basisD (fun x => (x : G)) f ℓ := by
  obtain ⟨m, hm, hfm⟩ := hf
  obtain ⟨ℓ, hℓ⟩ := labelTransport_exists basisD basisD (centralizerConjugation V m hm) n₀
  refine ⟨ℓ, fun y => ?_⟩
  have h1 := hℓ ((centralizerConjugation V m hm).symm y)
  rw [MulEquiv.apply_symm_apply] at h1
  show (basisD.representation ℓ).character y = f (y : G)
  rw [h1, hn₀, hfm]
  rfl

theorem coefficientBlockDefect_of_affords_D (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hdef₀ : coefficientBlockDefect basisD ideal 2 n₀ (V.subgroupOf (dV V))) {f : G → ℂ}
    (hf : f ∈ fOrbit V f₀) {ℓ : basisD.index} (hℓ : AffordsFun basisD (fun x => (x : G)) f ℓ) :
    coefficientBlockDefect basisD ideal 2 ℓ (V.subgroupOf (dV V)) := by
  obtain ⟨m, hm, hfm⟩ := hf
  have hLT := labelTransport_conj_of_affords basisD hn₀ hm hfm hℓ
  have hres : ∀ z, centralCharacterResidueHom basisD ideal ℓ
      (centralCoefficientTransport _ (centralizerConjugation V m hm) z) =
        centralCharacterResidueHom basisD ideal n₀ z := fun z =>
    centralCharacterResidueHom_labelTransport basisD basisD ideal _ hLT z
  have h1 := coefficientBlockDefect_map_equiv basisD basisD ideal 2 (centralizerConjugation V m hm)
    hres hdef₀
  rwa [subgroupOf_map_centralizerConjugation V hm] at h1

theorem block_unique_D (h : FreeBlockData V f₀) (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hblock₀ : ∀ ℓ : basisD.index,
      sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ →
      (∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
        (basisD.representation ℓ).character x = (basisD.representation ℓ).character x') →
      ∀ x, (basisD.representation ℓ).character x = (basisD.representation n₀).character x)
    {f f' : G → ℂ} (hf : f ∈ fOrbit V f₀) (hf' : f' ∈ fOrbit V f₀) {ℓ ℓ' : basisD.index}
    (hℓ : AffordsFun basisD (fun x => (x : G)) f ℓ)
    (hℓ' : AffordsFun basisD (fun x => (x : G)) f' ℓ')
    (hsame : sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) ℓ ℓ') : f = f' := by
  obtain ⟨m, hm, hfm⟩ := hf
  obtain ⟨m', hm', hfm'⟩ := hf'
  have hm1 : m⁻¹ * m' ∈ mV V := (mV V).mul_mem ((mV V).inv_mem hm) hm'
  have hLT := labelTransport_conj_of_affords basisD hn₀ hm hfm hℓ
  obtain ⟨ℓ₂, hℓ₂⟩ := labelTransport_exists basisD basisD (centralizerConjugation V m hm).symm ℓ'
  have hLT2 : LabelTransport basisD basisD (centralizerConjugation V m hm) ℓ₂ ℓ' :=
    labelTransport_symm' hℓ₂
  have hsame2 : sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ₂ :=
    sameCoefficientBlock_symm _ _
      ((sameCoefficientBlock_labelTransport_iff basisD basisD ideal _ hLT2 hLT).mpr
        (sameCoefficientBlock_symm _ _ hsame))
  have hℓ₂aff : ∀ x : dV V, (basisD.representation ℓ₂).character x =
      f₀ ((m⁻¹ * m')⁻¹ * (x : G) * (m⁻¹ * m')) := by
    intro x
    have h1 : (basisD.representation ℓ').character (centralizerConjugation V m hm x) =
        f' ((centralizerConjugation V m hm x : dV V) : G) := hℓ' _
    rw [← hLT2 x, h1, hfm', centralizerConjugation_apply]
    congr 1
    group
  have hVtrans : ∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
      (basisD.representation ℓ₂).character x = (basisD.representation ℓ₂).character x' := by
    intro x x' v hv hx
    rw [hℓ₂aff, hℓ₂aff, hx]
    have hv' : (m⁻¹ * m')⁻¹ * v * (m⁻¹ * m') ∈ V := inv_conj_mem_V hm1 hv
    have e : (m⁻¹ * m')⁻¹ * (v * (x' : G)) * (m⁻¹ * m') =
        ((m⁻¹ * m')⁻¹ * v * (m⁻¹ * m')) * ((m⁻¹ * m')⁻¹ * (x' : G) * (m⁻¹ * m')) := by group
    rw [e]
    exact h.transV _ hv' _
  have hall := hblock₀ ℓ₂ hsame2 hVtrans
  have hfix : ∀ g, f₀ ((m⁻¹ * m')⁻¹ * g * (m⁻¹ * m')) = f₀ g := by
    intro g
    by_cases hg : g ∈ dV V
    · have h1 := hall ⟨g, hg⟩
      rw [hℓ₂aff, hn₀] at h1
      exact h1
    · rw [h.supp g hg]
      apply h.supp
      intro hmem
      apply hg
      have := (conj_mem_dV_iff hm1).mpr hmem
      rwa [show (m⁻¹ * m') * ((m⁻¹ * m')⁻¹ * g * (m⁻¹ * m')) * (m⁻¹ * m')⁻¹ = g by group] at this
  have hm₁D : m⁻¹ * m' ∈ dV V := h.stab _ hm1 hfix
  funext g
  rw [hfm, hfm']
  have e : m'⁻¹ * g * m' = (m⁻¹ * m')⁻¹ * (m⁻¹ * g * m) * (m⁻¹ * m') := by group
  rw [e]
  exact (h.cls _ hm₁D _).symm

section Levels

variable {W : Type} [Group W] [Fintype W]

theorem exists_affords (basisD : FiniteIrreducibleCharacterBasis (dV V)) {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (wb : FiniteIrreducibleCharacterBasis W) (ι : W → G) (φ : W ≃* dV V)
    (hφ : ∀ w, (φ w : G) = ι w) {f : G → ℂ} (hf : f ∈ fOrbit V f₀) :
    ∃ n, AffordsFun wb ι f n := by
  obtain ⟨ℓ, hℓ⟩ := exists_affords_D basisD hn₀ hf
  obtain ⟨n, hn⟩ := labelTransport_exists basisD wb φ.symm ℓ
  refine ⟨n, (affordsFun_iff_of_labelTransport basisD wb φ.symm (fun x => (x : G)) ι
    (fun x => ?_) f hn).mp hℓ⟩
  rw [← hφ, MulEquiv.apply_symm_apply]

theorem defect_of_affords (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hdef₀ : coefficientBlockDefect basisD ideal 2 n₀ (V.subgroupOf (dV V)))
    (wb : FiniteIrreducibleCharacterBasis W) (ι : W → G) (φ : W ≃* dV V)
    (hφ : ∀ w, (φ w : G) = ι w) (QW : Subgroup W) (hQ : ∀ w, w ∈ QW ↔ ι w ∈ V) {f : G → ℂ}
    (hf : f ∈ fOrbit V f₀) {n : wb.index} (hn : AffordsFun wb ι f n) :
    coefficientBlockDefect wb ideal 2 n QW := by
  obtain ⟨ℓ, hℓ⟩ := labelTransport_exists wb basisD φ n
  have hℓaff : AffordsFun basisD (fun x => (x : G)) f ℓ :=
    (affordsFun_iff_of_labelTransport wb basisD φ ι (fun x => (x : G)) hφ f hℓ).mp hn
  have hdefℓ := coefficientBlockDefect_of_affords_D basisD ideal hn₀ hdef₀ hf hℓaff
  have hℓ' : LabelTransport basisD wb φ.symm ℓ n := labelTransport_symm' hℓ
  have hres : ∀ z, centralCharacterResidueHom wb ideal n
      (centralCoefficientTransport _ φ.symm z) = centralCharacterResidueHom basisD ideal ℓ z :=
    fun z => centralCharacterResidueHom_labelTransport basisD wb ideal φ.symm hℓ' z
  have h1 := coefficientBlockDefect_map_equiv basisD wb ideal 2 φ.symm hres hdefℓ
  have hmap : (V.subgroupOf (dV V)).map φ.symm.toMonoidHom = QW := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ V := hy
      show φ.symm y ∈ QW
      rw [hQ]
      have := hφ (φ.symm y)
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this]
      exact hy'
    · intro hw
      refine ⟨φ w, ?_, φ.symm_apply_apply w⟩
      show ((φ w : dV V) : G) ∈ V
      rw [hφ]
      exact (hQ w).mp hw
  rwa [hmap] at h1

theorem block_unique (h : FreeBlockData V f₀)
    (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hblock₀ : ∀ ℓ : basisD.index,
      sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ →
      (∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
        (basisD.representation ℓ).character x = (basisD.representation ℓ).character x') →
      ∀ x, (basisD.representation ℓ).character x = (basisD.representation n₀).character x)
    (wb : FiniteIrreducibleCharacterBasis W) (ι : W → G) (φ : W ≃* dV V)
    (hφ : ∀ w, (φ w : G) = ι w) {f f' : G → ℂ} (hf : f ∈ fOrbit V f₀) (hf' : f' ∈ fOrbit V f₀)
    {θ θ' : wb.index} (hθ : AffordsFun wb ι f θ) (hθ' : AffordsFun wb ι f' θ')
    (hsame : sameCoefficientBlock wb (localizedComplexIntegerRing ideal) θ θ') : f = f' := by
  obtain ⟨ℓ, hℓ⟩ := labelTransport_exists wb basisD φ θ
  obtain ⟨ℓ', hℓ'⟩ := labelTransport_exists wb basisD φ θ'
  exact block_unique_D h basisD ideal hn₀ hblock₀ hf hf'
    ((affordsFun_iff_of_labelTransport wb basisD φ ι (fun x => (x : G)) hφ f hℓ).mp hθ)
    ((affordsFun_iff_of_labelTransport wb basisD φ ι (fun x => (x : G)) hφ f' hℓ').mp hθ')
    ((sameCoefficientBlock_labelTransport_iff wb basisD ideal φ hℓ hℓ').mp hsame)

section LevelBlockFun

variable {H : Type} [Group H] [Fintype H]

theorem level_block_fun (h : FreeBlockData V f₀) (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hdef₀ : coefficientBlockDefect basisD ideal 2 n₀ (V.subgroupOf (dV V)))
    (hblock₀ : ∀ ℓ : basisD.index,
      sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ →
      (∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
        (basisD.representation ℓ).character x = (basisD.representation ℓ).character x') →
      ∀ x, (basisD.representation ℓ).character x = (basisD.representation n₀).character x)
    (ρ : H →* G) (hρ : Function.Injective ρ) (hρM : ∀ x, ρ x ∈ mV V)
    (P : Subgroup H) [P.Normal] (hP : IsPGroup 2 P)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPV : ∀ a, a ∈ P ↔ ρ a ∈ V)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (ι : Subgroup.centralizer (P : Set H) → G) (hι : ∀ w, ι w = ρ (w : H))
    (φ : Subgroup.centralizer (P : Set H) ≃* dV V) (hφ : ∀ w, (φ w : G) = ι w)
    (hb : FiniteIrreducibleCharacterBasis H) (X : Set G) (hX : ∀ g, g ∈ X ↔ ∃ x, ρ x = g)
    {f₁ : G → ℂ} (hf₁ : f₁ ∈ fOrbit V f₀) {β₀ : wb.index} (hβ₀ : AffordsFun wb ι f₁ β₀) :
    ∃ A : hb.index, coefficientBlockDefect hb ideal 2 A P ∧
      brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
        le_rfl (Subgroup.centralizer_le_normalizer _) wb β₀ =
          centralCharacterResidueHom hb ideal A ∧
      ∀ n : wb.index,
        brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
            le_rfl (Subgroup.centralizer_le_normalizer _) wb n =
          centralCharacterResidueHom hb ideal A ↔
        ∃ f ∈ gOrbit X f₁, ∃ n' : wb.index, AffordsFun wb ι f n' ∧
          sameCoefficientBlock wb (localizedComplexIntegerRing ideal) n' n := by
  have hdef : coefficientBlockDefect wb ideal 2 β₀
      (P.subgroupOf (Subgroup.centralizer (P : Set H))) :=
    defect_of_affords basisD ideal hn₀ hdef₀ wb ι φ hφ
      (P.subgroupOf (Subgroup.centralizer (P : Set H)))
      (fun w => by rw [Subgroup.mem_subgroupOf, hι, hPV]) hf₁ hβ₀
  have hconj : ∀ (x : H) (θ' : wb.index),
      LabelTransport wb wb (normalCentralizerConj P x) β₀ θ' ↔
        AffordsFun wb ι (fun g => f₁ ((ρ x)⁻¹ * g * ρ x)) θ' := by
    intro x θ'
    constructor
    · intro hθ' w
      have h1 := hθ' (normalCentralizerConj P x⁻¹ w)
      rw [normalCentralizerConj_apply_inv] at h1
      show (wb.representation θ').character w = f₁ ((ρ x)⁻¹ * ι w * ρ x)
      rw [h1, hβ₀, hι, hι, normalCentralizerConj_inv_apply, map_mul, map_mul, map_inv]
    · intro hθ' d
      have h1 := hθ' (normalCentralizerConj P x d)
      have h2 : (wb.representation θ').character (normalCentralizerConj P x d) =
          f₁ ((ρ x)⁻¹ * ι (normalCentralizerConj P x d) * ρ x) := h1
      rw [h2, hβ₀ d, hι, hι, normalCentralizerConj_apply, map_mul, map_mul, map_inv]
      congr 1
      group
  have hstab : ∀ (x : H) (θ' : wb.index),
      LabelTransport wb wb (normalCentralizerConj P x) β₀ θ' →
      sameCoefficientBlock wb (localizedComplexIntegerRing ideal) β₀ θ' →
      x ∈ Subgroup.centralizer (P : Set H) := by
    intro x θ' hθ' hsame
    have hxf : (fun g => f₁ ((ρ x)⁻¹ * g * ρ x)) ∈ fOrbit V f₀ :=
      fOrbit_smul_mem hf₁ (hρM x)
    have heq := block_unique h basisD ideal hn₀ hblock₀ wb ι φ hφ hf₁ hxf hβ₀
      ((hconj x θ').mp hθ') hsame
    have hD : ρ x ∈ dV V := h.stab_orbit hf₁ (hρM x) fun g => (congrFun heq g).symm
    have hw : ρ ((φ.symm ⟨ρ x, hD⟩ : Subgroup.centralizer (P : Set H)) : H) = ρ x := by
      rw [← hι, ← hφ, MulEquiv.apply_symm_apply]
    have hxw := hρ hw
    rw [← hxw]
    exact (φ.symm ⟨ρ x, hD⟩).2
  obtain ⟨A, hAdef, hAeq, hAiff⟩ := exists_level_block hb ideal P hP hPab wb β₀ hdef hstab
  refine ⟨A, hAdef, hAeq, fun n => ?_⟩
  rw [hAiff n]
  constructor
  · rintro ⟨x, θ', hθ', hsame⟩
    exact ⟨fun g => f₁ ((ρ x)⁻¹ * g * ρ x), ⟨ρ x, (hX _).mpr ⟨x, rfl⟩, fun g => rfl⟩, θ',
      (hconj x θ').mp hθ', hsame⟩
  · rintro ⟨f, ⟨k, hk, hfk⟩, n', hn', hsame⟩
    obtain ⟨x, rfl⟩ := (hX k).mp hk
    have hfun : f = fun g => f₁ ((ρ x)⁻¹ * g * ρ x) := funext hfk
    rw [hfun] at hn'
    exact ⟨x, n', (hconj x n').mpr hn', hsame⟩

end LevelBlockFun

end Levels

end DLevel

end CFSG.KleinFourBlocks
