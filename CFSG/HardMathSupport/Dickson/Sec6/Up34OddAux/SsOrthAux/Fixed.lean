module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrthAux.Centralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsOrth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (OddLieCentralQuotient
  oddLieCentralQuotient_of_centerQuotient_equiv exists_component_of_quotientFixed)

theorem mem_fixedSubgroup_iff' {G : Type*} [Group G] {φ : MulAut G} {g : G} :
    g ∈ fixedSubgroup φ ↔ φ g = g := Iff.rfl

section Transfer

theorem exists_component_of_isComponentOf_centralizer {X : Type*} [Group X] (Z : Subgroup X)
    [Z.Normal] (hcentral : Z ≤ Subgroup.center X) (x₀ : X) {I : Subgroup (X ⧸ Z)}
    (hI : CFSG.Open.IsComponentOf I
      (Subgroup.centralizer ({(x₀ : X ⧸ Z)} : Set (X ⧸ Z)))) :
    ∃ M₀ : Subgroup ↥(fixedSubgroup (MulAut.conj x₀)), CFSG.IsComponent M₀ ∧
      Nonempty (↥I ⧸ Subgroup.center ↥I ≃* ↥M₀ ⧸ Subgroup.center ↥M₀) := by
  set ψ : MulAut X := MulAut.conj x₀
  have hzfix : ∀ z ∈ Z, ψ z = z := fun z hz => by
    change x₀ * z * x₀⁻¹ = z
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp (hcentral hz) x₀)
  have hinv : Z.map ψ.toMonoidHom = Z := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hzfix z hz).symm ▸ hz
    · intro hy
      exact ⟨y, hy, hzfix y hy⟩
  have hfix : fixedSubgroup (CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient
      Z ψ hinv) = Subgroup.centralizer ({(x₀ : X ⧸ Z)} : Set (X ⧸ Z)) := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [mem_fixedSubgroup_iff', Subgroup.mem_centralizer_singleton_iff]
    change CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv
      ((QuotientGroup.mk' Z) y) = (QuotientGroup.mk' Z) y ↔ _
    rw [CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk]
    change (QuotientGroup.mk' Z) (x₀ * y * x₀⁻¹) = (QuotientGroup.mk' Z) y ↔ _
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hI' : CFSG.Open.IsComponentOf I (fixedSubgroup
      (CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
    rw [hfix]
    exact hI
  have hIle := hI'.1
  have hIc := isComponent_subgroupOf_of_open hI'
  obtain ⟨M₀, hM₀, ⟨e⟩⟩ := exists_component_of_quotientFixed Z hcentral ψ hinv hIc
  refine ⟨M₀, hM₀, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hIle).symm
    (Subgroup.map_center_eq _)).trans e

end Transfer

section Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {ℓ f : ℕ}

theorem conj_mem_orthDerived_of_mem_orthogonalGroup {G y : V ≃ₗ[K] V}
    (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hy : y ∈ orthDerived Q) :
    G * y * G⁻¹ ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup Q).map (MulAut.conj G).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hG ha) (inv_mem hG)
  have h1 : (MulAut.conj G).toMonoidHom y ∈ (orthDerived Q).map (MulAut.conj G).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hy
  rw [orthDerived, Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hle hle h1

theorem oddLie_of_component_fixed {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) (hp2 : Odd p) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {M₀ : Subgroup ↥(fixedSubgroup (MulAut.conj x))} (hM₀ : CFSG.IsComponent M₀) :
    OddLieCentralQuotient ℓ ↥M₀ := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V)
  set H0 : Subgroup (V ≃ₗ[K] V) :=
    (fixedSubgroup (MulAut.conj x)).map (orthDerived Q).subtype
  have hmem : ∀ g : V ≃ₗ[K] V, g ∈ H0 ↔ g ∈ orthDerived Q ∧ g * xe = xe * g := by
    intro g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      have h1 : x * c * x⁻¹ = c := hc
      have h2 : x * c = c * x := (mul_inv_eq_iff_eq_mul.mp h1)
      exact (congrArg Subtype.val h2).symm
    · rintro ⟨hgΩ, hgx⟩
      refine ⟨⟨g, hgΩ⟩, ?_, rfl⟩
      change x * ⟨g, hgΩ⟩ * x⁻¹ = ⟨g, hgΩ⟩
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext hgx.symm
  have hH0M : H0 ≤ isometryCentralizer Q xe := by
    intro g hg
    obtain ⟨hgΩ, hgx⟩ := (hmem g).1 hg
    exact Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hgΩ,
      Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
  have hnorm : (H0.subgroupOf (isometryCentralizer Q xe)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH0M]
    intro h m hh hm
    obtain ⟨hhΩ, hhx⟩ := (hmem h).1 hh
    have hmO : m ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hm).1
    have hmx : Commute m xe := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm).2
    rw [hmem]
    refine ⟨conj_mem_orthDerived_of_mem_orthogonalGroup hmO hhΩ, ?_⟩
    exact (((hmx.mul_left (show Commute h xe from hhx)).mul_left hmx.inv_left)).eq
  let eH : ↥(fixedSubgroup (MulAut.conj x)) ≃* ↥H0 :=
    (fixedSubgroup (MulAut.conj x)).equivMapOfInjective (orthDerived Q).subtype
      (orthDerived Q).subtype_injective
  have hM₁ : CFSG.IsComponent (M₀.map eH.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv eH hM₀
  obtain ⟨L, hLM, hLc, ⟨e⟩⟩ := exists_isComponent_of_normal hH0M hnorm hM₁
  have hOdd : OddLieCentralQuotient ℓ ↥L :=
    oddLie_isometryCentralizer hx hp2 hℓ hℓ2 hf hK hLM hLc
  let eM := M₀.equivMapOfInjective eH.toMonoidHom eH.injective
  exact oddLieCentralQuotient_of_centerQuotient_equiv
    ((QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans e) hOdd

theorem oddLie_component_projOrth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {a : ProjOrthDerived Q} (ha : orderOf a = 3) {I : Subgroup (ProjOrthDerived Q)}
    (hI : CFSG.Open.IsComponentOf I (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    OddLieCentralQuotient ℓ ↥I := by
  obtain ⟨-, hcenter, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift 3 Nat.prime_three (by norm_num) a ha
  have hring : ringChar K = ℓ := ringChar_eq_of_card_eq hℓ hf hK
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [hring]; exact hℓ3.symm) hQ x
    hxp
  have hcentral : (scalars K V).subgroupOf (orthDerived Q) ≤ Subgroup.center ↥(orthDerived Q) :=
    hcenter.symm.le
  have hI' : CFSG.Open.IsComponentOf I
      (Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q))) := by
    rw [hxa]
    exact hI
  obtain ⟨M₀, hM₀, ⟨e⟩⟩ := exists_component_of_isComponentOf_centralizer
    ((scalars K V).subgroupOf (orthDerived Q)) hcentral x hI'
  exact oddLieCentralQuotient_of_centerQuotient_equiv e
    (oddLie_of_component_fixed hx (by decide : Odd 3) hℓ hℓ2 hf hK hM₀)

end Orthogonal

end CFSG.HardMathSupport.Dickson.Sec6.SsOrth
