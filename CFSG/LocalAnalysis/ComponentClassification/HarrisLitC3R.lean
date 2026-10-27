module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3Q
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3B
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUi
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut StabU DiagU OIU CFSG.Assembly.LowTwoRank

section Via

variable {P D : Type*} [Group P] [Group D] {ι : P →* D}

@[expose] def conjVia (hι : Function.Injective ι) (hN : ι.range.Normal) (d : D) : MulAut P :=
  ((MonoidHom.ofInjective hι).trans (@MulAut.conjNormal D _ ι.range hN d)).trans
    (MonoidHom.ofInjective hι).symm

theorem conjVia_apply (hι : Function.Injective ι) (hN : ι.range.Normal) (d : D) (y : P) :
    ι (conjVia hι hN d y) = d * ι y * d⁻¹ := by
  simp only [conjVia, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

end Via

theorem false_of_swap_gen {X : Type*} [Group X] {φ γ : MulAut X} (hγφ : γ * φ = φ * γ)
    {J' : Subgroup X} (hJφ : J' ≤ OutInv.fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (OutInv.fixSub φ)))
    (huniq : ∀ R : Subgroup X, R ≤ OutInv.fixSub φ →
      IsComponent (R.subgroupOf (OutInv.fixSub φ)) → R ≤ J')
    (hJna : ∃ a b : ↥J', a * b ≠ b * a) (hcomm : ∀ a ∈ J', ∀ b ∈ J', γ a * b = b * γ a) :
    False := by
  obtain ⟨hle, hc⟩ := isComponent_map_of_commute hγφ hJφ hJ
  have hJJ := huniq _ hle hc
  obtain ⟨a, b, hab⟩ := hJna
  apply hab
  apply Subtype.ext
  apply γ.injective
  have hγb : γ b ∈ J' := hJJ ⟨b, b.2, rfl⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact hcomm _ a.2 _ hγb

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem anti_case (hp2 : p ≠ 2) {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hφ2 : φ ^ 2 = 1) (hφ : φ ∉ InnU p f K h) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJφ : J' ≤ OutInv.fixSub φ) (hJ : IsComponent (J'.subgroupOf (OutInv.fixSub φ)))
    (huniq : ∀ R : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)), R ≤ OutInv.fixSub φ →
      IsComponent (R.subgroupOf (OutInv.fixSub φ)) → R ≤ J')
    {m : ℕ} (hJm : Blueprint.LieModel ↥J' .PSL 2 p m) :
    m = 2 * f ∧ SelectorRowOU h φ J' := by
  classical
  have : Finite K := h.finite
  obtain ⟨-, hJna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hJm
  have : IsSimpleGroup ↥J' := (GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hJm).1
  have hJZ : center ↥J' = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hJna
  let eJ : ↥J' ⧸ center ↥J' ≃* ↥J' :=
    (QuotientGroup.quotientMulEquivOfEq hJZ).trans QuotientGroup.quotientBot
  have hJm' : Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hJm
  obtain ⟨A, ψ, hAu, hψ, hψA, c, hAA⟩ := exists_anti_form h hp2 hφ2 hφ
  obtain ⟨Y, hY, σY, hσs, hσk, hσv⟩ := exists_lift_component h hAu hψ hψA hAA hJφ hJ
  let eJX : ↥J' ≃* ↥(J'.map (GSThmB.Catalog7L4EU.ιU h)) :=
    J'.equivMapOfInjective _ (GSThmB.Catalog7L4EU.ιU_injective h)
  have hXm : Blueprint.LieModel (↥(J'.map (GSThmB.Catalog7L4EU.ιU h)) ⧸
      center ↥(J'.map (GSThmB.Catalog7L4EU.ιU h))) .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (GSThmB.Catalog7L4EU.centerQuotientCongr eJX) hJm'
  obtain ⟨-, hcase⟩ := anti_dichotomy h hp2 hAu hAA hY σY hσs hσk hXm
  rcases hcase with ⟨T, hT, hTc⟩ | ⟨E', _, _, hE', ⟨eP⟩⟩
  ·
    exfalso
    have hN := GSThmB.Catalog7L4EU.ιU_range_normal h
    have hι := GSThmB.Catalog7L4EU.ιU_injective h
    have hτ := StabU.antiunitaryMap_bijective h A
    have hτB := StabU.stdHermForm_antiunitaryMap h hAu
    have he : ∀ y, GSThmB.Catalog7L4EU.ιU h (φ y) =
        antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) hτ hτB
          (GSThmB.Catalog7L4EU.ιU h y) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hψ, GSThmB.Catalog7L4EU.ιU_mk, GSThmB.Catalog7L4EU.ιU_mk, antiProjConj_mk]
      congr 1
      exact (GSThmB.Catalog7L4EU.toSesqUnitary_antiConj h hAu g (ψ g) (hψA g)).symm
    set d : sesqProjUnitary h (stdHermForm h 4) := QuotientGroup.mk T with hd
    have hαd : antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) hτ hτB d = d := by
      rw [hd, antiProjConj_mk]
      exact congrArg QuotientGroup.mk hT
    set γ := conjVia hι hN d with hγdef
    have hγ : ∀ y, GSThmB.Catalog7L4EU.ιU h (γ y) = d * GSThmB.Catalog7L4EU.ιU h y * d⁻¹ :=
      fun y => conjVia_apply hι hN d y
    have hγφ : γ * φ = φ * γ := by
      apply MulEquiv.ext
      intro y
      apply hι
      rw [MulAut.mul_apply, MulAut.mul_apply, hγ, he, he, hγ, map_mul, map_mul, map_inv, hαd]
    have hmk : ∀ a ∈ J', ∃ y ∈ Y, GSThmB.Catalog7L4EU.ιU h a = QuotientGroup.mk y := by
      intro a ha
      obtain ⟨y, hy⟩ := hσs ⟨GSThmB.Catalog7L4EU.ιU h a, ⟨a, ha, rfl⟩⟩
      refine ⟨y, y.2, ?_⟩
      have h1 := hσv y
      rw [hy] at h1
      exact h1
    have hcomm : ∀ a ∈ J', ∀ b ∈ J', γ a * b = b * γ a := by
      intro a ha b hb
      apply hι
      obtain ⟨y₁, hy₁, e₁⟩ := hmk a ha
      obtain ⟨y₂, hy₂, e₂⟩ := hmk b hb
      have h1 := congrArg (QuotientGroup.mk (s := sesqNormOneScalars h (stdHermForm h 4)))
        (hTc y₁ hy₁ y₂ hy₂)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      rw [map_mul, map_mul, hγ, e₁, e₂, hd]
      exact h1
    exact false_of_swap_gen hγφ hJφ hJ huniq hJna hcomm
  ·
    have hE'odd : Odd (Nat.card E') := by
      rw [hE', h.card_fixedField]
      exact ((h.prime.odd_of_ne_two hp2).pow).pow
    have hpm := GSThmB.Catalog7L4EU.eq_card_of_quotient_psl2 h.prime hp2 hXm hE'odd eP
    rw [hE', h.card_fixedField, ← pow_mul] at hpm
    have hm : m = 2 * f := by
      have := Nat.pow_right_injective h.prime.two_le hpm
      omega
    subst hm
    exact ⟨rfl, selectorRowOU_of_component h hp2 hφ2 hφ hJφ hJ hJm'⟩

end CFSG.ComponentClassification.HarrisLit.C3
