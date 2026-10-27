module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Main
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Abs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Alg
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42A5

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Torus

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {M₁ M₂ S V : Subgroup G}

theorem CaseB.exists_torus (c : CaseB A R t) (F : c.Factors M₁ M₂) (P : Prod2 M₁ M₂ S V t)
    {k : Type} [Field k] (hk : Nat.card k = 4) (e : ↥(S ⊓ M₁) ≃* ↥(unipAll k))
    (hW : ∀ a : ↥(S ⊓ M₁), (a : G) ∈ c.W ↔ e a ∈ radOne k) :
    ∃ x : G, x ∈ M₁ ∧ Odd (orderOf x) ∧ x ∉ centralizer (c.W : Set G) ∧
      x ^ 3 ∈ centralizer (c.W : Set G) ∧ (∀ a ∈ S ⊓ M₁, x * a * x⁻¹ ∈ S ⊓ M₁) ∧
      ∃ μ : k, μ ≠ 0 ∧ μ ≠ 1 ∧ ∀ a a' : ↥(S ⊓ M₁), (a' : G) = x * a * x⁻¹ →
        coordA (e a') = μ * coordA (e a) ∧ coordB (e a') = μ * coordB (e a) := by
  have := charP_two_of_card_four_B42 hk
  obtain ⟨π, hπs, hπk⟩ := F.a5₁
  obtain ⟨Q, hQ⟩ := P.sylow₁.exists_sylow_eq_subgroupOf
  obtain ⟨y, hyN, hyodd, hyord⟩ := exists_borel_elt π hπs Q
  set x : G := (y : G) with hx
  have hxM : x ∈ M₁ := y.2
  have hxodd : Odd (orderOf x) := by rw [hx, Subgroup.orderOf_coe]; exact hyodd
  have hπy1 : π y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  have hπy3 : (π y) ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one _
  have hx1 : x ∉ centralizer (c.W : Set G) := fun h => hπy1 ((hπk y).mpr h)
  have hx3 : x ^ 3 ∈ centralizer (c.W : Set G) := by
    have : π (y ^ 3) = 1 := by rw [map_pow, hπy3]
    have h2 := (hπk (y ^ 3)).mp this
    simpa [hx] using h2
  have hxA : ∀ a ∈ S ⊓ M₁, x * a * x⁻¹ ∈ S ⊓ M₁ := by
    intro a ha
    have haQ : (⟨a, ha.2⟩ : ↥M₁) ∈ (Q : Subgroup ↥M₁) := by
      rw [hQ]; exact mem_subgroupOf.mpr ha
    have h1 := (mem_normalizer_iff.mp hyN _).mp haQ
    rw [hQ] at h1
    exact mem_subgroupOf.mp h1
  have hxn : x ∈ normalizer ((S ⊓ M₁ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun a ha => hxA a ha
  let φ : ↥(normalizer ((S ⊓ M₁ : Subgroup G) : Set G)) →* MulAut (unipAll k) :=
    (MulAut.congr e).toMonoidHom.comp (S ⊓ M₁).normalizerMonoidHom
  let α : MulAut (unipAll k) := φ ⟨x, hxn⟩
  have hαapp : ∀ a : ↥(S ⊓ M₁), α (e a) = e ⟨x * a * x⁻¹, hxA a a.2⟩ := by
    intro a
    have h1 : α (e a) = e (((S ⊓ M₁).normalizerMonoidHom ⟨x, hxn⟩) (e.symm (e a))) := rfl
    rw [h1, MulEquiv.symm_apply_apply]
    rfl
  have hαn : α ^ orderOf x = 1 := by
    have h1 : (⟨x, hxn⟩ : ↥(normalizer ((S ⊓ M₁ : Subgroup G) : Set G))) ^ orderOf x = 1 :=
      Subtype.ext (pow_orderOf_eq_one x)
    show φ ⟨x, hxn⟩ ^ orderOf x = 1
    rw [← map_pow, h1, map_one]
  have hF₁ : ∀ g ∈ radOne k, α g = g → g = 1 := by
    intro g hg hfix
    set a : ↥(S ⊓ M₁) := e.symm g with ha
    have hea : e a = g := by rw [ha, MulEquiv.apply_symm_apply]
    have haW : (a : G) ∈ c.W := (hW a).mpr (by rw [hea]; exact hg)
    have hfix' : e ⟨x * a * x⁻¹, hxA a a.2⟩ = e a := by rw [← hαapp, hea]; exact hfix
    have hconj : x * (a : G) * x⁻¹ = a := congrArg Subtype.val (e.injective hfix')
    have h1 := F.fpf₁ x hxM hx1 hx3 a ⟨haW, a.2.2⟩ hconj
    have ha1 : a = 1 := Subtype.ext h1
    rw [← hea, ha1, map_one]
  have hF₂ : ∃ g : unipAll k, coordB (α g) ≠ coordB g := by
    by_contra hno
    push Not at hno
    set a₀ : ↥(S ⊓ M₁) := e.symm (uelt 0 1 0) with ha₀
    have hea₀ : e a₀ = uelt 0 1 0 := by rw [ha₀, MulEquiv.apply_symm_apply]
    have ha₀sq : a₀ * a₀ = 1 := by
      apply e.injective
      rw [map_mul, hea₀, uelt_mul_self, map_one]
      simp
    have ha₀G : (a₀ : G) * (a₀ : G) = 1 := congrArg Subtype.val ha₀sq
    have ha₀W : (a₀ : G) ∉ c.W := by
      intro h
      have := (hW a₀).mp h
      rw [hea₀, mem_radOne, coordB_uelt] at this
      exact one_ne_zero this
    have ha₀K : (a₀ : G) ∉ centralizer (c.W : Set G) := by
      intro hK
      apply ha₀W
      refine F.two_elem _ hK ?_
      have hdvd : orderOf (a₀ : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha₀G)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact ⟨0, by rw [h1]; rfl⟩
      · exact ⟨1, by rw [h1]; rfl⟩
    set ya : ↥M₁ := ⟨(a₀ : G), a₀.2.2⟩ with hya
    have hya1 : π ya ≠ 1 := fun h => ha₀K ((hπk ya).mp h)
    have hyasq : π ya * π ya = 1 := by
      rw [← map_mul]
      have : ya * ya = 1 := Subtype.ext ha₀G
      rw [this, map_one]
    have hcoordB : coordB (e ⟨x * a₀ * x⁻¹, hxA a₀ a₀.2⟩ * (e a₀)⁻¹) = 0 := by
      rw [coordB_mul, coordB_inv, ← hαapp, hno (e a₀)]
      ring
    have hcomW : (⟨x * a₀ * x⁻¹, hxA a₀ a₀.2⟩ * a₀⁻¹ : ↥(S ⊓ M₁)).1 ∈ c.W := by
      refine (hW _).mpr ?_
      rw [map_mul, map_inv, mem_radOne]
      exact hcoordB
    have hcomK : x * (a₀ : G) * x⁻¹ * (a₀ : G)⁻¹ ∈ centralizer (c.W : Set G) := by
      have hcomW' : x * (a₀ : G) * x⁻¹ * (a₀ : G)⁻¹ ∈ c.W := hcomW
      refine mem_centralizer_iff.mpr fun h hh => ?_
      exact L34.comm_of_isElemAbelian c.W_elem hh hcomW'
    have hker : π (y * ya * y⁻¹ * ya⁻¹) = 1 := by
      rw [hπk]
      simpa [hx, hya] using hcomK
    have hcomm : π y * π ya = π ya * π y := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hker
      calc π y * π ya = π y * π ya * (π y)⁻¹ * (π ya)⁻¹ * (π ya * π y) := by group
        _ = π ya * π y := by rw [hker, one_mul]
    exact a5_no_order_six (π ya) (π y) hyasq hya1 hπy3 hπy1 hcomm.symm
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_scalar_of_odd hk hxodd hαn hF₁ hF₂
  refine ⟨x, hxM, hxodd, hx1, hx3, hxA, μ, hμ0, hμ1, fun a a' ha' => ?_⟩
  have h1 : a' = ⟨x * a * x⁻¹, hxA a a.2⟩ := Subtype.ext ha'
  have h2 : e a' = α (e a) := by rw [h1, hαapp]
  rw [h2]
  exact hμ (e a)

end Torus

end CFSG.OddStandard.Seitz77
