module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeCosetPoints

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal.SmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model

section Entrywise

variable {τ : Tag} {K : Type} [Field K] (σ : K →+* K)

theorem entrywiseGL_weylElt_one (i : Fin τ.rank) :
    entrywiseGL τ K σ (weylElt τ K i 1) = weylElt τ K i 1 := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, entrywiseGL_xUnit, entrywiseGL_yUnit]
  simp

theorem entrywiseGL_pinnedWeyl (α : Fin τ.rank → ℤ) :
    entrywiseGL τ K σ (pinnedWeyl τ K α) = pinnedWeyl τ K α := by
  simp only [pinnedWeyl, map_list_prod, List.map_reverse, List.map_map, Function.comp_def,
    entrywiseGL_weylElt_one]

theorem entrywiseGL_pinnedX (α : Fin τ.rank → ℤ) (c : K) :
    entrywiseGL τ K σ (pinnedX τ K α c) = pinnedX τ K α (σ c) := by
  simp only [pinnedX, map_mul, map_inv, entrywiseGL_pinnedWeyl, entrywiseGL_xUnit, map_zsmul]

theorem entrywiseGL_canonicalRep (w : WeylGroup τ) :
    entrywiseGL τ K σ (canonicalRep (coxeterSystem τ) K w) =
      canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  simp only [Function.comp_def, entrywiseGL_weylElt_one]

end Entrywise

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [Finite K] in
theorem entrywiseGL_frobenius_smallReeU (t b c : K) :
    entrywiseGL ReeTag.G2.tag K (frobenius K ReeTag.G2.prime) (smallReeU a K t b c) =
      smallReeU a K (t ^ 3) (b ^ 3) (c ^ 3) := by
  have h3 : ∀ x : K, frobenius K ReeTag.G2.prime x = x ^ 3 := fun x =>
    frobenius_def ReeTag.G2.prime x
  have hσ : ∀ x : K, frobenius K ReeTag.G2.prime (smallReeSigma a x) =
      smallReeSigma a (x ^ 3) := by
    intro x
    rw [h3, smallReeSigma, smallReeSigma, ← pow_mul, ← pow_mul, mul_comm]
  have e4 : frobenius K ReeTag.G2.prime (smallReeSigma a b - t ^ 3 * smallReeSigma a t) =
      smallReeSigma a (b ^ 3) - (t ^ 3) ^ 3 * smallReeSigma a (t ^ 3) := by
    rw [map_sub, map_mul, map_pow, hσ, hσ, h3]
  have e5 : frobenius K ReeTag.G2.prime (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2) =
      smallReeSigma a (c ^ 3) - (t ^ 3) ^ 3 * smallReeSigma a (t ^ 3) ^ 2 := by
    rw [map_sub, map_mul, map_pow, map_pow, hσ, hσ, h3]
  change entrywiseGL Tag.G2 K (frobenius K ReeTag.G2.prime) (smallReeCoord a K t b c) =
    smallReeCoord a K (t ^ 3) (b ^ 3) (c ^ 3)
  simp only [smallReeCoord, smallReeX, map_mul, entrywiseGL_pinnedX]
  rw [e4, e5, hσ, h3, h3, h3]

theorem finiteFrobeniusAut_mul_finiteExceptionalAut :
    ReeTag.G2.finiteFrobeniusAut K * ReeTag.G2.finiteExceptionalAut K =
      ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K := by
  apply MulEquiv.ext
  intro g
  have h := adjointGroup_hom_ext
    (f := (ReeTag.G2.finiteFrobeniusAut K * ReeTag.G2.finiteExceptionalAut K).toMonoidHom)
    (g := (ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K).toMonoidHom)
    (fun i c => by
      change ReeTag.G2.finiteFrobeniusAut K (ReeTag.G2.finiteExceptionalAut K (xElement i c)) =
        ReeTag.G2.finiteExceptionalAut K (ReeTag.G2.finiteFrobeniusAut K (xElement i c))
      have e1 := ReeTag.finiteFrobeniusAut_pow_xElement (K := K) (t := ReeTag.G2) 1
      simp only [pow_one] at e1
      rw [ReeTag.finiteExceptionalAut_xElement, e1, e1, ReeTag.finiteExceptionalAut_xElement,
        ← pow_mul, ← pow_mul, mul_comm])
    (fun i c => by
      change ReeTag.G2.finiteFrobeniusAut K (ReeTag.G2.finiteExceptionalAut K (yElement i c)) =
        ReeTag.G2.finiteExceptionalAut K (ReeTag.G2.finiteFrobeniusAut K (yElement i c))
      have e1 := ReeTag.finiteFrobeniusAut_pow_yElement (K := K) (t := ReeTag.G2) 1
      simp only [pow_one] at e1
      rw [ReeTag.finiteExceptionalAut_yElement, e1, e1, ReeTag.finiteExceptionalAut_yElement,
        ← pow_mul, ← pow_mul, mul_comm])
  exact DFunLike.congr_fun h g

theorem finiteFrobeniusAut_mul_finiteReeAut :
    ReeTag.G2.finiteFrobeniusAut K * ReeTag.G2.finiteReeAut K a =
      ReeTag.G2.finiteReeAut K a * ReeTag.G2.finiteFrobeniusAut K := by
  rw [ReeTag.finiteReeAut, ← mul_assoc, finiteFrobeniusAut_mul_finiteExceptionalAut, mul_assoc,
    mul_assoc, ← pow_succ', ← pow_succ]

theorem entrywiseGL_frobenius_mem_reeGamma {g : ModGL ReeTag.G2.tag K}
    (hg : g ∈ ReeTag.G2.reeGamma K a) :
    entrywiseGL ReeTag.G2.tag K (frobenius K ReeTag.G2.prime) g ∈ ReeTag.G2.reeGamma K a := by
  obtain ⟨hgC, hF⟩ := ReeTag.mem_reeGamma.1 hg
  refine ReeTag.mem_reeGamma.2 ⟨(ReeTag.G2.finiteFrobeniusAut K ⟨g, hgC⟩).2, ?_⟩
  have h1 := congrArg (fun φ : MulAut (adjointGroup ReeTag.G2.tag K) => φ ⟨g, hgC⟩)
    (finiteFrobeniusAut_mul_finiteReeAut (K := K) (a := a))
  simp only [MulAut.mul_apply, hF] at h1
  exact h1.symm

@[expose] def frobeniusHomΓ : ReeTag.G2.reeGamma K a →* ReeTag.G2.reeGamma K a :=
  ((entrywiseGL ReeTag.G2.tag K (frobenius K ReeTag.G2.prime)).comp
    (ReeTag.G2.reeGamma K a).subtype).codRestrict (ReeTag.G2.reeGamma K a)
      fun g => entrywiseGL_frobenius_mem_reeGamma g.2

theorem coe_frobeniusHomΓ (g : ReeTag.G2.reeGamma K a) :
    ((frobeniusHomΓ g : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
      entrywiseGL ReeTag.G2.tag K (frobenius K ReeTag.G2.prime) g :=
  rfl

theorem frobeniusHomΓ_injective :
    Function.Injective (frobeniusHomΓ : ReeTag.G2.reeGamma K a →* ReeTag.G2.reeGamma K a) :=
  fun _ _ h => Subtype.ext (entrywiseGL_injective _ (congrArg Subtype.val h))

@[expose] def frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a) :=
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  MulEquiv.ofBijective frobeniusHomΓ frobeniusHomΓ_injective.bijective_of_finite

theorem coe_frobeniusΓ (g : ReeTag.G2.reeGamma K a) :
    ((frobeniusΓ g : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
      entrywiseGL ReeTag.G2.tag K (frobenius K ReeTag.G2.prime) g :=
  rfl

theorem coe_frobeniusΓ_pow (k : ℕ) (g : ReeTag.G2.reeGamma K a)
    (hg : (g : ModGL ReeTag.G2.tag K) ∈ adjointGroup ReeTag.G2.tag K) :
    (((frobeniusΓ ^ k) g : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
      ((ReeTag.G2.finiteFrobeniusAut K ^ k) ⟨g, hg⟩ : ModGL ReeTag.G2.tag K) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, coe_frobeniusΓ, ih, pow_succ', MulAut.mul_apply,
      ReeTag.coe_finiteFrobeniusAut]

theorem frobeniusΓ_pow (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ (2 * a + 1) = 1 := by
  have hpow : ∀ c : K, c ^ ReeTag.G2.prime ^ (2 * a + 1) = c := fun c => by
    have := Fintype.ofFinite K
    change c ^ 3 ^ (2 * a + 1) = c
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ (2 * a + 1) = 1 := by
    apply MulEquiv.ext
    intro g
    have h := adjointGroup_hom_ext
      (f := (ReeTag.G2.finiteFrobeniusAut K ^ (2 * a + 1)).toMonoidHom)
      (g := (1 : MulAut (adjointGroup ReeTag.G2.tag K)).toMonoidHom)
      (fun i c => by
        change (ReeTag.G2.finiteFrobeniusAut K ^ (2 * a + 1)) (xElement i c) = xElement i c
        rw [ReeTag.finiteFrobeniusAut_pow_xElement, hpow])
      (fun i c => by
        change (ReeTag.G2.finiteFrobeniusAut K ^ (2 * a + 1)) (yElement i c) = yElement i c
        rw [ReeTag.finiteFrobeniusAut_pow_yElement, hpow])
    exact DFunLike.congr_fun h g
  apply MulEquiv.ext
  intro g
  obtain ⟨hgC, -⟩ := ReeTag.mem_reeGamma.1 g.2
  apply Subtype.ext
  rw [coe_frobeniusΓ_pow _ g hgC, hFr]
  rfl

theorem coe_frobeniusΓ_of_eq_smallReeU {u : ReeTag.G2.reeGamma K a} {t b c : K}
    (hu : (u : ModGL ReeTag.G2.tag K) = smallReeU a K t b c) :
    ((frobeniusΓ u : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
      smallReeU a K (t ^ 3) (b ^ 3) (c ^ 3) := by
  rw [coe_frobeniusΓ, hu, entrywiseGL_frobenius_smallReeU]

theorem frobeniusΓ_longestIn {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀) :
    frobeniusΓ (longestIn a K hw₀) = longestIn a K hw₀ := by
  apply Subtype.ext
  rw [coe_frobeniusΓ]
  exact entrywiseGL_canonicalRep _ w₀

end CFSG.ComponentClassification.LiteratureLocal.SmallRee
