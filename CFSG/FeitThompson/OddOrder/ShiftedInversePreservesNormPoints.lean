module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.OddOrder.PrimeLineFactorsProductOne
import CFSG.FeitThompson.OddOrder.AffineFieldCentralizers
import CFSG.FeitThompson.OddOrder.MiddleFactorIsInverse
import CFSG.FeitThompson.OddOrder.MobiusNormIteration
import CFSG.FeitThompson.OddOrder.ModuleCancellationWord
import CFSG.FeitThompson.OddOrder.DoubleCosetNormalForm
import CFSG.FeitThompson.OddOrder.ComparisonUnitsVanish

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {p q m : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

private theorem conj_mem_of_mem_normalizer {U : Subgroup G} {g : G}
    (hg : g ∈ normalizer (U : Set G)) {x : G} (hx : x ∈ U) : g⁻¹ * x * g ∈ U :=
  ((Subgroup.mem_set_normalizer_iff'' (S := (U : Set G)) (g := g)).1 hg x).1 hx

private theorem exists_normalForm_of_mem_sup (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {g : G} (hg : g ∈ P ⊔ U) :
    ∃ (u v : normOneUnits F) (c : F), c ∈ (⊥ : Subfield F) ∧
      g = (Ue u : G) * (Pe (ofAdd c) : G) * (Ue v : G) := by
  have hP := range_subtype_comp Pe
  have hU := range_subtype_comp Ue
  rw [← hP, ← hU] at hg
  obtain ⟨x, hx, r, hr, z, hz, hEq⟩ := exists_mul_primeLine_mul hp hcard hcop
    (Pe := P.subtype.comp Pe.toMonoidHom) (Ue := U.subtype.comp Ue.toMonoidHom) hact hg
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hz
  obtain ⟨c, hc, rfl⟩ := mem_primeLine.1 hr
  exact ⟨u, v, c, hc, hEq⟩

private theorem eq_inv_s_of_word_eq (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    [Finite G] [Finite F] (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {P₀ P₁ Q : Subgroup G}
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) (hyc : y ∈ ⁅Q, P₀⁆)
    {r₁ r₂ r₃ : G} {c₁ c₂ c₃ : F}
    (hc₁ : c₁ ∈ (⊥ : Subfield F)) (hc₂ : c₂ ∈ (⊥ : Subfield F)) (hc₃ : c₃ ∈ (⊥ : Subfield F))
    (hr₁ : r₁ = (Pe (ofAdd c₁) : G)) (hr₂ : r₂ = (Pe (ofAdd c₂) : G))
    (hr₃ : r₃ = (Pe (ofAdd c₃) : G)) (hr₁1 : r₁ ≠ 1)
    (hword : t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁) :
    r₁ = s⁻¹ := by
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ q := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hQcomm : IsMulCommutative ↥Q := isMulCommutative_iff_of_setLike.2 hQab
  have hPev : ∀ z, (P.subtype.comp Pe.toMonoidHom) z = (Pe z : G) := fun _ => rfl
  have hprod : r₁ * r₂ * r₃ = 1 := by
    have h := mul_mul_eq_one_of_conj_word_eq_primeSubfield hp hcardF
      (P.subtype.comp Pe.toMonoidHom) (P.subtype_injective.comp Pe.injective) (Q := Q)
      hQp (fun z hz => hQnorm (by rw [hP₀]; exact apply_ofAdd_mem_primeLine _ hz)) hy
      (t := t) (by rw [hPev, ← hs]; exact ht)
      hc₁ hc₂ hc₃ (by simp only [hPev]; rw [← hr₁, ← hr₂, ← hr₃]; exact hword)
    simp only [hPev] at h
    rw [hr₁, hr₂, hr₃]
    exact h
  set S := appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact with hS
  have hSs : S.s = s := by
    rw [AppendixCSetup.s_def, hS, appendixCSetupOfMulEquiv_pt, hs]; rfl
  have hSU : S.U = U := appendixCSetupOfMulEquiv_U
  have hSP₀ : S.P₀ = P₀ := by rw [hS, appendixCSetupOfMulEquiv_P₀, hP₀]
  have hr₁P₀ : r₁ ∈ P₀ := by rw [hP₀, hr₁]; exact apply_ofAdd_mem_primeLine _ hc₁
  have hr₂P₀ : r₂ ∈ P₀ := by rw [hP₀, hr₂]; exact apply_ofAdd_mem_primeLine _ hc₂
  have hr₃P₀ : r₃ ∈ P₀ := by rw [hP₀, hr₃]; exact apply_ofAdd_mem_primeLine _ hc₃
  have hshort := mul_inv_eq_inv_mul_of_word_relation S hQp (by rw [hSP₀]; exact hQnorm) hy
    (by rw [hSP₀, hSU, ← hP₁]; exact hP₁U) (by rw [hSP₀]; exact hyc)
    (hSP₀ ▸ hr₁P₀) (hSP₀ ▸ hr₂P₀) (hSP₀ ▸ hr₃P₀) (t := t) (t₁ := y⁻¹ * r₁ * y)
    (t₃ := y⁻¹ * r₃ * y) (by rw [hSs]; exact ht) rfl rfl hword hprod
  have hkey := S.eq_inv_s_of_mul_inv_eq hQp (by rw [hSP₀]; exact hQnorm) hy
    (by rw [hSP₀, hSU, ← hP₁]; exact hP₁U) (hSP₀ ▸ hr₁P₀) (hSP₀ ▸ hr₃P₀) hr₁1
    (by rw [hSs, ← ht]; exact hshort)
  rw [hkey, hSs]

theorem mem_normOneShiftSet_of_eq_shiftedInv [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) (hyc : y ∈ ⁅Q, P₀⁆)
    {a A : normOneUnits F} (ha : ((a : Fˣ) : F) ∈ normOneShiftSet F m)
    (hA : (Ue A : G) = shiftedInv t (Ue a : G)) :
    ((A : Fˣ) : F) ∈ normOneShiftSet F m := by
  rw [mem_normOneShiftSet] at ha
  have hcop' : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := hm ▸ hcop
  have hm0 : m ≠ 0 := hm ▸ ne_zero_of_eq_div hp hq.pos rfl
  have hfin : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have h2a : (2 : F) - ((a : Fˣ) : F) ≠ 0 := by
    intro h
    rw [h] at ha
    simpa [hm0] using ha.2
  have hbmem : Units.mk0 _ h2a ∈ normOneUnits F := by
    rw [mem_normOneUnits_iff_pow_eq_one hp hcard, ← hm]
    simpa using ha.2
  set b : normOneUnits F := ⟨Units.mk0 _ h2a, hbmem⟩ with hbdef
  have hbval : ((b : Fˣ) : F) = 2 - ((a : Fˣ) : F) := rfl
  have hab : ((a : Fˣ) : F) + ((b : Fˣ) : F) = 2 := by rw [hbval]; ring
  have hsP₀ : s ∈ P₀ := by rw [hP₀, hs]; exact apply_ofAdd_mem_primeLine _ (one_mem _)
  have htP₁ : t ∈ P₁ := by rw [hP₁, ht]; exact ⟨s, hsP₀, by simp [MulAut.conj]⟩
  have htU : t ∈ normalizer (U : Set G) := hP₁U htP₁
  have hsH : s ∈ P ⊔ U := le_sup_left (α := Subgroup G) (by rw [hs]; exact (Pe _).2)
  have hUH : ∀ x ∈ U, x ∈ P ⊔ U := fun x hx => le_sup_right (α := Subgroup G) hx
  have hconjt : ∀ (n : ℕ) (x : G), x ∈ U → (t ^ n)⁻¹ * x * t ^ n ∈ U :=
    fun n x hx => conj_mem_of_mem_normalizer (pow_mem htU n) hx
  have hW₁ : s * ((t ^ 3)⁻¹ * (Ue a : G)⁻¹ * t ^ 3) * (s ^ 2)⁻¹ ∈ P ⊔ U :=
    mul_mem (mul_mem hsH (hUH _ (hconjt 3 _ (inv_mem (Ue a).2)))) (inv_mem (pow_mem hsH 2))
  have hW₂ : s ^ 3 * ((t ^ 2)⁻¹ * ((Ue a : G) * (Ue b : G)⁻¹) * t ^ 2) * s⁻¹ ∈ P ⊔ U :=
    mul_mem (mul_mem (pow_mem hsH 3)
      (hUH _ (hconjt 2 _ (mul_mem (Ue a).2 (inv_mem (Ue b).2))))) (inv_mem hsH)
  have hW₃ : s ^ 2 * (t⁻¹ * (Ue b : G) * t) * (s ^ 3)⁻¹ ∈ P ⊔ U := by
    refine mul_mem (mul_mem (pow_mem hsH 2) (hUH _ ?_)) (inv_mem (pow_mem hsH 3))
    simpa using hconjt 1 _ (Ue b).2
  obtain ⟨u₁, v₁, c₁, hc₁, h₁⟩ := exists_normalForm_of_mem_sup hp hcard hcop' Pe Ue hact hW₁
  obtain ⟨u₂, v₂, c₂, hc₂, h₂⟩ := exists_normalForm_of_mem_sup hp hcard hcop' Pe Ue hact hW₂
  obtain ⟨u₃, v₃, c₃, hc₃, h₃⟩ := exists_normalForm_of_mem_sup hp hcard hcop' Pe Ue hact hW₃
  have hUeinv : (Ue a⁻¹ : G) = (Ue a : G)⁻¹ := by rw [map_inv, Subgroup.coe_inv]
  have heq₁ : s ^ (1 : ℤ) * ((t ^ (3 : ℤ))⁻¹ * (Ue a⁻¹ : G) * t ^ (3 : ℤ)) * s ^ (-(2 : ℤ))
      = (Ue u₁ : G) * (Pe (ofAdd c₁) : G) * (Ue v₁ : G) := by
    rw [hUeinv]; simpa using h₁
  have hco := coord_eq_and_apply_ofAdd_ne_one_of_mul_mul_eq hp hq hqp hcard hcop' Pe Ue hPU hact
    (H := H) (P₁ := P₁) (Q := Q) hH hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht hc₁ heq₁
  have hr₁1 : (Pe (ofAdd c₁) : G) ≠ 1 :=
    hco.2.2 (not_intModEq_of_sub_eq_neg_one hp (by norm_num))
  have hcw := comparison_units_eq_one_and_word_eq hp hq hqp hcard hcop' Pe Ue hPU hact
    (H := H) (P₀ := P₀) (P₁ := P₁) (Q := Q) hH hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht hyc
    hab hc₁ hc₂ hc₃ (r₁ := (Pe (ofAdd c₁) : G)) (r₂ := (Pe (ofAdd c₂) : G))
    (r₃ := (Pe (ofAdd c₃) : G)) rfl rfl rfl h₁ h₂ h₃ rfl rfl rfl
  have hr₁s : (Pe (ofAdd c₁) : G) = s⁻¹ :=
    eq_inv_s_of_word_eq hp hq hqp hcard hcop' Pe Ue hPU hact hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U
      ht hyc hc₁ hc₂ hc₃ rfl rfl rfl hr₁1 hcw.2.2.2
  have hc₁val : c₁ = -1 := by
    have h : (Pe (ofAdd c₁) : G) = (Pe (ofAdd (-1 : F)) : G) := by
      rw [hr₁s, hs, ← Subgroup.coe_inv, ← map_inv, ← ofAdd_neg]
    exact ofAdd.injective (Pe.injective (Subtype.ext h))
  have hAeq : A = u₁ * v₁ := by
    have h : (Ue A : G) = (Ue (u₁ * v₁) : G) := by
      rw [hA, shiftedInv_apply, map_mul, Subgroup.coe_mul, ← hco.1, hUeinv]
      simp
    exact Ue.injective (Subtype.ext h)
  have hAval : ((A : Fˣ) : F) = ((u₁ : Fˣ) : F) * ((v₁ : Fˣ) : F) := by
    rw [hAeq]; push_cast; ring
  have hcoord : c₁ = ((1 : ℤ) : F) * ((u₁ : Fˣ) : F) - ((2 : ℤ) : F) / ((v₁ : Fˣ) : F) := hco.2.1
  have hv0 : ((v₁ : Fˣ) : F) ≠ 0 := (v₁ : Fˣ).ne_zero
  have hsum : ((v₁ : Fˣ) : F) + ((A : Fˣ) : F) = 2 := by
    rw [hAval]
    rw [hc₁val] at hcoord
    field_simp at hcoord
    linear_combination -hcoord
  refine mem_normOneShiftSet.2 ⟨?_, ?_⟩
  · have h := (mem_normOneUnits_iff_pow_eq_one hp hcard (A : Fˣ)).1 A.2
    rwa [← hm] at h
  · have h := (mem_normOneUnits_iff_pow_eq_one hp hcard (v₁ : Fˣ)).1 v₁.2
    rw [← hm] at h
    rwa [show (2 : F) - ((A : Fˣ) : F) = ((v₁ : Fˣ) : F) from by linear_combination -hsum]

theorem mapsTo_shiftedInv_normOneShiftImage [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneSubgroup F m ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) (hyc : y ∈ ⁅Q, P₀⁆) :
    Set.MapsTo (shiftedInv t) (normOneShiftImage fun u => (Ue u : G))
      (normOneShiftImage fun u => (Ue u : G)) := by
  have hfin : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  set e : normOneUnits F ≃* normOneSubgroup F m :=
    (MulEquiv.subgroupCongr (normOneSubgroup_eq_normOneUnits hp hcard hm)).symm with he
  have hcoe : ∀ u : normOneUnits F, ((e u : Fˣ) : F) = ((u : Fˣ) : F) := by
    intro u; rw [he]; norm_cast
  have hcoe' : ∀ u : normOneSubgroup F m, ((e.symm u : Fˣ) : F) = ((u : Fˣ) : F) := by
    intro u; rw [he]; norm_cast
  set Ue' : normOneUnits F ≃* U := e.trans Ue with hUe'
  have hUe'v : ∀ u : normOneUnits F, (Ue' u : G) = (Ue (e u) : G) := fun _ => rfl
  have hact' : ∀ (z : F) (w : normOneUnits F),
      (Ue' w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue' w : G)
        = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G) := by
    intro z w
    rw [hUe'v, ← hcoe w]
    exact hact z (e w)
  have hsP₀ : s ∈ P₀ := by rw [hP₀, hs]; exact apply_ofAdd_mem_primeLine _ (one_mem _)
  have htP₁ : t ∈ P₁ := by rw [hP₁, ht]; exact ⟨s, hsP₀, by simp [MulAut.conj]⟩
  have htU : t ∈ normalizer (U : Set G) := hP₁U htP₁
  intro g hg
  rw [mem_normOneShiftImage] at hg
  obtain ⟨u, hu, rfl⟩ := hg
  have hfa : ((e.symm u : Fˣ) : F) ∈ normOneShiftSet F m := by
    rw [mem_normOneShiftSet, hcoe' u]
    exact ⟨pow_eq_one_of_mem_normOneSubgroup u.2, mem_normOneShiftSubset.1 hu⟩
  have hga : (Ue' (e.symm u) : G) = (Ue u : G) := by rw [hUe'v, MulEquiv.apply_symm_apply]
  have hmem : shiftedInv t (Ue u : G) ∈ U := by
    rw [shiftedInv_apply]
    exact conj_mem_of_mem_normalizer (pow_mem htU 3) (inv_mem (Ue u).2)
  set A : normOneUnits F := Ue'.symm ⟨shiftedInv t (Ue u : G), hmem⟩ with hAdef
  have hAv : (Ue' A : G) = shiftedInv t (Ue u : G) := by rw [hAdef]; simp
  have hAmem : ((A : Fˣ) : F) ∈ normOneShiftSet F m :=
    mem_normOneShiftSet_of_eq_shiftedInv hp hq hqp hcard hm hcop Pe Ue' hPU hact' hH hP₀ hs hQab
      hQp hQnorm hy hP₁ hP₁U ht hyc hfa (by rw [hAv, ← hga])
  refine mem_normOneShiftImage.2 ⟨e A, ?_, ?_⟩
  · rw [mem_normOneShiftSubset, hcoe A]
    exact (mem_normOneShiftSet.1 hAmem).2
  · rw [← hUe'v, hAv]

end

end CFSG.FeitThompson
