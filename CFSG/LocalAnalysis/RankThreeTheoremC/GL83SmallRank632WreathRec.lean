module

import CFSG.RankThree.Transfer.Wreath
import CFSG.RankThree.Transfer.PGroup
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

section WreathRec

variable {A : Type*} [CommGroup A]

private theorem wreathRec_exists_hom_ne_one (hA : ∀ a : A, a ^ 3 = 1) {w : A} (hw : w ≠ 1) :
    ∃ θ : A →* Multiplicative (ZMod 3), θ w ≠ 1 := by
  let _ : Module (ZMod 3) (Additive A) := AddCommGroup.zmodModule (n := 3) fun x => by
    rw [← toMul_eq_one, toMul_nsmul]
    exact hA _
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 3) (x := Additive.ofMul w)
    (by simpa using hw)
  refine ⟨AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom, fun h => hf ?_⟩
  simpa using h

private theorem wreathRec_exists_norm_ne_one [Finite A] (hA : ∀ a : A, a ^ 3 = 1)
    (hcard : Nat.card A = 27) (α : A →* A)
    (hfix : ∀ S : Subgroup A, (∀ a ∈ S, α a = a) → Nat.card S ≤ 3) :
    ∃ u : A, u * α u * α (α u) ≠ 1 := by
  by_contra h
  push Not at h
  let β : A →* A :=
    { toFun := fun w => w⁻¹ * α w
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hβ : ∀ w, β w = w⁻¹ * α w := fun _ => rfl
  have hββ : ∀ w, β (β w) = w * α w * α (α w) := by
    intro w
    have h3 : (α w)⁻¹ * (α w)⁻¹ = α w := by
      rw [← mul_inv, inv_eq_iff_mul_eq_one, ← pow_three', hA]
    rw [hβ, hβ, map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc, mul_assoc w, h3]
  have hker : Nat.card β.ker ≤ 3 := hfix β.ker fun a ha => by
    rw [MonoidHom.mem_ker, hβ, inv_mul_eq_one] at ha
    exact ha.symm
  have hle : β.range ≤ β.ker := by
    rintro _ ⟨w, rfl⟩
    rw [MonoidHom.mem_ker, hββ, h w]
  have hrange : Nat.card β.range ≤ Nat.card β.ker := Subgroup.card_le_of_le hle
  have hmul := Subgroup.card_ker_mul_card_range β
  rw [hcard] at hmul
  have : Nat.card β.ker * Nat.card β.range ≤ 3 * 3 :=
    Nat.mul_le_mul hker (hrange.trans hker)
  omega

private theorem wreathRec_prod_three {M : Type*} [CommMonoid M]
    (f : Multiplicative (ZMod 3) → M) :
    ∏ x, f x = f (Multiplicative.ofAdd 0) * f (Multiplicative.ofAdd 1) *
      f (Multiplicative.ofAdd 2) :=
  Fin.prod_univ_three f

end WreathRec

theorem nonempty_mulEquiv_wreath_of_card_eq_eighty_one {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 81) {E : Subgroup P} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27)
    {z : P} (hz : z ∈ center P) (hz3 : orderOf z = 3)
    (hZ : ∀ w ∈ center P, w ^ 3 = 1 → w ∈ zpowers z) :
    Nonempty (P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) := by
  classical
  have _ := hz
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hP]; norm_num)
  have hEtop : E ≠ ⊤ := by
    rintro rfl
    rw [Subgroup.card_top, hP] at hEc
    norm_num at hEc
  obtain ⟨φ, hφs, hEφ⟩ := CFSG.RankThree.Transfer.exists_surjective_zmod_of_ne_top hPp hEtop
  have hkc : Nat.card φ.ker = 27 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hφs
    rw [hP, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 3))] at h
    simp only [Fintype.card_multiplicative, ZMod.card] at h
    omega
  have hker : E = φ.ker := Subgroup.eq_of_le_of_card_ge hEφ (by rw [hkc, hEc])
  rw [hker] at hE
  clear hEc hEφ hker
  have : IsMulCommutative φ.ker := hE.1
  let _ : CommGroup φ.ker := IsMulCommutative.instCommGroup
  have hK3 : ∀ a : φ.ker, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  obtain ⟨c, hc⟩ := hφs (Multiplicative.ofAdd 1)
  set α : MulAut φ.ker := MulAut.conjNormal c⁻¹ with hα
  set t : Multiplicative (ZMod 3) → P := fun x => c ^ (Multiplicative.toAdd x).val with ht_def
  have ht : ∀ x, φ (t x) = x := by
    intro x
    simp only [ht_def, map_pow, hc, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_val,
      ZMod.cast_id', id_eq, ofAdd_toAdd]
  have hdecomp : ∀ g : P, ∃ e ∈ φ.ker, ∃ k : ℕ, g = e * c ^ k := by
    intro g
    refine ⟨g * (t (φ g))⁻¹, ?_, (Multiplicative.toAdd (φ g)).val, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, ht]
      exact mul_inv_cancel _
    · simp [ht_def]
  have hfixz : ∀ w : φ.ker, α w = w → (w : P) ∈ zpowers z := by
    intro w hw
    have hwc : (w : P) * c = c * w := by
      have h1 := congrArg Subtype.val hw
      rw [hα, MulAut.conjNormal_apply, inv_inv] at h1
      calc (w : P) * c = c * (c⁻¹ * w * c) := by group
        _ = c * w := by rw [h1]
    refine hZ _ ?_ (by simpa using hE.2 w w.2)
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨e, he, k, rfl⟩ := hdecomp g
    have hew : e * w = w * e := congrArg Subtype.val (mul_comm (⟨e, he⟩ : φ.ker) w)
    have hck : c ^ k * w = w * c ^ k := (Commute.pow_left (show Commute c (w : P) from
      hwc.symm) k).eq
    calc e * c ^ k * w = e * (c ^ k * w) := mul_assoc _ _ _
      _ = e * w * c ^ k := by rw [hck, mul_assoc]
      _ = w * (e * c ^ k) := by rw [hew, mul_assoc]
  have hfixcard : ∀ S : Subgroup φ.ker, (∀ a ∈ S, α.toMonoidHom a = a) → Nat.card S ≤ 3 := by
    intro S hS
    have hinj : Function.Injective
        (fun s : S => (⟨((s : φ.ker) : P), hfixz _ (hS s s.2)⟩ : zpowers z)) := by
      intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    calc Nat.card S ≤ Nat.card (zpowers z) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_zpowers, hz3]
  obtain ⟨u, hu⟩ := wreathRec_exists_norm_ne_one hK3 hkc α.toMonoidHom hfixcard
  obtain ⟨θ, hθ⟩ := wreathRec_exists_hom_ne_one hK3 hu
  obtain ⟨Ψ, hΨ⟩ := CFSG.RankThree.Transfer.exists_surjective_regularWreathProduct
    Nat.prime_three φ t ht θ u (by
      rw [wreathRec_prod_three]
      have h0 : t (Multiplicative.ofAdd 0) = 1 := by simp [ht_def]
      have h1 : t (Multiplicative.ofAdd 1) = c := by
        change c ^ (1 : ZMod 3).val = c
        rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
      have h2 : t (Multiplicative.ofAdd 2) = c ^ 2 := rfl
      rw [h0, h1, h2, inv_one, map_one, ← inv_pow, map_pow, ← hα, pow_two, MulAut.one_apply,
        MulAut.mul_apply, ← map_mul, ← map_mul]
      simpa using hθ)
  have hbij : Function.Bijective Ψ := hΨ.bijective_of_nat_card_le (by
    rw [hP, RegularWreathProduct.card]
    simp)
  exact ⟨MulEquiv.ofBijective Ψ hbij⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
