module

public import CFSG.Fischer.Classification.Uniqueness.Star
public import CFSG.Fischer.Classification.Basic.Transitivity

public section

namespace CFSG.LargeExtraspecial.AS35L

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

theorem mulAut_eq_one_of_fix_far (hP : Pair X E) (hZ : center X = ⊥)
    (hS : IsSimpleGroup (_root_.commutator X))
    (hna : ∃ a b : _root_.commutator X, a * b ≠ b * a) {d c : X} (hd : d ∈ E) (hc : c ∈ E)
    (hcd : c * d ≠ d * c) (β : MulAut X) (hβd : β d = d)
    (hβD : ∀ f ∈ LocalClass E d, β f = f) (hβc : β c = c) : β = 1 := by
  have hfixK : ∀ g ∈ closure (insert d (LocalClass E d)), β g = g := by
    intro g hg
    induction hg using closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hβd
      · exact hβD x hx
    | one => exact map_one β
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hfixE : ∀ e ∈ E, β e = e := by
    intro e he
    by_cases hed : e = d
    · rw [hed, hβd]
    by_cases hec : e * d = d * e
    · exact hβD e ⟨he, hed, hec⟩
    obtain ⟨g, hg, rfl⟩ := Pair.exists_conj_far hP hZ hS hna hd hc hcd e he hec
    rw [map_mul, map_mul, map_inv, hfixK g hg, hβc]
  have h1 := MonoidHom.eq_of_eqOn_dense hP.2.2.2.2 (f := β.toMonoidHom) (g := MonoidHom.id X)
    fun e he => hfixE e he
  exact MulEquiv.ext fun x => congrArg (fun φ : X →* X => φ x) h1

theorem mulAut_eq_one_or_conj_of_fix (hP : Pair X E) (hZ : center X = ⊥)
    (hS : IsSimpleGroup (_root_.commutator X))
    (hna : ∃ a b : _root_.commutator X, a * b ≠ b * a) (hT : TripleProperty E) {d : X}
    (hd : d ∈ E) (β : MulAut X) (hβE : ∀ e ∈ E, β e ∈ E) (hβd : β d = d)
    (hβD : ∀ f ∈ LocalClass E d, β f = f) : β = 1 ∨ β = MulAut.conj d := by
  obtain ⟨c, hc, hcd⟩ : ∃ c ∈ E, c * d ≠ d * c := by
    by_contra hall
    push Not at hall
    have hdZ : d ∈ center X := (Pair.mem_center_iff hP).2 fun e he => hall e he
    rw [hZ, mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hβcd : β c * d ≠ d * β c := by
    intro h
    apply hcd
    apply β.injective
    rw [map_mul, map_mul, hβd]
    exact h
  have hmem : β c ∈ ySet E d c := by
    refine ⟨hβE c hc, fun s hs => ⟨hs.1.1, ?_, ?_⟩⟩
    · rintro rfl
      exact hβcd hs.1.2.2
    · have hs' : β s = s := hβD s hs.1
      have h1 := congrArg β hs.2.2.2
      rwa [map_mul, map_mul, hs'] at h1
  rcases hT d c hd hc (fun h => hcd h.symm) hmem with h | h | h
  · exact absurd (h ▸ hβcd) fun h' => h' rfl
  · exact Or.inl (mulAut_eq_one_of_fix_far hP hZ hS hna hd hc hcd β hβd hβD h)
  · right
    have h' : β c = d * c * d := h
    have hd2 : d * d = 1 := Pair.mul_self hP hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have h1 := mulAut_eq_one_of_fix_far hP hZ hS hna hd hc hcd (MulAut.conj d * β)
      (by rw [MulAut.mul_apply, hβd, MulAut.conj_apply, mul_inv_cancel_right])
      (fun f hf => by
        rw [MulAut.mul_apply, hβD f hf, MulAut.conj_apply, ← hf.2.2, mul_inv_cancel_right])
      (by
        rw [MulAut.mul_apply, h', MulAut.conj_apply, hdinv,
          show d * (d * c * d) * d = (d * d) * c * (d * d) by group, hd2, one_mul, mul_one])
    calc β = (MulAut.conj d)⁻¹ * (MulAut.conj d * β) := by group
      _ = MulAut.conj d := by
        rw [h1, mul_one, ← map_inv, hdinv]

end CFSG.LargeExtraspecial.AS35L
