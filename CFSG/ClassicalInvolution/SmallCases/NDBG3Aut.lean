module

public import CFSG.ClassicalInvolution.SmallCases.NDBG3Lin
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


variable {K : Type} [Field K] [Finite K] [CharP K 3]

theorem isInner_of_fix_xElement {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut ↥(adjointGroup ReeTag.G2.tag K)) (h : ↥(adjointGroup ReeTag.G2.tag K))
    (j : Fin ReeTag.G2.tag.rank)
    (hfix : ∀ c : K, α (h * xElement j c * h⁻¹) = h * xElement j c * h⁻¹) :
    ∃ b, α = MulAut.conj b := by
  have : CharP K ReeTag.G2.prime := inferInstanceAs (CharP K 3)
  have hK3 : 3 < Nat.card K := by
    rw [hK]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, k, hgk⟩ := G2_exists_conj_mul_pow (K := K) (by omega) hK α
  have key : ∀ c : K, (h⁻¹ * g * (ReeTag.G2.finiteExceptionalAut K ^ k) h) *
      (ReeTag.G2.finiteExceptionalAut K ^ k) (xElement j c) *
        (h⁻¹ * g * (ReeTag.G2.finiteExceptionalAut K ^ k) h)⁻¹ = xElement j c := by
    intro c
    have e := hfix c
    rw [hgk, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at e
    calc (h⁻¹ * g * (ReeTag.G2.finiteExceptionalAut K ^ k) h) *
          (ReeTag.G2.finiteExceptionalAut K ^ k) (xElement j c) *
            (h⁻¹ * g * (ReeTag.G2.finiteExceptionalAut K ^ k) h)⁻¹ =
          h⁻¹ * (g * ((ReeTag.G2.finiteExceptionalAut K ^ k) h *
            (ReeTag.G2.finiteExceptionalAut K ^ k) (xElement j c) *
              ((ReeTag.G2.finiteExceptionalAut K ^ k) h)⁻¹) * g⁻¹) * h := by group
      _ = h⁻¹ * (h * xElement j c * h⁻¹) * h := by rw [e]
      _ = xElement j c := by group
  have hlin : ∀ (j' : Fin ReeTag.G2.tag.rank) (σ : K →+* K),
      (∀ c, (ReeTag.G2.finiteExceptionalAut K ^ k) (xElement j c) = xElement j' (σ c)) →
        (∀ c, σ c = c) ∧ j' = j := by
    intro j' σ hφ
    set g' := h⁻¹ * g * (ReeTag.G2.finiteExceptionalAut K ^ k) h
    refine conj_xOp_g2 hK3
      ((g' : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K))
      (((g'⁻¹ : ↥(adjointGroup ReeTag.G2.tag K)) : ModGL ReeTag.G2.tag K) :
        Module.End K (RootModule ReeTag.G2.tag K)) ?_
      σ j j' fun c => ?_
    · have e := congrArg (fun y : ↥(adjointGroup ReeTag.G2.tag K) =>
        ((y : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K)))
        (inv_mul_cancel g')
      simp only [Subgroup.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one] at e
      exact e
    · have e := congrArg (fun y : ↥(adjointGroup ReeTag.G2.tag K) =>
        ((y : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K))) (key c)
      rw [hφ c] at e
      simp only [Subgroup.coe_mul, Units.val_mul] at e
      exact e
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hφ : ∀ c, (ReeTag.G2.finiteExceptionalAut K ^ (2 * m)) (xElement j c) =
        xElement j (iterateFrobenius K 3 m c) := fun c => by
      rw [finiteExceptionalAut_pow_two_mul, ReeTag.finiteFrobeniusAut_pow_xElement,
        iterateFrobenius_def]
      rfl
    obtain ⟨hσ, -⟩ := hlin j _ hφ
    have hσ' : ∀ c : K, c ^ 3 ^ m = c := fun c => by rw [← iterateFrobenius_def]; exact hσ c
    have hFr : ReeTag.G2.finiteFrobeniusAut K ^ m = 1 := by
      refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
      · change (ReeTag.G2.finiteFrobeniusAut K ^ m) (xElement i c) = xElement i c
        rw [ReeTag.finiteFrobeniusAut_pow_xElement]
        exact congrArg (xElement i) (hσ' c)
      · change (ReeTag.G2.finiteFrobeniusAut K ^ m) (yElement i c) = yElement i c
        rw [ReeTag.finiteFrobeniusAut_pow_yElement]
        exact congrArg (yElement i) (hσ' c)
    exact ⟨g, by rw [hgk, finiteExceptionalAut_pow_two_mul, hFr, mul_one]⟩
  · exfalso
    have hodd : ∀ c, (ReeTag.G2.finiteExceptionalAut K ^ (2 * m + 1)) (xElement j c) =
        (ReeTag.G2.finiteFrobeniusAut K ^ m)
          (xElement (ReeTag.G2.perm j) (c ^ ReeTag.G2.exponent j)) := fun c => by
      rw [pow_succ, MulAut.mul_apply, finiteExceptionalAut_pow_two_mul,
        ReeTag.finiteExceptionalAut_xElement]
    rcases fin_g2_cases j with rfl | rfl
    · have hφ : ∀ c, (ReeTag.G2.finiteExceptionalAut K ^ (2 * m + 1)) (xElement longIdx c) =
          xElement shortIdx (iterateFrobenius K 3 m c) := fun c => by
        rw [hodd, ReeTag.finiteFrobeniusAut_pow_xElement, iterateFrobenius_def,
          show ReeTag.G2.exponent longIdx = 1 by decide, pow_one]
        rfl
      exact longIdx_ne_shortIdx (hlin shortIdx _ hφ).2.symm
    · have hφ : ∀ c, (ReeTag.G2.finiteExceptionalAut K ^ (2 * m + 1)) (xElement shortIdx c) =
          xElement longIdx (iterateFrobenius K 3 (m + 1) c) := fun c => by
        rw [hodd, ReeTag.finiteFrobeniusAut_pow_xElement, iterateFrobenius_def,
          show ReeTag.G2.exponent shortIdx = 3 by decide, show ReeTag.G2.prime = 3 from rfl,
          ← pow_mul, ← pow_succ']
        rfl
      exact longIdx_ne_shortIdx (hlin longIdx _ hφ).2

end CFSG.ClassicalInvolution.NDB.NDBG3
