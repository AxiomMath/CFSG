module

public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

theorem exists_injective_quotient_mulAut_frattini {X : Type*} [Group X] [Finite X]
    (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hmax : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N ≤ Q)
    (hcent : ∀ x : X, (∀ q ∈ Q, q * x = x * q) → x ∈ Q) :
    ∃ ψ : X ⧸ Q →* MulAut (↥Q ⧸ frattini ↥Q), Function.Injective ψ := by
  let ρ : X →* MulAut Q := MulAut.conjNormal
  let f : MulAut Q →* MulAut (↥Q ⧸ frattini ↥Q) :=
    CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q)
  let φ : X →* MulAut (↥Q ⧸ frattini ↥Q) := f.comp ρ
  have hcomm : ∀ a b : ↥Q ⧸ frattini ↥Q, a * b = b * a :=
    fun a b => (CFSG.GroupTheory.frattini_elementary_quotient hQ).2.1.is_comm.comm a b
  have hconj : ∀ (q : X) (hq : q ∈ Q) (element : ↥Q),
      ρ q element = ⟨q, hq⟩ * element * ⟨q, hq⟩⁻¹ := by
    intro q hq element
    apply Subtype.ext
    rw [show ρ q = MulAut.conjNormal (H := Q) q from rfl, MulAut.conjNormal_apply]
    rfl
  have hQle : Q ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    change f (ρ q) = 1
    rw [← MonoidHom.mem_ker]
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro element
    rw [hconj q hq element]
    rw [map_mul, map_mul, map_inv]
    rw [hcomm (QuotientGroup.mk' (frattini ↥Q) ⟨q, hq⟩)
      (QuotientGroup.mk' (frattini ↥Q) element)]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hkerle : φ.ker ≤ Q := by
    have hKpg : IsPGroup 2 φ.ker := by
      intro x
      have hfx : f (ρ (x : X)) = 1 := MonoidHom.mem_ker.mp x.2
      obtain ⟨k, hk⟩ :=
        (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
          (group := ↥Q) 2 hQ).exists_pow_pow_eq_one ⟨ρ (x : X), hfx⟩
      have hk' : (ρ (x : X)) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hxpow : ρ ((x : X) ^ 2 ^ k) = 1 := by
        rw [map_pow, hk']
      have hcentral : ∀ q ∈ Q, q * (x : X) ^ 2 ^ k = (x : X) ^ 2 ^ k * q := by
        intro q hq
        have h1 : ρ ((x : X) ^ 2 ^ k) ⟨q, hq⟩ = ⟨q, hq⟩ := by
          have := congrArg (fun a : MulAut Q => a ⟨q, hq⟩) hxpow
          simpa using this
        have h2 : (x : X) ^ 2 ^ k * q * ((x : X) ^ 2 ^ k)⁻¹ = q := by
          have h := congrArg (fun a : ↥Q => (a : X)) h1
          rw [show ρ ((x : X) ^ 2 ^ k) = MulAut.conjNormal (H := Q) ((x : X) ^ 2 ^ k)
            from rfl, MulAut.conjNormal_apply] at h
          simpa using h
        have h3 : (x : X) ^ 2 ^ k * q = q * (x : X) ^ 2 ^ k :=
          mul_inv_eq_iff_eq_mul.mp h2
        exact h3.symm
      have hyQ : (x : X) ^ 2 ^ k ∈ Q := hcent _ hcentral
      obtain ⟨m, hm⟩ := hQ.exists_pow_pow_eq_one ⟨(x : X) ^ 2 ^ k, hyQ⟩
      have hm' : ((x : X) ^ 2 ^ k) ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      refine ⟨k + m, ?_⟩
      apply Subtype.ext
      show (x : X) ^ 2 ^ (k + m) = 1
      rw [pow_add, pow_mul, hm']
    exact hmax φ.ker inferInstance hKpg
  refine ⟨QuotientGroup.lift Q φ hQle, ?_⟩
  rw [QuotientGroup.injective_lift_iff]
  exact le_antisymm hQle hkerle

theorem exists_rank_card_dvd {X : Type*} [Group X] [Finite X]
    (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hgen : ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = Q)
    (hmax : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N ≤ Q)
    (hcent : ∀ x : X, (∀ q ∈ Q, q * x = x * q) → x ∈ Q) :
    ∃ d : ℕ, d ≤ 4 ∧ Nat.card (↥Q ⧸ frattini ↥Q) = 2 ^ d ∧
      Nat.card (X ⧸ Q) ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  obtain ⟨s, hs4, hs⟩ := hgen
  have hrank : Group.rank ↥Q ≤ 4 := by
    rw [← hs]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs4
  obtain ⟨d, hd, hcard, hcomm, hpow⟩ :=
    CFSG.RankThree.PartOne.SectionalRank.frattini_quotient_elementary_of_rank_le_four hQ hrank
  obtain ⟨ψ, hψ⟩ := exists_injective_quotient_mulAut_frattini Q hQ hmax hcent
  have hdvd : Nat.card (X ⧸ Q) ∣ Nat.card (MulAut (↥Q ⧸ frattini ↥Q)) :=
    Subgroup.card_dvd_of_injective ψ hψ
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 2) hcomm hpow hcard
  have hMulAut : Nat.card (MulAut (↥Q ⧸ frattini ↥Q)) =
      ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) :=
    (CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e).trans
      (CFSG.SectionRank.Ccomm.card_GL_zmod d)
  exact ⟨d, hd, hcard, hMulAut ▸ hdvd⟩

end CFSG.EvenSporadicStandard.HNRecog.GH73
