module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverF0
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Check
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3TV

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 Subgroup
open scoped Matrix

section Facts

variable {X : Type*} [Group X] [Finite X] {k : Fin 6 → X}

theorem conj_coord {L : Type*} [Group L] {n : ℕ} {B : Subgroup L}
    (f : Multiplicative (Fin n → ZMod 3) ≃* B) (g : normalizer (B : Set L)) (v : Fin n → ZMod 3) :
    (g : L) * (f (Multiplicative.ofAdd v) : L) * (g : L)⁻¹ =
      (f (Multiplicative.ofAdd (conjMat f g *ᵥ v)) : L) := by
  have h1 : normalizerMonoidHom B g (f (Multiplicative.ofAdd v)) =
      f (Multiplicative.ofAdd (conjAdd f g v)) := by
    rw [conjAdd_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have h2 := congrArg Subtype.val h1
  have h3 : conjMat f g *ᵥ v = conjAdd f g v := by
    rw [conjMat, LinearMap.toMatrix'_mulVec]
    rfl
  rw [h3]
  exact h2

namespace J3Pkg

variable (h : J3Pkg k)
include h

@[expose] noncomputable def bEq : Multiplicative (Fin 4 → ZMod 3) ≃*
    (Subgroup.closure (Set.range (xB k))) :=
  basisEquiv h.x_pow h.x_comm h.basisProd_injective

theorem conjMat_gen (i : Fin 6) (hi : k i ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X)) :
    conjMat h.bEq ⟨k i, hi⟩ = actMat i := by
  have := rho_basis_eq (x := xB k) (hx := h.x_pow) (hc := h.x_comm) (hinj := h.basisProd_injective)
    ⟨k i, hi⟩ (actMat i) (fun j => h.act i j)
  exact this

theorem matrix_mem (y : X) (hy : y ∈ Subgroup.closure (Set.range k)) :
    ∃ hn : y ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X),
      conjMat h.bEq ⟨y, hn⟩ ∈ matS := by
  obtain ⟨hS1, hSg, hSm, hSi, -⟩ := matFacts
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hk : k i ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X) :=
      h.k_mem_normalizer i
    refine ⟨hk, ?_⟩
    rw [h.conjMat_gen i hk]
    exact hSg i
  | one =>
    refine ⟨one_mem _, ?_⟩
    have : (⟨1, one_mem _⟩ : normalizer (Subgroup.closure (Set.range (xB k)) : Set X)) = 1 := rfl
    rw [this, conjMat_one]
    exact hS1
  | mul a b ha hb iha ihb =>
    obtain ⟨hna, hsa⟩ := iha
    obtain ⟨hnb, hsb⟩ := ihb
    refine ⟨mul_mem hna hnb, ?_⟩
    have : (⟨a * b, mul_mem hna hnb⟩ : normalizer (Subgroup.closure (Set.range (xB k)) : Set X)) =
        ⟨a, hna⟩ * ⟨b, hnb⟩ := rfl
    rw [this, conjMat_mul]
    exact hSm _ hsa _ hsb
  | inv a ha iha =>
    obtain ⟨hna, hsa⟩ := iha
    refine ⟨inv_mem hna, ?_⟩
    obtain ⟨t, ht, hst⟩ := hSi _ hsa
    have hmul : conjMat h.bEq ⟨a, hna⟩ * conjMat h.bEq ⟨a⁻¹, inv_mem hna⟩ = 1 := by
      rw [← conjMat_mul]
      have : (⟨a, hna⟩ : normalizer (Subgroup.closure (Set.range (xB k)) : Set X)) *
          ⟨a⁻¹, inv_mem hna⟩ = 1 := Subtype.ext (mul_inv_cancel a)
      rw [this, conjMat_one]
    have hts : t * conjMat h.bEq ⟨a, hna⟩ = 1 := mul_eq_one_comm.1 hst
    have : conjMat h.bEq ⟨a⁻¹, inv_mem hna⟩ = t := by
      calc conjMat h.bEq ⟨a⁻¹, inv_mem hna⟩
          = (t * conjMat h.bEq ⟨a, hna⟩) * conjMat h.bEq ⟨a⁻¹, inv_mem hna⟩ := by rw [hts, one_mul]
        _ = t * (conjMat h.bEq ⟨a, hna⟩ * conjMat h.bEq ⟨a⁻¹, inv_mem hna⟩) := by rw [mul_assoc]
        _ = t := by rw [hmul, mul_one]
    rw [this]
    exact ht

theorem conj_basisProd (i : Fin 6) (a : Fin 4 → ZMod 3) :
    k i * basisProd (xB k) a * (k i)⁻¹ = basisProd (xB k) (actMat i *ᵥ a) := by
  have hk : k i ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X) :=
    h.k_mem_normalizer i
  have := conj_coord h.bEq ⟨k i, hk⟩ a
  rw [h.conjMat_gen i hk] at this
  have e1 : ((h.bEq (Multiplicative.ofAdd a) : Subgroup.closure (Set.range (xB k))) : X) =
      basisProd (xB k) a := coe_basisEquiv _ _ _ a
  have e2 : ((h.bEq (Multiplicative.ofAdd (actMat i *ᵥ a)) :
      Subgroup.closure (Set.range (xB k))) : X) = basisProd (xB k) (actMat i *ᵥ a) :=
    coe_basisEquiv _ _ _ _
  rw [e1, e2] at this
  exact this

theorem not_transvection (y : X) (hy : y ∈ Subgroup.closure (Set.range k))
    (hn : y ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X)) :
    ¬ IsTransvectionOn
      ((Subgroup.closure (Set.range (xB k))).normalizerMonoidHom ⟨y, hn⟩) := by
  intro hT
  obtain ⟨-, -, -, -, hS5⟩ := matFacts
  obtain ⟨hn', hs⟩ := h.matrix_mem y hy
  obtain ⟨hsq, hne⟩ := tv_necessary h.bEq ⟨y, hn⟩ hT
  rcases hS5 _ hs with h1 | ⟨v, hv⟩
  · obtain ⟨v, hv⟩ := hne
    apply hv
    have : conjMat h.bEq ⟨y, hn⟩ = 1 := h1
    rw [this, sub_self, Matrix.zero_mulVec]
  · exact hv (hsq v)

end J3Pkg

end Facts

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
