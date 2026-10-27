module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel
public import CFSG.Adapters.RankTwoModelTransports

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_coe glCongr_statedScalars statedProjCongr)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Congr

variable {K L : Type} [Field K] [Field L] (φ : K ≃+* L) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem glCongr_mulVec (A : GL ι K) (v : ι → K) :
    ((glCongr φ A : GL ι L) : Matrix ι ι L) *ᵥ (φ ∘ v) = φ ∘ ((A : Matrix ι ι K) *ᵥ v) := by
  funext i
  rw [glCongr_coe, Function.comp_apply]
  exact (RingHom.map_mulVec (φ : K →+* L) (A : Matrix ι ι K) v i).symm

variable {QK : (ι → K) → K} {QL : (ι → L) → L}

theorem glCongr_preserves_iff (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) (A : GL ι K) :
    (∀ w, QL (((glCongr φ A : GL ι L) : Matrix ι ι L) *ᵥ w) = QL w) ↔
      ∀ v, QK ((A : Matrix ι ι K) *ᵥ v) = QK v := by
  constructor
  · intro h v
    have h' := h (φ ∘ v)
    rw [glCongr_mulVec, hQ, hQ] at h'
    exact φ.injective h'
  · intro h w
    obtain ⟨v, rfl⟩ : ∃ v, φ ∘ v = w := ⟨φ.symm ∘ w, funext fun i => φ.apply_symm_apply _⟩
    rw [glCongr_mulVec, hQ, hQ, h]

theorem map_closure_preserving (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) :
    (Subgroup.closure {A : GL ι K | ∀ v, QK ((A : Matrix ι ι K) *ᵥ v) = QK v}).map
        (glCongr φ).toMonoidHom =
      Subgroup.closure {B : GL ι L | ∀ w, QL ((B : Matrix ι ι L) *ᵥ w) = QL w} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (glCongr_preserves_iff φ hQ A).2 hA
  · intro hB
    refine ⟨(glCongr φ).symm B, (glCongr_preserves_iff φ hQ _).1 ?_,
      (glCongr φ).apply_symm_apply B⟩
    rwa [MulEquiv.apply_symm_apply]

theorem map_statedOmega (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) :
    (StatedOmega QK).map (glCongr φ).toMonoidHom = StatedOmega QL := by
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, map_closure_preserving φ hQ]

theorem statedQuadMinus_comp {n : ℕ} {b c : K} {b' c' : L} (hb : φ b = b') (hc : φ c = c')
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n L b' c' (φ ∘ v) = φ (StatedQuadMinus n K b c v) := by
  subst hb hc
  simp only [StatedQuadMinus, Function.comp_apply, map_add, map_mul, map_pow, map_sum]

end Congr

theorem exists_mulEquiv_zmod_of_lieModel {J : Type} [Group J] {n : ℕ}
    (hJ : CFSG.Blueprint.LieModel J .POmegaMinus n 2 1) :
    4 ≤ n ∧
      Nonempty (J ≃* orthElementaryGroup (quadTail (n - 1) (minusTailForm (ZMod 2) 1 1))) := by
  rcases hJ with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hc
    have hn' : 4 ≤ n := hn
    have hK2 : Nat.card K = 2 := by rw [hcard, pow_one]
    have hchar : CharP K 2 :=
      finite_field_prime_power_characteristic (K := K) Nat.prime_two le_rfl hcard
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hc1 : c = 1 := by
      rcases eq_zero_or_eq_one hK2 c with h | h
      · exact absurd (by rw [h]; ring) (hirr 0)
      · exact h
    subst hc1
    have hb1 : b = 1 := by
      rcases eq_zero_or_eq_one hK2 b with h | h
      · exact absurd (by rw [h]; linear_combination h2) (hirr 1)
      · exact h
    subst hb1
    set σ : K ≃+* ZMod 2 := (binEquiv hK2).symm
    have hE := commutator_orthogonalGroup_quadMinus (n := n) (K := ZMod 2) (b := 1) (c := 1) hn'
      (by decide)
    exact ⟨hn', ⟨((e.trans (statedProjCongr (glCongr σ)
      (map_statedOmega σ (statedQuadMinus_comp σ (map_one σ) (map_one σ)))
      (glCongr_statedScalars σ))).trans
      (tailProjEquiv (minusTailIsometry n (ZMod 2) 1 1) (coe_quadMinus n (ZMod 2) 1 1) hE)).trans
      ((QuotientGroup.quotientMulEquivOfEq (elemScalars_quadTail_eq_bot (by omega))).trans
        QuotientGroup.quotientBot)⟩⟩
  all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
