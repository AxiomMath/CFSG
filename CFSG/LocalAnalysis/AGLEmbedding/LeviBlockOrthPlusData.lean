module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusExt
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusTypes
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs

public section

namespace CFSG.AGLEmbedding

open Matrix QuadraticMap CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise

namespace LeviBlock

section Sum

variable {ι₁ ι₂ : Type}

@[expose, reducible] def plusSumGroup (G₁ : ι₁ → Type) (G₂ : ι₂ → Type) : ι₁ ⊕ ι₂ → Type
  | .inl a => G₁ a
  | .inr b => G₂ b

noncomputable instance plusSumGroup.instGroup {G₁ : ι₁ → Type} {G₂ : ι₂ → Type}
    [∀ j, Group (G₁ j)] [∀ j, Group (G₂ j)] : (j : ι₁ ⊕ ι₂) → Group (plusSumGroup G₁ G₂ j)
  | .inl a => inferInstanceAs (Group (G₁ a))
  | .inr b => inferInstanceAs (Group (G₂ b))

instance plusSumGroup.instFinite {G₁ : ι₁ → Type} {G₂ : ι₂ → Type} [∀ j, Group (G₁ j)]
    [∀ j, Group (G₂ j)] [∀ j, Finite (G₁ j)] [∀ j, Finite (G₂ j)] :
    (j : ι₁ ⊕ ι₂) → Finite (plusSumGroup G₁ G₂ j)
  | .inl a => inferInstanceAs (Finite (G₁ a))
  | .inr b => inferInstanceAs (Finite (G₂ b))

theorem hasLeviBlocks_of_sum {Q : Type} [Group Q] {𝒯 : Set ℕ} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] {G₁ : ι₁ → Type} [∀ j, Group (G₁ j)] [∀ j, Finite (G₁ j)]
    {G₂ : ι₂ → Type} [∀ j, Group (G₂ j)] [∀ j, Finite (G₂ j)]
    (S₁ : ∀ j, Subgroup (G₁ j)) (S₂ : ∀ j, Subgroup (G₂ j))
    (β₁ : ∀ j, Q →* G₁ j) (β₂ : ∀ j, Q →* G₂ j)
    (hker : ∀ N : Subgroup Q, (∀ q ∈ N, (∀ j, β₁ j q = 1) ∧ ∀ j, β₂ j q = 1) → IsPGroup 2 N)
    (hs₁ : ∀ j, ∀ x ∈ S₁ j, ∃ q, β₁ j q = x ∧ (∀ j', j' ≠ j → β₁ j' q = 1) ∧ ∀ j', β₂ j' q = 1)
    (hs₂ : ∀ j, ∀ x ∈ S₂ j, ∃ q, β₂ j q = x ∧ (∀ j', j' ≠ j → β₂ j' q = 1) ∧ ∀ j', β₁ j' q = 1)
    (hc₁ : ∀ j, ⁅(β₁ j).range, (β₁ j).range⁆ ≤ S₁ j)
    (hc₂ : ∀ j, ⁅(β₂ j).range, (β₂ j).range⁆ ≤ S₂ j)
    (hS₁ : ∀ j, CFSG.Open.IsQuasisimple (S₁ j) ∨ Group.IsSolvable (S₁ j))
    (hS₂ : ∀ j, CFSG.Open.IsQuasisimple (S₂ j) ∨ Group.IsSolvable (S₂ j))
    (h𝒯₁ : ∀ j, CFSG.Open.IsQuasisimple (S₁ j) →
      Nat.card (↥(S₁ j) ⧸ Subgroup.center ↥(S₁ j)) ∈ 𝒯)
    (h𝒯₂ : ∀ j, CFSG.Open.IsQuasisimple (S₂ j) →
      Nat.card (↥(S₂ j) ⧸ Subgroup.center ↥(S₂ j)) ∈ 𝒯) : HasLeviBlocks Q 𝒯 := by
  let S : ∀ j, Subgroup (plusSumGroup G₁ G₂ j) := fun j => match j with
    | .inl a => S₁ a
    | .inr b => S₂ b
  let β' : ∀ j, Q →* plusSumGroup G₁ G₂ j := fun j => match j with
    | .inl a => β₁ a
    | .inr b => β₂ b
  refine HasLeviBlocks.of_index S (MonoidHom.pi β') ?_ ?_ ?_ ?_ ?_
  · refine hker _ fun q hq => ⟨fun j => ?_, fun j => ?_⟩
    · exact congrFun (MonoidHom.mem_ker.1 hq) (Sum.inl j)
    · exact congrFun (MonoidHom.mem_ker.1 hq) (Sum.inr j)
  · rw [Subgroup.pi_le_iff]
    rintro (a | b) _ ⟨x, hx, rfl⟩
    · obtain ⟨q, hq, h1, h2⟩ := hs₁ a x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · by_cases ha : a' = a
        · subst ha
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => ha (Sum.inl_injective h))]
          exact h1 a' ha
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inr_ne_inl]
        exact h2 b'
    · obtain ⟨q, hq, h1, h2⟩ := hs₂ b x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
        exact h2 a'
      · by_cases hb : b' = b
        · subst hb
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => hb (Sum.inr_injective h))]
          exact h1 b' hb
  · intro z hz
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    have hmap := Subgroup.map_commutator (MonoidHom.pi β').range (MonoidHom.pi β').range
      (Pi.evalMonoidHom (plusSumGroup G₁ G₂) j)
    have hz' : Pi.evalMonoidHom (plusSumGroup G₁ G₂) j z ∈
        ⁅((MonoidHom.pi β').range.map (Pi.evalMonoidHom _ j)),
          ((MonoidHom.pi β').range.map (Pi.evalMonoidHom _ j))⁆ := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    have hr : (MonoidHom.pi β').range.map (Pi.evalMonoidHom (plusSumGroup G₁ G₂) j) =
        (β' j).range := by
      rw [MonoidHom.range_eq_map, Subgroup.map_map, MonoidHom.range_eq_map]
      rfl
    rw [hr] at hz'
    rcases j with a | b
    · exact hc₁ a hz'
    · exact hc₂ b hz'
  · rintro (a | b)
    · exact hS₁ a
    · exact hS₂ b
  · rintro (a | b)
    · exact h𝒯₁ a
    · exact h𝒯₂ b

end Sum

variable {r : ℕ} {K : Type} [Field K]

theorem commutator_range_plusEBlockHom_le {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ}
    (hb : b ∈ D) : ⁅(plusEBlockHom (K := K) hD hb).range, (plusEBlockHom hD hb).range⁆ ≤
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b - predCut D b)) K →* _).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rintro _ ⟨x, hx, rfl⟩
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  have hc : x ∈ commutator ↥(plusFlagStab K r D) := by rwa [commutator_def]
  exact Abelianization.commutator_subset_ker
    (Matrix.GeneralLinearGroup.det.comp (plusEBlockHom hD hb)) hc

theorem exists_plusFlagLevi_of_mem [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {b : ℕ} (hb : b ∈ D) {x : GL (Fin (b - predCut D b)) K}
    (hx : x ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b - predCut D b)) K →*
      _).range) :
    ∃ q : ↥(plusFlagStab K r D), plusEBlockHom hD hb q = x ∧
      (∀ b' (hb' : b' ∈ D), b' ≠ b → plusEBlockHom hD hb' q = 1) ∧
      ∀ {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r), b ≤ t →
        plusResBlockHom hD ht htm q = 1 := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨⟨plusFlagLevi K (hD b hb) _, plusFlagLevi_mem_plusFlagStab hr hD hb _⟩,
    plusEBlockHom_plusFlagLevi_self hr hD hb _,
    fun b' hb' hne => plusEBlockHom_plusFlagLevi_of_ne hr hD hb hb' hne _,
    fun ht htm hbt => plusResBlockHom_plusFlagLevi hr hD ht htm hb hbt _⟩

theorem sup_eq_zero_or_mem (D : Finset ℕ) : D.sup id = 0 ∨ D.sup id ∈ D := by
  rcases D.eq_empty_or_nonempty with he | hne
  · left
    rw [he, Finset.sup_empty]
    rfl
  · right
    obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [hce]
    exact hc

end LeviBlock

open LeviBlock

variable {r : ℕ} {K : Type} [Field K]

theorem hasLeviBlocks_plusFlagStab_top [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hrD : r ∈ D) :
    HasLeviBlocks ↥(plusFlagStab K r D) (plusBlockOrders (Nat.card K)) := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have ht : D.sup id = r := le_antisymm (Finset.sup_le hD') (Finset.le_sup (f := id) hrD)
  refine hasLeviBlocks_of_sum (ι₁ := ↥D) (ι₂ := Empty)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => Unit)
    (fun b => (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
      _).range) (fun _ => ⊥) (fun b => plusEBlockHom hD' b.2) (fun e => e.elim) ?_ ?_
    (fun e => e.elim) (fun b => commutator_range_plusEBlockHom_le hD' b.2) (fun e => e.elim)
    (fun b => isQuasisimple_or_isSolvable_rangeSL _) (fun e => e.elim)
    (fun b => card_rangeSL_quotient_center) (fun e => e.elim)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    rw [ht] at hx ⊢
    rw [show 2 * r - r = r by omega] at hx
    have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈ plusCutSpace r K r := by
      rw [← flag_eq_plusCutSpace le_rfl, ← smul_flag_of_mem_plusFlagStab g.2 (Or.inr hrD)]
      rw [← flag_eq_plusCutSpace le_rfl] at hx
      exact ⟨x, hx, rfl⟩
    exact sub_mem hgx hx
  · intro b x hx
    obtain ⟨q, h1, h2, -⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    exact ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun e => e.elim⟩

namespace LeviBlock

theorem finite_plusAut [Finite K] (m : ℕ) :
    Finite ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
  Finite.of_injective (β := (Fin m ⊕ Fin m → K) → (Fin m ⊕ Fin m → K)) (fun e => ⇑e)
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem plusResBlockHom_eq_one_of_plusResAut {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) {g : ↥(plusFlagStab K r D)}
    (hg : plusResAut hD ht htm g = 1) : plusResBlockHom hD ht htm g = 1 :=
  (matrixEquiv m K).injective (by rw [map_one]; exact hg)

theorem plusResExt_mem_plusFlagStab_of_mem {D : Finset ℕ} {t m : ℕ} (htm : t + m = r)
    (hDt : ∀ d ∈ D, d ≤ t) {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hE : plusResExt K htm h ∈ orthElementaryGroup (quadPlus r K)) :
    plusResExt K htm h ∈ plusFlagStab K r D := by
  refine mem_plusFlagStab.2 ⟨hE, fun d hd => ?_⟩
  refine smul_flag_of_plusCut ((hDt d hd).trans (by omega))
    (plusCut_plusResExt htm h (Or.inl (hDt d hd))) ?_
  rw [← map_inv]
  exact plusCut_plusResExt htm h⁻¹ (Or.inl (hDt d hd))

theorem plusResExt_mem_plusFlagStab [CharP K 2] {D : Finset ℕ} {t m : ℕ} (htm : t + m = r)
    (hm : 3 ≤ m) (hDt : ∀ d ∈ D, d ≤ t)
    {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hh : h ∈ orthElementaryGroup (quadPlus m K)) :
    plusResExt K htm h ∈ plusFlagStab K r D :=
  plusResExt_mem_plusFlagStab_of_mem htm hDt (plusResExt_mem_orthElementaryGroup htm hm hh)

theorem plusResAut_plusResExt {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hq : plusResExt K htm h ∈ plusFlagStab K r D) :
    plusResAut hD ht htm ⟨plusResExt K htm h, hq⟩ = h := by
  apply autMat_injective
  change autMat (matrixEquiv m K (plusResBlockHom hD ht htm _)) = _
  rw [autMat_apply, toMatrix'_matrixEquiv, coe_plusResBlockHom]
  change (autMat (plusResExt K htm h)).submatrix _ _ = _
  rw [autMat_plusResExt, submatrix_extendMat]

theorem plusEBlockHom_plusResExt {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (htm : t + m = r) (hDt : ∀ d ∈ D, d ≤ t) {b : ℕ} (hb : b ∈ D)
    {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hq : plusResExt K htm h ∈ plusFlagStab K r D) :
    plusEBlockHom hD hb ⟨plusResExt K htm h, hq⟩ = 1 := by
  refine Units.ext ?_
  rw [coe_plusEBlockHom, Units.val_one]
  change (autMat (plusResExt K htm h)).submatrix _ _ = 1
  rw [autMat_plusResExt]
  refine submatrix_extendMat_of_disjoint _ (plusEIdx_injective _) (fun k x hkx => ?_) _
  have h1 := (mem_range_plusResIdx htm (plusEIdx (hD b hb) k)).1 ⟨x, hkx.symm⟩
  simp only [plusEIdx, plusPos_inl] at h1
  have := k.isLt
  have := hDt b hb
  omega

end LeviBlock

theorem hasLeviBlocks_plusFlagStab_res [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht3 : D.sup id + 3 ≤ r) :
    HasLeviBlocks ↥(plusFlagStab K r D) (plusBlockOrders (Nat.card K)) := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  set t := D.sup id with htdef
  have ht : t = 0 ∨ t ∈ D := sup_eq_zero_or_mem D
  have htm : t + (r - t) = r := by omega
  have hm : 3 ≤ r - t := by omega
  have hDt : ∀ d ∈ D, d ≤ t := fun d hd => Finset.le_sup (f := id) hd
  have := finite_plusAut (K := K) (r - t)
  obtain ⟨f, -, hK⟩ : ∃ f, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  refine hasLeviBlocks_of_sum (ι₁ := ↥D) (ι₂ := Unit)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K)
    (G₂ := fun _ => (Fin (r - t) ⊕ Fin (r - t) → K) ≃ₗ[K] (Fin (r - t) ⊕ Fin (r - t) → K))
    (fun b => (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
      _).range) (fun _ => orthElementaryGroup (quadPlus (r - t) K))
    (fun b => plusEBlockHom hD' b.2) (fun _ => plusResAut hD' ht htm) ?_ ?_ ?_
    (fun b => commutator_range_plusEBlockHom_le hD' b.2) ?_
    (fun b => isQuasisimple_or_isSolvable_rangeSL _)
    (fun _ => Or.inl (isQuasisimple_plusElementary hm).1)
    (fun b => card_rangeSL_quotient_center)
    (fun _ _ => Or.inr ⟨r - t, hm, card_plusElementary_quotient_center hm hK⟩)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht htm
      (plusResBlockHom_eq_one_of_plusResAut hD' ht htm ((hN g hg).2 ())) hx
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun _ => ?_⟩
    change matrixEquiv (r - t) K (plusResBlockHom hD' ht htm q) = 1
    rw [h3 ht htm (hDt b b.2), map_one]
  · rintro ⟨⟩ h hh
    exact ⟨⟨plusResExt K htm h, plusResExt_mem_plusFlagStab htm hm hDt hh⟩,
      plusResAut_plusResExt hD' ht htm _, fun ⟨⟩ hne => absurd rfl hne,
      fun b => plusEBlockHom_plusResExt hD' htm hDt b.2 _⟩
  · rintro ⟨⟩
    rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus hm]
    have hle : (plusResAut (K := K) hD' ht htm).range ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus (r - t) K) := by
      rintro _ ⟨g, rfl⟩
      exact plusResAut_mem_orthogonalGroup hD' ht htm g
    exact Subgroup.commutator_mono hle hle

end CFSG.AGLEmbedding
