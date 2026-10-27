module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3D
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3C
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit InvClassL HBlocks

section ToSL

variable {H : Type*} [Group H] {n : ℕ} {R : Type*} [CommRing R]

@[expose] def toSL (f : H →* GL (Fin n) R) (hf : ∀ h, (f h : Matrix (Fin n) (Fin n) R).det = 1) :
    H →* SpecialLinearGroup (Fin n) R where
  toFun h := ⟨f h, hf h⟩
  map_one' := Subtype.ext (by
    change ((f 1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1
    rw [map_one, Units.val_one])
  map_mul' a b := Subtype.ext (by
    change ((f (a * b) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (f a : Matrix (Fin n) (Fin n) R) * (f b : Matrix (Fin n) (Fin n) R)
    rw [map_mul, Units.val_mul])

theorem toGL_toSL (f : H →* GL (Fin n) R) (hf : ∀ h, (f h : Matrix (Fin n) (Fin n) R).det = 1)
    (h : H) : SpecialLinearGroup.toGL (toSL f hf h) = f h := Units.ext rfl

theorem det_eq_one_of_perfect [Group.IsPerfect H] (f : H →* GL (Fin n) R) (h : H) :
    (f h : Matrix (Fin n) (Fin n) R).det = 1 := by
  have key := eq_of_perfect_of_center (α := GeneralLinearGroup.det.comp f) (β := 1)
    fun g => Subgroup.mem_center_iff.mpr fun _ => mul_comm _ _
  have h1 := DFunLike.congr_fun key h
  rw [MonoidHom.comp_apply, MonoidHom.one_apply] at h1
  rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]

end ToSL

section SL4

variable {K : Type} [Field K]

theorem slConjugation_mem_center {P : GL (Fin 4) K} {s : SpecialLinearGroup (Fin 4) K}
    (hs : s ∈ center (SpecialLinearGroup (Fin 4) K)) :
    CatalogueBHigherLinearAction.slConjugation 4 K P s = s := by
  apply SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  have hc : SpecialLinearGroup.toGL s * P = P * SpecialLinearGroup.toGL s := by
    have h1 := (scalars_eq_center 4 K).symm ▸ hs
    obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, hc]
    exact (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ _) _).eq
  rw [← hc, mul_inv_cancel_right]

theorem mem_scalars_of_slConjugation_mem {P : GL (Fin 4) K} {s : SpecialLinearGroup (Fin 4) K}
    (hs : CatalogueBHigherLinearAction.slConjugation 4 K P s ∈ scalars 4 K) : s ∈ scalars 4 K := by
  rw [scalars_eq_center] at hs ⊢
  have h := slConjugation_mem_center (P := P⁻¹) hs
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h
  rw [h]
  exact hs

theorem X1_eq_smul (l : K) : X1 l = l • X1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1]

end SL4

theorem rowOHom_neg_one {k : Type} [Field k] {m : ℕ} {δ : kˣ}
    (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k)) :
    rowOHom δ ψ (-1) = 1 := by
  have h : rowOAction δ (-1) = 1 := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    rw [rowOAction_val, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.conjTranspose_neg, Matrix.conjTranspose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]
    rfl
  rw [rowOHom, MonoidHom.comp_apply, h, map_one]

variable {G : Type} [Group G] {Q : Subgroup G} {K : Type} [Field K] [Finite K]

theorem rowO_x_alternative (hK2 : ringChar K ≠ 2) {x : G} (hx : x ∈ normalizer (Q : Set G))
    (e : ↥Q ⧸ center ↥Q ≃* projectiveSL 4 K) {θ : SpecialLinearGroup (Fin 4) K →* ↥Q}
    (hθs : Function.Surjective θ) (hθ : ∀ s, piQ e (θ s) = proj 4 K s)
    (hθk : θ.ker ≤ scalars 4 K) (hθ1 : θ negOne4 = 1) (hLZ : center ↥(Lay Q x) = ⊥)
    (hrow : SelectorRowO 4 K (MonoidHom.id (MulAut (projectiveSL 4 K)))
      (OuterAutomorphisms.inner (projectiveSL 4 K)) (phi hx e) ((Jp e x).map MulAut.conj)) :
    ∀ w ∈ Lay Q x, orderOf w = 2 →
      ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
        X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
        (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
        X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
        IsSLTwoOver (Nat.card K) ↥X₁ ∧ IsSLTwoOver (Nat.card K) ↥X₂ := by
  classical
  obtain ⟨δ, hδ, ψ, R, C, -, -, -, -, -, hL, -, hker, -⟩ := hrow
  have : Fact (¬ IsSquare (δ : K)) := ⟨hδ⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hEcard := extension_card (δ : K)
  have : Finite (extension (δ : K)) := Nat.finite_of_card_ne_zero (by
    rw [hEcard]
    exact pow_ne_zero _ Nat.card_pos.ne')
  have := Fintype.ofFinite (extension (δ : K))
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) (extension (δ : K))) := by
    apply LinearGroups.special_linear_dimension_two_perfect
    have hq : 3 ≤ Nat.card K := by
      have := Fintype.ofFinite K
      have hodd := FiniteField.odd_card_of_char_ne_two (F := K) hK2
      have h1 : 1 < Fintype.card K := Fintype.one_lt_card
      rw [Nat.card_eq_fintype_card]
      omega
    have h4 : 4 ≤ Fintype.card (extension (δ : K)) := by
      rw [← Nat.card_eq_fintype_card, hEcard]
      nlinarith
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (extension (δ : K)))) (n := 4)
      (by rw [Finset.card_univ]; exact h4)
    exact ⟨s, hs⟩
  set σO := toSL (rowOHom δ ψ) (det_eq_one_of_perfect _) with hσO
  set sC := CatalogueBHigherLinearAction.slConjugation 4 K C with hsC
  set lam := θ.comp (sC.toMonoidHom.comp σO) with hlam
  have hconj : ∀ g, MulAut.conj (piQ e (lam g)) =
      MulAut.conj (conjAut 4 K C) (conjAut 4 K (rowOHom δ ψ g)) := by
    intro g
    change MulAut.conj (piQ e (θ (sC (σO g)))) = _
    rw [hθ, ← conjAut_toGL, hsC, CatalogueBHigherLinearAction.toGL_slConjugation, hσO, toGL_toSL,
      map_mul, map_mul, map_inv]
    rfl
  rw [Subgroup.map_id] at hL
  have hmemJ : ∀ g, piQ e (lam g) ∈ Jp e x := by
    intro g
    have h1 : MulAut.conj (piQ e (lam g)) ∈ (Jp e x).map MulAut.conj := by
      rw [hL, hconj]
      exact mem_map_of_mem _ ⟨g, rfl⟩
    obtain ⟨j, hj, hjeq⟩ := h1
    rwa [CSL.conj_injective hjeq] at hj
  have hlamL : lam.range ≤ LQ Q x := by
    apply le_LQ_of_perfect e
    · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
        hperf.commutator_eq_top]
    · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hmemJ g
  intro w hwL hw2
  have hwQ : w ∈ Q := (Lay_le hwL).1
  set q : ↥Q := ⟨w, hwQ⟩ with hq
  have hqL : q ∈ LQ Q x := hwL
  have hπq : MulAut.conj (piQ e q) ∈ (rowOJ δ ψ).map (MulAut.conj (conjAut 4 K C)).toMonoidHom := by
    rw [← hL]
    exact mem_map_of_mem _ (mem_map_of_mem _ hqL)
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hπq
  have hqlam : q = lam g := by
    apply piQ_injOn e hLZ hqL (hlamL ⟨g, rfl⟩)
    apply CSL.conj_injective
    rw [hconj]
    exact hg.symm
  set t' := sC (σO g) with ht'
  have hθt' : θ t' = q := hqlam.symm
  have hw1 : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hθt2 : θ (t' * t') = 1 := by
    rw [map_mul, hθt']
    exact Subtype.ext hw1
  have hgg : g * g = 1 ∨ g * g = -1 := by
    rw [← hker]
    have h1 : t' * t' ∈ scalars 4 K := hθk hθt2
    rw [ht', ← map_mul, ← map_mul] at h1
    have h3 := mem_scalars_of_slConjugation_mem h1
    have h4 : conjAut 4 K (SpecialLinearGroup.toGL (σO (g * g))) = 1 := by
      rw [conjAut_toGL, proj_eq_one_iff.mpr h3, map_one]
    rwa [hσO, toGL_toSL] at h4
  have hσO1 : σO (-1) = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [hσO, toGL_toSL, rowOHom_neg_one, map_one]
  have ht'2 : t' * t' = 1 := by
    rw [ht', ← map_mul, ← map_mul]
    rcases hgg with h | h <;> rw [h]
    · rw [map_one, map_one]
    · rw [hσO1, map_one]
  have hw1' : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2
    omega
  have hns : ∀ a : K, (t' : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
    intro a ha
    apply hw1'
    have hmat : (t' : Matrix (Fin 4) (Fin 4) K) * t' = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ht'2, Matrix.SpecialLinearGroup.coe_one]
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hmat
    have ha2 : a * a = 1 := by
      have := congrFun (congrFun hmat 0) 0
      simpa using this
    have hθ1' : θ t' = 1 := by
      rcases mul_self_eq_one_iff.mp ha2 with rfl | rfl
      · have : t' = 1 := Subtype.ext (by rw [ha, one_smul, Matrix.SpecialLinearGroup.coe_one])
        rw [this, map_one]
      · have : t' = negOne4 := Subtype.ext (by rw [ha, neg_one_smul]; rfl)
        rw [this, hθ1]
    rw [hθt'] at hθ1'
    exact congrArg Subtype.val hθ1'
  have hX : (t' : Matrix (Fin 4) (Fin 4) K) * t' = (1 : K) • 1 := by
    rw [one_smul, ← Matrix.SpecialLinearGroup.coe_mul, ht'2, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨l, hl0, hl1, -, P, hP⟩ | ⟨l, hl0, hl1, hdet, -⟩ | ⟨hsq, -⟩ :=
    classify_inv hK2 hX one_ne_zero hns
  · have hl : l = 1 ∨ l = -1 := by
      have : l * l = 1 := by rw [← sq, ← hl1]
      exact mul_self_eq_one_iff.mp this
    have htP : (t' : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K) * X1 l := by
      rw [X1_eq_smul l, Matrix.mul_smul, ← hP, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0,
        one_smul]
    set θ' := θ.comp (CatalogueBHigherLinearAction.slConjugation 4 K P).toMonoidHom with hθ'
    set t := CatalogueBHigherLinearAction.slConjugation 4 K P⁻¹ t' with htdef
    have ht : (t : Matrix (Fin 4) (Fin 4) K) = X1 l := by
      rw [htdef, coe_slConjugation, inv_inv, Matrix.mul_assoc, htP, ← Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hθ't : θ' t = q := by
      rw [hθ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, htdef, ← MulAut.mul_apply,
        ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, hθt']
    have hθ's : Function.Surjective θ' := hθs.comp (MulEquiv.surjective _)
    have hθ'k : θ'.ker ≤ scalars 4 K := fun s hs =>
      mem_scalars_of_slConjugation_mem (hθk hs)
    have hθ'1 : θ' negOne4 = 1 := by
      rw [hθ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        slConjugation_mem_center (scalars_le_center 4 K (by
          rw [mem_scalars]
          refine ⟨-1, by norm_num, ?_⟩
          change (-1 : Matrix (Fin 4) (Fin 4) K) = scalar (Fin 4) ((-1 : Kˣ) : K)
          rw [Units.val_neg, Units.val_one, map_neg, map_one])), hθ1]
    have hres := x_alternative hK2 hθ's hθ'k hθ'1 hl ht
    rw [hθ't] at hres
    exact hres
  · exfalso
    have hdet1 : (l⁻¹ • (t' : Matrix (Fin 4) (Fin 4) K)).det = 1 := by
      rw [Matrix.det_smul, t'.2, mul_one, Fintype.card_fin, inv_pow,
        show l ^ 4 = (l ^ 2) ^ 2 by ring, ← hl1, one_pow, inv_one]
    rw [hdet1] at hdet
    apply h2
    linear_combination hdet
  · exact absurd ⟨1, (one_mul 1).symm⟩ hsq

end CFSG.ComponentClassification.HarrisLit.C3
