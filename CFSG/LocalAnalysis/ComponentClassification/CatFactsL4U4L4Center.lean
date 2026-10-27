module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

theorem sq_mem_of_index_le_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.index ≤ 2) (g : G) : g ^ 2 ∈ N := by
  have hi0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 by omega) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact Subgroup.mem_top _
  · have := Subgroup.normal_of_index_eq_two h2
    have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, h2]
    have h1 : (QuotientGroup.mk g : G ⧸ N) ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1

theorem card_ker_det_two (E : Type*) [Field E] [Fintype E] :
    Nat.card (GeneralLinearGroup.det : GL (Fin 2) E →* Eˣ).ker =
      Fintype.card E * (Fintype.card E ^ 2 - 1) := by
  classical
  set Q := Fintype.card E with hQ
  have h := Subgroup.card_ker_mul_card_of_surjective
    (f := (GeneralLinearGroup.det : GL (Fin 2) E →* Eˣ)) GeneralLinearGroup.det_surjective
  have hunits : Nat.card Eˣ = Q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hGL : Nat.card (GL (Fin 2) E) = (Q ^ 2 - 1) * (Q ^ 2 - Q) := by
    rw [Matrix.card_GL_field (𝔽 := E) 2, Fin.prod_univ_two]
    norm_num [hQ]
  rw [hunits, hGL] at h
  have hq : 2 ≤ Q := Fintype.one_lt_card
  have h2 : (Q ^ 2 - 1) * (Q ^ 2 - Q) = Q * (Q ^ 2 - 1) * (Q - 1) := by
    have : Q ^ 2 - Q = Q * (Q - 1) := by
      rw [Nat.mul_sub, mul_one, pow_two]
    rw [this]
    ring
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (show 0 < Q - 1 by omega) h

theorem scalar_neg_one_mem_of_perfect {F : Type} [Field F] [Fintype F] (k : GL (Fin 4) F)
    (l : Fˣ) (hsq : k ^ 2 = GeneralLinearGroup.scalar (Fin 4) l) (hns : ¬ IsSquare (l : F))
    (hl1 : (l : F) = -1) (J₁ : Subgroup (Subgroup.centralizer {k})) (hJ₁ : ⁅J₁, J₁⁆ = J₁)
    (hcard : Fintype.card F ^ 2 * (Fintype.card F ^ 4 - 1) ≤ 2 * Nat.card J₁) :
    ordinaryCentralizerScalar k (-1) ∈ J₁ := by
  classical
  have hstr := nonsquare_projective_centralizer_structure 4 (by norm_num) k l hsq hns
  let : Fact (¬ IsSquare l.val) := ⟨hns⟩
  let := matrixModule k l hsq
  dsimp only at hstr
  obtain ⟨-, hfinE, hm, -, -, -, -, -, -, -, -, e', -, -, -, -, -, -, he'scal, -⟩ := hstr
  have hm2 : Module.finrank (extension l.val) (Fin 4 → F) = 2 := by omega
  have : Finite (extension l.val) := Module.finite_of_finite F
  let : Fintype (extension l.val) := Fintype.ofFinite _
  have hcardE : Fintype.card (extension l.val) = Fintype.card F ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := F), hfinE]
  set τ : GL (Fin (Module.finrank (extension l.val) (Fin 4 → F))) (extension l.val) ≃*
      GL (Fin 2) (extension l.val) :=
    Units.mapEquiv (Matrix.reindexRingEquiv (extension l.val) (finCongr hm2)).toMulEquiv with hτ
  set ρ : Subgroup.centralizer {k} →* GL (Fin 2) (extension l.val) :=
    τ.toMonoidHom.comp e'.toMonoidHom with hρ
  have hρinj : Function.Injective ρ := τ.injective.comp e'.injective
  set J₂ := J₁.map ρ with hJ₂
  set D := (GeneralLinearGroup.det : GL (Fin 2) (extension l.val) →* (extension l.val)ˣ).ker
    with hD
  have hJ₂D : J₂ ≤ D := by
    have hp : ⁅J₂, J₂⁆ = J₂ := by rw [hJ₂, ← Subgroup.map_commutator, hJ₁]
    rw [← hp, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hJ₂card : Nat.card J₂ = Nat.card J₁ := Subgroup.card_map_of_injective hρinj
  have hDcard : Nat.card D = Fintype.card F ^ 2 * (Fintype.card F ^ 4 - 1) := by
    rw [hD, card_ker_det_two, hcardE, ← pow_mul]
  have hidx : (J₂.subgroupOf D).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (J₂.subgroupOf D)
    have h2 : Nat.card (J₂.subgroupOf D) = Nat.card J₂ := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hJ₂D]
    rw [h2, hJ₂card, hDcard] at h1
    have hpos : 0 < Nat.card J₁ := Nat.card_pos
    by_contra hlt
    have : 3 * Nat.card J₁ ≤ Nat.card J₁ * (J₂.subgroupOf D).index := by
      rw [mul_comm 3]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  set r : extension l.val := AdjoinRoot.root (quadraticPolynomial l.val) with hr
  have hr2 : r ^ 2 = -1 := by
    rw [hr, extension_root_square, congrArg (algebraMap F (extension l.val)) hl1, map_neg,
      map_one]
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hr2
    exact zero_ne_one (neg_eq_zero.1 hr2.symm).symm
  let u : GL (Fin 2) (extension l.val) :=
    ⟨Matrix.diagonal ![r, r⁻¹], Matrix.diagonal ![r⁻¹, r],
      by rw [Matrix.diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, hr0],
      by rw [Matrix.diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, hr0]⟩
  have huD : u ∈ D := by
    rw [hD, MonoidHom.mem_ker]
    apply Units.ext
    simp [u, GeneralLinearGroup.val_det_apply, Matrix.det_diagonal, Fin.prod_univ_two, hr0]
  have hu2 : u ^ 2 = -1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, pow_two,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, ← pow_two, hr2, inv_pow, Matrix.neg_apply]
  have hneg : (-1 : GL (Fin 2) (extension l.val)) ∈ J₂ := by
    have h1 := sq_mem_of_index_le_two hidx ⟨u, huD⟩
    rw [Subgroup.mem_subgroupOf] at h1
    rw [← hu2]
    exact h1
  have hρneg : ρ (ordinaryCentralizerScalar k (-1)) = -1 := by
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      he'scal (-1)]
    apply Units.ext
    have h1 : ((GeneralLinearGroup.scalar (Fin (Module.finrank (extension l.val) (Fin 4 → F))))
        (Units.map (algebraMap F (extension l.val)).toMonoidHom (-1)) :
        Matrix (Fin (Module.finrank (extension l.val) (Fin 4 → F)))
          (Fin (Module.finrank (extension l.val) (Fin 4 → F))) (extension l.val)) = -1 := by
      rw [GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [hτ, Units.coe_mapEquiv, Units.val_neg, Units.val_one]
    change Matrix.reindex _ _ _ = _
    rw [h1]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.reindex_apply]
    · have hij' : (finCongr hm2).symm i ≠ (finCongr hm2).symm j := fun h => hij (by
        simpa using congrArg (finCongr hm2) h)
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.neg_apply,
        Matrix.one_apply_ne hij, Matrix.one_apply_ne hij']
  rw [← hρneg] at hneg
  exact (Subgroup.mem_map_iff_mem hρinj).1 hneg

theorem center_eq_bot_of_inner_L4 {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ2 : IsPGroup 2 (Subgroup.center Y)) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hq : Odd (Fintype.card F)) (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 4 F))
    {ℓ : Y} (hℓ : ℓ ∉ Subgroup.center Y) (hℓ2 : ℓ ^ 2 ∈ Subgroup.center Y)
    {J : Subgroup Y} (hJ : J ≤ Subgroup.centralizer {ℓ}) (hJp : ⁅J, J⁆ = J)
    (hJc : Fintype.card F ^ 2 * (Fintype.card F ^ 4 - 1) ≤ 2 * Nat.card J)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1)
    (hsJ : s ∣ Nat.card J)
    (hnc : ∀ x ∈ J, (∀ w ∈ J, x * w = w * x) → x * x = 1 → x = 1) :
    Subgroup.center Y = ⊥ := by
  classical
  have := Fact.mk hs
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := J) s hsJ
  set y : Y := (y' : Y) with hydef
  have hy : orderOf y = s := by rw [hydef, Subgroup.orderOf_coe, hy']
  have hyℓ : y * ℓ = ℓ * y := Subgroup.mem_centralizer_singleton_iff.mp (hJ y'.2)
  have hq3 := card_mod_four_of_inner_L4 hZ2 hq e hℓ hℓ2 hs hs2 hsq hy hyℓ
  by_contra hZ
  obtain ⟨ψ, hψ⟩ := exists_equiv_statedSL_four hZ2 hZ hq3 e
  set φ₁ : Y →* GL (Fin 4) F := (StatedSL 4 F).subtype.comp ψ.toMonoidHom with hφ₁
  have hφ₁inj : Function.Injective φ₁ := Subtype.val_injective.comp ψ.injective
  have hmk : ∀ u : Y, projToPGL 4 F (QuotientGroup.mk (ψ u)) = ProjGenLinGroup.mk (φ₁ u) :=
    fun u => rfl
  have hmk1 : ∀ u : Y, ProjGenLinGroup.mk (φ₁ u) = 1 ↔ u ∈ Subgroup.center Y := by
    intro u
    rw [← hmk, (projToPGL_injective 4).eq_iff' (map_one _), ← hψ, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
  set k : GL (Fin 4) F := φ₁ ℓ with hk
  have hyZ : y ∉ Subgroup.center Y := not_mem_of_isPGroup_two hZ2 hs hs2 hy
  obtain ⟨l, hl, hns⟩ := not_isSquare_of_comm_odd_order (n := 4) (e := 1) (by norm_num) hq hs
    hs2 (by simpa using hsq) (by norm_num) k
    (by rw [hk]; exact fun h1 => hℓ ((hmk1 ℓ).1 h1))
    (by rw [hk, ← map_pow, ← map_pow]; exact (hmk1 _).2 hℓ2) (φ₁ y)
    (fun h1 => hyZ ((hmk1 y).1 h1))
    (by rw [← map_pow, ← map_pow, show y ^ s = 1 by rw [← hy]; exact pow_orderOf_eq_one y,
      map_one, map_one])
    (by rw [hk, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hyℓ])
  have hl1 : (l : F) = -1 :=
    (sq_eq_neg_one_of_det_eq_one k l hl hns (det_eq_one_of_mem_statedSL (ψ ℓ).2)).1
  have hJk : J.map φ₁ ≤ Subgroup.centralizer {k} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hk, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hJ hx)]
  set J₁ := (J.map φ₁).subgroupOf (Subgroup.centralizer {k}) with hJ₁
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by
    apply Subgroup.map_injective (Subgroup.centralizer {k}).subtype_injective
    rw [Subgroup.map_commutator, hJ₁, Subgroup.map_subgroupOf_eq_of_le hJk,
      ← Subgroup.map_commutator, hJp]
  have hJ₁c : Nat.card J₁ = Nat.card J := by
    rw [hJ₁, ← Subgroup.card_map_of_injective (Subgroup.centralizer {k}).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hJk, Subgroup.card_map_of_injective hφ₁inj]
  have hmem := scalar_neg_one_mem_of_perfect k l hl hns hl1 J₁ hJ₁p (by rw [hJ₁c]; exact hJc)
  rw [hJ₁, Subgroup.mem_subgroupOf, ordinaryCentralizerScalar_apply] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have hneg1 : (GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) : GL (Fin 4) F) = -1 := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hneg1] at hxe
  apply hZ
  exfalso
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, map_one] at hxe
    have h2 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) hxe
    simp only [Units.val_one, Units.val_neg, Matrix.one_apply_eq, Matrix.neg_apply] at h2
    have h3 : (2 : F) = 0 := by linear_combination h2
    have hc : ringChar F ∣ 2 := (ringChar.spec F 2).1 (by exact_mod_cast h3)
    have hc2 : ringChar F = 2 :=
      (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 hc
    have := FiniteField.even_card_iff_char_two.1 hc2
    omega
  apply hx1
  refine hnc x hx (fun w _ => hφ₁inj ?_) (hφ₁inj ?_)
  · rw [map_mul, map_mul, hxe]
    exact (Commute.neg_one_left _).eq
  · rw [map_mul, hxe, map_one, neg_one_mul, neg_neg]

end CFSG.ComponentClassification.CatFactsL4U4
