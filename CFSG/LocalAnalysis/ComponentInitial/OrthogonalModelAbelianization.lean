module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin

section CharTwo

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem abelianization_of_reflect_eq_of_two_eq_zero [Finite K] (h2 : (2 : K) = 0)
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂) {v w : V}
    (hv : Q v ≠ 0) (hw : Q w ≠ 0) :
    Abelianization.of (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Q) =
      Abelianization.of ⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v / Q w)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hc
    exact hc.elim hv hw
  have hnorm : Q v = Q (c • w) := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    field_simp at hc
    linear_combination hc
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  have hcw0 : c • w ≠ 0 := fun h => hv (by rw [hnorm, h, QuadraticMap.map_zero])
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hQ hP hv0 hcw0 hnorm
  have hgO := elementaryGroup_le_orthogonalGroup Q hg
  have hconj : (⟨g, hgO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) *
      ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ * ⟨g, hgO⟩⁻¹ =
        ⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ := by
    refine Subtype.ext ?_
    change g * reflect Q v * g⁻¹ = reflect Q w
    rw [reflect_conj hgO, hgv, reflect_smul_of_ne_zero hc0]
  rw [← hconj, map_mul, map_mul, map_inv, mul_comm (Abelianization.of _), mul_inv_cancel_right]

theorem char_two_orthogonal_abelianization_bound [Finite K] (h2 : (2 : K) = 0)
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂)
    (hE : elementaryGroup Q ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q)) :
    CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 2 := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  have hrefl1 : ∀ v, Q v = 0 →
      Abelianization.of (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : O) = 1 := fun v hv => by
    have : (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : O) = 1 :=
      Subtype.ext (reflect_of_map_eq_zero hv)
    rw [this, map_one]
  obtain ⟨x, hx2, hx⟩ : ∃ x : Abelianization O, x ^ 2 = 1 ∧
      ∀ v, Abelianization.of (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : O) ∈
        Subgroup.zpowers x := by
    by_cases h : ∃ v₀, Q v₀ ≠ 0
    · obtain ⟨v₀, hv₀⟩ := h
      refine ⟨Abelianization.of ⟨reflect Q v₀, reflect_mem_orthogonalGroup Q v₀⟩, ?_,
        fun v => ?_⟩
      · have h1 : (⟨reflect Q v₀, reflect_mem_orthogonalGroup Q v₀⟩ : O) ^ 2 = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact reflect_mul_self Q v₀)
        rw [← map_pow, h1, map_one]
      · by_cases hv : Q v = 0
        · rw [hrefl1 v hv]
          exact Subgroup.one_mem _
        · rw [abelianization_of_reflect_eq_of_two_eq_zero h2 hQ hP hv hv₀]
          exact Subgroup.mem_zpowers _
    · push Not at h
      exact ⟨1, one_pow 2, fun v => by rw [hrefl1 v (h v)]; exact Subgroup.one_mem _⟩
  set T : Subgroup (V ≃ₗ[K] V) :=
    ((Subgroup.zpowers x).comap (Abelianization.of : O →* Abelianization O)).map O.subtype
  have hgenT : Set.range (reflect Q) ∪ (elementaryGroup Q : Set (V ≃ₗ[K] V)) ⊆ T := by
    rintro _ (⟨v, rfl⟩ | he)
    · exact ⟨⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩, hx v, rfl⟩
    · have heO : _ ∈ O := elementaryGroup_le_orthogonalGroup Q he
      refine ⟨⟨_, heO⟩, ?_, rfl⟩
      have hmem : (⟨_, heO⟩ : O) ∈ commutator O := by
        have h := hE he
        rw [← Subgroup.map_subtype_commutator] at h
        obtain ⟨y, hy, hyeq⟩ := h
        rwa [show (⟨_, heO⟩ : O) = y from Subtype.ext hyeq.symm]
      have h1 : Abelianization.of (⟨_, heO⟩ : O) = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hmem
      change Abelianization.of _ ∈ Subgroup.zpowers x
      rw [h1]
      exact Subgroup.one_mem _
  have hOT : O ≤ T := hgen.trans ((Subgroup.closure_le T).mpr hgenT)
  have hall : ∀ y : Abelianization O, y ∈ Subgroup.zpowers x := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g', hg', hgg'⟩ := hOT g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  have hexp : ∀ y : Abelianization O, y ^ 2 = 1 := by
    intro y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hall y)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  refine ⟨{ is_comm := ⟨mul_comm⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }, ?_⟩
  have hpos : 0 < orderOf x :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, hx2⟩)
  have : Finite (Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hinj : Function.Injective
      (fun y : Abelianization O => (⟨y, hall y⟩ : Subgroup.zpowers x)) :=
    fun a b h => congrArg Subtype.val h
  calc Nat.card (Abelianization O) ≤ Nat.card (Subgroup.zpowers x) :=
        Nat.card_le_card_of_injective _ hinj
    _ = orderOf x := Nat.card_zpowers x
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hx2)

end CharTwo

@[expose] def IsometryAbelianizationBound (p : ℕ) {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (Q : QuadraticForm K V) : Prop :=
  CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
    (p ≠ 2 → Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 4) ∧
    (p = 2 → Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 2)

@[expose] def WitnessIsometryAbelianizationBound (T : Type) [Group T] (t : StatedLieTag)
    (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ Q : QuadraticForm K (Fin n ⊕ Fin n ⊕ Unit → K), ⇑Q = StatedQuadOdd n K →
      ∀ _e : T ≃* StatedProj (StatedOmega (StatedQuadOdd n K)), IsometryAbelianizationBound p Q
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ Q : QuadraticForm K (Fin n ⊕ Fin n → K), ⇑Q = StatedQuadPlus n K →
      ∀ _e : T ≃* StatedProj (StatedOmega (StatedQuadPlus n K)), IsometryAbelianizationBound p Q
  | .POmegaMinus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ Q : QuadraticForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
        ⇑Q = StatedQuadMinus n K b c →
      ∀ _e : T ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
        IsometryAbelianizationBound p Q
  | _ => True

theorem isometryAbelianizationBound_of_odd {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} (hp2 : p ≠ 2)
    (hchar : ringChar K = p) (hQ : (polarBilin Q).Nondegenerate) :
    IsometryAbelianizationBound p Q := by
  obtain ⟨hEA, hcard, -, -⟩ := odd_orthogonal_abelianization_order_bound (hchar ▸ hp2) hQ
  exact ⟨hEA, fun _ => hcard, fun h => absurd h hp2⟩

theorem orthogonal_model_isometry_abelianization_order_bound (T : Type) [Group T]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel T t n p f) : WitnessIsometryAbelianizationBound T t n p f := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hp, hf, hn, hp2⟩ := h.1
    intro K _ _ hK Q hQ _
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    obtain rfl : Q = quadOdd n K := DFunLike.coe_injective (hQ.trans (coe_quadOdd n K).symm)
    exact isometryAbelianizationBound_of_odd hp2 hchar (regular_quadOdd h2 hn).1
  · obtain ⟨hp, hf, hn⟩ := h.1
    intro K _ _ hK Q hQ _
    have hchar := ringChar_eq_of_card_eq hp hf hK
    obtain rfl : Q = quadPlus n K := DFunLike.coe_injective (hQ.trans (coe_quadPlus n K).symm)
    have hnd := nondegenerate_polarBilin_quadPlus n K
    by_cases hp2 : p = 2
    · subst hp2
      have h2 : (2 : K) = 0 := (two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp)).mpr hchar
      have hn0 : 0 < n := by omega
      obtain ⟨hEA, hcard⟩ := char_two_orthogonal_abelianization_bound h2 hnd
        (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
          (by simp [Fin.ext_iff]))
        (commutator_orthogonalGroup_quadPlus (by omega)).ge
        (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd h2
          (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
          (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) hn0)
      exact ⟨hEA, fun h => absurd rfl h, fun _ => hcard⟩
    · exact isometryAbelianizationBound_of_odd hp2 hchar hnd
  · obtain ⟨hp, hf, hn⟩ := h.1
    intro K _ _ hK b c hirr Q hQ _
    have hchar := ringChar_eq_of_card_eq hp hf hK
    obtain rfl : Q = quadMinus n K b c :=
      DFunLike.coe_injective (hQ.trans (coe_quadMinus n K b c).symm)
    have hnd := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
    by_cases hp2 : p = 2
    · subst hp2
      have h2 : (2 : K) = 0 := (two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp)).mpr hchar
      have hn0 : 0 < n - 1 := by omega
      obtain ⟨hEA, hcard⟩ := char_two_orthogonal_abelianization_bound h2 hnd
        (minusPair_orth (K := K) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
          (by simp [Fin.ext_iff]))
        (commutator_orthogonalGroup_quadMinus hn hirr).ge
        (orthogonalGroup_le_closure_of_two_eq_zero (minusFamily_orth hn0) hnd h2
          (fun x hx hQx => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hx hQx)
          (fun x hx hx0 y hy hxy =>
            exists_eq_smul_of_mem_tailSpace_minusFamily h2 hirr hn0 hx hx0 hy hxy) hn0)
      exact ⟨hEA, fun h => absurd rfl h, fun _ => hcard⟩
    · exact isometryAbelianizationBound_of_odd hp2 hchar hnd

end CFSG.LocalAnalysis.ComponentInitial
