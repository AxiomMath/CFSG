module

public import CFSG.ClassicalInvolution.Phan.PhanD3Coord
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Main

public section

namespace CFSG.ClassicalInvolution.PhanD4

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.MF15

section Spans

variable {F : Type} [Field F] {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (h2 : (2 : F) ≠ 0)

include h2 in
theorem two_eq_zero_of_eq_neg {a : F} (h : a = -a) : a = 0 := by
  have : (2 : F) * a = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

include hε h4 h2 in
theorem mem_inf01 (x : Fin 4 ⊕ Fin 4 → F) :
    x ∈ (frame0 (F := F)).span ⊓ (frame1 ε hε h4).span ↔
      ∃ a b : F, x = vecXY ![a, b, 0, 0] ![-a, -ε * b, 0, 0] := by
  rw [Submodule.mem_inf, Frame.mem_span_iff_inv _ h2, Frame.mem_span_iff_inv _ h2]
  constructor
  · rintro ⟨h0, h1⟩
    rw [vecXY_eta x] at h0 h1
    rw [La_neg_one_frame0] at h0
    rw [La_neg_one_frame1] at h1
    have a2 := congrFun h0 (Sum.inl 2)
    have a3 := congrFun h0 (Sum.inl 3)
    have b2 := congrFun h0 (Sum.inr 2)
    have b3 := congrFun h0 (Sum.inr 3)
    have c0 := congrFun h1 (Sum.inr 0)
    have c1 := congrFun h1 (Sum.inr 1)
    simp at a2 a3 b2 b3 c0 c1
    have x2 := two_eq_zero_of_eq_neg h2 a2
    have x3 := two_eq_zero_of_eq_neg h2 a3
    have y2 := two_eq_zero_of_eq_neg h2 b2
    have y3 := two_eq_zero_of_eq_neg h2 b3
    refine ⟨x (.inl 0), x (.inl 1), ?_⟩
    ext s
    rcases s with i | i <;> fin_cases i <;> simp [x2, x3, y2, y3] <;>
      first | linear_combination c0 | linear_combination -c0 | linear_combination c1
  · rintro ⟨a, b, rfl⟩
    rw [La_neg_one_frame0, La_neg_one_frame1]
    refine ⟨?_, ?_⟩ <;>
    · ext s
      rcases s with i | i <;> fin_cases i <;> simp <;> field_simp

include hε h4 h2 in
theorem mem_inf12 (x : Fin 4 ⊕ Fin 4 → F) :
    x ∈ (frame1 ε hε h4).span ⊓ (frame2 (F := F)).span ↔
      ∃ a b : F, x = vecXY ![0, 0, a, b] ![0, 0, a, ε * b] := by
  rw [Submodule.mem_inf, Frame.mem_span_iff_inv _ h2, Frame.mem_span_iff_inv _ h2]
  constructor
  · rintro ⟨h1, h0⟩
    rw [vecXY_eta x] at h0 h1
    rw [La_neg_one_frame2] at h0
    rw [La_neg_one_frame1] at h1
    have a0 := congrFun h0 (Sum.inl 0)
    have a1 := congrFun h0 (Sum.inl 1)
    have b0 := congrFun h0 (Sum.inr 0)
    have b1 := congrFun h0 (Sum.inr 1)
    have c2 := congrFun h1 (Sum.inl 2)
    have c3 := congrFun h1 (Sum.inr 3)
    simp at a0 a1 b0 b1 c2 c3
    have x0 := two_eq_zero_of_eq_neg h2 a0
    have x1 := two_eq_zero_of_eq_neg h2 a1
    have y0 := two_eq_zero_of_eq_neg h2 b0
    have y1 := two_eq_zero_of_eq_neg h2 b1
    refine ⟨x (.inl 2), x (.inl 3), ?_⟩
    ext s
    rcases s with i | i <;> fin_cases i <;> simp [x0, x1, y0, y1] <;>
      first | linear_combination c2 | linear_combination -c2 | linear_combination c3 |
        linear_combination -c3
  · rintro ⟨a, b, rfl⟩
    rw [La_neg_one_frame2, La_neg_one_frame1]
    refine ⟨?_, ?_⟩ <;>
    · ext s
      rcases s with i | i <;> fin_cases i <;> simp <;> field_simp

omit h4 in
@[expose] def mapB (ε : F) : (F × F) →ₗ[F] (Fin 4 ⊕ Fin 4 → F) where
  toFun p := vecXY ![p.1, p.2, 0, 0] ![-p.1, -ε * p.2, 0, 0]
  map_add' p q := by
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
    all_goals ring
  map_smul' c p := by
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
    all_goals ring

omit h4 in
@[expose] def mapC (ε : F) : (F × F) →ₗ[F] (Fin 4 ⊕ Fin 4 → F) where
  toFun p := vecXY ![0, 0, p.1, p.2] ![0, 0, p.1, ε * p.2]
  map_add' p q := by
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
    all_goals ring
  map_smul' c p := by
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
    all_goals ring

omit h4 in
theorem mapB_injective : Function.Injective (mapB ε) := by
  intro p q h
  have h1 := congrFun h (Sum.inl 0)
  have h2' := congrFun h (Sum.inl 1)
  simp [mapB] at h1 h2'
  exact Prod.ext h1 h2'

omit h4 in
theorem mapC_injective : Function.Injective (mapC ε) := by
  intro p q h
  have h1 := congrFun h (Sum.inl 2)
  have h2' := congrFun h (Sum.inl 3)
  simp [mapC] at h1 h2'
  exact Prod.ext h1 h2'

include hε h4 h2 in
theorem inf01_eq_range :
    (frame0 (F := F)).span ⊓ (frame1 ε hε h4).span = LinearMap.range (mapB ε) := by
  ext x
  rw [mem_inf01 hε h4 h2, LinearMap.mem_range]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩

include hε h4 h2 in
theorem inf12_eq_range :
    (frame1 ε hε h4).span ⊓ (frame2 (F := F)).span = LinearMap.range (mapC ε) := by
  ext x
  rw [mem_inf12 hε h4 h2, LinearMap.mem_range]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩

include hε h4 h2 in
theorem finrank_inf01 :
    Module.finrank F ↥((frame0 (F := F)).span ⊓ (frame1 ε hε h4).span) = 2 := by
  rw [inf01_eq_range hε h4 h2, LinearMap.finrank_range_of_inj mapB_injective]
  simp

include hε h4 h2 in
theorem finrank_inf12 :
    Module.finrank F ↥((frame1 ε hε h4).span ⊓ (frame2 (F := F)).span) = 2 := by
  rw [inf12_eq_range hε h4 h2, LinearMap.finrank_range_of_inj mapC_injective]
  simp

include hε h4 h2 in
theorem not_hasSingularVector_inf01 (hεs : ¬ IsSquare (-ε)) :
    ¬ HasSingularVector (quadPlus 4 F) ((frame0 (F := F)).span ⊓ (frame1 ε hε h4).span) := by
  rintro ⟨v, hv, hv0, hQ⟩
  obtain ⟨a, b, rfl⟩ := (mem_inf01 hε h4 h2 v).mp hv
  rw [Q_vecXY] at hQ
  simp [Fin.sum_univ_four] at hQ
  have hb : b = 0 := by
    by_contra hb
    exact hεs ⟨a / b, by field_simp; linear_combination hQ⟩
  subst hb
  have ha : a = 0 := by
    simpa using hQ
  subst ha
  exact hv0 (by ext s; rcases s with i | i <;> fin_cases i <;> simp)

include hε h4 h2 in
theorem not_hasSingularVector_inf12 (hεs : ¬ IsSquare (-ε)) :
    ¬ HasSingularVector (quadPlus 4 F) ((frame1 ε hε h4).span ⊓ (frame2 (F := F)).span) := by
  rintro ⟨v, hv, hv0, hQ⟩
  obtain ⟨a, b, rfl⟩ := (mem_inf12 hε h4 h2 v).mp hv
  rw [Q_vecXY] at hQ
  simp [Fin.sum_univ_four] at hQ
  have hb : b = 0 := by
    by_contra hb
    exact hεs ⟨a / b, by field_simp; linear_combination -hQ⟩
  subst hb
  have ha : a = 0 := by
    simpa using hQ
  subst ha
  exact hv0 (by ext s; rcases s with i | i <;> fin_cases i <;> simp)

end Spans

section Orth

variable {F : Type} [Field F]

theorem polar_incl_frame0_frame2 (X Y : Matrix (Fin 2) (Fin 2) F) :
    polar (quadPlus 4 F) ((frame0 (F := F)).incl X) ((frame2 (F := F)).incl Y) = 0 := by
  simp [Frame.incl_apply, frame0, frame2, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂,
    Frame.f₂, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, polar_vecXY,
    Fin.sum_univ_four]

theorem frame0_La_comm_frame2 (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (frame0 (F := F)).La A * (frame2 (F := F)).La B =
      (frame2 (F := F)).La B * (frame0 (F := F)).La A :=
  Frame.La_comm_of_orth polar_incl_frame0_frame2 A B

theorem frame0_La_comm_frame2_swap (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (frame0 (F := F)).La A * (frame2 (F := F)).swap.La B =
      (frame2 (F := F)).swap.La B * (frame0 (F := F)).La A :=
  Frame.La_comm_of_orth (fun X Y => by
    rw [Frame.incl_swap, polar_incl_frame0_frame2]) A B

theorem frame2_La_comm_swap (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (frame2 (F := F)).La A * (frame2 (F := F)).swap.La B =
      (frame2 (F := F)).swap.La B * (frame2 (F := F)).La A :=
  Frame.La_comm_La_swap _ A B

end Orth

section Homs

open CFSG.ClassicalInvolution.Phan (Su B12 B23)

variable {F K' : Type} [Field F] [Field K'] [Algebra F K'] [Finite F] [Finite K']
  {p e : ℕ} [Fact p.Prime] [CharP K' p] {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0)
  (h2 : (2 : F) ≠ 0) (hεs : ¬ IsSquare (-ε)) (hK : Nat.card F = p ^ e)
  (hK' : Nat.card K' = (p ^ e) ^ 2) (hodd : Odd (Nat.card F))

include hε h4 h2 hεs hK hK' hodd in
theorem exists_hom_01 :
    ∃ θ : Su K' p e 3 →* ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)), Function.Injective θ ∧
      θ.range = (frame0 (F := F)).La.range ⊔ (frame1 ε hε h4).La.range ∧
      (B12 K' p e).map θ = (frame0 (F := F)).La.range ∧
      (B23 K' p e).map θ = (frame1 ε hε h4).La.range :=
  Frame.exists_hom_of_not_hasSingularVector hK hK' hodd (frame1_comm_frame0 ε hε h4).symm
    (finrank_inf01 hε h4 h2) (not_hasSingularVector_inf01 hε h4 h2 hεs)

include hε h4 h2 hεs hK hK' hodd in
theorem exists_hom_12 :
    ∃ θ : Su K' p e 3 →* ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)), Function.Injective θ ∧
      θ.range = (frame1 ε hε h4).La.range ⊔ (frame2 (F := F)).La.range ∧
      (B12 K' p e).map θ = (frame1 ε hε h4).La.range ∧
      (B23 K' p e).map θ = (frame2 (F := F)).La.range :=
  Frame.exists_hom_of_not_hasSingularVector hK hK' hodd (frame2_comm_frame1 ε hε h4)
    (finrank_inf12 hε h4 h2) (not_hasSingularVector_inf12 hε h4 h2 hεs)

include hε h4 h2 hεs hK hK' hodd in
theorem exists_hom_13 :
    ∃ θ : Su K' p e 3 →* ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)), Function.Injective θ ∧
      θ.range = (frame1 ε hε h4).La.range ⊔ (frame2 (F := F)).swap.La.range ∧
      (B12 K' p e).map θ = (frame1 ε hε h4).La.range ∧
      (B23 K' p e).map θ = (frame2 (F := F)).swap.La.range :=
  Frame.exists_hom_of_not_hasSingularVector hK hK' hodd
    (by rw [Frame.La_swap_neg_one]; exact frame2_comm_frame1 ε hε h4)
    (by rw [Frame.span_eq_swap_span]; exact finrank_inf12 hε h4 h2)
    (by rw [Frame.span_eq_swap_span]; exact not_hasSingularVector_inf12 hε h4 h2 hεs)

end Homs

end CFSG.ClassicalInvolution.PhanD4
