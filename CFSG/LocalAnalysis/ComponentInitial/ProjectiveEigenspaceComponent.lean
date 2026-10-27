module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentQuadratic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentLift

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CatalogueBProjectiveInvolution
open scoped MatrixGroups

namespace ProjectiveEigenspace

variable {K : Type*} [Field K] {n : ℕ}

theorem mk_mem_centralizer_of_mem_map {T g : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    (hg : g ∈ L.map (centralizer {T}).subtype) :
    ProjGenLinGroup.mk g ∈ centralizer {ProjGenLinGroup.mk T} := by
  obtain ⟨x, -, rfl⟩ := hg
  exact (ordinaryCentralizerProjection T x).2

theorem mk_mem_of_mem_map {T g : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hLB : L.map (ordinaryCentralizerProjection T) = B)
    (hg : g ∈ L.map (centralizer {T}).subtype) :
    (⟨ProjGenLinGroup.mk g, mk_mem_centralizer_of_mem_map hg⟩ :
      centralizer {ProjGenLinGroup.mk T}) ∈ B := by
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← hLB]
  exact ⟨x, hx, rfl⟩

@[expose] def mkRestrict {T : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hLB : L.map (ordinaryCentralizerProjection T) = B) :
    L.map (centralizer {T}).subtype →* B where
  toFun g := ⟨⟨ProjGenLinGroup.mk g, mk_mem_centralizer_of_mem_map g.2⟩, mk_mem_of_mem_map hLB g.2⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' _ _ := Subtype.ext (Subtype.ext (map_mul _ _ _))

theorem mkRestrict_apply {T : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hLB : L.map (ordinaryCentralizerProjection T) = B) (g : L.map (centralizer {T}).subtype) :
    ((mkRestrict hLB g : centralizer {ProjGenLinGroup.mk T}) : ProjGenLinGroup (Fin n) K) =
      ProjGenLinGroup.mk (g : GL (Fin n) K) := rfl

theorem mkRestrict_surjective {T : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hLB : L.map (ordinaryCentralizerProjection T) = B) : Function.Surjective (mkRestrict hLB) := by
  rintro ⟨b, hb⟩
  rw [← hLB] at hb
  obtain ⟨x, hx, rfl⟩ := hb
  exact ⟨⟨x, mem_map_of_mem _ hx⟩, rfl⟩

theorem mkRestrict_injective {T : GL (Fin n) K} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hLB : L.map (ordinaryCentralizerProjection T) = B) {W : Submodule K (Fin n → K)}
    (hW : W ≠ ⊥) (hfix : ∀ x ∈ L, ∀ w ∈ W,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) :
    Function.Injective (mkRestrict hLB) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, hg⟩ h1
  have hmk : ProjGenLinGroup.mk g = 1 := congrArg (fun b : B => (b : ProjGenLinGroup (Fin n) K)) h1
  obtain ⟨x, hx, rfl⟩ := hg
  exact Subtype.ext (eq_one_of_mk_eq_one_of_fix hW hmk (hfix x hx))

variable [Finite K]

theorem split_conclusion (htwo : (2 : K) ≠ 0) {T : GL (Fin n) K} {c : Kˣ}
    (hsq : T ^ 2 = GeneralLinearGroup.scalar (Fin n) (c ^ 2))
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})} {L : Subgroup (centralizer {T})}
    (hL : CFSG.IsComponent L) (hLB : L.map (ordinaryCentralizerProjection T) = B)
    (hfix : ∀ x ∈ L, ∀ w ∈ (splitMatrixOperator T).eigenspace (-c.val),
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w)
    (hA : (splitMatrixOperator T).eigenspace c.val ≠ ⊥)
    (hW : (splitMatrixOperator T).eigenspace (-c.val) ≠ ⊥) {R : Subgroup (GL (Fin n) K)}
    (hR : R ≤ centralizer ((L.map (centralizer {T}).subtype : Subgroup (GL (Fin n) K)) :
      Set (GL (Fin n) K)))
    (hRp : ⁅R, R⁆ = R) :
    2 ≤ Module.finrank K ((splitMatrixOperator T).eigenspace c.val) ∧
      ((L.map (centralizer {T}).subtype : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) =
        summandSpecialLinear ((splitMatrixOperator T).eigenspace c.val)
          ((splitMatrixOperator T).eigenspace (-c.val)) ∧
      (∃ e : L.map (centralizer {T}).subtype ≃* B, ∀ g : L.map (centralizer {T}).subtype,
        ((e g : centralizer {ProjGenLinGroup.mk T}) : ProjGenLinGroup (Fin n) K) =
          ProjGenLinGroup.mk (g : GL (Fin n) K)) ∧
      ∀ g ∈ R, ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ a = a :=
  ⟨(splitFst_map_eq htwo hsq hL hfix hA).2, map_subtype_eq_summandSpecialLinear htwo hsq hL hfix hA,
    ⟨MulEquiv.ofBijective (mkRestrict hLB)
      ⟨mkRestrict_injective hLB hW hfix, mkRestrict_surjective hLB⟩, fun _ => rfl⟩,
    fun _ hg => apply_eq_of_isPerfect_of_le_centralizer_split htwo hsq hL hfix hA hR hRp hg⟩

end ProjectiveEigenspace

open ProjectiveEigenspace

theorem odd_projective_linear_local_component_supported_on_eigenspace
    {K : Type*} [Field K] [Finite K] (htwo : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {u : ProjGenLinGroup (Fin n) K} (hu : u ≠ 1) (hu2 : u ^ 2 = 1)
    {T : GeneralLinearGroup (Fin n) K} (hT : ProjGenLinGroup.mk T = u)
    {B : Subgroup (centralizer {u})} (hB : CFSG.IsComponent B)
    {Q : Subgroup (ProjGenLinGroup (Fin n) K)}
    (hQB : Q ≤ centralizer ((B.map (centralizer {u}).subtype : Subgroup _) :
      Set (ProjGenLinGroup (Fin n) K)))
    (hQ : Q ≠ ⊥) (hQp : ⁅Q, Q⁆ = Q) {Bhat Qhat : Subgroup (GeneralLinearGroup (Fin n) K)}
    (hBhat : Bhat = ⁅(B.map (centralizer {u}).subtype).comap ProjGenLinGroup.mk,
      (B.map (centralizer {u}).subtype).comap ProjGenLinGroup.mk⁆)
    (hQhat : Qhat = ⁅Q.comap ProjGenLinGroup.mk, Q.comap ProjGenLinGroup.mk⁆) :
    ∃ lam : Kˣ, T ^ 2 = GeneralLinearGroup.scalar (Fin n) (lam ^ 2) ∧
      IsCompl ((splitMatrixOperator T).eigenspace lam.val)
        ((splitMatrixOperator T).eigenspace (-lam.val)) ∧
      (splitMatrixOperator T).eigenspace lam.val ≠ ⊥ ∧
      (splitMatrixOperator T).eigenspace (-lam.val) ≠ ⊥ ∧
      ∃ A W : Submodule K (Fin n → K),
        (A = (splitMatrixOperator T).eigenspace lam.val ∧
            W = (splitMatrixOperator T).eigenspace (-lam.val) ∨
          A = (splitMatrixOperator T).eigenspace (-lam.val) ∧
            W = (splitMatrixOperator T).eigenspace lam.val) ∧
        2 ≤ Module.finrank K A ∧
        (Bhat : Set (GeneralLinearGroup (Fin n) K)) = summandSpecialLinear A W ∧
        (∃ e : Bhat ≃* B, ∀ g : Bhat,
          ((e g : centralizer {u}) : ProjGenLinGroup (Fin n) K) =
            ProjGenLinGroup.mk (g : GeneralLinearGroup (Fin n) K)) ∧
        ∀ g ∈ Qhat, ∀ a ∈ A, (g : Matrix (Fin n) (Fin n) K) *ᵥ a = a := by
  subst hT hBhat hQhat
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  set P := (B.map (centralizer {ProjGenLinGroup.mk T}).subtype).comap ProjGenLinGroup.mk
  set R := Q.comap (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K)
  have hBB : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.1 hB.1.1
  have hBN := le_ordinaryRange_of_perfect T hBB
  obtain ⟨hLcomp, hLB⟩ := isComponent_commutator_comap T hB
  set L := ⁅B.comap (ordinaryCentralizerProjection T), B.comap (ordinaryCentralizerProjection T)⁆
  have hPL : ⁅P, P⁆ = L.map (centralizer {T}).subtype := commutator_comap_eq_map T hBN
  obtain ⟨hQhatp, hQhatmap⟩ := commutator_comap_perfect_map hQp
  have hQhat : ⁅R, R⁆ ≠ ⊥ := fun h => hQ (by rw [← hQhatmap, h, Subgroup.map_bot])
  have hBhatp : ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⁅P, P⁆ := by
    rw [hPL, ← map_commutator, Subgroup.isPerfect_iff.1 hLcomp.1.1]
  have hcent : ⁅⁅P, P⁆, ⁅R, R⁆⁆ ≤ center (GL (Fin n) K) :=
    (commutator_mono (commutator_le_self P) (commutator_le_self R)).trans
      (commutator_le_center_of_commute fun p hp r hr => mem_centralizer_iff.1 (hQB hr) _ hp)
  have hQcent : ⁅R, R⁆ ≤ centralizer ((L.map (centralizer {T}).subtype :
      Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) := by
    rw [← hPL, ← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact commutator_eq_bot_of_le_center hBhatp hcent
  rw [hPL]
  obtain ⟨μ, hμ⟩ := matrix_square_scalar T hu2
  by_cases hsq : IsSquare μ.val
  swap
  · exact absurd (eq_bot_of_isPerfect_of_le_centralizer_quadratic htwo hn hμ hsq hLcomp hQcent
      hQhatp) hQhat
  obtain ⟨lam, hlam⟩ := exists_unit_square_root μ hsq
  have hsql : T ^ 2 = GeneralLinearGroup.scalar (Fin n) (lam ^ 2) := by rw [hlam]; exact hμ
  have hsquare := splitMatrixOperator_square T lam hsql
  have hnonscalar := projective_nontrivial_operator_nonscalar T hu
  obtain ⟨hAne, hWne⟩ := squareScalar_eigenspaces_ne_bot (splitMatrixOperator T) lam.val
    lam.ne_zero htwo hsquare hnonscalar
  refine ⟨lam, hsql, squareScalar_eigenspaces_isCompl (splitMatrixOperator T) lam.val lam.ne_zero
    htwo hsquare, hAne, hWne, ?_⟩
  rcases fix_or_fix_of_isComponent htwo hsql hLcomp with hfix | hfix
  · obtain ⟨hdim, hset, he, hQfix⟩ :=
      split_conclusion htwo hsql hLcomp hLB hfix hAne hWne hQcent hQhatp
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, hdim, hset, he, hQfix⟩
  · have hsql' : T ^ 2 = GeneralLinearGroup.scalar (Fin n) ((-lam) ^ 2) := by
      rw [neg_sq]
      exact hsql
    have hfix' : ∀ x ∈ L, ∀ w ∈ (splitMatrixOperator T).eigenspace (-(-lam).val),
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
      simpa only [Units.val_neg, neg_neg] using hfix
    have hAne' : (splitMatrixOperator T).eigenspace (-lam).val ≠ ⊥ := by
      simpa only [Units.val_neg] using hWne
    have hWne' : (splitMatrixOperator T).eigenspace (-(-lam).val) ≠ ⊥ := by
      simpa only [Units.val_neg, neg_neg] using hAne
    obtain ⟨hdim, hset, he, hQfix⟩ :=
      split_conclusion htwo hsql' hLcomp hLB hfix' hAne' hWne' hQcent hQhatp
    simp only [Units.val_neg, neg_neg] at hdim hset hQfix
    exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, hdim, hset, he, hQfix⟩

end CFSG.LocalAnalysis.ComponentInitial
