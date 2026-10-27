module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointCountBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointCount

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

@[expose] def restrictedPointCountEquiv (W : Submodule K V) :
    singularLinesIn (Q.restrict W) ⊤ ≃ singularLinesIn Q W where
  toFun L := ⟨L.val.map W.subtype, W.map_subtype_le L.val,
    (Submodule.finrank_map_subtype_eq W L.val).trans L.property.2.1, by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact L.property.2.2 y hy⟩
  invFun L := ⟨L.val.comap W.subtype, le_top,
    (Submodule.comapSubtypeEquivOfLe L.property.1).finrank_eq.trans L.property.2.1,
    fun x hx => L.property.2.2 x hx⟩
  left_inv L := Subtype.ext
    (Submodule.comap_map_eq_of_injective W.subtype_injective L.val)
  right_inv L := Subtype.ext
    ((Submodule.map_comap_subtype W L.val).trans (inf_of_le_right L.property.1))

theorem restrictedPointCountEquiv_submodule (W : Submodule K V)
    (L : singularLinesIn (Q.restrict W) ⊤) :
    (restrictedPointCountEquiv Q W L).val = L.val.map W.subtype := rfl

theorem restrictedPointCountEquiv_symm_submodule (W : Submodule K V)
    (L : singularLinesIn Q W) :
    ((restrictedPointCountEquiv Q W).symm L).val = L.val.comap W.subtype := rfl

theorem restricted_point_count (W : Submodule K V) :
    Nat.card (singularLinesIn (Q.restrict W) ⊤) = Nat.card (singularLinesIn Q W) :=
  Nat.card_congr (restrictedPointCountEquiv Q W)

variable {Q}

@[expose] def restrictedPair (P : HypPair Q) {W : Submodule K V}
    (he : P.e ∈ W) (hf : P.f ∈ W) : HypPair (Q.restrict W) where
  e := ⟨P.e, he⟩
  f := ⟨P.f, hf⟩
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := by rw [polar_restrict]; exact P.polar_ef

theorem restricted_pair_e (P : HypPair Q) {W : Submodule K V}
    (he : P.e ∈ W) (hf : P.f ∈ W) :
    (restrictedPair P he hf).e = ⟨P.e, he⟩ := rfl

theorem restricted_pair_f (P : HypPair Q) {W : Submodule K V}
    (he : P.e ∈ W) (hf : P.f ∈ W) :
    (restrictedPair P he hf).f = ⟨P.f, hf⟩ := rfl

theorem restricted_pair_perp_submodule (P : HypPair Q) {W : Submodule K V}
    (he : P.e ∈ W) (hf : P.f ∈ W) :
    (restrictedPair P he hf).perp = (W ⊓ P.perp).comap W.subtype := by
  ext x
  rw [HypPair.mem_perp, restricted_pair_e, restricted_pair_f, polar_restrict,
    polar_restrict, Submodule.mem_comap, Submodule.mem_inf, HypPair.mem_perp]
  exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩

theorem orthogonal_pair_mem_perp {P R : HypPair Q} (h : P.Orth R) :
    R.e ∈ P.perp ∧ R.f ∈ P.perp :=
  ⟨HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩, HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩⟩

variable [FiniteDimensional K V]

theorem nested_complement_finrank (P R S : HypPair Q)
    (hPS : P.Orth S) (hRS : R.Orth S) :
    2 ≤ Module.finrank K (P.perp ⊓ R.perp : Submodule K V) := by
  have hPSmem := orthogonal_pair_mem_perp hPS
  have hRSmem := orthogonal_pair_mem_perp hRS
  have hspan : Submodule.span K {S.e, S.f} ≤ P.perp ⊓ R.perp := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨hPSmem.1, hRSmem.1⟩
    · exact ⟨hPSmem.2, hRSmem.2⟩
  rw [← finrank_span_pair_hyp S]
  exact Submodule.finrank_mono hspan

theorem restricted_pair_perp_finrank (P R : HypPair Q) (hPR : P.Orth R) :
    Module.finrank K (restrictedPair R (orthogonal_pair_mem_perp hPR).1
      (orthogonal_pair_mem_perp hPR).2).perp =
      Module.finrank K (P.perp ⊓ R.perp : Submodule K V) := by
  have hdim := finrank_inf_perp_add_two R
    (orthogonal_pair_mem_perp hPR).1 (orthogonal_pair_mem_perp hPR).2
  rw [hyperbolic_perp_finrank]
  omega

theorem first_complement_finrank (P R S : HypPair Q)
    (hPR : P.Orth R) (hPS : P.Orth S) (hRS : R.Orth S) :
    4 ≤ Module.finrank K P.perp := by
  have hdim := finrank_inf_perp_add_two R
    (orthogonal_pair_mem_perp hPR).1 (orthogonal_pair_mem_perp hPR).2
  have hpos := nested_complement_finrank P R S hPS hRS
  omega

theorem exists_adapted_three_pairs (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Points Q) :
    ∃ P R S : HypPair Q, L.val = K ∙ P.e ∧ P.Orth R ∧ P.Orth S ∧ R.Orth S := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  obtain ⟨P, R, S, hPe, hPR, hPS, hRS⟩ :=
    quadratic_three_hyperbolic_pairs hQ hT hQx hx
  exact ⟨P, R, S, by rw [pointMk_submodule, hPe], hPR, hPS, hRS⟩

theorem exists_adapted_regular_complements (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Points Q) :
    ∃ P R S : HypPair Q, L.val = K ∙ P.e ∧ P.Orth R ∧ P.Orth S ∧ R.Orth S ∧
      R.e ∈ P.perp ∧ R.f ∈ P.perp ∧ PolarNondegOn Q P.perp ∧
      PolarNondegOn Q (P.perp ⊓ R.perp) ∧
      2 ≤ Module.finrank K (P.perp ⊓ R.perp : Submodule K V) ∧
      4 ≤ Module.finrank K P.perp := by
  obtain ⟨P, R, S, hL, hPR, hPS, hRS⟩ := exists_adapted_three_pairs hQ hT L
  have hmem := orthogonal_pair_mem_perp hPR
  have hreg := HypPair.polarNondegOn_perp hQ P
  exact ⟨P, R, S, hL, hPR, hPS, hRS, hmem.1, hmem.2, hreg,
    hreg.inf_perp R hmem.1 hmem.2, nested_complement_finrank P R S hPS hRS,
    first_complement_finrank P R S hPR hPS hRS⟩

variable [Finite K]

theorem complement_point_count_congruence (P R S : HypPair Q)
    (hPR : P.Orth R) (hPS : P.Orth S) (hRS : R.Orth S) :
    Nat.card (singularLinesIn Q P.perp) ≡ 1 [MOD Nat.card K] := by
  let R' := restrictedPair R (orthogonal_pair_mem_perp hPR).1
    (orthogonal_pair_mem_perp hPR).2
  have hpos : 1 ≤ Module.finrank K R'.perp := by
    rw [restricted_pair_perp_finrank P R hPR]
    have h := nested_complement_finrank P R S hPS hRS
    omega
  have h := (orthogonal_geometry_hyperbolic_point_count R').2.2.2 hpos
  rw [restricted_point_count Q P.perp] at h
  exact h

theorem perpendicular_point_count_divisibility (P R S : HypPair Q)
    (hPR : P.Orth R) (hPS : P.Orth S) (hRS : R.Orth S)
    (L : Points Q) (hL : L.val = K ∙ P.e) :
    Nat.card K ∣ Nat.card (perpendicularPoints Q L) ∧
      ¬ Nat.card K ^ 2 ∣ Nat.card (perpendicularPoints Q L) := by
  rw [perpendicular_point_count P L hL]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hnot : ¬ Nat.card K ∣ Nat.card (singularLinesIn Q P.perp) := by
    intro hdiv
    have h1 := (complement_point_count_congruence P R S hPR hPS hRS).dvd_iff
      (dvd_refl (Nat.card K)) |>.mp hdiv
    have hq1 := Nat.dvd_one.mp h1
    omega
  refine ⟨Nat.dvd_mul_right _ _, ?_⟩
  rw [pow_two, Nat.mul_dvd_mul_iff_left (by omega : 0 < Nat.card K)]
  exact hnot

theorem nonperpendicular_point_count_divisibility (P R S : HypPair Q)
    (hPR : P.Orth R) (hPS : P.Orth S) (hRS : R.Orth S)
    (L : Points Q) (hL : L.val = K ∙ P.e) :
    Nat.card K ^ 2 ∣ Nat.card (nonperpendicularPoints Q L) := by
  rw [nonperpendicular_point_count P L hL, ← hyperbolic_perp_finrank P]
  exact Nat.pow_dvd_pow _ (by
    have h := first_complement_finrank P R S hPR hPS hRS
    omega)

theorem point_subdegree_divisibility (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Points Q) :
    Nat.card K ∣ Nat.card (perpendicularPoints Q L) ∧
      ¬ Nat.card K ^ 2 ∣ Nat.card (perpendicularPoints Q L) ∧
      Nat.card K ^ 2 ∣ Nat.card (nonperpendicularPoints Q L) ∧
      Nat.card (perpendicularPoints Q L) ≠ Nat.card (nonperpendicularPoints Q L) := by
  obtain ⟨P, R, S, hL, hPR, hPS, hRS⟩ := exists_adapted_three_pairs hQ hT L
  have hp := perpendicular_point_count_divisibility P R S hPR hPS hRS L hL
  have hn := nonperpendicular_point_count_divisibility P R S hPR hPS hRS L hL
  refine ⟨hp.1, hp.2, hn, ?_⟩
  intro h
  exact hp.2 (h ▸ hn)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointCount
