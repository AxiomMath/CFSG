module

public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices Subgroup

@[expose] def g2Long : Fin Tag.G2.rank → ℤ := ![1, 0]

@[expose] def g2Short : Fin Tag.G2.rank → ℤ := ![1, 2]

theorem isRoot_g2Long : IsRoot .G2 g2Long := by
  rw [RootCertificate.isRoot_iff Tag.G2.rootCertificate_check]
  decide

theorem isRoot_g2Short : IsRoot .G2 g2Short := by
  rw [RootCertificate.isRoot_iff Tag.G2.rootCertificate_check]
  decide

theorem iform_g2 : iform g2Long g2Short = 0 := by decide

theorem not_isRoot_g2_add : ¬ IsRoot .G2 (g2Long + g2Short) := by
  rw [RootCertificate.isRoot_iff Tag.G2.rootCertificate_check]
  decide

theorem not_isRoot_g2_sub : ¬ IsRoot .G2 (g2Long - g2Short) := by
  rw [RootCertificate.isRoot_iff Tag.G2.rootCertificate_check]
  decide

section G2

variable {K : Type} [Field K]

theorem g2_commute_rootSL2
    (A B : SL2 K) :
    rootSL2 .G2 K g2Long A * rootSL2 .G2 K g2Short B =
      rootSL2 .G2 K g2Short B * rootSL2 .G2 K g2Long A :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .G2 K isRoot_g2Long
    isRoot_g2Short iform_g2 not_isRoot_g2_add not_isRoot_g2_sub _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

theorem rootSL2_mem_adjoint
    (β : Fin Tag.G2.rank → ℤ) (A : SL2 K) :
    rootSL2 .G2 K β A ∈ adjointGroup .G2 K :=
  (exceptional_Lang_root_rank_one_data .G2 K β).2.2.2.2.1 A

theorem rootSL2_injective'
    (hK : ringChar K ≠ 2) (β : Fin Tag.G2.rank → ℤ) :
    Function.Injective (rootSL2 .G2 K β) :=
  ((exceptional_Lang_root_rank_one_data .G2 K β).2.2.2.2.2.2.2.1 hK).1

noncomputable def g2LongHom
    (K : Type) [Field K] : SL2 K →* ↥(adjointGroup .G2 K) :=
  (rootSL2 .G2 K g2Long).codRestrict _ (rootSL2_mem_adjoint g2Long)

noncomputable def g2ShortHom
    (K : Type) [Field K] : SL2 K →* ↥(adjointGroup .G2 K) :=
  (rootSL2 .G2 K g2Short).codRestrict _ (rootSL2_mem_adjoint g2Short)

theorem g2LongHom_comm
    (A B : SL2 K) : g2LongHom K A * g2ShortHom K B = g2ShortHom K B * g2LongHom K A :=
  Subtype.ext (g2_commute_rootSL2 A B)

noncomputable def g2Hom
    (K : Type) [Field K] : SL2 K × SL2 K →* ↥(adjointGroup .G2 K) :=
  MonoidHom.noncommCoprod (g2LongHom K) (g2ShortHom K) fun A B => g2LongHom_comm A B

theorem g2Hom_apply
    (A B : SL2 K) : g2Hom K (A, B) = g2LongHom K A * g2ShortHom K B :=
  MonoidHom.noncommCoprod_apply _ _ _ _

theorem g2_factors_central
    (hK : ringChar K ≠ 2) {A B : SL2 K}
    (hc : g2Hom K (A, B) ∈ Subgroup.center ↥(adjointGroup .G2 K)) :
    A ∈ Subgroup.center (SL2 K) ∧ B ∈ Subgroup.center (SL2 K) := by
  rw [g2Hom_apply] at hc
  constructor
  · rw [Subgroup.mem_center_iff]
    intro C
    have h1 := Subgroup.mem_center_iff.1 hc (g2LongHom K C)
    have h2 : g2LongHom K C * g2ShortHom K B = g2ShortHom K B * g2LongHom K C :=
      g2LongHom_comm C B
    have h3 : g2LongHom K C * g2LongHom K A = g2LongHom K A * g2LongHom K C := by
      apply mul_right_cancel (b := g2ShortHom K B)
      calc g2LongHom K C * g2LongHom K A * g2ShortHom K B
          = g2LongHom K C * (g2LongHom K A * g2ShortHom K B) := by rw [mul_assoc]
        _ = (g2LongHom K A * g2ShortHom K B) * g2LongHom K C := h1
        _ = g2LongHom K A * (g2ShortHom K B * g2LongHom K C) := by rw [mul_assoc]
        _ = g2LongHom K A * (g2LongHom K C * g2ShortHom K B) := by rw [h2]
        _ = g2LongHom K A * g2LongHom K C * g2ShortHom K B := by rw [mul_assoc]
    have h4 : rootSL2 .G2 K g2Long (C * A) = rootSL2 .G2 K g2Long (A * C) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h3
    exact rootSL2_injective' hK _ h4
  · rw [Subgroup.mem_center_iff]
    intro C
    have h1 := Subgroup.mem_center_iff.1 hc (g2ShortHom K C)
    have h2 : g2LongHom K A * g2ShortHom K C = g2ShortHom K C * g2LongHom K A :=
      g2LongHom_comm A C
    have h3 : g2ShortHom K C * g2ShortHom K B = g2ShortHom K B * g2ShortHom K C := by
      apply mul_left_cancel (a := g2LongHom K A)
      calc g2LongHom K A * (g2ShortHom K C * g2ShortHom K B)
          = (g2LongHom K A * g2ShortHom K C) * g2ShortHom K B := by rw [mul_assoc]
        _ = (g2ShortHom K C * g2LongHom K A) * g2ShortHom K B := by rw [h2]
        _ = g2ShortHom K C * (g2LongHom K A * g2ShortHom K B) := by rw [mul_assoc]
        _ = (g2LongHom K A * g2ShortHom K B) * g2ShortHom K C := h1
        _ = g2LongHom K A * (g2ShortHom K B * g2ShortHom K C) := by rw [mul_assoc]
    have h4 : rootSL2 .G2 K g2Short (C * B) = rootSL2 .G2 K g2Short (B * C) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h3
    exact rootSL2_injective' hK _ h4

theorem rankCertified_adjointQuotient_G2
    [Finite K] (hK : ringChar K ≠ 2) :
    RankCertified (AdjointQuotient .G2 K) 3 := by
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hK).1
  let Q : QuatRep K := QuatRep.ofSq hK h
  let ρ : Q8 →* SL2 K := quatHom h
  let α : Q8 × Q8 →* ↥(adjointGroup .G2 K) := (g2Hom K).comp (ρ.prodMap ρ)
  refine ⟨Q8 × Q8, V4 × V4, inferInstance, inferInstance, inferInstance,
    (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 K))).comp α,
    q8Frattini.prodMap q8Frattini, q8Frattini_surjective.prodMap q8Frattini_surjective,
    fun a b => mul_comm a b, by decide, ?_, ?_⟩
  · rw [Nat.card_prod, card_V4]
    norm_num
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
    obtain ⟨h1, h2⟩ := g2_factors_central hK (A := ρ g.1) (B := ρ g.2) hg
    obtain ⟨r₁, -, hr₁⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h1
    obtain ⟨r₂, -, hr₂⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h2
    refine MonoidHom.mem_ker.2 (Prod.ext ?_ ?_)
    · exact (Q.scalar_eq g.1 r₁ hr₁.symm).1
    · exact (Q.scalar_eq g.2 r₂ hr₂.symm).1

end G2

theorem rankCertified_of_lieModel_G2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    (hS : LieModel S .G2 0 p f) : RankCertified S 3 := by
  rcases hS with ⟨ht, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    exact (rankCertified_adjointQuotient_G2 (ringChar_ne_two_of_card_eq hp hp2 hK)).of_mulEquiv
      e.symm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.GH74.Generic
