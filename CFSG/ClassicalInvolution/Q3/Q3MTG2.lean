module

public import CFSG.ClassicalInvolution.Q3.Q3MTG2Struct
public import CFSG.ClassicalInvolution.Q3.Q3MTU5
public import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallF
public import CFSG.ClassicalInvolution.Q3.Q3MTG2Chart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups


section Core

theorem natCard_galoisField_three_one : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem eq_of_isMaxPGroup_le_normalizer_g2_three :
    ∀ Q ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 3 1 Fact.out).D,
      ∀ g : (modelUniv StatedLieTag.G2 0 3 1 Fact.out).K,
        ∀ R : Subgroup (modelUniv StatedLieTag.G2 0 3 1 Fact.out).K,
          R ≤ conjSub g Q → IsPGroup 2 R →
          (∀ T : Subgroup (modelUniv StatedLieTag.G2 0 3 1 Fact.out).K,
            T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
          R ≤ Subgroup.normalizer (Q : Set (modelUniv StatedLieTag.G2 0 3 1 Fact.out).K) →
          conjSub g Q = Q := by
  change ∀ Q ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField 3 1)),
    ∀ g : ↥(adjointGroup Tag.G2 (GaloisField 3 1)),
      ∀ R : Subgroup ↥(adjointGroup Tag.G2 (GaloisField 3 1)),
        R ≤ conjSub g Q → IsPGroup 2 R →
        (∀ T : Subgroup ↥(adjointGroup Tag.G2 (GaloisField 3 1)),
          T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
        R ≤ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.G2 (GaloisField 3 1))) →
        conjSub g Q = Q
  have h3 := natCard_galoisField_three_one
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [h3]
    decide
  intro Q hQ g R hRJ hR2 hmax hRN
  obtain ⟨g₀, γ, hγ, rfl⟩ := hQ
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  obtain ⟨Φ₀, hinj, hrange, H1₀⟩ := exists_standard_chart_g2 hodd hγroot
  rw [← hrange] at hRJ hmax hRN ⊢
  have hz : Φ₀ (-1) * Φ₀ (-1) = 1 := by
    rw [← map_mul]
    simp
  have hz1 : Φ₀ (-1) ≠ 1 := fun h =>
    CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd (hinj (h.trans (map_one Φ₀).symm))
  exact eq_of_sylow_le_normalizer_of_chart3 hodd hinj H1₀
    (fun Ψ hΨ hc => chart_neg_one_eq_of_commutes_g2 hodd h3 hz hz1 hΨ hc) g₀ g hRJ hR2 hmax hRN

end Core

section Datum

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem dEdgeless_g2_three (M : Ih8Model 3 1 Ω .G2 0 e)
    (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) : Disconnected.DEdgeless Ω := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center (by norm_num) (Or.inl rfl) 0 he M.ψ M.ker_le_center
  obtain rfl : e = 1 := M.exp_eq_f (by decide)
  exact dEdgeless_of_model M.ψ hinj M.surj M.mem_iff htrans fun Q hQ =>
    eq_of_isMaxPGroup_le_normalizer_g2_three Q (M.cls_sub hQ)

theorem g2_omegaStarNbr_nonempty_three (M : Ih8Model 3 1 Ω .G2 0 e)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty) :
    ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inl rfl) 0 he M.ψ M.ker_le_center
  obtain rfl : e = 1 := M.exp_eq_f (by decide)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [natCard_galoisField_three_one]
    decide
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :
      ∃ c j d : (modelUniv .G2 0 3 1 Fact.out).K, IsUniqueInvolution R c ∧ j ∈ R ∧
        orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ c ∧ j * d = d * j :=
    MuTab.g2_exists_orderFour hp2 he (M.cls_sub hR)
  obtain ⟨h, hh⟩ : ∃ h : (modelUniv .G2 0 3 1 Fact.out).K, h * d * h⁻¹ = c :=
    g2_involutions_conj hodd hd hc.sq hd1 hc.ne_one
  have hL : conjSub h R ∈ M.cls := M.cls_conj R hR h
  have hjL : h * j * h⁻¹ ∈ conjSub h R := conj_mem_conjSub hj
  have hj4' : orderOf (h * j * h⁻¹) = 4 := by
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective j
    rw [hj4] at this
    exact this
  have hgc : h * j * h⁻¹ * c * (h * j * h⁻¹)⁻¹ = c := by
    rw [← hh]
    calc h * j * h⁻¹ * (h * d * h⁻¹) * (h * j * h⁻¹)⁻¹ = h * (j * d * j⁻¹) * h⁻¹ := by group
      _ = h * (d * j * j⁻¹) * h⁻¹ := by rw [hjd]
      _ = h * d * h⁻¹ := by group
  have hcL : IsUniqueInvolution (conjSub (h * j * h⁻¹) R) c := by
    have := hc.conj (h * j * h⁻¹)
    rwa [hgc] at this
  have hNT := noTwins_g2 (by norm_num) he R (M.cls_sub hR) c hc (h * j * h⁻¹) hcL
  have hj'N : h * j * h⁻¹ ∈ Subgroup.normalizer (R : Set _) :=
    mem_normalizer_iff_conjSub_eq.mpr hNT
  have hg4 : orderOf (M.ψ (h * j * h⁻¹)) = 4 := by
    rw [orderOf_injective M.ψ hinj]
    exact hj4'
  refine ⟨R.map M.ψ, M.map_mem hR, (conjSub h R).map M.ψ, M.map_mem hL, ?_,
    Subgroup.zpowers (M.ψ (h * j * h⁻¹)),
    mem_USet3 hΩ (M.map_mem hL) (Subgroup.mem_map_of_mem _ hjL) hg4,
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hjL), ?_⟩
  · intro heq
    have hRh : conjSub h R = R := Subgroup.map_injective hinj heq
    have hcc : h * c * h⁻¹ = c := hc.conj_eq hRh
    apply hdc
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = h⁻¹ * c * h := by rw [hh]
      _ = h⁻¹ * (h * c * h⁻¹) * h := by rw [hcc]
      _ = c := by group
  · rw [Subgroup.zpowers_le, normalizer_map_of_bijective M.ψ hinj M.surj R]
    exact Subgroup.mem_map_of_mem _ hj'N

end Datum

section Field

theorem g2Shape3 : SmallShape3 .G2 0 := by
  intro G _ _ _ Ω hΩ _ hne htrans hL
  have hshape : KindShape Ω (muKind false .G2 0) = ShapeS3 Ω := by
    rw [muKind_g2]
    rfl
  rw [hshape]
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  exact ⟨dEdgeless_g2_three M htrans, g2_omegaStarNbr_nonempty_three M hΩ hne⟩

end Field

end CFSG.ClassicalInvolution.Q3.Q3MT
