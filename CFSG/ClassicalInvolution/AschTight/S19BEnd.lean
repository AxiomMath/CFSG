module

public import CFSG.ClassicalInvolution.AschTight.S19BStmt
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_centralizer {B L : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBL : B ≤ centralizerModOdd ⊤ L) {l : G} (hl : l ∈ L) :
    ∃ o ∈ oddCoreOf L, l * o ∈ Subgroup.centralizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ b ∈ B, ∀ o ∈ oddCoreOf L, l⁻¹ * (b * (l * o) * b⁻¹) ∈ oddCoreOf L := by
    intro b hb o ho
    obtain ⟨-, -, hbO, hcomm⟩ := hBL hb
    have h1 : ⁅b, l⁆ ∈ oddCoreOf L := hcomm l hl
    have h2 : b * o * b⁻¹ ∈ oddCoreOf L := (Subgroup.mem_normalizer_iff.mp hbO o).mp ho
    have hlN : l⁻¹ ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (L.inv_mem hl))
    have h3 : l⁻¹ * ⁅b, l⁆ * l⁻¹⁻¹ ∈ oddCoreOf L :=
      (Subgroup.mem_normalizer_iff.mp hlN _).mp h1
    have e : l⁻¹ * (b * (l * o) * b⁻¹) = (l⁻¹ * ⁅b, l⁆ * l⁻¹⁻¹) * (b * o * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (oddCoreOf L).mul_mem h3 h2
  let : MulAction ↥B ↥(oddCoreOf L) :=
    { smul := fun b o => ⟨l⁻¹ * ((b : G) * (l * (o : G)) * (b : G)⁻¹), hconj b b.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change l⁻¹ * ((1 : G) * (l * (o : G)) * (1 : G)⁻¹) = (o : G)
        group)
      mul_smul := fun b₁ b₂ o => Subtype.ext (by
        change l⁻¹ * (((b₁ : G) * (b₂ : G)) * (l * (o : G)) * ((b₁ : G) * (b₂ : G))⁻¹) =
          l⁻¹ * ((b₁ : G) * (l * (l⁻¹ * ((b₂ : G) * (l * (o : G)) * (b₂ : G)⁻¹))) *
            (b₁ : G)⁻¹)
        group) }
  have hodd : ¬ 2 ∣ Nat.card ↥(oddCoreOf L) := by
    obtain ⟨k, hk⟩ := oddCoreOf_odd_natCard L
    rintro ⟨m, hm⟩
    omega
  obtain ⟨o₀, ho₀⟩ := hB2.nonempty_fixed_point_of_prime_not_dvd_card ↥(oddCoreOf L) hodd
  refine ⟨o₀, o₀.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have h1 : l⁻¹ * (b * (l * (o₀ : G)) * b⁻¹) = (o₀ : G) :=
    congrArg Subtype.val (ho₀ ⟨b, hb⟩)
  calc b * (l * (o₀ : G)) = l * (l⁻¹ * (b * (l * (o₀ : G)) * b⁻¹)) * b := by group
    _ = l * (o₀ : G) * b := by rw [h1]

theorem surjective_mk_inf_centralizer {B L : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBL : B ≤ centralizerModOdd ⊤ L) :
    Function.Surjective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.centralizer (B : Set G) ≤ L))) := by
  intro q
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨o, ho, hc⟩ := exists_mul_mem_centralizer hB2 hBL hl
  obtain ⟨x, hx, rfl⟩ := ho
  refine ⟨⟨l * (x : G), L.mul_mem hl x.2, hc⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e : (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.centralizer (B : Set G) ≤ L)
      ⟨l * (x : G), L.mul_mem hl x.2, hc⟩)⁻¹ * ⟨l, hl⟩ = x⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  rw [e]
  exact (classicalInvolutionOddCore ↥L).inv_mem hx

theorem false_of_stronglyClosed (hB1 : GoldschmidtB1Tmp) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {B L : Subgroup G}
    (hBS : B ≤ (S : Subgroup G)) (hB : B ≠ ⊥) (hsc : fusionStronglyClosed (B : Set G) S)
    (hBL : B ≤ centralizerModOdd ⊤ L)
    (hL : ¬ Group.IsSolvable (↥L ⧸ classicalInvolutionOddCore ↥L)) : False := by
  have h1 := hB1 G hnonab S B hBS hB hsc
  rw [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  have h2 : Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mp h1
  have h3 : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (B : Set G)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_right : L ⊓ Subgroup.centralizer (B : Set G) ≤ _))
  exact hL (Group.isSolvable_of_surjective
    (surjective_mk_inf_centralizer (S.isPGroup'.to_le hBS) hBL))

theorem nontrivial_sl2 (F : Type) [Field F] : Nontrivial SL(2, F) := by
  refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => ?_⟩⟩
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp at this

omit [Finite G] in
theorem not_isSolvable_quotient_of_isClassicalMember {p f : ℕ} [Fact p.Prime] (hq : 5 ≤ p ^ f)
    {L : Subgroup G} {t : G} (h : IsClassicalMember p f L t) :
    ¬ Group.IsSolvable (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  intro hsol
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    omega
  have : Group.IsPerfect SL(2, GaloisField p f) := sl2_isPerfect h4
  have : Nontrivial SL(2, GaloisField p f) := nontrivial_sl2 _
  exact Group.IsPerfect.not_isSolvable SL(2, GaloisField p f)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
