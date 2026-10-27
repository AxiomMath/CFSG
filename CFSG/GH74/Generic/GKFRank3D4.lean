module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.Filter.ClassicalOdd CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices Subgroup

theorem ringChar_subfield {K : Type} [Field K] (s : Subfield K) : ringChar ↥s = ringChar K := by
  have h : CharP ↥s (ringChar K) :=
    (s.subtype.charP_iff Subtype.val_injective (ringChar K)).2 inferInstance
  exact ringChar.eq ↥s (ringChar K)

theorem factors_central_of_commuting_SL2 {G : Type} [Group G] {K₁ K₂ : Type} [Field K₁]
    [Field K₂] (φ₁ : SL2 K₁ →* G) (φ₂ : SL2 K₂ →* G) (i₁ : Function.Injective φ₁)
    (i₂ : Function.Injective φ₂) (hc : ∀ A B, φ₁ A * φ₂ B = φ₂ B * φ₁ A) {A : SL2 K₁}
    {B : SL2 K₂} (h : φ₁ A * φ₂ B = 1) :
    A ∈ Subgroup.center (SL2 K₁) ∧ B ∈ Subgroup.center (SL2 K₂) := by
  have hA : φ₁ A = (φ₂ B)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hB : φ₂ B = (φ₁ A)⁻¹ := eq_inv_of_mul_eq_one_right h
  constructor
  · rw [Subgroup.mem_center_iff]
    intro C
    apply i₁
    rw [map_mul, map_mul, hA]
    exact (Commute.inv_right (hc C B)).eq
  · rw [Subgroup.mem_center_iff]
    intro C
    apply i₂
    rw [map_mul, map_mul, hB]
    exact (Commute.inv_right (hc A C).symm).eq

theorem rankCertified_of_commuting_SL2 {G : Type} [Group G] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Finite K₁] [Finite K₂] (h₁ : ringChar K₁ ≠ 2) (h₂ : ringChar K₂ ≠ 2)
    (φ₁ : SL2 K₁ →* G) (φ₂ : SL2 K₂ →* G) (i₁ : Function.Injective φ₁)
    (i₂ : Function.Injective φ₂) (hc : ∀ A B, φ₁ A * φ₂ B = φ₂ B * φ₁ A) :
    RankCertified G 3 := by
  obtain ⟨a₁, b₁, e₁⟩ := (odd_field_two_dimensional_quaternion_matrices h₁).1
  obtain ⟨a₂, b₂, e₂⟩ := (odd_field_two_dimensional_quaternion_matrices h₂).1
  let Q₁ : QuatRep K₁ := QuatRep.ofSq h₁ e₁
  let Q₂ : QuatRep K₂ := QuatRep.ofSq h₂ e₂
  let ρ₁ : Q8 →* SL2 K₁ := quatHom e₁
  let ρ₂ : Q8 →* SL2 K₂ := quatHom e₂
  let α : Q8 × Q8 →* G :=
    MonoidHom.noncommCoprod (φ₁.comp ρ₁) (φ₂.comp ρ₂) fun a b => hc (ρ₁ a) (ρ₂ b)
  refine ⟨Q8 × Q8, V4 × V4, inferInstance, inferInstance, inferInstance, α,
    q8Frattini.prodMap q8Frattini, q8Frattini_surjective.prodMap q8Frattini_surjective,
    fun a b => mul_comm a b, by decide, by rw [Nat.card_prod, card_V4]; norm_num, ?_⟩
  intro g hg
  have h1 : φ₁ (ρ₁ g.1) * φ₂ (ρ₂ g.2) = 1 := by
    have h0 : α g = 1 := MonoidHom.mem_ker.1 hg
    have h2 : α g = φ₁ (ρ₁ g.1) * φ₂ (ρ₂ g.2) :=
      MonoidHom.noncommCoprod_apply (φ₁.comp ρ₁) (φ₂.comp ρ₂) _ g
    rw [← h2]
    exact h0
  obtain ⟨c₁, c₂⟩ := factors_central_of_commuting_SL2 φ₁ φ₂ i₁ i₂ hc h1
  obtain ⟨r₁, -, hr₁⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 c₁
  obtain ⟨r₂, -, hr₂⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 c₂
  refine MonoidHom.mem_ker.2 (Prod.ext ?_ ?_)
  · exact (Q₁.scalar_eq g.1 r₁ hr₁.symm).1
  · exact (Q₂.scalar_eq g.2 r₂ hr₂.symm).1

theorem rankCertified_derivedCentralQuotient_D4
    {K : Type} [Field K] [Finite K] {q : ℕ}
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ q) (hq : Nat.card K = q ^ 3) (hK : ringChar K ≠ 2) :
    RankCertified (DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) 3 := by
  have : Fintype K := Fintype.ofFinite K
  let σe : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
  have h3 : σe ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_three_apply]
    have hc : c ^ (q ^ 3) = c := by
      rw [← hq, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    calc σe (σe (σe c)) = ((c ^ q) ^ q) ^ q := by
          change σ (σ (σ c)) = _
          rw [hσ, hσ, hσ]
      _ = c ^ (q ^ 3) := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = c := hc
  rw [← hσe]
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σe h3
  obtain ⟨-, -, hH⟩ := odd_diagram_fixed_root_group_perfect .D4 K hK σe
  have hZ := center_graphFixedRootGroup_eq_bot (t := .D4) (K := K) (σ := σe.toRingHom)
    σe.surjective
  let e₁ : ↥(graphFixedRootGroup .D4 K σe.toRingHom) ≃*
      ↥⁅twistedFixedGroup .D4 K σe.toRingHom, twistedFixedGroup .D4 K σe.toRingHom⁆ :=
    MulEquiv.subgroupCongr hH.symm
  let π : ↥(graphFixedRootGroup .D4 K σe.toRingHom) →*
      DerivedCentralQuotient (twistedFixedGroup .D4 K σe.toRingHom) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom
  have hπ : Function.Injective π := by
    refine (injective_iff_map_eq_one π).2 fun x hx => ?_
    have h1 : e₁ x ∈ Subgroup.center
        ↥⁅twistedFixedGroup .D4 K σe.toRingHom, twistedFixedGroup .D4 K σe.toRingHom⁆ :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : x ∈ Subgroup.center ↥(graphFixedRootGroup .D4 K σe.toRingHom) := by
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e₁.injective
      rw [map_mul, map_mul]
      exact h1 (e₁ g)
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have h2 : ringChar (fixSubfield σe) ≠ 2 := by
    rw [ringChar_subfield]
    exact hK
  exact rankCertified_of_commuting_SL2 hK h2 (π.comp ι) (π.comp η) (hπ.comp hι) (hπ.comp hη)
    fun A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm A B]

theorem rankCertified_of_lieModel_3D4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type}
    [Group S] (hS : CFSG.Blueprint.LieModel S .trialityD4 0 p f) : RankCertified S 3 := by
  rcases hS with ⟨ht, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmodel
    have hq : Nat.card K = (p ^ f) ^ 3 := hK
    have hK2 : ringChar K ≠ 2 :=
      ringChar_ne_two_of_card_eq hp hp2 (f := f * 3) (by rw [hq, ← pow_mul])
    exact (rankCertified_derivedCentralQuotient_D4 σ hσ hq hK2).of_mulEquiv e.symm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem rank_3D4_of_lieModel
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    (hS : CFSG.Blueprint.LieModel S .trialityD4 0 p f) : ¬ SectionalTwoRankLE S 3 :=
  (rankCertified_of_lieModel_3D4 hp hp2 hS).not_sectionalTwoRankLE

end CFSG.GH74.Generic
