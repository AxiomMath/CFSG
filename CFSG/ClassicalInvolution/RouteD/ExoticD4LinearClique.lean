module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (SpinCtx spinCtx_pOmegaPlus longestFundamental
  fundamentalSubgroups_subset_longest)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (IsFundamental)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23 blockSL pair_normalize
  coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

section Involution

variable {F : Type} [Field F] {X : Type} [Group X]

theorem exists_not_commute_of_linearBlockStandardPair (h2 : (2 : F) ≠ 0) {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) {a : X} (ha : a ∈ U) (ha2 : orderOf a = 2) :
    ∃ v ∈ V, a * v ≠ v * a := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  rw [← hU] at ha
  have hθ := Gaps.eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) ha ha2
  let tr : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  set n : SL(3, F) := blockSL F 3 2 0 (by omega) (-1) with hn
  set b : SL(3, F) := blockSL F 3 2 1 (by omega) tr with hb
  refine ⟨θ b, by rw [← hV]; exact ⟨b, ⟨tr, rfl⟩, rfl⟩, ?_⟩
  intro hcomm
  rw [hθ, ← map_mul, ← map_mul] at hcomm
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), z = (b * n)⁻¹ * (n * b) := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
  obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk)
  have h' : n * b = b * n * z := by rw [hz]; group
  have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hω, hn, hb, CFSG.ClassicalInvolution.Models.coe_blockSL_neg_one,
    coe_blockSL_three_one] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e12 := congrFun (congrFun hm 1) 2
  simp [CFSG.ClassicalInvolution.Models.negBlock_eq_diagonal, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Matrix.diagonal_apply, Matrix.scalar_apply, tr] at e00 e12
  exact h2 (by linear_combination e00 - e12)

end Involution

section Spin

variable {p f : ℕ} [Fact p.Prime]

theorem exists_central_involution {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
    [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}
    {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx p f Q 𝔉) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ 𝔉) : ∃ c ∈ R, orderOf c = 2 ∧ ∀ r ∈ R, c * r = r * c := by
  obtain ⟨i, hI⟩ := S.map R hR
  obtain ⟨c, hcR, hci⟩ : i ∈ R.map (spinAction Q) := hI.mem
  have hc2 : c * c = 1 := by
    refine S.inj R hR (c * c) (R.mul_mem hcR hcR) ?_
    rw [map_mul, hci]
    exact hI.mul_self
  have hc1 : c ≠ 1 := fun h => hI.ne_one S.odd_card (by rw [← hci, h, map_one])
  refine ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1, fun r hr => ?_⟩
  have hcomm : c * r * c⁻¹ * r⁻¹ = 1 := by
    refine S.inj R hR _ (R.mul_mem (R.mul_mem (R.mul_mem hcR hr) (R.inv_mem hcR))
      (R.inv_mem hr)) ?_
    have hcen := Subgroup.mem_centralizer_singleton_iff.mp
      (hI.le_centralizer ⟨r, hr, rfl⟩)
    simp only [map_mul, map_inv, hci]
    rw [← hcen]
    group
  have : c * r = r * c := by
    calc c * r = (c * r * c⁻¹ * r⁻¹) * (r * c) := by group
      _ = r * c := by rw [hcomm, one_mul]
  exact this

theorem d4LinearClique_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hZ : ∀ {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))},
      R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
        (plusDatum 4 (GaloisField p f) (by norm_num)) →
      R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus
        (plusDatum 4 (GaloisField p f) (by norm_num)) → Commutes R₁ R₂ →
      ∀ {c₁ c₂ : spinGroup (quadPlus 4 (GaloisField p f))}, c₁ ∈ R₁ → c₂ ∈ R₂ →
        (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) → c₁ ≠ 1 → c₂ ≠ 1 →
        c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))))
    {X : Type} [Group X] (φ : spinGroup (quadPlus 4 (GaloisField p f)) →* X)
    (hker : φ.ker ≤ Subgroup.center _)
    {R₁ R₂ R₃ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (h₃ : R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hcomm : Commutes R₁ R₂)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map φ) (R₃.map φ)) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map φ) (R₃.map φ) := by
  have S := spinCtx_pOmegaPlus (p := p) (n := 4) (e := f) (by norm_num) hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  have hsub := fundamentalSubgroups_subset_longest (t := .POmegaPlus) (by decide) (by decide)
    (plusDatum 4 (GaloisField p f) (by norm_num))
  have h₁' := hsub h₁
  have h₂' := hsub h₂
  have h₃' := hsub h₃
  have hfin := S.fin
  have hlin13 : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₃ :=
    Gaps.exists_lin_of_map S.four_le S.hC φ hker (S.perf_le h₁') (S.perf_le h₃') hlin
  obtain ⟨W, hW⟩ := hlin13
  obtain ⟨c₁, hc₁, ho₁, hz₁⟩ := exists_central_involution S h₁'
  obtain ⟨c₂, hc₂, ho₂, hz₂⟩ := exists_central_involution S h₂'
  obtain ⟨c₃, hc₃, ho₃, hz₃⟩ := exists_central_involution S h₃'
  have hne1 : ∀ {c : spinGroup (quadPlus 4 (GaloisField p f))}, orderOf c = 2 → c ≠ 1 :=
    fun ho h => by
      rw [h, orderOf_one] at ho
      omega
  have hsq : ∀ {c : spinGroup (quadPlus 4 (GaloisField p f))}, orderOf c = 2 → c * c = 1 :=
    fun {c} ho => by
      rw [← pow_two]
      exact ho ▸ pow_orderOf_eq_one c
  have hζ := hZ h₁ h₂ hcomm hc₁ hc₂ hz₁ hz₂ (hne1 ho₁) (hne1 ho₂)
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := Gaps.standardPair_involutions_commute h2 hW hc₁ hc₃ ho₁ ho₃
  have h₁₂ : c₁ * c₂ = c₂ * c₁ := hcomm c₁ hc₁ c₂ hc₂
  have hc₂eq : c₂ = c₁ * (c₁ * c₂) := by
    rw [← mul_assoc, hsq ho₁, one_mul]
  have hc₁eq : c₁ = (c₁ * c₂) * c₂ := by
    rw [mul_assoc, hsq ho₂, mul_one]
  have h₂₃ : c₂ * c₃ = c₃ * c₂ := by
    have hz := Subgroup.mem_center_iff.mp hζ c₃
    calc c₂ * c₃ = (c₁ * (c₁ * c₂)) * c₃ := by rw [← hc₂eq]
      _ = c₁ * (c₃ * (c₁ * c₂)) := by rw [hz]; group
      _ = (c₁ * c₃) * (c₁ * c₂) := by group
      _ = (c₃ * c₁) * (c₁ * c₂) := by rw [h₁₃]
      _ = c₃ * (c₁ * (c₁ * c₂)) := by group
      _ = c₃ * c₂ := by rw [← hc₂eq]
  have hne₁₃ : R₁ ≠ R₃ := ne_of_linearBlockStandardPair hW
  have hnc₁₃ : ¬ Commutes R₁ R₃ := not_commutes_of_linearBlockStandardPair hW
  have hne₂₃ : R₂ ≠ R₃ := by
    rintro rfl
    exact hnc₁₃ hcomm
  have hnc₂₃ : ¬ Commutes R₂ R₃ := by
    intro hc23
    obtain ⟨v, hv, hvne⟩ := exists_not_commute_of_linearBlockStandardPair h2 hW hc₁ ho₁
    apply hvne
    have hz := Subgroup.mem_center_iff.mp hζ v
    calc c₁ * v = ((c₁ * c₂) * c₂) * v := by rw [← hc₁eq]
      _ = (c₁ * c₂) * (c₂ * v) := by group
      _ = (c₁ * c₂) * (v * c₂) := by rw [hc23 c₂ hc₂ v hv]
      _ = ((c₁ * c₂) * v) * c₂ := by group
      _ = (v * (c₁ * c₂)) * c₂ := by rw [← hz]
      _ = v * c₁ := by rw [mul_assoc, ← hc₁eq]
  obtain ⟨W', hW'⟩ := S.sign_linear h₁' h₃' h₂' hc₁ hc₃ hc₂ ho₁ ho₃ ho₂ h₁₃ h₂₃ h₁₂ hcomm hne₁₃
    hne₂₃ hnc₁₃ hnc₂₃ ⟨W, hW⟩
  exact ⟨_, Gaps.linearBlockStandardPair_map φ hker (linearBlockStandardPair_symm hW')⟩

end Spin

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem d4LinearClique_pOmegaPlus_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ (X : Type) [Group X] (φ : (Generic.modelUniv .POmegaPlus 4 p f Fact.out).K →* X),
      φ.ker ≤ Subgroup.center _ →
      ∀ R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
          (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D,
        ∀ R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus
            (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D,
          ∀ R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus
              (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D,
            R₁ ≠ R₂ → Commutes R₁ R₂ →
              (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map φ) (R₃.map φ)) →
              ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map φ) (R₃.map φ) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_rfl⟩
  have hM : Generic.modelUniv .POmegaPlus 4 p f Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p f Fact.out =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus 4 p f Fact.out).trans
        (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3)
  have hZ : ∀ {R₁ R₂ : Subgroup (Generic.modelUniv .POmegaPlus 4 p f Fact.out).K},
      R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
        (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D →
      R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus
        (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D → Commutes R₁ R₂ →
      ∀ {c₁ c₂ : (Generic.modelUniv .POmegaPlus 4 p f Fact.out).K}, c₁ ∈ R₁ → c₂ ∈ R₂ →
        (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) → c₁ ≠ 1 → c₂ ≠ 1 →
        c₁ * c₂ ∈ Subgroup.center (Generic.modelUniv .POmegaPlus 4 p f Fact.out).K :=
    fun {R₁ R₂} h₁ h₂ hc {c₁ c₂} hc₁ hc₂ hz₁ hz₂ h₁' h₂' =>
      fund_pair_mul_central_of_eq hp2 hq rfl rfl rfl hadm h₁ h₂ hc hc₁ hc₂ hz₁ hz₂ h₁' h₂'
  have key : ∀ M : LieUniversal,
      M = ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ →
      (∀ {R₁ R₂ : Subgroup M.K}, R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
        R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D → Commutes R₁ R₂ →
        ∀ {c₁ c₂ : M.K}, c₁ ∈ R₁ → c₂ ∈ R₂ → (∀ r ∈ R₁, c₁ * r = r * c₁) →
          (∀ r ∈ R₂, c₂ * r = r * c₂) → c₁ ≠ 1 → c₂ ≠ 1 → c₁ * c₂ ∈ Subgroup.center M.K) →
      ∀ (X : Type) [Group X] (φ : M.K →* X), φ.ker ≤ Subgroup.center _ →
        ∀ R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
          ∀ R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
            ∀ R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
              R₁ ≠ R₂ → Commutes R₁ R₂ →
                (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map φ) (R₃.map φ)) →
                ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map φ) (R₃.map φ) := by
    intro M hM hZ X _ φ hker R₁ h₁ R₂ h₂ R₃ h₃ _ hcomm hlin
    subst hM
    exact d4LinearClique_spin hp2 hq hZ φ hker h₁ h₂ h₃ hcomm hlin
  exact key _ hM hZ

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
