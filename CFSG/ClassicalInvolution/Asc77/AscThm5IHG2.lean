module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHInner
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHChart
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4One
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.Q27
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section G2Core

variable {F : Type} [Field F] [Finite F]

theorem thm5IH_g2_oddCore_toral (hodd : Odd (Nat.card F))
    {a : Fin Tag.G2.rank → Fˣ} (ha : a = ![-1, 1]) {N : Subgroup (ModGL Tag.G2 F)}
    (hNX : N ≤ toralCentralizer Tag.G2 F a)
    (hNconj : ∀ x ∈ toralCentralizer Tag.G2 F a, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  classical
  obtain ⟨hsign, hne, hker, -, -, -⟩ := g2_toral_data_a1 hodd ha
  have hAmem : g2vec 0 1 ∈ rootCharKernel a := by rw [hker]; simp
  have hBmem : g2vec 2 3 ∈ rootCharKernel a := by rw [hker]; simp
  have hQA : (g2ChartA F).range ≤ toralCentralizer Tag.G2 F a := by
    rw [g2ChartA_range]
    exact rootPair_le_toralCentralizer hAmem
  have hQB : (g2ChartB F).range ≤ toralCentralizer Tag.G2 F a := by
    rw [g2ChartB_range]
    exact rootPair_le_toralCentralizer hBmem
  have hXA : toralCentralizer Tag.G2 F a ≤
      Subgroup.normalizer ((g2ChartA F).range : Set (ModGL Tag.G2 F)) := by
    rw [g2ChartA_range]
    exact toralCentralizer_le_normalizer_rootPair hodd hsign hne hAmem
  have hXB : toralCentralizer Tag.G2 F a ≤
      Subgroup.normalizer ((g2ChartB F).range : Set (ModGL Tag.G2 F)) := by
    rw [g2ChartB_range]
    exact toralCentralizer_le_normalizer_rootPair hodd hsign hne hBmem
  have hcA := thm5IH_odd_normal_centralizes_chart hodd (g2ChartA_injective hodd) hQA hXA hNX
    hNconj hNodd
  have hcB := thm5IH_odd_normal_centralizes_chart hodd (g2ChartB_injective hodd) hQB hXB hNX
    hNconj hNodd
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨t, ht, A₁, B₁, hnt⟩ := toralCentralizer_le_prod hodd ha (hNX hn)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hactA : ∀ M : SL2 F, glConjSL (diagGL (rootChar b ((1 : WeylGroup Tag.G2) •
      (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ)))) (A₁ * M * A₁⁻¹) = M := by
    intro M
    have h1 : n * g2ChartA F M * n⁻¹ = g2ChartA F M := by
      rw [hcA n hn M]
      group
    have h2 : n * g2ChartA F M * n⁻¹ = g2ChartA F (glConjSL (diagGL (rootChar b ((1 : WeylGroup
        Tag.G2) • (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ)))) (A₁ * M * A₁⁻¹)) := by
      have hBA : g2ChartB F B₁ * g2ChartA F M * (g2ChartB F B₁)⁻¹ = g2ChartA F M := by
        rw [← hcomm M B₁]
        group
      calc n * g2ChartA F M * n⁻¹
          = t * g2ChartA F A₁ * (g2ChartB F B₁ * g2ChartA F M * (g2ChartB F B₁)⁻¹) *
              (g2ChartA F A₁)⁻¹ * t⁻¹ := by rw [hnt]; group
        _ = t * g2ChartA F (A₁ * M * A₁⁻¹) * t⁻¹ := by
            rw [hBA]
            simp only [map_mul, map_inv]
            group
        _ = _ := by
            rw [hb]
            exact rootDiagUnit_conj_rootChart 1 g2i1 b _
    exact g2ChartA_injective hodd (h2.symm.trans h1)
  have hactB : ∀ M : SL2 F, glConjSL (diagGL (rootChar b (g2WeylU •
      (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)))) (B₁ * M * B₁⁻¹) = M := by
    intro M
    have h1 : n * g2ChartB F M * n⁻¹ = g2ChartB F M := by
      rw [hcB n hn M]
      group
    have h2 : n * g2ChartB F M * n⁻¹ = g2ChartB F (glConjSL (diagGL (rootChar b (g2WeylU •
        (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)))) (B₁ * M * B₁⁻¹)) := by
      calc n * g2ChartB F M * n⁻¹
          = t * (g2ChartA F A₁ * g2ChartB F (B₁ * M * B₁⁻¹) * (g2ChartA F A₁)⁻¹) * t⁻¹ := by
            rw [hnt]
            simp only [map_mul, map_inv]
            group
        _ = t * g2ChartB F (B₁ * M * B₁⁻¹) * t⁻¹ := by
            rw [hcomm A₁ (B₁ * M * B₁⁻¹)]
            group
        _ = _ := by
            rw [hb]
            exact rootDiagUnit_conj_rootChart g2WeylU g2i0 b _
    exact g2ChartB_injective hodd (h2.symm.trans h1)
  have hsclA := thm5IH_scalar_of_glConjSL hodd (D := diagGL (rootChar b ((1 : WeylGroup Tag.G2) •
      (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ))) * Matrix.SpecialLinearGroup.toGL A₁) (fun M => by
    rw [glConjSL_mul, glConjSL_toGL]
    exact hactA M)
  have hsclB := thm5IH_scalar_of_glConjSL hodd (D := diagGL (rootChar b (g2WeylU •
      (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ))) * Matrix.SpecialLinearGroup.toGL B₁) (fun M => by
    rw [glConjSL_mul, glConjSL_toGL]
    exact hactB M)
  obtain ⟨s₁, hs₁⟩ := thm5IH_exists_HSL hsclA
  obtain ⟨s₂, hs₂⟩ := thm5IH_exists_HSL hsclB
  have hnT : n ∈ torusGroup Tag.G2 F := by
    rw [hnt, hs₁, hs₂]
    exact mul_mem (mul_mem ht (rootChart_HSL_mem_torusGroup 1 g2i1 s₁))
      (rootChart_HSL_mem_torusGroup g2WeylU g2i0 s₂)
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hnT
  have hχA : rootChar b' ((1 : WeylGroup Tag.G2) •
      (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ)) = 1 := by
    have hscal : ∀ M : SL2 F, glConjSL (diagGL (rootChar b' ((1 : WeylGroup Tag.G2) •
        (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ)))) M = M := by
      intro M
      have h1 : n * g2ChartA F M * n⁻¹ = g2ChartA F M := by
        rw [hcA n hn M]
        group
      rw [hb'] at h1
      have h2 := rootDiagUnit_conj_rootChart (K := F) (1 : WeylGroup Tag.G2) g2i1 b' M
      exact g2ChartA_injective hodd (h2.symm.trans h1)
    obtain ⟨μ, hμ⟩ := thm5IH_scalar_of_glConjSL hodd hscal
    have h00 := congrFun (congrFun hμ 0) 0
    have h11 := congrFun (congrFun hμ 1) 1
    simp [diagGL] at h00 h11
    exact Units.ext (by rw [one_smul, h00, ← h11]; rfl)
  have hχB : rootChar b' (g2WeylU •
      (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)) = 1 := by
    have hscal : ∀ M : SL2 F, glConjSL (diagGL (rootChar b' (g2WeylU •
        (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)))) M = M := by
      intro M
      have h1 : n * g2ChartB F M * n⁻¹ = g2ChartB F M := by
        rw [hcB n hn M]
        group
      rw [hb'] at h1
      have h2 := rootDiagUnit_conj_rootChart (K := F) g2WeylU g2i0 b' M
      exact g2ChartB_injective hodd (h2.symm.trans h1)
    obtain ⟨μ, hμ⟩ := thm5IH_scalar_of_glConjSL hodd hscal
    have h00 := congrFun (congrFun hμ 0) 0
    have h11 := congrFun (congrFun hμ 1) 1
    simp [diagGL] at h00 h11
    exact Units.ext (by rw [h00, ← h11]; rfl)
  rw [one_smul, g2_single_1, rootChar_g2vec] at hχA
  rw [g2WeylU_smul_single, rootChar_g2vec] at hχB
  have hb1 : b' g2i1 = 1 := by simpa using hχA
  have hb0 : b' g2i0 ^ 2 = 1 := by simpa [hb1] using hχB
  have hbb : b' * b' = 1 := by
    funext i
    fin_cases i
    · show b' g2i0 * b' g2i0 = 1
      rw [← sq]
      exact hb0
    · show b' g2i1 * b' g2i1 = 1
      rw [hb1, one_mul]
  have hnn : n * n = 1 := by
    rw [hb', ← rootDiagUnit_mul, hbb, rootDiagUnit_one]
  have hd2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
  have hdc : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdc
    obtain ⟨k, hk⟩ := hdc
    have := Nat.odd_iff.mp hNodd
    omega

end G2Core


section Model

variable {p : ℕ} [Fact p.Prime]

theorem thm5IH_torusGroup_le_adjointGroup (F : Type) [Field F] [Finite F]
    (a : Fin Tag.G2.rank → Fˣ) : torusGroup Tag.G2 F ≤ adjointGroup Tag.G2 F := by
  have h := (Chevalley_toral_centralizer_Bruhat_factors Tag.G2 F a).2.2.2
  have h1 : torusGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F a := by
    rw [h]
    exact le_sup_left.trans le_sup_left
  exact h1.trans inf_le_left

theorem thm5IH_g2_oddCoreTrivial {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 0 p e) :
    InvolutionOddCoreTrivial (modelUniv .G2 0 p e Fact.out).K := by
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  change InvolutionOddCoreTrivial ↥(adjointGroup Tag.G2 (GaloisField p e))
  set F := GaloisField p e with hF
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  obtain ⟨hsign, hne, hker, -, -, -⟩ := g2_toral_data_a1 (F := F) hodd ha₀
  have hdmem : rootDiagUnit Tag.G2 a₀ ∈ adjointGroup Tag.G2 F :=
    thm5IH_torusGroup_le_adjointGroup F a₀ (g2_rootDiagUnit_mem_torusGroup _)
  set u₀ : ↥(adjointGroup Tag.G2 F) := ⟨_, hdmem⟩ with hu₀
  have hnegA : g2ChartA F (-1) = rootDiagUnit Tag.G2 a₀ :=
    rootChart_neg_one hodd hsign hne (γ := g2vec 0 1) (by rw [hker]; simp)
      (w := 1) (i := g2i1) (by rw [one_smul, g2_single_1])
  apply involutionOddCoreTrivial_of_conj
    (fun u v hu hv hu1 hv1 => g2_involutions_conj hodd hu hv hu1 hv1)
  refine ⟨u₀, ?_, ?_, ?_⟩
  ·
    apply Subtype.ext
    show rootDiagUnit Tag.G2 a₀ * rootDiagUnit Tag.G2 a₀ = 1
    rw [← rootDiagUnit_mul]
    have : a₀ * a₀ = 1 := by
      funext i
      show a₀ i * a₀ i = 1
      rcases hsign i with h | h <;> rw [h] <;> simp
    rw [this, rootDiagUnit_one]
  ·
    intro h
    have h1 : rootDiagUnit Tag.G2 a₀ = 1 := congrArg Subtype.val h
    rw [← hnegA, ← map_one (g2ChartA F)] at h1
    have h2 := g2ChartA_injective hodd h1
    have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h2
    have h2F : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
    apply h2F
    simp at h3
    linear_combination -h3
  · intro N hNc hNconj hNodd
    set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype
      with hι
    have hιinj : Function.Injective ι := Subtype.val_injective
    have hιu : ι u₀ = rootDiagUnit Tag.G2 a₀ := rfl
    have hNX : N.map ι ≤ toralCentralizer Tag.G2 F a₀ := by
      rintro _ ⟨n, hn, rfl⟩
      rw [mem_toralCentralizer]
      refine ⟨n.2, ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hNc hn)
      have h2 : ι n * rootDiagUnit Tag.G2 a₀ = rootDiagUnit Tag.G2 a₀ * ι n := by
        rw [← hιu, ← map_mul, ← map_mul, h1]
      rw [mul_inv_eq_iff_eq_mul]
      exact h2.symm
    have hNc' : ∀ x ∈ toralCentralizer Tag.G2 F a₀, ∀ n ∈ N.map ι, x * n * x⁻¹ ∈ N.map ι := by
      intro x hx n' hn'
      obtain ⟨n, hn, hnn'⟩ := hn'
      rw [mem_toralCentralizer] at hx
      obtain ⟨hxA, hxd⟩ := hx
      set y : ↥(adjointGroup Tag.G2 F) := ⟨x, hxA⟩ with hy
      have hyc : y ∈ Subgroup.centralizer ({u₀} : Set ↥(adjointGroup Tag.G2 F)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        show x * rootDiagUnit Tag.G2 a₀ = rootDiagUnit Tag.G2 a₀ * x
        rw [mul_inv_eq_iff_eq_mul] at hxd
        exact hxd.symm
      refine ⟨y * n * y⁻¹, hNconj y hyc n hn, ?_⟩
      rw [map_mul, map_mul, map_inv, hnn']
      rfl
    have hNodd' : Odd (Nat.card (N.map ι)) := by
      rw [Subgroup.card_map_of_injective hιinj]
      exact hNodd
    have hbot := thm5IH_g2_oddCore_toral hodd ha₀ hNX hNc' hNodd'
    exact (Subgroup.map_eq_bot_iff_of_injective N hιinj).mp hbot

end Model


section Instance

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_g2 {k e : ℕ} (P : Prop → Prop) : T5BaseAt p f .G2 k e P :=
  t5BaseAt_of_model P fun hp2 hq hfund hadm hef => by
    have hef' : e = f := hef.resolve_right fun h => nomatch h.1
    subst hef'
    have hk : k = 0 := hadm.2.2.1
    subst hk
    refine ⟨⟨(ModelFacts.isQuasisimple_modelUniv .G2 0 p e Fact.out hfund hadm).1⟩,
      CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0
        hadm.2.1,
      thm5IH_g2_oddCoreTrivial hp2 hadm, ?_⟩
    intro u₁ u₂ h₁ h₂ h₁1 h₂1 hne hcomm
    have h := g2CentralizersGenerate_of_nonToral g2NonToralGenerate_all hp2 hq hadm u₁ u₂ h₁ h₂
      h₁1 h₂1 hne hcomm
    rw [h]
    simp

end Instance

end CFSG.ClassicalInvolution.Asc77
