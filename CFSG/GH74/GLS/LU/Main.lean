module

public import CFSG.GH74.GLS.LU.Compat
public import CFSG.GH74.GLS.LU.Final
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.GH74.GLS.LU

open Matrix Subgroup Blueprint Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports

theorem nonempty_mulEquiv_of_lieModel_psl {G G' : Type} [Group G] [Group G'] {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (h : LieModel G StatedLieTag.PSL 4 p f)
    (h' : LieModel G' StatedLieTag.PSL 4 p f) : Nonempty (G ≃* G') := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ {X : Type} [Group X], LieModel X StatedLieTag.PSL 4 p f →
      Nonempty (X ≃* ProjectiveSpecialLinearGroup (Fin 4) (GaloisField p f)) := by
    intro X _ hX
    rcases hX with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 4 p f hf hK)⟩
    · omega
    · omega
    · omega
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  exact ⟨e.trans e'.symm⟩

theorem nonempty_mulEquiv_of_lieModel_psu {G G' : Type} [Group G] [Group G'] {p f : ℕ}
    (h : LieModel G StatedLieTag.PSU 4 p f) (h' : LieModel G' StatedLieTag.PSU 4 p f) :
    Nonempty (G ≃* G') := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · rcases h' with ⟨-, -, K', _, _, hK', ⟨e'⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · let _ : Fintype K := Fintype.ofFinite K
      let _ : Fintype K' := Fintype.ofFinite K'
      have hcard : Fintype.card K = Fintype.card K' := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK']
      let φ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
      let e1 := statedProjCongr (glCongr (ι := Fin 4) φ) (glCongr_statedSU φ 4 (p ^ f))
        (glCongr_statedScalars φ)
      exact ⟨(e.trans e1).trans e'.symm⟩
    · omega
    · omega
    · omega
  · omega
  · omega
  · omega

@[expose] def LUNeighborhood : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (Gs : Type) [Group Gs],
    IsTwoCentralClassicalTypeCompat G Gs → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = p ^ f ∧ IsCentralInvolution z ∧ IsLinearA3Neighborhood K z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G)) ∧
    ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
        (_ : Finite F) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ IsCentralInvolution z ∧
          IsUnitaryA3Neighborhood (p ^ f) K F z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))

@[expose] def LUMax6A : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (Gs : Type) [Group Gs],
    IsTwoCentralClassicalTypeCompat G Gs → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) →
    ∀ z : G, IsCentralInvolution z → MaxOverCentralizerPSp4 z p f

theorem S_stage5_LU_compat_of_inputs (hN : LUNeighborhood) (h6A : LUMax6A) :
    S_stage5_LU_compat := by
  intro G _ _ hG Gs _ hGs hcompat
  obtain ⟨p, f, hp, hp2, hq, hmodel⟩ := hGs
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hq
      omega
    · exact h0
  have : Fact p.Prime := ⟨hp⟩
  rcases hmodel with ⟨h8, hL⟩ | ⟨h8, hU⟩
  · obtain ⟨K, _, _, z, u, Y, hK, hz, hA, hCN⟩ :=
      (hN G hG Gs hcompat p f hp hp2 hq).1 ⟨h8, hL⟩
    have hG' := hA.lieModel hG.1 p f hp hp2 hK hq hCN
      (h6A G hG Gs hcompat p f hp hp2 hq (Or.inl ⟨h8, hL⟩) z hz)
    exact nonempty_mulEquiv_of_lieModel_psl hp hf hG' hL
  · obtain ⟨K, _, _, _, F, _, _, z, u, Y, hK, hF, hz, hA, hCN⟩ :=
      (hN G hG Gs hcompat p f hp hp2 hq).2 ⟨h8, hU⟩
    have hG' := hA.lieModel hG.1 hK hF hp2 hq hCN
      (h6A G hG Gs hcompat p f hp hp2 hq (Or.inr ⟨h8, hU⟩) z hz)
    exact nonempty_mulEquiv_of_lieModel_psu hG' hU

end CFSG.GH74.GLS.LU
