module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial

section Basic

theorem charP_of_card_eq_pow {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : Nat.card F = p ^ f) : CharP F p := by
  have hℓ : (ringChar F).Prime := CharP.prime_ringChar F
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : p ∣ (ringChar F) ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, h]
    exact dvd_pow_self p (by omega)
  have hpℓ : p = ringChar F :=
    (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hdvd)
  rw [hpℓ]
  exact ringChar.charP F

end Basic

section Parabolics

variable {Y : Type} [Group Y] {p f : ℕ}

theorem l2_borelTitsConcl (hp : p.Prime) (h : Blueprint.LieModel Y .PSL 2 p f) :
    BorelTitsConcl p Y := by
  obtain ⟨-, hf, -, -, F, _, _, hcard, ⟨e⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_pow hp hf hcard
  have hX : LieType.BorelTits.Holds (PSL2 F) p :=
    LieType.BorelTits.holds_projectiveSpecialLinearGroup 2 F p
  have hY : LieType.BorelTits.Holds Y p := hX.of_mulEquiv e.symm
  intro U hU hUp
  obtain ⟨S, M, hM, hN, -, -, hS⟩ := hY U hU hUp
  exact ⟨S, M, hM, hN, hS⟩

theorem l2_evenParabolics (hp : p.Prime) (hp2 : p ≠ 2) (h : Blueprint.LieModel Y .PSL 2 p f) :
    EvenParabolics p Y := by
  classical
  obtain ⟨-, hf, -, -, -⟩ := ComponentClassification.AutL2Facts.lieModel_psl2_data h
  obtain ⟨K, _, hKfin, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_pow hp hf hcard
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  intro S M hSM hMtop
  let φ : Y →* LinearFlag.projectiveSL 2 K := e.toMonoidHom
  have hbij : Function.Bijective φ := e.bijective
  let T : Sylow p (LinearFlag.projectiveSL 2 K) := Sylow.mapSurjective (f := φ) hbij.2 S
  have hT : (T : Subgroup (LinearFlag.projectiveSL 2 K)) = (S : Subgroup Y).map φ := rfl
  have hNT : normalizer ((T : Subgroup (LinearFlag.projectiveSL 2 K)) : Set _) ≤ M.map φ := by
    rw [hT, ← Subgroup.map_normalizer_eq_of_bijective _ hbij]
    exact Subgroup.map_mono hSM
  have hM'top : M.map φ ≠ ⊤ := by
    intro htop
    apply hMtop
    rw [eq_top_iff]
    intro y _
    have hy : φ y ∈ M.map φ := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmy⟩ := hy
    exact (hbij.1 hmy) ▸ hm
  obtain ⟨M₁, hM₁, hM'le⟩ := (eq_top_or_exists_le_coatom (M.map φ)).resolve_left hM'top
  have hmem : M₁ ∈ LinearFlag.maximalParabolics (LinearFlag.projectiveSL 2 K) p :=
    ⟨hM₁, _, ⟨T, rfl⟩, hNT.trans hM'le⟩
  rw [(LinearFlag.maximal_parabolics p (by norm_num : 1 ≤ 2)).1] at hmem
  obtain ⟨W, ⟨hW0, hWtop⟩, rfl⟩ := hmem
  have hlt : Module.finrank K W < 2 := by
    have := Submodule.finrank_lt (hWtop.ne)
    rwa [Module.finrank_fin_fun] at this
  have hpos : Module.finrank K W ≠ 0 := fun h0 => hW0.ne' (Submodule.finrank_eq_zero.mp h0)
  have hrank : Module.finrank K W = 1 := by omega
  have hidx := (LinearFlag.subspace_index (K := K) (n := 2) (k := 1) (by norm_num)).2 W hrank
  have hq2 : 2 ≤ Nat.card K := by
    rw [hcard]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hqodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hq1 : ((Nat.card K : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ Nat.card K := by exact_mod_cast hq2
    linarith
  have hgauss : LinearFlag.gaussianCoeff 2 1 (Nat.card K) = (Nat.card K : ℚ) + 1 := by
    simp only [LinearFlag.gaussianCoeff, Finset.range_one, Finset.prod_singleton]
    norm_num
    field_simp
    ring
  have hindex : (LinearFlag.projStabilizer W).index = Nat.card K + 1 := by
    have h1 : ((LinearFlag.projStabilizer W).index : ℚ) = (Nat.card K : ℚ) + 1 := by
      rw [hidx, hgauss]
    exact_mod_cast h1
  have hev : Even (LinearFlag.projStabilizer W).index := by
    rw [hindex]
    exact hqodd.add_one
  rw [← Subgroup.index_map_of_bijective hbij M, ← Subgroup.relIndex_mul_index hM'le]
  exact hev.mul_left _

end Parabolics

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
