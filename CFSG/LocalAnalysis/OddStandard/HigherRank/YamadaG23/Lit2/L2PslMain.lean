module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Sylow
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Transfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Symp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslCover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslScale
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslLA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslM

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem l2NoPauliPSL_of_table
    (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable) : L2NoPauliPSL := by
  intro S _ _ H _ _ ρ A hρs hq hρk hH2 hE hP hsyl n p f hn8 hn4 hq4 hX
  obtain ⟨K, _, _, π, α, hK, hπs, hπk, hαs, hρα⟩ := l2_psl_cover hG (by omega) hX hq ρ hρs hρk
  subst hρα
  have hn0 : 0 < n := by omega
  have hcardK : Nat.card K % 4 = 1 := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [hK] at hpos ⊢
    generalize p ^ f = N at hpos hq4 ⊢
    omega
  have h2 : (2 : K) ≠ 0 := l2_two_ne_zero (by omega)
  obtain ⟨m, hmM, hm1, hm2, hmc, hmu0⟩ := l2_sl_neg_one h2 hn0 ⟨n / 2, by omega⟩
  have hmker : m ∈ (ρ.comp α).ker := by rw [hπk]; exact hmc
  have hmu : ∀ u ∈ (ρ.comp α).ker, u * u = 1 → u = 1 ∨ u = m := by
    intro u hu
    rw [hπk] at hu
    exact hmu0 u hu
  have hcen : ∀ u ∈ (ρ.comp α).ker, ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
      u * x = x * u := by
    intro u hu x
    rw [hπk] at hu
    exact ((Subgroup.mem_center_iff.mp hu) x).symm
  obtain ⟨hP1, hP2, hP3⟩ := l2_pauli_transfer α hαs ρ hρk hH2 hE hP hm1 hm2 hmker hmu hcen
  have hmcen : ∀ x : Matrix.SpecialLinearGroup (Fin n) K, m * x = x * m :=
    fun x => ((Subgroup.mem_center_iff.mp hmc) x).symm
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, hb₁, ha₂, hb₂, hab₁, hab₂, hc₁₂, hc₁₂', hc₂₁, hcbb, hgen⟩ :=
    l2_symp_basis (ρ.comp α) hπs hE hmcen hm1 hm2 hcen hP1 hP2
  have hscale : ∀ x : Matrix.SpecialLinearGroup (Fin n) K, (ρ.comp α) x ∈ A → ∃ μ : K, μ ≠ 0 ∧
      (μ • (x : Matrix (Fin n) (Fin n) K)) * (μ • (x : Matrix (Fin n) (Fin n) K)) = 1 := by
    intro x hx
    obtain ⟨x', hx'e, k, hk, hko, h2'⟩ := hP3 ((ρ.comp α) x) hx
    refine l2_scale_involution hcardK hn0 x x' k m ?_ ?_ hko hmM h2'
    · rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, hx'e, mul_inv_cancel]
    · rwa [hπk] at hk
  have hs : ∀ (c d : K) (X Y : Matrix (Fin n) (Fin n) K),
      (c • X) * (d • Y) = (c * d) • (X * Y) := by
    intro c d X Y
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hanti : ∀ x y : Matrix.SpecialLinearGroup (Fin n) K, ⁅x, y⁆ = m →
      (x : Matrix (Fin n) (Fin n) K) * y = -((y : Matrix (Fin n) (Fin n) K) * x) := by
    intro x y h
    have h' : x * y = m * (y * x) := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = m * (y * x) := by rw [← commutatorElement_def, h]
    have h'' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
      (z : Matrix (Fin n) (Fin n) K)) h'
    simpa [hmM] using h''
  have hcomm : ∀ x y : Matrix.SpecialLinearGroup (Fin n) K, ⁅x, y⁆ = 1 →
      (x : Matrix (Fin n) (Fin n) K) * y = y * x := by
    intro x y h
    have h' := commutatorElement_eq_one_iff_mul_comm.mp h
    simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
      (z : Matrix (Fin n) (Fin n) K)) h'
  obtain ⟨μ₁, hμ₁, hμ₁s⟩ := hscale a₁ ha₁
  obtain ⟨ν₁, hν₁, hν₁s⟩ := hscale b₁ hb₁
  obtain ⟨μ₂, hμ₂, hμ₂s⟩ := hscale a₂ ha₂
  obtain ⟨ν₂, hν₂, hν₂s⟩ := hscale b₂ hb₂
  have r₁ : (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K)) * (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) =
      -((ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) * (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K))) := by
    rw [hs, hs, hanti a₁ b₁ hab₁, mul_comm ν₁ μ₁, smul_neg]
  have r₂ : (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K)) * (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) =
      -((ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) * (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K))) := by
    rw [hs, hs, hanti a₂ b₂ hab₂, mul_comm ν₂ μ₂, smul_neg]
  have r₃ : (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K)) * (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K)) =
      (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K)) * (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K)) := by
    rw [hs, hs, hcomm a₁ a₂ hc₁₂, mul_comm μ₁ μ₂]
  have r₄ : (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K)) * (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) =
      (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) * (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K)) := by
    rw [hs, hs, hcomm a₁ b₂ hc₁₂', mul_comm μ₁ ν₂]
  have r₅ : (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) * (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K)) =
      (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K)) * (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) := by
    rw [hs, hs, hcomm b₁ a₂ hc₂₁, mul_comm ν₁ μ₂]
  have r₆ : (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) * (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) =
      (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) * (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) := by
    rw [hs, hs, hcomm b₁ b₂ hcbb, mul_comm ν₁ ν₂]
  obtain ⟨g, hg2, hgdet, hgns, hg₁, hg₂, hg₃, hg₄⟩ :=
    l2_psl_la h2 (by omega : 4 < n) (μ₁ • (a₁ : Matrix (Fin n) (Fin n) K))
      (ν₁ • (b₁ : Matrix (Fin n) (Fin n) K)) (μ₂ • (a₂ : Matrix (Fin n) (Fin n) K))
      (ν₂ • (b₂ : Matrix (Fin n) (Fin n) K)) hμ₁s hν₁s hμ₂s hν₂s r₁ r₂ r₃ r₄ r₅ r₆
  let g' : Matrix.SpecialLinearGroup (Fin n) K := ⟨g, hgdet⟩
  have hcancel : ∀ (μ : K) (x : Matrix.SpecialLinearGroup (Fin n) K), μ ≠ 0 →
      g * (μ • (x : Matrix (Fin n) (Fin n) K)) = (μ • (x : Matrix (Fin n) (Fin n) K)) * g →
      g' * x = x * g' := by
    intro μ x hμ h
    apply Subtype.ext
    change g * (x : Matrix (Fin n) (Fin n) K) = (x : Matrix (Fin n) (Fin n) K) * g
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ hμ h
  have hga₁ := hcancel μ₁ a₁ hμ₁ hg₁
  have hgb₁ := hcancel ν₁ b₁ hν₁ hg₂
  have hga₂ := hcancel μ₂ a₂ hμ₂ hg₃
  have hgb₂ := hcancel ν₂ b₂ hν₂ hg₄
  have hgy : ∀ y : Matrix.SpecialLinearGroup (Fin n) K, (ρ.comp α) y ∈ A → g' * y = y * g' := by
    intro y hy
    have hle : Subgroup.closure (({a₁, b₁, a₂, b₂} : Set (Matrix.SpecialLinearGroup (Fin n) K)) ∪
        (((ρ.comp α).ker : Subgroup _) : Set (Matrix.SpecialLinearGroup (Fin n) K))) ≤
        Subgroup.centralizer ({g'} : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hz with hz | hz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hga₁
        · exact hgb₁
        · exact hga₂
        · exact hgb₂
      · exact (hcen z hz g').symm
    exact (Subgroup.mem_centralizer_iff.mp (hle (hgen y hy))) g' (Set.mem_singleton g')
  have hs2 : (ρ.comp α) g' * (ρ.comp α) g' = 1 := by
    rw [← map_mul]
    have : g' * g' = 1 := Subtype.ext hg2
    rw [this, map_one]
  have hsc : ∀ a ∈ A, a * (ρ.comp α) g' = (ρ.comp α) g' * a := by
    intro a ha
    obtain ⟨y, rfl⟩ := hπs a
    rw [← map_mul, ← map_mul, (hgy y ha).symm]
  have hsA : (ρ.comp α) g' ∉ A := by
    intro hsA
    by_cases hs1 : (ρ.comp α) g' = 1
    · have hgc : g' ∈ center (Matrix.SpecialLinearGroup (Fin n) K) := by
        rw [← hπk]
        exact hs1
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hgc
      apply hgns r
      have : (g' : Matrix (Fin n) (Fin n) K) = g := rfl
      rw [← this, ← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · obtain ⟨y, hyA, hy⟩ := hP2 g' hsA hs1
      have h1 : ⁅g', y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hgy y hyA)
      exact hm1 (hy.symm.trans h1)
  exact l2_not_sylow_of_extra hsc hsA hs2 hsyl

end CFSG.OddStandard.HigherRank.YamadaG23
