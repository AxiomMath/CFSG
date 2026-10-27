module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Finish
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Transfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Symp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PsuCover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2SuNegOne
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2SuScale
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PsuLA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Matrix

theorem l2NoPauliPSU_of_table
    (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable) : L2NoPauliPSU := by
  intro S _ _ H _ _ ρ A hρs hq hρk hH2 hE hP hsyl n p f hn8 hn4 hq4 hX
  obtain ⟨K, _, _, π, α, hp, hK, hπs, hπk, hαs, hρα⟩ :=
    l2_psu_cover hG (by omega) hX hq ρ hρs hρk
  subst hρα
  have hn0 : 0 < n := by omega
  have hqodd : p ^ f % 2 = 1 := by omega
  have he : Even n := ⟨n / 2, by omega⟩
  have h2 : (2 : K) ≠ 0 := by
    refine l2_two_ne_zero ?_
    rw [hK, Nat.pow_mod, hqodd]
  obtain ⟨m, hmM, hm1, hm2, hmc, hmu0⟩ := l2_su_neg_one hp hK hn0 he (Nat.odd_iff.mpr hqodd)
  have hmker : m ∈ (ρ.comp α).ker := by rw [hπk]; exact hmc
  have hmu : ∀ u ∈ (ρ.comp α).ker, u * u = 1 → u = 1 ∨ u = m := by
    intro u hu
    rw [hπk] at hu
    exact hmu0 u hu
  have hcen : ∀ u ∈ (ρ.comp α).ker, ∀ x : ↥(CFSG.Open.StatedSU n (p ^ f) K),
      u * x = x * u := by
    intro u hu x
    rw [hπk] at hu
    exact ((Subgroup.mem_center_iff.mp
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _ hu)) x).symm
  obtain ⟨hP1, hP2, hP3⟩ := l2_pauli_transfer α hαs ρ hρk hH2 hE hP hm1 hm2 hmker hmu hcen
  have hmcen : ∀ x : ↥(CFSG.Open.StatedSU n (p ^ f) K), m * x = x * m := fun x =>
    ((Subgroup.mem_center_iff.mp
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _ hmc)) x).symm
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, hb₁, ha₂, hb₂, hab₁, hab₂, hc₁₂, hc₁₂', hc₂₁, hcbb, hgen⟩ :=
    l2_symp_basis (ρ.comp α) hπs hE hmcen hm1 hm2 hcen hP1 hP2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  let σ : K →+* K := iterateFrobenius K p f
  have hσ : ∀ x : K, σ x = x ^ p ^ f := fun x => rfl
  have hσσ : ∀ x : K, σ (σ x) = x := by
    intro x
    rw [hσ, hσ, ← pow_mul, ← pow_two]
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hSU : ∀ x : ↥(CFSG.Open.StatedSU n (p ^ f) K),
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    intro x
    have hmem : (x : GL (Fin n) K) ∈ (CFSG.Open.StatedSU n (p ^ f) K : Set (GL (Fin n) K)) :=
      x.2
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hK hn0).1] at hmem
    exact hmem.2
  have hunit : ∀ (ν : K) (X : Matrix (Fin n) (Fin n) K), ν ^ (p ^ f + 1) = 1 →
      (X.map σ)ᵀ * X = 1 → ((ν • X).map σ)ᵀ * (ν • X) = 1 := by
    intro ν X hν hX
    have h1 : (ν • X).map σ = (ν ^ p ^ f) • X.map σ := by
      ext i j
      simp [hσ, mul_pow]
    rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ, hν,
      one_smul, hX]
  have hscale : ∀ x : ↥(CFSG.Open.StatedSU n (p ^ f) K), (ρ.comp α) x ∈ A → ∃ ν : K, ν ≠ 0 ∧
      (ν • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (ν • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 ∧
      ((ν • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map σ)ᵀ *
        (ν • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    intro x hx
    obtain ⟨x', hx'e, k, hk, hko, h2'⟩ := hP3 ((ρ.comp α) x) hx
    obtain ⟨ν, hν, hν2⟩ := l2_su_scale hp hK hq4 hn0 x x' k m
      (by rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, hx'e, mul_inv_cancel])
      (by rwa [hπk] at hk) hko hmM h2'
    refine ⟨ν, ?_, hν2, hunit ν _ hν (hSU x)⟩
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hν
    exact zero_ne_one hν
  have hs : ∀ (c d : K) (X Y : Matrix (Fin n) (Fin n) K),
      (c • X) * (d • Y) = (c * d) • (X * Y) := by
    intro c d X Y
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hanti : ∀ x y : ↥(CFSG.Open.StatedSU n (p ^ f) K), ⁅x, y⁆ = m →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix _ _ K) =
        -(((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix _ _ K)) := by
    intro x y h
    have h' : x * y = m * (y * x) := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = m * (y * x) := by rw [← commutatorElement_def, h]
    have h'' := congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h'
    simpa [hmM] using h''
  have hcomm : ∀ x y : ↥(CFSG.Open.StatedSU n (p ^ f) K), ⁅x, y⁆ = 1 →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix _ _ K) =
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix _ _ K) := by
    intro x y h
    have h' := commutatorElement_eq_one_iff_mul_comm.mp h
    simpa using congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h'
  obtain ⟨μ₁, hμ₁, hμ₁s, hμ₁u⟩ := hscale a₁ ha₁
  obtain ⟨ν₁, hν₁, hν₁s, hν₁u⟩ := hscale b₁ hb₁
  obtain ⟨μ₂, hμ₂, hμ₂s, hμ₂u⟩ := hscale a₂ ha₂
  obtain ⟨ν₂, hν₂, hν₂s, hν₂u⟩ := hscale b₂ hb₂
  set A₁ : Matrix (Fin n) (Fin n) K := ((a₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA₁
  set B₁ : Matrix (Fin n) (Fin n) K := ((b₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hB₁
  set A₂ : Matrix (Fin n) (Fin n) K := ((a₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA₂
  set B₂ : Matrix (Fin n) (Fin n) K := ((b₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hB₂
  have r₁ : (μ₁ • A₁) * (ν₁ • B₁) = -((ν₁ • B₁) * (μ₁ • A₁)) := by
    rw [hs, hs, hanti a₁ b₁ hab₁, mul_comm ν₁ μ₁, smul_neg]
  have r₂ : (μ₂ • A₂) * (ν₂ • B₂) = -((ν₂ • B₂) * (μ₂ • A₂)) := by
    rw [hs, hs, hanti a₂ b₂ hab₂, mul_comm ν₂ μ₂, smul_neg]
  have r₃ : (μ₁ • A₁) * (μ₂ • A₂) = (μ₂ • A₂) * (μ₁ • A₁) := by
    rw [hs, hs, hcomm a₁ a₂ hc₁₂, mul_comm μ₁ μ₂]
  have r₄ : (μ₁ • A₁) * (ν₂ • B₂) = (ν₂ • B₂) * (μ₁ • A₁) := by
    rw [hs, hs, hcomm a₁ b₂ hc₁₂', mul_comm μ₁ ν₂]
  have r₅ : (ν₁ • B₁) * (μ₂ • A₂) = (μ₂ • A₂) * (ν₁ • B₁) := by
    rw [hs, hs, hcomm b₁ a₂ hc₂₁, mul_comm ν₁ μ₂]
  have r₆ : (ν₁ • B₁) * (ν₂ • B₂) = (ν₂ • B₂) * (ν₁ • B₁) := by
    rw [hs, hs, hcomm b₁ b₂ hcbb, mul_comm ν₁ ν₂]
  obtain ⟨g, hg2, hgdet, hgu, hgns, hg₁, hg₂, hg₃, hg₄⟩ :=
    l2_psu_la σ hσσ h2 (by omega : 4 < n) (μ₁ • A₁) (ν₁ • B₁) (μ₂ • A₂) (ν₂ • B₂)
      hμ₁s hν₁s hμ₂s hν₂s hμ₁u hν₁u hμ₂u hν₂u r₁ r₂ r₃ r₄ r₅ r₆
  let gG : GL (Fin n) K := ⟨g, g, hg2, hg2⟩
  have hgmem : gG ∈ CFSG.Open.StatedSU n (p ^ f) K := by
    have hm : gG ∈ (CFSG.Open.StatedSU n (p ^ f) K : Set (GL (Fin n) K)) := by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hK hn0).1]
      exact ⟨hgdet, hgu⟩
    exact hm
  let g' : ↥(CFSG.Open.StatedSU n (p ^ f) K) := ⟨gG, hgmem⟩
  have hcancel : ∀ (μ : K) (x : ↥(CFSG.Open.StatedSU n (p ^ f) K)), μ ≠ 0 →
      g * (μ • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        (μ • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * g → g' * x = x * g' := by
    intro μ x hμ h
    apply Subtype.ext
    apply Units.ext
    change g * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ hμ h
  have hg'2 : g' * g' = 1 := Subtype.ext (Units.ext hg2)
  have hgn : g' ∉ (ρ.comp α).ker := by
    intro hmem
    rw [hπk, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := hmem
    apply hgns (c : K)
    have h := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at h
    have h' : g = Matrix.scalar (Fin n) (c : K) := h.symm
    rw [h', Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  exact l2_pauli_finish (ρ.comp α) hπs hm1 hcen hP2 hgen hg'2 hgn
    (hcancel μ₁ a₁ hμ₁ hg₁) (hcancel ν₁ b₁ hν₁ hg₂) (hcancel μ₂ a₂ hμ₂ hg₃)
    (hcancel ν₂ b₂ hν₂ hg₄) hsyl

end CFSG.OddStandard.HigherRank.YamadaG23
