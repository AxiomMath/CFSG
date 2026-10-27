module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Nu
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.Blueprint CFSG.ABGLocalTools CFSG.GH74.L5U5 CFSG.GH74.GLS.LU.Local
  CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem jmlu_sylow_center_psl {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 ≠ 1) (hL : LieModel K .PSL 4 p f)
    (T : Sylow 2 K) :
    ∃ z₁ : K, orderOf z₁ = 2 ∧
      (center ↥(T : Subgroup K)).map (T : Subgroup K).subtype = zpowers z₁ := by
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  have hcases : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  obtain ⟨S₀, t, u, hd⟩ : ∃ (S : Sylow 2 (PG (ModelData.lin F))) (t u : PG (ModelData.lin F)),
      LUModelData (PG (ModelData.lin F)) (Nat.card F) 1 (yP _) S (K1 _) (K2 _) t u := by
    rcases hcases with h | h | h
    · exact luModelData_lin_zs h2 h5' (by rw [hF]; omega)
    · exact luModelData_lin_mu4 h2 h5' (by rw [hF]; omega)
    · exact luModelData_lin_zs h2 h5' (by rw [hF]; omega)
  exact sylow_center_transport (show K ≃* PG (ModelData.lin F) from e) S₀ (yP _) hd.syl.z_inv
    ((centerIs_iff _ _).1 hd.syl.z_cen) T

theorem jmlu_sylow_center_psu {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 ≠ 7) (hU : LieModel K .PSU 4 p f)
    (T : Sylow 2 K) :
    ∃ z₁ : K, orderOf z₁ = 2 ∧
      (center ↥(T : Subgroup K)).map (T : Subgroup K).subtype = zpowers z₁ := by
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
  have : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
  have hcases : p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  obtain ⟨S₀, t, u, hd⟩ : ∃ (S : Sylow 2 (PG (ModelData.uni hF))) (t u : PG (ModelData.uni hF)),
      LUModelData (PG (ModelData.uni hF)) (p ^ f) (-1) (yP _) S (K1 _) (K2 _) t u := by
    rcases hcases with h | h | h
    · exact luModelData_uni_zs hF hp2 h5 (by omega)
    · exact luModelData_uni_mu4 hF hp2 h5 h
    · exact luModelData_uni_zs hF hp2 h5 (by omega)
  exact sylow_center_transport (show K ≃* PG (ModelData.uni hF) from e) S₀ (yP _) hd.syl.z_inv
    ((centerIs_iff _ _).1 hd.syl.z_cen) T

theorem jmlu_card_inf_of_comps {K : Type} [Group K] [Finite K] {q : ℕ} {z : K}
    {E₁ E₂ : Subgroup K} (hc : LUComps K q z E₁ E₂) (hz2 : orderOf z = 2) (P : Sylow 2 K)
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) :
    Nat.card ↥((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) = 2 ^ nuQ q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : (P : Subgroup K) ≤ Cz z := fun x hx => mem_centralizer_singleton_iff.mpr (hzc x hx)
  have htop : IsSylowOf 2 (P : Subgroup K) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hsyl : IsSylowOf 2 (P : Subgroup K) (Cz z) := htop.of_le hPC le_top
  have hE_le : E₁ ⊔ E₂ ≤ Cz z := sup_le hc.comp₁.1 hc.comp₂.1
  have hnorm : Cz z ≤ normalizer ((E₁ ⊔ E₂ : Subgroup K) : Set K) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hc.conj_sup_mem hg hk
    · intro hk
      have := hc.conj_sup_mem (inv_mem hg) hk
      simpa [mul_assoc] using this
  have hsyl' := hsyl.inf_of_le_normalizer hE_le hnorm
  rw [hsyl'.card_eq]
  have hcard : Nat.card ↥(E₁ ⊔ E₂) * 2 = (q * (q ^ 2 - 1)) ^ 2 := by
    rw [hc.card_sup hz2, card_of_hasSL2Model hc.sl₁, card_of_hasSL2Model hc.sl₂]
    exact (sq _).symm
  unfold nuQ
  rw [← hcard, Nat.mul_div_cancel _ (by norm_num)]

theorem jm_card_lu {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f)
    (hK : (p ^ f % 8 ≠ 1 ∧ LieModel K .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel K .PSU 4 p f))
    (P : Sylow 2 K) {z : K} (hzP : z ∈ (P : Subgroup K)) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) :
    Nat.card ↥(P : Subgroup K) = 2 ^ nuQ (p ^ f) * 4 := by
  obtain ⟨z₁, hz₁, hcen₁⟩ : ∃ z₁ : K, orderOf z₁ = 2 ∧
      (center ↥(P : Subgroup K)).map (P : Subgroup K).subtype = zpowers z₁ := by
    rcases hK with ⟨h8, hL⟩ | ⟨h8, hU⟩
    · exact jmlu_sylow_center_psl hp hp2 h5 h8 hL P
    · exact jmlu_sylow_center_psu hp hp2 h5 h8 hU P
  have hzmem : z ∈ (center ↥(P : Subgroup K)).map (P : Subgroup K).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  rw [hcen₁] at hzmem
  have hzz : z = z₁ := ModelBlock.eq_of_mem_zpowers_of_orderOf_two hz₁ hz2 hzmem
  have hcen : (center ↥(P : Subgroup K)).map (P : Subgroup K).subtype = zpowers z := by
    rw [hcen₁, hzz]
  have key := luModelLeaf K p f hp hp2 h5 P z hcen
  obtain ⟨ε, E₁, E₂, t, u, hd⟩ :
      ∃ (ε : ℤ) (E₁ E₂ : Subgroup K) (t u : K), LUModelData K (p ^ f) ε z P E₁ E₂ t u := by
    rcases hK with ⟨h8, hL⟩ | ⟨h8, hU⟩
    · obtain ⟨E₁, E₂, t, u, hd⟩ := key.1 ⟨h8, hL⟩
      exact ⟨1, E₁, E₂, t, u, hd⟩
    · obtain ⟨E₁, E₂, t, u, hd⟩ := key.2 ⟨h8, hU⟩
      exact ⟨-1, E₁, E₂, t, u, hd⟩
  rw [hd.syl.card_S, jmlu_card_inf_of_comps hd.comps hz2 P hzc]
  ring

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
