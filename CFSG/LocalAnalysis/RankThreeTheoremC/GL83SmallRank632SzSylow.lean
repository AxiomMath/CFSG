module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint CFSG.LieType.Ree

private theorem szSylow_not_nearCyclic_of_pow_four {V : Type*} [Group V] [Finite V]
    (hcard : 16 < Nat.card V) (hexp : ∀ v : V, v ^ 4 = 1) : ¬ NearCyclic V := by
  rintro ⟨C, -, hC, hidx⟩
  have hdvd : Nat.card C ∣ 4 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hexp x)
  have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hmul := C.index_mul_card
  have : Nat.card V ≤ 4 * 4 := hmul ▸ Nat.mul_le_mul hidx hle
  omega

private theorem szSylow_suzukiSElt_pow_four {a : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiSElt a K u v ^ 4 = 1 := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  have hsq : suzukiSElt a K u v ^ 2 = suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * u) := by
    rw [sq, suzukiSElt_mul hK]
    congr 1
    · linear_combination u * h2
    · linear_combination v * h2
  have h4 : suzukiSElt a K u v ^ 4 = (suzukiSElt a K u v ^ 2) ^ 2 := by
    rw [← pow_mul]
  rw [h4, hsq, sq]
  exact CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiSElt_zero_mul_self hK _

private theorem szSylow_pow_four_of_mem {a : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (Q : Sylow 2 (suzukiGroup a K))
    {g : suzukiGroup a K} (hg : g ∈ (Q : Subgroup (suzukiGroup a K))) : g ^ 4 = 1 := by
  obtain ⟨U, hU⟩ := CFSG.ShultStronglyClosedTI.SuzukiModel.exists_sylow_eq_suzukiU hK
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) U Q
  have hmem : x⁻¹ * g * x ∈ (U : Subgroup (suzukiGroup a K)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg
    simpa [MulAut.smul_def] using hg
  rw [hU, mem_suzukiU_iff hK] at hmem
  obtain ⟨u, v, hs⟩ := hmem
  have h4 : (x⁻¹ * g * x) ^ 4 = 1 := hs ▸ szSylow_suzukiSElt_pow_four hK u v
  have hg' : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  rw [hg', conj_pow, h4, mul_one, mul_inv_cancel]

theorem SuzukiModel.not_nearCyclic_sylow {S : Type} [Group S]
    [Finite S] {f : ℕ} (h : SuzukiModel S 2 f) (Q : Sylow 2 S) :
    ¬ NearCyclic ↥(Q : Subgroup S) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  refine szSylow_not_nearCyclic_of_pow_four ?_ fun v => ?_
  · have hdvd : 2 ^ ((2 * a + 1) * 2) ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv, suzuki_order hK, pow_mul]
      exact (dvd_mul_right _ _).mul_right _
    have hle := Nat.le_of_dvd Nat.card_pos (Q.pow_dvd_card_of_pow_dvd_card hdvd)
    have h64 : 2 ^ 6 ≤ 2 ^ ((2 * a + 1) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    change 16 < Nat.card Q
    omega
  · refine Subtype.ext (e.injective ?_)
    have hv : (v : S) ∈ (Q : Subgroup S) := v.2
    have hf : Function.Surjective e.toMonoidHom := e.surjective
    have h4 : (e (v : S)) ^ 4 = 1 := by
      refine szSylow_pow_four_of_mem hK (Q.mapSurjective hf) ?_
      rw [Sylow.coe_mapSurjective]
      exact ⟨v, hv, rfl⟩
    simpa using h4

end CFSG.LocalAnalysis.RankThreeTheoremC
