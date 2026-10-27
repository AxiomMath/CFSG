module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432BD4Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FStable
public import CFSG.LocalAnalysis.SectionRank.PRank

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]


set_option linter.unusedSectionVars false

theorem card_le_pow_seven_of_isPGroup [CharP K 3] (E : Subgroup ↥(adjointGroup Tag.D4 K))
    (hE : IsPGroup 3 E) (hcomm : ∀ u ∈ E, ∀ w ∈ E, u * w = w * u) :
    Nat.card E ≤ Nat.card K ^ 7 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (adjointGroup Tag.D4 K) P₀ S
  set U₀ : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) with hU₀
  have hS : (S : Subgroup ↥(adjointGroup Tag.D4 K)) = U₀.map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₀]
    rfl
  set E' : Subgroup ↥(adjointGroup Tag.D4 K) := E.map (MulAut.conj x)⁻¹.toMonoidHom with hE'
  have hE'0 : E' ≤ unitN Tag.D4 K 0 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ U₀.map (MulAut.conj x).toMonoidHom := hS ▸ hES ha
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.1 h1
    have e : (MulAut.conj x)⁻¹ a = u := by
      rw [← hua]
      exact (MulAut.conj x).symm_apply_apply u
    change (MulAut.conj x)⁻¹ a ∈ unitN Tag.D4 K 0
    rw [e]
    exact unitN_zero_of_mem_pos (Subgroup.mem_subgroupOf.1 hu)
  have hE'comm : ∀ u ∈ E', ∀ w ∈ E', u * w = w * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change (MulAut.conj x)⁻¹ a * (MulAut.conj x)⁻¹ b = (MulAut.conj x)⁻¹ b * (MulAut.conj x)⁻¹ a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj x)⁻¹.injective
  rw [← hcard]
  exact card_le_pow_seven_of_comm E' hE'0 hE'comm

theorem pRank_top_le_seven {T : Type} [Group T] [Finite T] (hK : Nat.card K = 3)
    (e : T ≃* ↥(adjointGroup Tag.D4 K)) : CFSG.Open.pRank 3 (⊤ : Subgroup T) ≤ 7 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 3 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hEp : IsPGroup 3 E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  have h := card_le_pow_seven_of_isPGroup E hEp fun u hu w hw => d3f_commute hE hu hw
  rwa [hK] at h

end CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

end
