module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7Glue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
open scoped commutatorElement

theorem i227m_sylow_map {A : Type*} [Group A] [Finite A] {S : Subgroup A} (hS : IsPGroup 3 S)
    (hcard : Nat.card S = 3 ^ (Nat.card A).factorization 3) (N : Subgroup A) [N.Normal] :
    IsPGroup 3 (S.map (QuotientGroup.mk' N)) ∧
      Nat.card (S.map (QuotientGroup.mk' N)) = 3 ^ (Nat.card (A ⧸ N)).factorization 3 := by
  have hSb : IsPGroup 3 (S.map (QuotientGroup.mk' N)) :=
    hS.of_surjective ((QuotientGroup.mk' N).subgroupMap S)
      ((QuotientGroup.mk' N).subgroupMap_surjective S)
  refine ⟨hSb, (i247_card_iff hSb).2 fun hd => ?_⟩
  exact ((i247_card_iff hS).1 hcard)
    (hd.trans (Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective N)))

theorem i227m_quotient_weakCore (hFi : Fi22WeakCore3) {K : Type} [Group K] [Finite K]
    (hK : FiCoverK K) {P : Subgroup K} (hP3 : IsPGroup 3 P)
    (hPcard : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup (K ⧸ ⁅GLAPPrimeCore 5 K, (⊤ : Subgroup K)⁆)) ≤
      weakCoreIn 3 (P.map (QuotientGroup.mk' ⁅GLAPPrimeCore 5 K, (⊤ : Subgroup K)⁆)) ⊤ := by
  set R : Subgroup K := GLAPPrimeCore 5 K with hR
  set W : Subgroup K := ⁅R, (⊤ : Subgroup K)⁆ with hWdef
  have hWn : W.Normal := Subgroup.commutator_normal R ⊤
  have hWR : W ≤ R := Subgroup.commutator_le_left R ⊤
  have hperf : commutator (K ⧸ W) = ⊤ := by
    have : Group.IsPerfect K := Group.isPerfect_def.2 hK.perfect
    exact (Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)).commutator_eq_top
  set Nb : Subgroup (K ⧸ W) := R.map (QuotientGroup.mk' W) with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective W)
  have hcen : Nb ≤ Subgroup.center (K ⧸ W) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have hc : ⁅r, y⁆ ∈ W := Subgroup.commutator_mem_commutator hr (Subgroup.mem_top y)
    have e1 : r * y = ⁅r, y⁆ * (y * r) := by simp [commutatorElement_def, mul_assoc]
    show QuotientGroup.mk y * QuotientGroup.mk r = QuotientGroup.mk r * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e1,
      QuotientGroup.mk_mul W (⁅r, y⁆ : K) (y * r), (QuotientGroup.eq_one_iff _).2 hc, one_mul]
  have hF22 : IsFiTwentyTwo ((K ⧸ W) ⧸ Nb) := by
    obtain ⟨e⟩ := hK.fi
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient W R hWR).trans e⟩
  obtain ⟨hPb3, hPbcard⟩ := i227m_sylow_map hP3 hPcard W
  exact hFi (K ⧸ W) hperf Nb hcen hF22 _ hPb3 hPbcard

end CFSG.HardMathSupport.Solomon.Coordinator
