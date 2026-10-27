module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Bridge.Fi22Surj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise

theorem i227m_fi22_facts
    {F : Type*} [Group F] (h : IsFiTwentyTwo F) :
    IsSimpleGroup F ∧ (∃ a b : F, a * b ≠ b * a) ∧ 3 ∣ Nat.card F := by
  obtain ⟨e⟩ := h
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  have e1 : CFSG.Blueprint.NativeSporadic.Fi22 ≃* F := b.trans e.symm
  have hcard : Nat.card F = 64561751654400 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact CFSG.Sporadic.Fi22.card_Fi22
  have hsF : IsSimpleGroup F := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e1.symm
  have h3 : 3 ∣ Nat.card F := by
    rw [hcard]
    exact Nat.dvd_of_mod_eq_zero (by norm_num)
  refine ⟨hsF, ?_, h3⟩
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative F := ⟨⟨fun a b => hcon a b⟩⟩
  have hp := IsSimpleGroup.prime_card (α := F)
  rw [hcard] at hp
  exact absurd hp (by norm_num)

theorem i227m_openKGroup_of_surjective {A B : Type*} [Group A] [Group B]
    (hA : CFSG.Open.IsKGroup A) (f : A →* B) (hf : Function.Surjective f) :
    CFSG.Open.IsKGroup B :=
  hA.of_surjective f hf

theorem i227m_three_le_pRank_of_sylow {K : Type*} [Group K] [Finite K]
    (h5 : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) {P : Subgroup K}
    (hcard : Nat.card P = 3 ^ (Nat.card K).factorization 3) : 3 ≤ CFSG.Open.pRank 3 P := by
  have hp : 1 < 3 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup K)
  have hE3 : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  let S : Sylow 3 K := Sylow.ofCard P hcard
  obtain ⟨Q, hEQ⟩ := hE3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q S
  have hS : (S : Subgroup K) = P := Sylow.coe_ofCard P hcard
  set f : K →* K := (MulAut.conj g).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj g).injective
  have hle : E.map f ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g) • x ∈ MulAut.conj g • (Q : Subgroup K) :=
      Subgroup.smul_mem_pointwise_smul x _ _ (hEQ hx)
    have h2 : (MulAut.conj g • (Q : Subgroup K)) = (S : Subgroup K) := by
      rw [← hg]
      rfl
    rw [h2, hS] at h1
    exact h1
  have := CFSG.SectionRank.le_pRank hp hle (CFSG.SectionRank.isElemAbelian_map hE f)
    (k := CFSG.Open.pRank 3 (⊤ : Subgroup K)) (by rw [Subgroup.card_map_of_injective hfi, hEc])
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
