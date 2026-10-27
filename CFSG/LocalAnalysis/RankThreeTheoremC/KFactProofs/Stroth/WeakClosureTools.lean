module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

variable {K : Type} [Group K] [Finite K]

private theorem map_conj_map_conj (H : Subgroup K) (a b : K) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one (H : Subgroup K) : H.map (MulAut.conj (1 : K)).toMonoidHom = H := by
  ext x
  simp [MulAut.conj_apply]

theorem WCOn.of_sylow {p : ℕ} [Fact p.Prime] (P₀ : Sylow p K)
    (h : IsMulCommutative (P₀ : Subgroup K) → 2 ≤ CFSG.Open.pRank p (P₀ : Subgroup K) →
      ∀ A : Subgroup K, A ≤ (P₀ : Subgroup K) → Nat.card A = p →
        ∃ g : K, A.map (MulAut.conj g).toMonoidHom ≤ (P₀ : Subgroup K) ∧
          A.map (MulAut.conj g).toMonoidHom ≠ A) :
    WCOn p K := by
  intro P hPab hrank A hAP hA
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P₀ P
  have hPc : (P : Subgroup K) = (P₀ : Subgroup K).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  have hP₀ : (P₀ : Subgroup K) = (P : Subgroup K).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [hPc, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hP₀ab : IsMulCommutative (P₀ : Subgroup K) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : (MulAut.conj c) (a : K) ∈ (P : Subgroup K) := by
      rw [hPc]; exact ⟨a, a.2, rfl⟩
    have hb : (MulAut.conj c) (b : K) ∈ (P : Subgroup K) := by
      rw [hPc]; exact ⟨b, b.2, rfl⟩
    have h1 := congrArg Subtype.val (hPab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    simp only [Subgroup.coe_mul] at h1 ⊢
    rw [← map_mul, ← map_mul] at h1
    exact (MulAut.conj c).injective h1
  have hrank₀ : 2 ≤ CFSG.Open.pRank p (P₀ : Subgroup K) := by
    rw [hP₀]
    exact hrank.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p
      Fact.out _ (MulAut.conj c⁻¹).injective _)
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : Subgroup K, A₀ = A.map (MulAut.conj c⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hA₀P : A₀ ≤ (P₀ : Subgroup K) := by
    rw [hA₀def, hP₀]
    exact Subgroup.map_mono hAP
  have hA₀ : Nat.card A₀ = p := by
    rw [hA₀def, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hA]
  obtain ⟨g₀, hg₀P, hg₀A⟩ := h hP₀ab hrank₀ A₀ hA₀P hA₀
  have hA' : A = A₀.map (MulAut.conj c).toMonoidHom := by
    rw [hA₀def, map_conj_map_conj, mul_inv_cancel, map_conj_one]
  refine ⟨c * g₀ * c⁻¹, ?_, fun heq => hg₀A ?_⟩
  · have e : A.map (MulAut.conj (c * g₀ * c⁻¹)).toMonoidHom =
        (A₀.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
      rw [hA', map_conj_map_conj, map_conj_map_conj, show c * g₀ * c⁻¹ * c = c * g₀ by group]
    rw [e, hPc]
    exact Subgroup.map_mono hg₀P
  · have e : A₀.map (MulAut.conj g₀).toMonoidHom =
        (A.map (MulAut.conj (c * g₀ * c⁻¹)).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [hA₀def, map_conj_map_conj, map_conj_map_conj,
        show c⁻¹ * (c * g₀ * c⁻¹) = g₀ * c⁻¹ by group]
    rw [e, heq]
    exact hA₀def.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
