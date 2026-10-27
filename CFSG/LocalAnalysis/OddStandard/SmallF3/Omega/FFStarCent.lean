module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_toProj_signChange_compl (fr : NFrame Q (Fin 6) 1) (K : Finset (Fin 6)) :
    toProj Q (fr.signChange Kᶜ) = toProj Q (fr.signChange K) := by
  rw [show Kᶜ = symmDiff Finset.univ K by ext i; simp [Finset.mem_symmDiff],
    ← fr.signChange_mul, ← fr.piOrth_eq_signChange_univ, map_mul, toProj_piOrth, one_mul]

theorem ff_simHasType_signChange (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {K : Finset (Fin 6)} (hK : K.card = 1 ∨ K.card = 3) :
    ∃ α : ℤˣ, SimHasType (projOrthToProjSim Q (toProj Q (fr.signChange K))) K.card α := by
  refine ⟨invSign (fr.signChange K), simHasType_projOrthToProjSim ?_⟩
  simp only [HasType]
  refine ⟨?_, fr.signChange K, fr.signChange_mul_self K, ?_, rfl⟩
  · intro h1
    have hmem : fr.signChange K ∈ piGroup Q :=
      (QuotientGroup.eq_one_iff (fr.signChange K)).mp
        (by simpa only [QuotientGroup.mk'_apply] using h1)
    rcases mem_piGroup_iff.mp hmem with h | h
    · have hK0 : K = ∅ := fr.signChange_injective (h.trans fr.signChange_empty.symm)
      rw [hK0] at hK
      simp at hK
    · have hKu : K = Finset.univ := fr.signChange_injective (h.trans fr.piOrth_eq_signChange_univ)
      rw [hKu, Finset.card_univ, Fintype.card_fin] at hK
      omega
  · simp only [invType]
    exact Prod.ext (ffMono_invDim_signChange fr K) rfl

theorem ff_exists_mem_ffB1_signChange (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {K : Finset (Fin 6)} (hK : Even K.card) :
    ∃ b ∈ ffB1 hQ fr, (b : ProjOrth Q) = toProj Q (fr.signChange K) := by
  have hB0 : fr.signChange K ∈ ffB0 fr := signChange_mem_ffB0 fr hK
  have hΩ : fr.signChange K ∈ omegaGroup hQ := ffB0_le_omega hQ fr hB0
  refine ⟨omegaToProj hQ ⟨fr.signChange K, hΩ⟩, ?_, coe_omegaToProj hQ _⟩
  rw [ffB1]
  exact (mem_ffStar_iff hQ).mpr ⟨⟨fr.signChange K, hΩ⟩, hB0, rfl⟩

theorem ff_star_cent_kinds (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1)
    {z : ProjSim Q} (hz : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 z b = b) :
    (∃ b ∈ ffB1 hQ fr, z = projOrthToProjSim Q (b : ProjOrth Q)) ∨
      (∃ α : ℤˣ, SimHasType z 1 α) ∨ ∃ α : ℤˣ, SimHasType z 3 α := by
  obtain ⟨K, hK⟩ := ff_star_cent_sim hQ h2 fr hz
  rcases Nat.even_or_odd K.card with hKe | hKo
  · left
    obtain ⟨b, hb, hbe⟩ := ff_exists_mem_ffB1_signChange hQ fr hKe
    refine ⟨b, hb, ?_⟩
    rw [hK, hbe]
  · have hKle : K.card ≤ 6 := by simpa using Finset.card_le_univ K
    have hmem : K.card = 1 ∨ K.card = 3 ∨ K.card = 5 := by
      rcases hKo with ⟨m, hm⟩
      omega
    rcases hmem with h1 | h3 | h5
    · right; left
      obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := K) (Or.inl h1)
      rw [← hK, h1] at hα
      exact ⟨α, hα⟩
    · right; right
      obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := K) (Or.inr h3)
      rw [← hK, h3] at hα
      exact ⟨α, hα⟩
    · right; left
      have hKc : Kᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin]
        omega
      obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := Kᶜ) (Or.inl hKc)
      rw [ff_toProj_signChange_compl fr K, ← hK, hKc] at hα
      exact ⟨α, hα⟩

end CFSG.OddStandard.SmallF3.Omega
