module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.BorelTits

namespace Sp

variable {r : ℕ} {K : Type} [Field K]

theorem flag_one_eq (hr : 1 ≤ r) :
    SymplecticFlag.flag r K 1 = K ∙ (Pi.single (Sum.inl ⟨0, hr⟩) 1 : Fin r ⊕ Fin r → K) := by
  have hset : {j : Fin r | (j : ℕ) < 1} = {⟨0, hr⟩} := by
    ext j
    simp [Fin.ext_iff]
  rw [SymplecticFlag.flag, ite_eq_left hr, SymplecticFlag.isoFlag, hset, Set.image_singleton]

theorem single_inl_ne_zero (j : Fin r) :
    (Pi.single (Sum.inl j) 1 : Fin r ⊕ Fin r → K) ≠ 0 := fun h => by
  have := congrFun h (Sum.inl j)
  simp at this

theorem spForm_β_eq (u v : Fin r ⊕ Fin r → K) :
    (spForm r K).β u v = pairedSympForm K r u v :=
  (Matrix.toBilin'_apply' _ u v).symm

theorem perp_flag_self :
    (spForm r K).perp (SymplecticFlag.flag r K r) = SymplecticFlag.flag r K r := by
  ext v
  rw [SymplecticFlag.mem_flag_of_le le_rfl, SymplecticFlag.mem_isoFlag]
  have : v ∈ (spForm r K).perp (SymplecticFlag.flag r K r) ↔
      v ∈ (pairedSympForm K r).orthogonal (SymplecticFlag.isoFlag r K r) := by
    rw [ReflForm.mem_perp, LinearMap.BilinForm.mem_orthogonal_iff, SymplecticFlag.flag,
      ite_eq_left le_rfl]
    simp only [spForm_β_eq]
  rw [this, SymplecticFlag.mem_orthogonal_isoFlag]
  constructor
  · intro h
    exact ⟨fun j => h j j.2, fun j hj => absurd j.2 (not_lt.2 hj)⟩
  · rintro ⟨h1, -⟩ j _
    exact h1 j

theorem flag_self_ne_bot (hr : 1 ≤ r) : SymplecticFlag.flag r K r ≠ ⊥ := by
  intro h
  have hmem : (Pi.single (Sum.inl ⟨0, hr⟩) 1 : Fin r ⊕ Fin r → K) ∈
      SymplecticFlag.flag r K r := by
    rw [SymplecticFlag.mem_flag_of_le le_rfl, SymplecticFlag.mem_isoFlag]
    exact ⟨fun j => by simp, fun j hj => absurd j.2 (not_lt.2 hj)⟩
  rw [h] at hmem
  exact single_inl_ne_zero _ (Submodule.mem_bot K |>.1 hmem)

theorem charTwo_projStabilizer_flag_one [Finite K] [CharP K 2] (hr : 1 ≤ r) :
    CharTwo (SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 1)) := by
  rw [flag_one_eq hr]
  exact charTwo_projStabilizer_point (single_inl_ne_zero _)

theorem charTwo_projStabilizer_flag_self [Finite K] [CharP K 2] (hr : 1 ≤ r) :
    CharTwo (SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K r)) :=
  charTwo_projStabilizer_lagrangian perp_flag_self (flag_self_ne_bot hr)

end Sp

theorem sp4_sylowFacts {S : Type} [Group S] [Finite S] {f : ℕ} (_hf : 2 ≤ f)
    (hX : StatedClassicalModel S .PSp 2 2 f) {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) :
    SylowFacts S T := by
  have hS : IsSimpleGroup S :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp S 2 2 f hX
  obtain ⟨K, hF, hFin, hCh, φ, -, -, hRes, -⟩ := Setup.X7a.even_rank_two_residual_symplectic hX hT
  have hchar : ∀ j : Fin 2, CharTwo
      ((SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K ((j : ℕ) + 1))).map
        φ.symm.toMonoidHom) := by
    intro j
    refine CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv φ.symm ?_
    fin_cases j
    · exact Sp.charTwo_projStabilizer_flag_one (by norm_num)
    · exact Sp.charTwo_projStabilizer_flag_self (by norm_num)
  have h2 : 2 ∣ Nat.card S := by
    have := Sp.two_dvd_card_statedProj (K := K) (r := 2) (Sp.single_inl_ne_zero ⟨0, by norm_num⟩)
    rwa [← Nat.card_congr φ.toEquiv] at this
  exact sylowFacts_of_residualAt hT (ne_bot_of_two_dvd hT h2) hRes hchar

end CFSG.QuasithinUnique.B113Lie
