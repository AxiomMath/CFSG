module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {n : ℕ} {F : Type} [Field F]

theorem det_one_add_restrict_eq_one {x : Module.End F (Fin n → F)} {h : F[X]}
    [Fact (Irreducible h)]
    (N : Module.End (AdjoinRoot h) (primaryComponent x h)) (hNN : N * N = 0) :
    LinearMap.det (1 + N) = 1 := by
  refine det_one_add_of_range_le_ker (K := AdjoinRoot h) N (LinearMap.ker N) ?_ ?_
  · intro v
    rw [LinearMap.mem_ker]
    have := congrArg (fun g => g v) hNN
    simpa [Module.End.mul_apply] using this
  · intro w hw
    exact LinearMap.mem_ker.1 hw

theorem exists_mem_blockImage_of_commute {M : GL (Fin n) F} {x : Module.End F (Fin n → F)}
    (hax : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x) (hsq : Squarefree (minpoly F x))
    {β : Module.End F (Fin n → F)} (hβx : β * x = x * β) (hββ : β * β = 0)
    (h : primaryFactors x) :
    ∃ g ∈ blockImage hsq h, ∀ v, Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) v =
      v + (β * primaryProjection x (h : F[X])) v := by
  have hβc : Commute β x := hβx
  have hβP : Commute β (primaryProjection x (h : F[X])) := commute_aeval hβc _
  have hβ' : β * primaryProjection x (h : F[X]) ∈ commutant x := by
    rw [mem_commutant]
    exact hβc.mul_left (commute_aeval (Commute.refl x) _).symm
  have hββ' : (β * primaryProjection x (h : F[X])) * (β * primaryProjection x (h : F[X])) = 0 := by
    calc (β * primaryProjection x (h : F[X])) * (β * primaryProjection x (h : F[X]))
        = β * (primaryProjection x (h : F[X]) * β) * primaryProjection x (h : F[X]) := by
          simp only [mul_assoc]
      _ = β * (β * primaryProjection x (h : F[X])) * primaryProjection x (h : F[X]) := by
          rw [hβP.eq.symm]
      _ = (β * β) * (primaryProjection x (h : F[X]) * primaryProjection x (h : F[X])) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hββ, zero_mul]
  have hkill : ∀ k ∈ primaryFactors x, k ≠ (h : F[X]) → ∀ v ∈ primaryComponent x k,
      (β * primaryProjection x (h : F[X])) v = 0 := by
    intro k hk hkh v hv
    rw [Module.End.mul_apply, primaryProjection_of_mem_ne hsq h.2 hk hkh hv, map_zero]
  have hdet : LinearMap.det (1 + commutantRestrict (h : F[X])
      ⟨β * primaryProjection x (h : F[X]), hβ'⟩) = 1 := by
    refine det_one_add_restrict_eq_one _ ?_
    refine LinearMap.ext fun v => Subtype.ext ?_
    have := congrArg (fun g => g (v : Fin n → F)) hββ'
    simpa [Module.End.mul_apply] using this
  exact exists_mem_blockImage_one_add hsq hax h (β * primaryProjection x (h : F[X])) hβ' hββ'
    hkill hdet

theorem exists_mem_one_add_of_blocks {M : GL (Fin n) F} {x : Module.End F (Fin n → F)}
    (hax : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x) (hsq : Squarefree (minpoly F x))
    (𝒢 : Subgroup (SpecialLinearGroup (Fin n) F))
    (hblocks : ∀ h : primaryFactors x, blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL)
    {β : Module.End F (Fin n → F)} (hβx : β * x = x * β) (hββ : β * β = 0) :
    ∃ s ∈ 𝒢, ∀ v, Matrix.toLin' (s : Matrix (Fin n) (Fin n) F) v = v + β v := by
  classical
  have hβc : Commute β x := hβx
  have hstep : ∀ a ∈ primaryFactors x, ∃ s ∈ 𝒢, ∀ v,
      Matrix.toLin' (s : Matrix (Fin n) (Fin n) F) v = v + (β * primaryProjection x a) v := by
    intro a ha
    obtain ⟨g, hg, hgv⟩ := exists_mem_blockImage_of_commute hax hsq hβx hββ ⟨a, ha⟩
    obtain ⟨s, hs𝒢, hs⟩ := hblocks ⟨a, ha⟩ hg
    refine ⟨s, hs𝒢, fun v => ?_⟩
    have hsm : (s : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) :=
      congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) hs
    rw [hsm]
    exact hgv v
  have hind : ∀ S : Finset F[X], S ⊆ primaryFactors x → ∃ s ∈ 𝒢, ∀ v,
      Matrix.toLin' (s : Matrix (Fin n) (Fin n) F) v =
        v + (β * ∑ a ∈ S, primaryProjection x a) v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, 𝒢.one_mem, fun v => by simp⟩
    | insert a S haS ih =>
      intro hsub
      obtain ⟨s, hs𝒢, hsv⟩ := ih (fun b hb => hsub (Finset.mem_insert_of_mem hb))
      obtain ⟨s', hs'𝒢, hs'v⟩ := hstep a (hsub (Finset.mem_insert_self a S))
      refine ⟨s * s', 𝒢.mul_mem hs𝒢 hs'𝒢, fun v => ?_⟩
      have hcomm : ∀ b : F[X], Commute β (primaryProjection x b) := fun b =>
        commute_aeval hβc _
      have hcross : (β * ∑ b ∈ S, primaryProjection x b) * (β * primaryProjection x a) = 0 := by
        calc (β * ∑ b ∈ S, primaryProjection x b) * (β * primaryProjection x a)
            = ∑ b ∈ S, β * primaryProjection x b * β * primaryProjection x a := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun b _ => ?_
              simp only [mul_assoc]
          _ = 0 := by
              refine Finset.sum_eq_zero fun b hb => ?_
              have hba : b ≠ a := fun h => haS (h ▸ hb)
              have hbm : b ∈ primaryFactors x := hsub (Finset.mem_insert_of_mem hb)
              have hPP : primaryProjection x b * primaryProjection x a = 0 :=
                primaryProjection_mul_of_ne hsq hbm (hsub (Finset.mem_insert_self a S)) hba
              calc β * primaryProjection x b * β * primaryProjection x a
                  = β * (primaryProjection x b * β) * primaryProjection x a := by
                    simp only [mul_assoc]
                _ = β * (β * primaryProjection x b) * primaryProjection x a := by
                    rw [(hcomm b).eq.symm]
                _ = (β * β) * (primaryProjection x b * primaryProjection x a) := by
                    simp only [mul_assoc]
                _ = 0 := by rw [hPP, mul_zero]
      have h0 : (β * ∑ b ∈ S, primaryProjection x b) ((β * primaryProjection x a) v) = 0 := by
        have := congrArg (fun g => g v) hcross
        simpa [Module.End.mul_apply] using this
      have hmul : (↑(s * s') : Matrix (Fin n) (Fin n) F) =
          (s : Matrix (Fin n) (Fin n) F) * (s' : Matrix (Fin n) (Fin n) F) :=
        Matrix.SpecialLinearGroup.coe_mul s s'
      rw [hmul, Matrix.toLin'_mul, LinearMap.comp_apply, hs'v, map_add, hsv, hsv, h0,
        Finset.sum_insert haS, mul_add, LinearMap.add_apply]
      abel
  obtain ⟨s, hs𝒢, hsv⟩ := hind (primaryFactors x) (Finset.Subset.refl _)
  refine ⟨s, hs𝒢, fun v => ?_⟩
  rw [hsv, sum_primaryProjection hsq, mul_one]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
