module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Plane
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ3 CFSG.HardMathSupport.Malle.LocalAction

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem exists_conj_plane (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Plane5 K a)
    (F : Subgroup (ReeTag.F4.reeGamma K a)) (hFp : ∀ x ∈ F, x ^ 5 = 1) (hFc : Nat.card F = 5 ^ 2) :
    ∃ γ : ReeTag.F4.reeGamma K a, F = cj P.Ψ.range γ := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e, hsh⟩ : ∃ e, SylowShape 5 2 e (ReeTag.F4.reeGamma K a) :=
    ⟨_, sylowShape_ree_phi4 (K := K) (a := a) hK Nat.prime_five (by norm_num) (five_dvd_phi4 a)⟩
  have hE'p : ∀ x ∈ P.Ψ.range, x ^ 5 = 1 := pow_five_range_plane5 P
  have hE'c : Nat.card P.Ψ.range = 5 ^ 2 := card_range_plane5 P
  have hE'pg : IsPGroup 5 ↥P.Ψ.range := IsPGroup.of_card hE'c
  obtain ⟨S, hS⟩ := hE'pg.exists_le_sylow
  have h1 : IsPGroup 5 ↥(S : Subgroup (ReeTag.F4.reeGamma K a)) := S.isPGroup'
  have h2 : ¬ 5 ∣ (S : Subgroup (ReeTag.F4.reeGamma K a)).index := S.not_dvd_index
  obtain ⟨φ⟩ := hsh (S : Subgroup (ReeTag.F4.reeGamma K a)) h1 h2
  have hFpg : IsPGroup 5 ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (ReeTag.F4.reeGamma K a) S Q
  have hQS : (Q : Subgroup (ReeTag.F4.reeGamma K a)) =
      cj (S : Subgroup (ReeTag.F4.reeGamma K a)) c := by
    have h1 : ((c • S : Sylow 5 (ReeTag.F4.reeGamma K a)) : Subgroup (ReeTag.F4.reeGamma K a)) =
        (Q : Subgroup (ReeTag.F4.reeGamma K a)) := by rw [hc]
    rw [← h1, Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ (S : Subgroup (ReeTag.F4.reeGamma K a)) := by
    intro x hx
    have h1 : x ∈ cj (cj (S : Subgroup (ReeTag.F4.reeGamma K a)) c) c⁻¹ :=
      cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = P.Ψ.range :=
    plane_unique Nat.prime_five φ hFS hS (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  exact ⟨c, by rw [← hF', cj_inv_cj]⟩

end Conj

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
