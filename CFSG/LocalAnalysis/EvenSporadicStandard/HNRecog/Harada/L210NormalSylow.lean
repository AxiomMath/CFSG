module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210NormalCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

theorem L210_eq_of_burnside {M : Subgroup X} [M.Normal] (hAM : A ≤ M) (hAb : IsMulCommutative A)
    (S : Sylow 2 X) (hAS : A ≤ (S : Subgroup X)) (hSN : (S : Subgroup X) ≤ normalizer (A : Set X))
    (hMN : M ⊓ normalizer (A : Set X) = A)
    (hodd : ∀ P : Subgroup X, P.Normal → Odd (Nat.card P) → P = ⊥) : M = A := by
  have hSMA : (S : Subgroup X) ⊓ M = A := by
    apply le_antisymm
    · rw [← hMN]
      exact le_inf inf_le_right (inf_le_left.trans hSN)
    · exact le_inf hAS hAM
  have hA2 : IsPGroup 2 (A.subgroupOf M) :=
    (S.isPGroup'.to_le hAS).comap_subtype (K := M)
  have hrel : A.relIndex M = (S : Subgroup X).relIndex ((S : Subgroup X) ⊔ M) := by
    have h1 : M.relIndex ((S : Subgroup X) ⊔ M) = M.relIndex (S : Subgroup X) :=
      Subgroup.relIndex_sup_right (H := (S : Subgroup X)) (K := M)
    have h2 : M.relIndex (S : Subgroup X) = A.relIndex (S : Subgroup X) := by
      rw [← Subgroup.inf_relIndex_right (H := M) (K := (S : Subgroup X)), inf_comm, hSMA]
    have h3 : A.relIndex (S : Subgroup X) * (S : Subgroup X).relIndex ((S : Subgroup X) ⊔ M)
        = A.relIndex M * M.relIndex ((S : Subgroup X) ⊔ M) := by
      rw [Subgroup.relIndex_mul_relIndex (H := A) (K := (S : Subgroup X))
            (L := (S : Subgroup X) ⊔ M) hAS le_sup_left,
          Subgroup.relIndex_mul_relIndex (H := A) (K := M)
            (L := (S : Subgroup X) ⊔ M) hAM le_sup_right]
    rw [h1, h2] at h3
    have hpos : 0 < A.relIndex (S : Subgroup X) :=
      Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := A) (K := (S : Subgroup X)))
        Nat.card_pos
    rw [mul_comm (A.relIndex M) (A.relIndex (S : Subgroup X))] at h3
    exact (mul_left_cancel₀ hpos.ne' h3).symm
  have hoddidx : ¬ 2 ∣ A.relIndex M := by
    rw [hrel]
    intro h
    exact S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hAodd : ¬ 2 ∣ (A.subgroupOf M).index := hoddidx
  let P : Sylow 2 M := hA2.toSylow hAodd
  have hPcoe : (P : Subgroup M) = A.subgroupOf M := IsPGroup.toSylow_coe hA2 hAodd
  have hnorm_eq : Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) = A.subgroupOf M := by
    rw [← Subgroup.subgroupOf_normalizer_eq hAM]
    conv_rhs => rw [← hMN]
    rw [Subgroup.inf_subgroupOf_left]
  have hP : Subgroup.normalizer ((P : Subgroup M) : Set M) ≤
      Subgroup.centralizer ((P : Subgroup M) : Set M) := by
    have hnorm : Subgroup.normalizer ((P : Subgroup M) : Set M) = (P : Subgroup M) := by
      rw [hPcoe]
      exact hnorm_eq
    rw [hnorm]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (hPcoe.symm ▸ (inferInstance : IsMulCommutative (A.subgroupOf M)))
  haveI : Finite (Sylow 2 M) := Sylow.finite_of_finiteIndex P
  let K : Subgroup M := (MonoidHom.transferSylow P hP).ker
  have hcomp : IsComplement' K P := MonoidHom.ker_transferSylow_isComplement' P hP
  have hK_odd : Odd (Nat.card K) := by
    have hcard : Nat.card K = P.index := hcomp.index_eq_card.symm
    rw [hcard]
    exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact P.not_dvd_index)
  have hK_le : K ≤ goldschmidtOddCore (↥M) :=
    le_sSup ⟨inferInstance, hK_odd⟩
  have hcore : goldschmidtOddCore (↥M) = ⊥ :=
    goldschmidtOddCore_eq_bot_of_normal (M := M) hodd
  have hKbot : K = ⊥ := le_bot_iff.mp (hK_le.trans (le_of_eq hcore))
  have hPtop : (P : Subgroup M) = ⊤ := by
    rw [hKbot] at hcomp
    exact isComplement'_bot_left.mp hcomp
  have hAtop : A.subgroupOf M = ⊤ := hPcoe.symm.trans hPtop
  have hMA : M ≤ A := Subgroup.subgroupOf_eq_top.mp hAtop
  exact le_antisymm hMA hAM

theorem exists_conj_mem_sylow_of_le {N : Subgroup X} (S : Sylow 2 X) (hSN : (S : Subgroup X) ≤ N)
    {q : X} (hq : q ∈ N) (hq2 : q * q = 1) : ∃ n ∈ N, n * q * n⁻¹ ∈ (S : Subgroup X) := by
  let S' : Sylow 2 N := S.subtype hSN
  let qN : N := ⟨q, hq⟩
  have hqN2 : qN * qN = 1 := Subtype.ext (by simpa [qN] using hq2)
  have h2grp : IsPGroup 2 (Subgroup.zpowers qN) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hqN2)
  obtain ⟨T', hT'⟩ := h2grp.exists_le_sylow
  haveI : Finite (Sylow 2 N) := Sylow.finite_of_finiteIndex S'
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M := N) S' T'
  have hmq : m⁻¹ * qN * m ∈ (S' : Subgroup N) := by
    have hmem : qN ∈ ((m • S' : Sylow 2 N) : Subgroup N) := by
      rw [hm]
      exact hT' (Subgroup.mem_zpowers qN)
    rw [Sylow.coe_subgroup_smul] at hmem
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv] at hmem
    simpa [mul_assoc] using hmem
  refine ⟨(m⁻¹ : N), m⁻¹.2, ?_⟩
  have := Subgroup.mem_subgroupOf.mp hmq
  simpa using this

end CFSG.EvenSporadicStandard.HNRecog.Harada
