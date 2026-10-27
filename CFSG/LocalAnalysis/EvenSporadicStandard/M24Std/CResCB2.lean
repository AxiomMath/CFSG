module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResCB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSqInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResZMod

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem exists_decomp_centralizer (h : Setup L A C z) {y : egQD C}
    (hy : y ∈ centralizer ({zt h} : Set (egQD C))) :
    ∃ n : egNL L A, y = psi h n ∨ y = psi h n * zt h := by
  rw [centralizer_quot_eq h] at hy
  have hle : zpowers (zt h) ≤ centralizer ((psi h).range : Set (egQD C)) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => by
      obtain ⟨n, rfl⟩ := hy
      exact psi_comm h n
  obtain ⟨a, ⟨n, rfl⟩, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hy
  refine ⟨n, ?_⟩
  rcases mem_zpowers_zt h hb with rfl | rfl
  · exact Or.inl (by rw [hab, mul_one])
  · exact Or.inr hab

theorem card_fixSub_z_le (h : Setup L A C z) : Nat.card (fixSub C z) ≤ 64 := by
  have hmem : ∀ c : fixSub C z, ((c : C) : G) ∈ A := fun c => by
    refine mem_A_of_comm h (c : C).2 ?_
    have : z * ((c : C) : G) * z⁻¹ = (c : C) := c.2
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  calc Nat.card (fixSub C z)
      ≤ Nat.card A := Nat.card_le_card_of_injective
        (fun c => (⟨((c : C) : G), hmem c⟩ : A))
        (fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab)))
    _ = 64 := h.hF.card_A

theorem card_fixSub_le_of_involution
    (h : Setup L A C z) (hty : SextetType L A) {H : Subgroup (egNL L A)} (hH : H.index = 2)
    {d : G} (hd : d ∈ normalizer (C : Set G)) (n : egNL L A)
    (hdn : qdMk C ⟨d, hd⟩ = psi h n ∨ qdMk C ⟨d, hd⟩ = psi h n * zt h)
    (hd2 : qdMk C ⟨d, hd⟩ * qdMk C ⟨d, hd⟩ = 1) (hd1 : qdMk C ⟨d, hd⟩ ≠ 1) :
    Nat.card (fixSub C d) ≤ 256 ∧ (n ∉ H → Nat.card (fixSub C d) ≤ 64) := by
  have hCab := h.hC.comm
  have hnN : (n : G) ∈ normalizer (C : Set G) := egNL_le_normalizer_C h n.2
  have hzN : z ∈ normalizer (C : Set G) := z_mem_normalizer_C h
  have hzt : qdMk C ⟨z, hzN⟩ = zt h := rfl
  have hψn : qdMk C ⟨(n : G), hnN⟩ = psi h n := rfl
  have hn2 : (n : G) * n ∈ A := by
    have hψ2 : psi h n * psi h n = 1 := by
      rcases hdn with h1 | h1
      · rw [h1] at hd2
        exact hd2
      · rw [h1] at hd2
        have hc : psi h n * zt h = zt h * psi h n := psi_comm h n
        calc psi h n * psi h n = psi h n * psi h n * (zt h * zt h) := by rw [zt_mul_self h, mul_one]
          _ = (psi h n * zt h) * (psi h n * zt h) := by
            calc psi h n * psi h n * (zt h * zt h)
                = psi h n * (psi h n * zt h) * zt h := by group
              _ = psi h n * (zt h * psi h n) * zt h := by rw [hc]
              _ = (psi h n * zt h) * (psi h n * zt h) := by group
          _ = 1 := hd2
    have : n * n ∈ (psi h).ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hψ2
    rw [ker_psi h] at this
    exact mem_subgroupOf.1 this
  by_cases hnA : (n : G) ∈ A
  ·
    have hψ1 : psi h n = 1 := by
      rw [← MonoidHom.mem_ker, ker_psi h]
      exact mem_subgroupOf.2 hnA
    have hdz : qdMk C ⟨d, hd⟩ = qdMk C ⟨z, hzN⟩ := by
      rcases hdn with h1 | h1
      · exact absurd (h1.trans hψ1) hd1
      · rw [h1, hψ1, one_mul, hzt]
    rw [fixSub_eq_of_qdMk_eq hCab hd hzN hdz]
    have hnH : n ∈ H := by
      obtain ⟨hAL, e, hA⟩ := hty
      rw [(Sym6.index_two_iff hA hAL H).1 hH, Subgroup.mem_comap,
        Equiv.Perm.mem_alternatingGroup]
      have := Sym6.le_ker_tetE hA (Subgroup.mem_subgroupOf.2 hnA)
      rw [MonoidHom.mem_ker] at this
      rw [this, map_one]
    exact ⟨(card_fixSub_z_le h).trans (by norm_num), fun hnH' => absurd hnH hnH'⟩
  · obtain ⟨h16, h8⟩ := card_fix_sq_mem_of_type hty H hH n hn2 hnA
    have hC' : Nat.card (fixSub C d) ≤ Nat.card (fixSub A (n : G)) ^ 2 := by
      rcases hdn with h1 | h1
      · rw [fixSub_eq_of_qdMk_eq hCab hd hnN (h1.trans hψn.symm)]
        exact card_fixSub_le h n.2
      · have hzn : qdMk C ⟨z * (n : G), mul_mem hzN hnN⟩ = psi h n * zt h := by
          show qdMk C (⟨z, hzN⟩ * ⟨(n : G), hnN⟩) = _
          rw [map_mul, hzt, hψn]
          exact (psi_comm h n).symm
        rw [fixSub_eq_of_qdMk_eq hCab hd (mul_mem hzN hnN) (h1.trans hzn.symm)]
        exact card_fixSub_zmul_le h n.2
    have hAe : Nat.card (fixSub A (n : G)) =
        Nat.card {a : A // (n : G) * a * (n : G)⁻¹ = a} := rfl
    refine ⟨?_, fun hnH => ?_⟩
    · have hA16 : Nat.card (fixSub A (n : G)) ≤ 16 := by
        rw [hAe]
        by_cases hnH : n ∈ H
        · exact (h16 hnH).le
        · exact ((h8 hnH).le).trans (by norm_num)
      calc Nat.card (fixSub C d) ≤ Nat.card (fixSub A (n : G)) ^ 2 := hC'
        _ ≤ 16 ^ 2 := Nat.pow_le_pow_left hA16 2
        _ = 256 := by norm_num
    · have h8' : Nat.card (fixSub A (n : G)) = 8 := by rw [hAe]; exact h8 hnH
      calc Nat.card (fixSub C d) ≤ Nat.card (fixSub A (n : G)) ^ 2 := hC'
        _ = 64 := by rw [h8']; norm_num

end CSide

end CFSG.EvenSporadicStandard.M24Std
