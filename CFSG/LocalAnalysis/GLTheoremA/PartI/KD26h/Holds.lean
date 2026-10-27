module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Linear
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Unitary
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.CoverLinear
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.CoverUnitary
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Decode

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Matrix


theorem kd26h_holds : KD26h := by
  intro K _ _ hK p hp hp2 q lin hS hpq hZ d hd hd1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  cases lin with
  | true =>
    obtain ⟨m, F, _, _, hmn, hFq, ⟨e0⟩⟩ := exists_psl_of_isLnEps hS
    subst hmn
    have hpF : (m + 1) ∣ Nat.card F - 1 := by
      have : qEps true q = q - 1 := by simp [qEps]
      rw [this, ← hFq] at hpq
      exact hpq
    have hm2 : 2 ≤ m := by omega
    have hF1 : 1 < Nat.card F := Finite.one_lt_card
    have hF4 : 4 ≤ Nat.card F := by
      have := Nat.le_of_dvd (by omega) hpF
      omega
    obtain ⟨φ, hφ⟩ : ∃ φ : SpecialLinearGroup (Fin (m + 1)) F ≃* K, ∀ g,
        e0 (QuotientGroup.mk (φ g)) =
          (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin (m + 1)) F) := by
      by_cases hex : m = 2 ∧ Nat.card F = 4
      · obtain ⟨rfl, h4⟩ := hex
        exact exists_mulEquiv_sl_of_cover_three_four hK h4 e0 hZ
      · exact exists_mulEquiv_sl_of_cover hK hm2 hp hpF hex e0 hZ
    obtain ⟨d, rfl⟩ := φ.surjective d
    have hdp : d ^ (m + 1) ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
      have h2 := hφ (d ^ (m + 1))
      rw [map_pow] at h2
      have h3 : (QuotientGroup.mk (φ d ^ (m + 1)) : K ⧸ Subgroup.center K) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hd
      rw [h3, map_one] at h2
      exact (QuotientGroup.eq_one_iff _).1 h2.symm
    obtain ⟨r, hr, hrd⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hdp
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    have hdc : (SpecialLinearGroup.toGL d) ^ (m + 1) =
        GeneralLinearGroup.scalar (Fin (m + 1)) (Units.mk0 r hr0) := by
      apply Units.ext
      have h1 := hrd
      simp only [Matrix.SpecialLinearGroup.coe_pow] at h1
      simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Units.val_mk0]
      exact h1.symm
    have hc1 : Units.mk0 r hr0 ≠ 1 := by
      intro h1
      apply hd1
      rw [← map_pow]
      have : d ^ (m + 1) = 1 := by
        apply SpecialLinearGroup.toGL_injective
        rw [map_pow, hdc, h1, map_one, map_one]
      rw [this, map_one]
    obtain ⟨L, hLC, hLq, hLn, hpL⟩ := exists_block_map φ
      (exists_block_linear hp hp2 hF4 hpF d _ hdc hc1)
    exact glaPLayer_ne_bot_of_block hp hLC hLq hLn hpL
  | false =>
    obtain ⟨m, ℓ, f, F, _, hU, hmn, hℓq, h3, ⟨e0⟩⟩ := exists_psu_of_isLnEps hS
    subst hmn
    subst hℓq
    have hpq' : (m + 1) ∣ ℓ ^ f + 1 := by
      have : qEps false (ℓ ^ f) = ℓ ^ f + 1 := by simp [qEps]
      rw [this] at hpq
      exact hpq
    have hm3 : m ≠ 3 := by
      rintro rfl
      norm_num at hp
    have hq4 : 4 ≤ ℓ ^ f := by
      have h1 := Nat.le_of_dvd (by omega) hpq'
      by_cases hm : m = 2
      · have := h3 hm
        subst hm
        omega
      · omega
    have hq : (m + 1, ℓ ^ f) ≠ (3, 2) := by
      intro h
      have := (Prod.mk.inj h).2
      omega
    obtain ⟨φ, hφ⟩ := exists_mulEquiv_su_of_cover hK hU hp hp2 hpq' hq e0 hZ
    obtain ⟨d, rfl⟩ := φ.surjective d
    have hmem : d ^ (m + 1) ∈
        (StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (ℓ ^ f) F) := by
      have h2 := hφ (d ^ (m + 1))
      rw [map_pow] at h2
      have h3' : (QuotientGroup.mk (φ d ^ (m + 1)) : K ⧸ Subgroup.center K) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hd
      rw [h3', map_one] at h2
      exact (QuotientGroup.eq_one_iff _).1 h2.symm
    obtain ⟨c, hc⟩ : ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin (m + 1)) c =
        ((d : GL (Fin (m + 1)) F)) ^ (m + 1) := by
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hmem
      exact ⟨c, by rw [hc]; simp⟩
    have hc1 : c ≠ 1 := by
      intro h1
      apply hd1
      rw [← map_pow]
      have : d ^ (m + 1) = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hc, h1, map_one, Subgroup.coe_one])
      rw [this, map_one]
    obtain ⟨L, hLC, hLq, hLn, hpL⟩ := exists_block_map φ
      (exists_block_unitary hU hp hp2 hpq' hq4 d c hc.symm hc1)
    exact glaPLayer_ne_bot_of_block hp hLC hLq hLn hpL

end CFSG.LocalAnalysis.GLTheoremA
