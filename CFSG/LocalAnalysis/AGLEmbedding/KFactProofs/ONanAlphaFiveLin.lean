module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveTorus
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.AGLEmbedding.KFactProofs.AlphaFive

open CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups

section Linear

variable {F : Type} [Field F] {n : ℕ}

theorem mem_statedSL_iff {A : GL (Fin n) F} :
    A ∈ StatedSL n F ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem det_sw {a c : Fin n} (hac : a ≠ c) :
    ((sw F a c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  unfold sw
  rw [Units.val_mul, Matrix.det_mul, det_permGL, Equiv.Perm.sign_swap hac, det_diagHom,
    ← Units.coe_prod, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

theorem transvection_mul_diagonal_comm {i j : Fin n} (c : F) (d : Fin n → F)
    (hd : d i = d j) :
    Matrix.transvection i j c * Matrix.diagonal d =
      Matrix.diagonal d * Matrix.transvection i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab, hd, mul_comm]
    · simp [hab, h]

theorem exists_three_outside (hn : 5 ≤ n) (i j : Fin n) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧ c ≠ i ∧ c ≠ j := by
  have h : 2 < ((Finset.univ : Finset (Fin n)) \ {i, j}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at ha hb hc
  exact ⟨a, b, c, hab, hac, hbc, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2⟩

theorem torusHyp_statedSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = p)
    (hn : 4 ≤ n) : TorusHyp (StatedSL n F) p ζ where
  prime := hp
  ne_two := hp2
  orderOf_eq := hζ
  four_le := hn
  diag_mem d hd _ := by
    rw [mem_statedSL_iff, det_diagHom, ← Units.coe_prod, hd, Units.val_one]
  sw_mem a c hac := by
    rw [mem_statedSL_iff]
    exact det_sw hac

theorem statedSL_le_closure (hn : 5 ≤ n) (ζ : Fˣ) :
    StatedSL n F ≤ Subgroup.closure {A : GL (Fin n) F | A ∈ StatedSL n F ∧ ∃ a b c : Fin n,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Commute A (diagHom n (dlt ζ a c)) ∧
        Commute A (diagHom n (dlt ζ b c))} := by
  intro A hA
  rw [statedSL_eq_range_toGL] at hA
  obtain ⟨B, rfl⟩ := hA
  have hB : B ∈ Subgroup.closure (elementarySet n F) := by
    rw [special_linear_elementary_generation]
    exact Subgroup.mem_top B
  have hle : (Subgroup.closure (elementarySet n F)).map Matrix.SpecialLinearGroup.toGL ≤
      Subgroup.closure {A : GL (Fin n) F | A ∈ StatedSL n F ∧ ∃ a b c : Fin n,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Commute A (diagHom n (dlt ζ a c)) ∧
          Commute A (diagHom n (dlt ζ b c))} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨T, ⟨i, j, hij, c, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [statedSL_eq_range_toGL]
      exact ⟨_, rfl⟩
    · obtain ⟨a, b, c', hab, hac, hbc, hai, haj, hbi, hbj, hci, hcj⟩ :=
        exists_three_outside hn i j
      refine ⟨a, b, c', hab, hac, hbc, ?_, ?_⟩
      · refine Units.ext ?_
        change Matrix.transvection i j c * Matrix.diagonal (fun k => (dlt ζ a c' k : F)) =
          Matrix.diagonal (fun k => (dlt ζ a c' k : F)) * Matrix.transvection i j c
        refine transvection_mul_diagonal_comm c _ ?_
        rw [dlt_apply_other ζ (Ne.symm hai) (Ne.symm hci), dlt_apply_other ζ (Ne.symm haj)
          (Ne.symm hcj)]
      · refine Units.ext ?_
        change Matrix.transvection i j c * Matrix.diagonal (fun k => (dlt ζ b c' k : F)) =
          Matrix.diagonal (fun k => (dlt ζ b c' k : F)) * Matrix.transvection i j c
        refine transvection_mul_diagonal_comm c _ ?_
        rw [dlt_apply_other ζ (Ne.symm hbi) (Ne.symm hci), dlt_apply_other ζ (Ne.symm hbj)
          (Ne.symm hcj)]
  exact hle ⟨B, hB, rfl⟩

theorem glbCore_eq_top_of_statedSL [Finite F] {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (hpF : p ∣ Nat.card F - 1) (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL n F))
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (T : Sylow p K) :
    Open.GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hpF
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hcard
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  let φ : K →* StatedProj (StatedSL n F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact glbCore_eq_top_of_torus (torusHyp_statedSL hp hp2 hζ (by omega)) hφ hker.le hperf
    (by rw [hker]; exact z.2) hz1 hzp (statedSL_le_closure hn ζ) T

end Linear

end CFSG.AGLEmbedding.KFactProofs.AlphaFive
