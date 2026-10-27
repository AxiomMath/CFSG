module

public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.CGT.PushingUpLit.A78.BenderTIBasic

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Open Subgroup
open scoped MatrixGroups

theorem exists_psl2_of_abelian_sylow {Y : Type} [Group Y] [Finite Y]
    (hY : fusionIsBenderGroup Y) (Q : Sylow 2 Y)
    (hab : ∀ x ∈ (Q : Subgroup Y), ∀ y ∈ (Q : Subgroup Y), x * y = y * x) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (Q : Subgroup Y) = 2 ^ n ∧
      Nonempty (Y ≃* PSL(2, GaloisField 2 n)) := by
  have key : ∀ q k : ℕ, fusionBenderBorel Y q k →
      Nat.card (Q : Subgroup Y) = q ^ k ∧ q = q ^ k := by
    intro q k hB
    obtain ⟨-, -, -, hZ, hQ⟩ := hB Q
    have htop : Subgroup.center (Q : Subgroup Y) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hab g g.2 z z.2)
    have hcard := Subgroup.card_top (G := (Q : Subgroup Y))
    rw [← htop, hZ, hQ] at hcard
    exact ⟨hQ, hcard⟩
  rcases hY with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv Y e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm
    obtain ⟨hQ, -⟩ := key _ _ hB
    exact ⟨f, hf, by simpa using hQ, ⟨e⟩⟩
  · exfalso
    have : Finite (PSU3 2 f) := Finite.of_equiv Y e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
      f hf).map_mulEquiv e.symm
    obtain ⟨-, h⟩ := key _ _ hB
    rw [← pow_mul] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  · exfalso
    have : Finite (Sz a) := Finite.of_equiv Y e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
      a ha).map_mulEquiv e.symm
    obtain ⟨-, h⟩ := key _ _ hB
    rw [← pow_mul] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega

theorem exists_odd_normal_series {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) {e : ℕ} (he : 2 ≤ e)
    (hexp : ∀ x ∈ (S : Subgroup X), x * x = 1)
    (hab : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x)
    (hcard : Nat.card (S : Subgroup X) = 2 ^ e)
    (hSE : fusionStronglyEmbedded (normalizer ((S : Subgroup X) : Set X))) :
    ∃ M N : Subgroup X, M.Normal ∧ N.Normal ∧ M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧
      Nat.card N = Nat.card M * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 X _
    hSE with hS | ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hB⟩
  · exfalso
    rcases hS S with hcyc | ⟨r, hr, ⟨φ⟩⟩
    · obtain ⟨c, hc⟩ := hcyc.exists_generator
      have h1 : orderOf c = Nat.card (S : Subgroup X) := orderOf_eq_card_of_forall_mem_zpowers hc
      have h2 : orderOf c ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hexp c c.2))
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have hn : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
      set x : (S : Subgroup X) := φ.symm (QuaternionGroup.a 1) with hx
      have h1 : orderOf x = 2 * 2 ^ (r - 2) := by
        rw [hx, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
      have h2 : orderOf x ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hexp x x.2))
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h5 : 2 ≤ 2 ^ (r - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  ·
    have hSN : (S : Subgroup X) ≤ N := fun x hx =>
      mem_of_two_pow_of_odd_index N hNodd ⟨1, by simpa [pow_two] using hexp x hx⟩
    set M' : Subgroup N := M.subgroupOf N with hM'
    have hMcard : Nat.card M' = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
    have he' : (Nat.card X).factorization 2 = e := by
      have h := S.card_eq_multiplicity
      rw [hcard] at h
      exact (Nat.pow_right_injective (le_refl 2) h).symm
    have hNfac : (Nat.card N).factorization 2 = e := by
      have h1 := Subgroup.card_mul_index N
      have h2 : N.index ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero (by
        obtain ⟨k, hk⟩ := hNodd
        omega))
      have h3 : (Nat.card X).factorization 2 =
          (Nat.card N).factorization 2 + N.index.factorization 2 := by
        rw [← h1, Nat.factorization_mul Nat.card_pos.ne' h2]
        rfl
      have h4 : N.index.factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by
          obtain ⟨k, hk⟩ := hNodd
          omega)
      omega
    set Z' : Subgroup N := (S : Subgroup X).subgroupOf N with hZ'
    have hZ'card : Nat.card Z' = 2 ^ (Nat.card N).factorization 2 := by
      rw [hNfac, ← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    let SN : Sylow 2 N := Sylow.ofCard Z' hZ'card
    have hSNc : (SN : Subgroup N) = Z' := rfl
    let Y := N ⧸ M'
    have hsurj : Function.Surjective (QuotientGroup.mk' M') := QuotientGroup.mk'_surjective M'
    let Q : Sylow 2 Y := SN.mapSurjective hsurj
    have hQc : (Q : Subgroup Y) = Z'.map (QuotientGroup.mk' M') := rfl
    have hab' : ∀ x ∈ (Q : Subgroup Y), ∀ y ∈ (Q : Subgroup Y), x * y = y * x := by
      rw [hQc]
      rintro _ ⟨z1, hz1, rfl⟩ _ ⟨z2, hz2, rfl⟩
      have : z1 * z2 = z2 * z1 := Subtype.ext (hab _ hz1 _ hz2)
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
    obtain ⟨n, hn2, hQcard, ⟨φ⟩⟩ := exists_psl2_of_abelian_sylow hB Q hab'
    have hYfac : (Nat.card Y).factorization 2 = e := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M'
      have h2 : Nat.card M' ≠ 0 := Nat.card_pos.ne'
      have h3 : (Nat.card N).factorization 2 =
          (Nat.card Y).factorization 2 + (Nat.card M').factorization 2 := by
        rw [h1, Nat.factorization_mul Nat.card_pos.ne' h2]
        rfl
      have h4 : (Nat.card M').factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by
          rw [hMcard]
          obtain ⟨k, hk⟩ := hModd
          omega)
      omega
    have hne : n = e := by
      have h := Q.card_eq_multiplicity
      rw [hQcard, hYfac] at h
      exact Nat.pow_right_injective (le_refl 2) h
    subst hne
    have hYcard : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      (Nat.card_congr φ.toEquiv).trans
        (Nat.card_congr (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 n)).toEquiv)
    refine ⟨M, N, hMn, hNn, hMN, hModd, hNodd, ?_⟩
    rw [← hYcard, ← hMcard, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup M'

end CFSG.CGT.PushingUpLit.A78
