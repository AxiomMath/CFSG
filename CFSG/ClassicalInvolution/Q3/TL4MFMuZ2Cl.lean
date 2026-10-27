module

public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Ord
public import CFSG.GH74.Generic.Context
public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem center_fstar_eq_bot [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) :
    Subgroup.center ↥(genFittingFStar X) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar X)) with
    h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab

omit [Finite X] in
theorem nonempty_fstar_equiv (hZ : Subgroup.center ↥(genFittingFStar X) = ⊥) :
    Nonempty (↥(genFittingFStar X) ≃* TL4.FStarQuot X) :=
  ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)⟩

omit [Finite X] in
theorem card_fstarQuot_dvd : Nat.card (TL4.FStarQuot X) ∣ Nat.card X :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)

theorem eq_top_of_sixteen_dvd {R : Subgroup X} {S : Sylow 2 R} {z : X} (hd : TightDatum R S z)
    (hgen : TightSelfGen R) (h32 : ¬ 32 ∣ Nat.card X)
    (h16 : 16 ∣ Nat.card (TL4.FStarQuot X)) : genFittingFStar X = ⊤ := by
  have hn : (genFittingFStar X).Normal := genFittingFStar_normal X
  have h16F : 16 ∣ Nat.card ↥(genFittingFStar X) := h16.trans (Subgroup.card_quotient_dvd_card _)
  have hodd : ¬ 2 ∣ (genFittingFStar X).index := fun h2 => h32 (by
    have := Nat.mul_dvd_mul h16F h2
    rwa [(genFittingFStar X).card_mul_index] at this)
  refine TA3.TightDatum.eq_top_of_normal_le hd hgen hn fun s hs => ?_
  have hS2 : IsPGroup 2 ((S : Subgroup R).map R.subtype) := S.isPGroup'.map R.subtype
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsk)
  have hcop : (genFittingFStar X).index.Coprime (orderOf s) := by
    rw [hj]
    exact Nat.Coprime.pow_right j
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ s) m

omit [Finite X] in
theorem lieModel_of_mulEquiv_classical {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (h : LieModel Z t n p f) : LieModel Y t n p f := by
  rcases h with ⟨htc, hadm, hm⟩ | ⟨-, htc, -⟩ | ⟨-, htc, -⟩ | ⟨-, htc, -⟩
  · refine Or.inl ⟨htc, hadm, ?_⟩
    rcases ht with rfl | rfl
    · obtain ⟨K, hK, hKf, hc, ⟨e'⟩⟩ := hm
      exact ⟨K, hK, hKf, hc, ⟨e.trans e'⟩⟩
    · obtain ⟨K, hK, hKf, hc, ⟨e'⟩⟩ := hm
      exact ⟨K, hK, hKf, hc, ⟨e.trans e'⟩⟩
  all_goals rcases ht with rfl | rfl <;> exact absurd htc (by decide)

omit [Finite X] in
theorem simple_and_model_of_eq_top [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) (htop : genFittingFStar X = ⊤)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (hL : LieModel (TL4.FStarQuot X) t n p f) : IsSimpleGroup X ∧ LieModel X t n p f := by
  obtain ⟨eF⟩ := nonempty_fstar_equiv (center_fstar_eq_bot hnab)
  let eX : X ≃* ↥(genFittingFStar X) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm
  exact ⟨eX.isSimpleGroup, lieModel_of_mulEquiv_classical (eX.trans eF) ht hL⟩

variable {R : Subgroup X} {S : Sylow 2 R} {z : X}

theorem u3_clause (hm : TL4.EdgelessMember3 R S z) [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) (h32 : ¬ 32 ∣ Nat.card X) {p f : ℕ}
    (hL : LieModel (TL4.FStarQuot X) .PSU 3 p f) :
    IsSimpleGroup X ∧ LieModel X .PSU 3 p f ∧ p ^ f % 4 = 1 := by
  have hadm := (CFSG.GH74.Generic.stated_of_lieModel_PSU hL).1
  obtain ⟨hp, hf, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have hc : Nat.card (TL4.FStarQuot X) = Nat.card (Assembly.LowTwoRank.StatedProj
      (Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) :=
    Nat.card_congr e.toEquiv
  have hdvd := card_fstarQuot_dvd (X := X)
  by_cases hp2 : p = 2
  · subst hp2
    exfalso
    have hf2 : 2 ≤ f := by
      obtain ⟨-, -, -, hne⟩ := hadm
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact hne rfl
    exact h32 ((hc ▸ thirtyTwo_dvd_psu3_of_two hf2 hK).trans hdvd)
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h1 | h3
  · have htop := eq_top_of_sixteen_dvd hm.datum hm.cls.2.1 h32
      (hc ▸ sixteen_dvd_psu3_of_one hp hf hK h1)
    obtain ⟨hs, hl⟩ := simple_and_model_of_eq_top hnab htop (Or.inr rfl) hL
    exact ⟨hs, hl, h1⟩
  · exact (h32 ((hc ▸ thirtyTwo_dvd_psu3_of_three hp hf hK h3).trans hdvd)).elim

theorem l3_clause_odd (hm : TL4.EdgelessMember3 R S z) [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) (h32 : ¬ 32 ∣ Nat.card X) {p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (TL4.FStarQuot X) .PSL 3 p f) :
    IsSimpleGroup X ∧ LieModel X .PSL 3 p f := by
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  have hc : Nat.card (TL4.FStarQuot X) = Nat.card (Assembly.LowTwoRank.StatedProj
      (Assembly.LowTwoRank.StatedSL 3 K)) :=
    Nat.card_congr e.toEquiv
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h1 | h3
  · have h := thirtyTwo_dvd_psl3_of_one (K := K) (by rw [hK]; exact h1)
    exact (h32 ((hc ▸ h).trans card_fstarQuot_dvd)).elim
  · have h := sixteen_dvd_psl3_of_three (K := K) (by rw [hK]; exact h3)
    exact simple_and_model_of_eq_top hnab (eq_top_of_sixteen_dvd hm.datum hm.cls.2.1 h32
      (hc ▸ h)) (Or.inl rfl) hL

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2
