module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank Matrix

theorem l3b_exists_piField_true {K : Type} [Field K] [Finite K] (h : Nat.card K % 3 = 1) :
    ∃ p f : ℕ, PiField true p f K ∧ ModThree true (p ^ f) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hn0⟩ := FiniteField.card K p
  have hn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  refine ⟨p, n, ⟨hpp, n.pos, ?_⟩, ?_⟩
  · rw [piCard, Bool.cond_true, hn]
  · rw [ModThree, Bool.cond_true]
    rw [hn] at h
    exact h

theorem l3b_exists_piField_false {K : Type} [Field K] [Finite K] {q : ℕ}
    (hcard : Nat.card K = q ^ 2) (hq : q % 3 = 2) :
    ∃ p f : ℕ, q = p ^ f ∧ PiField false p f K ∧ ModThree false (p ^ f) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hn0⟩ := FiniteField.card K p
  have hn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  have hqd : q ∣ p ^ (n : ℕ) := by
    rw [← hn, hcard]
    exact Dvd.intro_left q (sq q).symm
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hf
      omega
    · exact h0
  refine ⟨p, f, hf, ⟨hpp, hf1, ?_⟩, ?_⟩
  · rw [piCard, Bool.cond_false, ← hf, hcard]
  · rw [ModThree, Bool.cond_false, ← hf]
    exact hq

@[expose] noncomputable def l3bProjHom {K : Type} [Field K] (L : Subgroup (GL (Fin 3) K)) :
    StatedProj L →* ProjGenLinGroup (Fin 3) K :=
  QuotientGroup.lift _ ((ProjGenLinGroup.mk : GL (Fin 3) K →* _).comp L.subtype) (by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      mk_eq_one_iff_mem_statedScalars]
    exact ha)

theorem l3bProjHom_mk {K : Type} [Field K] (L : Subgroup (GL (Fin 3) K)) (a : ↥L) :
    l3bProjHom L (QuotientGroup.mk a) = ProjGenLinGroup.mk (a : GL (Fin 3) K) := rfl

theorem l3bProjHom_injective {K : Type} [Field K] (L : Subgroup (GL (Fin 3) K)) :
    Function.Injective (l3bProjHom L) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [l3bProjHom_mk, mk_eq_one_iff_mem_statedScalars] at ha
    exact (QuotientGroup.eq_one_iff a).2 ha

end CFSG.HardMathSupport.Solomon.Coordinator
