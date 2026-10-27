module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Reduction
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem pPrimeCore_eq_bot_of_doubleCover {K : Type} [Group K] [Finite K] {n : ℕ}
    (h : IsDoubleCoverOfAlt K n) : pPrimeCore 2 K = ⊥ := by
  obtain ⟨hq, hc, -⟩ := h
  have hn : (pPrimeCore 2 K).Normal := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
  have hodd : Odd (Nat.card (pPrimeCore 2 K)) := Nat.coprime_two_left.mp hcop
  rcases LocalCores.quasisimple_normal_subgroups hq hn with h1 | h1
  · exfalso
    have h2 : 2 ∣ Nat.card K := by
      have := Subgroup.card_subgroup_dvd_card (center K)
      rwa [hc] at this
    have h3 : Nat.card (pPrimeCore 2 K) = Nat.card K := by
      rw [h1]; exact Subgroup.card_top
    rw [h3] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · have h2 : Nat.card (pPrimeCore 2 K) ∣ 2 := by
      have := Subgroup.card_dvd_of_le h1
      rwa [hc] at this
    have h3 : Nat.card (pPrimeCore 2 K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact Subgroup.card_eq_one.mp h3

theorem alternatingGroup_not_comm {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩, ?_⟩,
    ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨3, by omega⟩, ?_⟩, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg (fun p : alternatingGroup (Fin n) =>
      (p : Equiv.Perm (Fin n)) ⟨2, by omega⟩) h
    simp [Equiv.swap_apply_def] at h2

theorem self_mem_centralizer {G : Type*} [Group G] (t : G) : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem isDoubleCoverOfAlt_of_cover {G : Type} [Group G] {t : G} (ht : orderOf t = 2) {n : ℕ}
    (hn : 5 ≤ n) (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hZ : center ↥(centralizer ({t} : Set G)) =
      zpowers (⟨t, self_mem_centralizer t⟩ : ↥(centralizer ({t} : Set G))))
    (hq : Nonempty (↥(centralizer ({t} : Set G)) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ : ↥(centralizer ({t} : Set G))) ≃*
        alternatingGroup (Fin n))) :
    IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) n := by
  obtain ⟨e₀⟩ := hq
  have e : ↥(centralizer ({t} : Set G)) ⧸ center ↥(centralizer ({t} : Set G)) ≃*
      alternatingGroup (Fin n) := (QuotientGroup.quotientMulEquivOfEq hZ).trans e₀
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  refine ⟨⟨hperf, e.isSimpleGroup, ?_⟩, ?_⟩
  · obtain ⟨a, b, hab⟩ := alternatingGroup_not_comm (by omega : 4 ≤ n)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · refine ⟨?_, ⟨e⟩⟩
    rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk]
    exact ht

theorem localStructure_of_solomon2AnInput
    (h : ComponentClassification.GSThmB.Solomon2AnInput) : Solomon75LocalStructure := by
  intro G _ _ _ z hz L n hn hLC hLpc hzL hperf hcard hquot
  have hcov : ∃ m : ℕ, 8 ≤ m ∧ m ≤ 11 ∧ IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) m := by
    rcases h G z hz L n hn hLC hLpc hzL hperf hcard hquot with he | he
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
          he hz
      exact ⟨8, le_rfl, by norm_num, isDoubleCoverOfAlt_of_cover hz (by norm_num) h1 h2 h3⟩
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple he z hz
      exact ⟨11, by norm_num, le_rfl, ⟨h1, h2, h3⟩⟩
  obtain ⟨m, hm8, hm11, hcm⟩ := hcov
  refine ⟨m, hm8, hm11, ?_⟩
  have hbot := pPrimeCore_eq_bot_of_doubleCover hcm
  let e : ↥(centralizer ({z} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set G)) ≃*
      ↥(centralizer ({z} : Set G)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e.symm hcm

end CFSG.OddStandard.Solomon75
