module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

variable {Y : Type} [Group Y] [Finite Y]

theorem kConcl_of_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B) {n : ℕ}
    (hn : 5 ≤ n) (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))
    (hp3 : p = 3 → n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 9 ∧ n ≠ 10) : KConcl p K B := by
  classical
  rcases KD264Z.center_eq_bot_or_three hp hp2 h.qs h.core hn eK with hZ | ⟨hZ3, h67⟩
  · let e : K ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eK
    have hpn : p ≤ n := by
      by_contra hlt
      push Not at hlt
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hcardK : Nat.card K = n.factorial / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have hndvd : ¬ p ∣ Nat.card K := by
        rw [hcardK]
        intro hd
        have h2 : n.factorial / 2 ∣ n.factorial :=
          Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega))
        have hpf : p ∣ n.factorial := hd.trans h2
        exact absurd ((Nat.Prime.dvd_factorial hp).1 hpf) (by omega)
      haveI := isQuasisimple_nontrivial h.qs
      have htop : (⊤ : Subgroup K) ≤ GLAPPrimeCore p K :=
        le_sSup ⟨inferInstance, by
          rw [Subgroup.card_top]
          exact (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd⟩
      rw [h.core] at htop
      obtain ⟨x, hx⟩ := exists_ne (1 : K)
      exact hx (Subgroup.mem_bot.1 (htop (Subgroup.mem_top x)))
    obtain ⟨E, hEB, hEel, hEcard, hEl⟩ :=
      KD264Core.alt_core hp hp2 hn hpn K B h.normal e hZ h.elem h.card h.maxrank h.cent hp3
    exact ⟨E, hEB, hEel, hEcard, hEl⟩
  ·
    have h3 : p = 3 := by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, ha⟩ := (KD264Z.isPGroup_center_of_pPrimeCore hp h.core).exists_card_eq
      rw [hZ3] at ha
      have hpdvd : p ∣ 3 := by
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · rw [h0, pow_zero] at ha
          omega
        · rw [ha]
          exact dvd_pow_self p h0.ne'
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpdvd
    obtain ⟨h6, h7, -, -⟩ := hp3 h3
    omega

theorem kDescFam_alt5 (p : ℕ) : KDescFam p fAlt5 := by
  intro hp hp2 Y _ _ K B h hc _
  obtain ⟨i, hi, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    change n = 5 at hi
    subst hi
    exact Or.inl (kConcl_of_alt hp hp2 h hn eK fun _ => by omega)

theorem kDescFam_alt8 (p : ℕ) : KDescFam p fAlt8 := by
  intro hp hp2 Y _ _ K B h hc _
  obtain ⟨i, hi, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    change n = 8 at hi
    subst hi
    exact Or.inl (kConcl_of_alt hp hp2 h hn eK fun _ => by omega)

theorem kConcl_of_alt6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {K B : Subgroup Y}
    (h : KHyp p K B) (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) : KConcl p K B :=
  kConcl_of_alt hp hp2 h (by norm_num) eK fun h3 => absurd h3 hp3

end CFSG.LocalAnalysis.GLTheoremA
