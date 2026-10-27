module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

theorem shape15On_of_families (h1 : Shape15On KD264Lie.isLinearIdx)
    (h2 : Shape15On KD264Lie.isUnitaryIdx) (h3 : Shape15On KD264Lie.isClassicalBCDIdx)
    (h4 : Shape15On KD264Lie.isTrialityIdx) (h5 : Shape15On KD264Lie.isExcUntwistedIdx)
    (h6 : Shape15On KD264Lie.isExcTwistedIdx) : Shape15On fun _ => True := by
  intro G _ _ p L J A d b hS hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie dd =>
    obtain ⟨d0, hv⟩ := dd
    cases d0 with
    | A n q => exact h1 G p L J A d b hS ⟨.lie ⟨.A n q, hv⟩, trivial, ⟨e⟩⟩
    | twistedA n q =>
      exact h2 G p L J A d b hS ⟨.lie ⟨.twistedA n q, hv⟩, trivial, ⟨e⟩⟩
    | B n q => exact h3 G p L J A d b hS ⟨.lie ⟨.B n q, hv⟩, trivial, ⟨e⟩⟩
    | C n q => exact h3 G p L J A d b hS ⟨.lie ⟨.C n q, hv⟩, trivial, ⟨e⟩⟩
    | D n q => exact h3 G p L J A d b hS ⟨.lie ⟨.D n q, hv⟩, trivial, ⟨e⟩⟩
    | twistedD n q =>
      exact h3 G p L J A d b hS ⟨.lie ⟨.twistedD n q, hv⟩, trivial, ⟨e⟩⟩
    | E6 q => exact h5 G p L J A d b hS ⟨.lie ⟨.E6 q, hv⟩, trivial, ⟨e⟩⟩
    | E7 q => exact h5 G p L J A d b hS ⟨.lie ⟨.E7 q, hv⟩, trivial, ⟨e⟩⟩
    | E8 q => exact h5 G p L J A d b hS ⟨.lie ⟨.E8 q, hv⟩, trivial, ⟨e⟩⟩
    | F4 q => exact h5 G p L J A d b hS ⟨.lie ⟨.F4 q, hv⟩, trivial, ⟨e⟩⟩
    | G2 q => exact h5 G p L J A d b hS ⟨.lie ⟨.G2 q, hv⟩, trivial, ⟨e⟩⟩
    | twistedE6 q =>
      exact h6 G p L J A d b hS ⟨.lie ⟨.twistedE6 q, hv⟩, trivial, ⟨e⟩⟩
    | trialityD4 q =>
      exact h4 G p L J A d b hS ⟨.lie ⟨.trialityD4 q, hv⟩, trivial, ⟨e⟩⟩
    | suzuki k => exact h6 G p L J A d b hS ⟨.lie ⟨.suzuki k, hv⟩, trivial, ⟨e⟩⟩
    | reeG2 k => exact h6 G p L J A d b hS ⟨.lie ⟨.reeG2 k, hv⟩, trivial, ⟨e⟩⟩
    | reeF4 k => exact h6 G p L J A d b hS ⟨.lie ⟨.reeF4 k, hv⟩, trivial, ⟨e⟩⟩
    | tits => exact h6 G p L J A d b hS ⟨.lie ⟨.tits, hv⟩, trivial, ⟨e⟩⟩
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi


@[expose] def AmbiguousAltFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (n : ℕ) (hn : 5 ≤ n),
    (n = 5 ∨ n = 6 ∨ n = 8) →
    Setup p L J A d b → catalogIs (PSimple p L) (fun i => i = .alternating n hn) → False

theorem i171LieShapeAt_of_setup_conditional (hS : Shape15On fun _ => True)
    (hAmb : AmbiguousAltFalse)
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (h : Setup p L J A d b) : I171.I171LieShapeAt p L := by
  rcases h.chev2 with hcat | hamb
  · refine hS G p L J A d b h ?_
    refine S10.catalogIs_imp ?_ hcat
    intro i hi
    cases i with
    | lie _ => trivial
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
  · obtain ⟨i, hi, ⟨e⟩⟩ := hamb
    cases i with
    | lie idx => exact hS G p L J A d b h ⟨.lie idx, trivial, ⟨e⟩⟩
    | cyclic _ _ => simp [ambiguousChev] at hi
    | sporadic _ => simp [ambiguousChev] at hi
    | alternating n hn =>
      have h5 : 5 ≤ n := by
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
      have hn168 : n = 5 ∨ n = 6 ∨ n = 8 := by
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
      exact False.elim (hAmb G p L J A d b n h5 hn168 h ⟨.alternating n hn, rfl, ⟨e⟩⟩)

theorem lin_case_false {p N : ℕ} (hp : 3 ≤ p) (h2p : 2 * p ≤ N)
    (hN : N - 2 ≤ 1 + N / p) : False := by
  have h3p : 3 * (N / p) ≤ N := by
    calc 3 * (N / p) ≤ p * (N / p) := Nat.mul_le_mul_right _ hp
      _ = N / p * p := Nat.mul_comm _ _
      _ ≤ N := Nat.div_mul_le_self N p
  have h3 : 3 * (N - 2) ≤ 3 + 3 * (N / p) := by
    calc 3 * (N - 2) ≤ 3 * (1 + N / p) := Nat.mul_le_mul_left 3 hN
      _ = 3 + 3 * (N / p) := by ring
  omega

theorem uni_case_eq {p N : ℕ} (hp : 3 ≤ p) (hN3 : 3 ≤ N)
    (h3le : 3 ≤ 1 + N / p) (hN : N - 3 ≤ 1 + N / p) : p = 3 ∧ N = 6 := by
  have h3p : 3 * (N / p) ≤ N := by
    calc 3 * (N / p) ≤ p * (N / p) := Nat.mul_le_mul_right _ hp
      _ = N / p * p := Nat.mul_comm _ _
      _ ≤ N := Nat.div_mul_le_self N p
  have h2p : 2 * p ≤ N := by
    have h2 : 2 ≤ N / p := by omega
    calc 2 * p = p * 2 := Nat.mul_comm _ _
      _ ≤ N := by
        calc p * 2 ≤ p * (N / p) := Nat.mul_le_mul_left p h2
          _ = N / p * p := Nat.mul_comm _ _
          _ ≤ N := Nat.div_mul_le_self N p
  have h3 : 3 * (N - 3) ≤ 3 + 3 * (N / p) := by
    calc 3 * (N - 3) ≤ 3 * (1 + N / p) := Nat.mul_le_mul_left 3 hN
      _ = 3 + 3 * (N / p) := by ring
  constructor <;> omega

theorem t171ShapeFact_of_conditional (hS : Shape15On fun _ => True) (hAmb : AmbiguousAltFalse)
    (hLU : LinUniBound) (hE6 : E6Bound false) (hLin : LowerLin) (hUni : LowerUni)
    (hE6l : LowerE6) : T171.T171ShapeFact := by
  intro p Ω _ _ B x L D K β _ hcfg hmax _ hpre hK hch hβ hβD hni
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨A, d, -, -, hSetup, hcardB⟩ := setup_of_cfg hcfg hpre hK hch hβ hβD hni
  obtain ⟨i, hi, ⟨e⟩⟩ := i171LieShapeAt_of_setup_conditional hS hAmb hSetup
  cases i with
  | lie idx =>
    obtain ⟨d0, hv⟩ := idx
    cases d0 with
    | A n q =>
      obtain ⟨hq2, hdvd⟩ := hi
      have hpN : p ∣ n + 1 := (Nat.dvd_gcd_iff.mp hdvd).1
      have hpdvd : p ∣ q.card - 1 := (Nat.dvd_gcd_iff.mp hdvd).2
      have hN3 : 3 ≤ n + 1 :=
        hp3.trans (Nat.le_of_dvd (Nat.succ_pos n) hpN)
      have hcatLin : catalogIs (PSimple p L) (onLie fun i => ∃ q',
          i = .A (n + 1 - 1) q' ∧ q'.p = 2 ∧ p ∣ q'.card - 1) :=
        ⟨.lie ⟨.A n q, hv⟩, ⟨q, by rw [Nat.add_sub_cancel], hq2, hpdvd⟩, ⟨e⟩⟩
      obtain ⟨E, U, hEL, hUL, hEel, hU2, hU1, hEU, hlow⟩ :=
        hLin Ω L p (n + 1) hp hp2 hN3 hcfg.qs hcatLin
      have hcard := card_le_of_twoLocal hcfg hmax hEL hUL hEel hU2 hU1 hEU
      set X : Subgroup Ω := E ⊓ Subgroup.centralizer (L : Set Ω) with hX
      have hXpos : 0 < Nat.card ↥X := Nat.card_pos
      have hpowB : p ^ (n + 1 - 1) ≤ Nat.card B := by
        have h1 : p ^ (n + 1 - 2) * Nat.card ↥X * p ≤ Nat.card E * p :=
          Nat.mul_le_mul_right p hlow
        have h2 : p * Nat.card E ≤ Nat.card B * Nat.card ↥X := hcard
        have h3 : p ^ (n + 1 - 1) * Nat.card ↥X ≤ Nat.card B * Nat.card ↥X := by
          calc p ^ (n + 1 - 1) * Nat.card ↥X
              = p ^ (n + 1 - 2) * Nat.card ↥X * p := by
                have hexp : n + 1 - 1 = (n + 1 - 2) + 1 := by omega
                rw [hexp, pow_succ]
                ring
            _ ≤ Nat.card E * p := h1
            _ = p * Nat.card E := Nat.mul_comm _ _
            _ ≤ Nat.card B * Nat.card ↥X := h2
        exact Nat.le_of_mul_le_mul_right h3 hXpos
      rw [hcardB] at hpowB
      have hA_low : p ^ (n + 1 - 2) ≤ Nat.card A := by
        have h1 : p * p ^ (n + 1 - 2) ≤ p * Nat.card A := by
          calc p * p ^ (n + 1 - 2) = p ^ (n + 1 - 1) := by
                have hexp : n + 1 - 1 = (n + 1 - 2) + 1 := by omega
                rw [hexp, pow_succ]
                ring
            _ ≤ p * Nat.card A := hpowB
        exact Nat.le_of_mul_le_mul_left h1 hp.pos
      have hcatLU : catalogIs (PSimple p L) (onLie fun i => ∃ q',
          (i = .A (n + 1 - 1) q' ∨ i = .twistedA (n + 1 - 1) q') ∧ I171.I171LieShape p i) :=
        ⟨.lie ⟨.A n q, hv⟩, ⟨q, Or.inl (by rw [Nat.add_sub_cancel]), ⟨hq2, hdvd⟩⟩, ⟨e⟩⟩
      have hA_up : Nat.card A ≤ p ^ (1 + (n + 1) / p) := hLU Ω p L K A d β (n + 1) hSetup hcatLU
      have hle : n + 1 - 2 ≤ 1 + (n + 1) / p :=
        (Nat.pow_le_pow_iff_right hp.one_lt).1 (hA_low.trans hA_up)
      have h3le : 3 ≤ 1 + (n + 1) / p := by
        have h4 : p ^ 3 ≤ Nat.card A := by
          have h5 : p ^ 4 ≤ Nat.card B := hcfg.card_ge
          rw [hcardB] at h5
          have h6 : p ^ 3 * p ≤ Nat.card A * p := by
            calc p ^ 3 * p = p ^ 4 := by ring
              _ ≤ p * Nat.card A := h5
              _ = Nat.card A * p := Nat.mul_comm _ _
          exact Nat.le_of_mul_le_mul_right h6 hp.pos
        exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h4.trans hA_up)
      have h2p : 2 * p ≤ n + 1 := by
        have h2 : 2 ≤ (n + 1) / p := by omega
        calc 2 * p = p * 2 := Nat.mul_comm _ _
          _ ≤ p * ((n + 1) / p) := Nat.mul_le_mul_left p h2
          _ = (n + 1) / p * p := Nat.mul_comm _ _
          _ ≤ n + 1 := Nat.div_mul_le_self (n + 1) p
      exact (lin_case_false hp3 h2p hle).elim
    | twistedA n q =>
      obtain ⟨hq2, hdvd⟩ := hi
      have hpN : p ∣ n + 1 := (Nat.dvd_gcd_iff.mp hdvd).1
      have hpdvd : p ∣ q.card + 1 := (Nat.dvd_gcd_iff.mp hdvd).2
      have hN3 : 3 ≤ n + 1 :=
        hp3.trans (Nat.le_of_dvd (Nat.succ_pos n) hpN)
      have hcatUni : catalogIs (PSimple p L) (onLie fun i => ∃ q',
          i = .twistedA (n + 1 - 1) q' ∧ q'.p = 2 ∧ p ∣ q'.card + 1) :=
        ⟨.lie ⟨.twistedA n q, hv⟩, ⟨q, by rw [Nat.add_sub_cancel], hq2, hpdvd⟩, ⟨e⟩⟩
      obtain ⟨E, U, hEL, hUL, hEel, hU2, hU1, hEU, hlow⟩ :=
        hUni Ω L p (n + 1) hp hp2 hN3 hcfg.qs hcatUni
      have hcard := card_le_of_twoLocal hcfg hmax hEL hUL hEel hU2 hU1 hEU
      set X : Subgroup Ω := E ⊓ Subgroup.centralizer (L : Set Ω) with hX
      have hXpos : 0 < Nat.card ↥X := Nat.card_pos
      have hpowB : p ^ (n + 1 - 2) ≤ Nat.card B := by
        have h1 : p ^ (n + 1 - 3) * Nat.card ↥X * p ≤ Nat.card E * p :=
          Nat.mul_le_mul_right p hlow
        have h2 : p * Nat.card E ≤ Nat.card B * Nat.card ↥X := hcard
        have h3 : p ^ (n + 1 - 2) * Nat.card ↥X ≤ Nat.card B * Nat.card ↥X := by
          calc p ^ (n + 1 - 2) * Nat.card ↥X
              = p ^ (n + 1 - 3) * Nat.card ↥X * p := by
                have hexp : n + 1 - 2 = (n + 1 - 3) + 1 := by omega
                rw [hexp, pow_succ]
                ring
            _ ≤ Nat.card E * p := h1
            _ = p * Nat.card E := Nat.mul_comm _ _
            _ ≤ Nat.card B * Nat.card ↥X := h2
        exact Nat.le_of_mul_le_mul_right h3 hXpos
      rw [hcardB] at hpowB
      have hA_low : p ^ (n + 1 - 3) ≤ Nat.card A := by
        have h1 : p * p ^ (n + 1 - 3) ≤ p * Nat.card A := by
          calc p * p ^ (n + 1 - 3) = p ^ (n + 1 - 2) := by
                have hexp : n + 1 - 2 = (n + 1 - 3) + 1 := by omega
                rw [hexp, pow_succ]
                ring
            _ ≤ p * Nat.card A := hpowB
        exact Nat.le_of_mul_le_mul_left h1 hp.pos
      have hcatLU : catalogIs (PSimple p L) (onLie fun i => ∃ q',
          (i = .A (n + 1 - 1) q' ∨ i = .twistedA (n + 1 - 1) q') ∧ I171.I171LieShape p i) :=
        ⟨.lie ⟨.twistedA n q, hv⟩, ⟨q, Or.inr (by rw [Nat.add_sub_cancel]), ⟨hq2, hdvd⟩⟩, ⟨e⟩⟩
      have hA_up : Nat.card A ≤ p ^ (1 + (n + 1) / p) := hLU Ω p L K A d β (n + 1) hSetup hcatLU
      have hle : n + 1 - 3 ≤ 1 + (n + 1) / p :=
        (Nat.pow_le_pow_iff_right hp.one_lt).1 (hA_low.trans hA_up)
      have h3le : 3 ≤ 1 + (n + 1) / p := by
        have h4 : p ^ 3 ≤ Nat.card A := by
          have h5 : p ^ 4 ≤ Nat.card B := hcfg.card_ge
          rw [hcardB] at h5
          have h6 : p ^ 3 * p ≤ Nat.card A * p := by
            calc p ^ 3 * p = p ^ 4 := by ring
              _ ≤ p * Nat.card A := h5
              _ = Nat.card A * p := Nat.mul_comm _ _
          exact Nat.le_of_mul_le_mul_right h6 hp.pos
        exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h4.trans hA_up)
      obtain ⟨hp3', hN6⟩ := uni_case_eq hp3 hN3 h3le hle
      have hn5 : n = 5 := by omega
      subst n
      have hpdvd3 : 3 ∣ q.card + 1 := hp3' ▸ hpdvd
      have hodd : Odd q.exponent := by
        refine CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one ?_
        have hqcard : q.card = 2 ^ q.exponent := by
          rw [TauCeti.PrimePower.card_def, hq2]
        rwa [hqcard] at hpdvd3
      refine ⟨hp3', q.exponent, hodd, Or.inl ?_⟩
      exact ⟨.lie ⟨.twistedA 5 q, hv⟩, ⟨hq2, rfl⟩, ⟨e⟩⟩
    | E6 q =>
      obtain ⟨hp3', hq2, hdvd⟩ := hi
      subst p
      have hcatE6 : catalogIs (PSimple 3 L) (onLie fun i => ∃ q',
          I171.I171LieShape 3 i ∧ i = .E6 q') :=
        ⟨.lie ⟨.E6 q, hv⟩, ⟨q, ⟨rfl, hq2, hdvd⟩, by rfl⟩, ⟨e⟩⟩
      have hA_up : Nat.card A ≤ 3 ^ 4 := hE6 Ω L K A d β hSetup hcatE6
      have hcatLow : catalogIs (PSimple 3 L) (onLie fun i => ∃ q',
          i = .E6 q' ∧ q'.p = 2 ∧ 3 ∣ q'.card - 1) :=
        ⟨.lie ⟨.E6 q, hv⟩, ⟨q, rfl, hq2, hdvd⟩, ⟨e⟩⟩
      obtain ⟨E, U, hEL, hUL, hEel, hU2, hU1, hEU, hlow⟩ :=
        hE6l Ω L hcfg.qs hcatLow
      have hcard := card_le_of_twoLocal hcfg hmax hEL hUL hEel hU2 hU1 hEU
      set X : Subgroup Ω := E ⊓ Subgroup.centralizer (L : Set Ω) with hX
      have hXpos : 0 < Nat.card ↥X := Nat.card_pos
      have h1 : 3 ^ 5 * Nat.card ↥X ≤ Nat.card E := hlow
      have h2 : 3 * Nat.card E ≤ Nat.card B * Nat.card ↥X := hcard
      rw [hcardB] at h2
      have h2' : 3 * Nat.card E ≤ 3 * (Nat.card A * Nat.card ↥X) := by
        calc 3 * Nat.card E ≤ 3 * Nat.card A * Nat.card ↥X := h2
          _ = 3 * (Nat.card A * Nat.card ↥X) := by ring
      have h3 : Nat.card E ≤ Nat.card A * Nat.card ↥X :=
        Nat.le_of_mul_le_mul_left h2' (by norm_num : 0 < 3)
      have h4 : 3 ^ 5 ≤ Nat.card A := by
        apply Nat.le_of_mul_le_mul_right (c := Nat.card ↥X) _ hXpos
        calc 3 ^ 5 * Nat.card ↥X ≤ Nat.card E := h1
          _ ≤ Nat.card A * Nat.card ↥X := h3
      have h5 : 3 ^ 5 ≤ 3 ^ 4 := h4.trans hA_up
      norm_num at h5
    | twistedE6 q =>
      obtain ⟨hp3', hq2, hdvd⟩ := hi
      have hodd : Odd q.exponent := by
        refine CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one ?_
        have hqcard : q.card = 2 ^ q.exponent := by
          rw [TauCeti.PrimePower.card_def, hq2]
        rwa [hqcard] at hdvd
      refine ⟨hp3', q.exponent, hodd, Or.inr ?_⟩
      exact ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨hq2, rfl⟩, ⟨e⟩⟩
    | B n q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | C n q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | D n q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | twistedD n q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | E7 q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | E8 q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | F4 q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | G2 q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | trialityD4 q => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | suzuki k => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | reeG2 k => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | reeF4 k => exact absurd hi (by simp [onLie, I171.I171LieShape])
    | tits => exact absurd hi (by simp [onLie, I171.I171LieShape])
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
