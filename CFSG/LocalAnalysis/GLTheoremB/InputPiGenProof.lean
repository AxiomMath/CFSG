module

public import CFSG.LocalAnalysis.GLTheoremB.PiGenDefs
public import CFSG.LocalAnalysis.GLTheoremB.PiGenSeven
public import CFSG.LocalAnalysis.GL83PartI.I_27_9
public import CFSG.LocalAnalysis.AGLEmbedding.AltAlpha
public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Center

variable {K : Type*} [Group K] [Finite K]

theorem prime_eq_of_dvd_card_center {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p K = ⊥)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card (Subgroup.center K)) : q = p := by
  by_contra hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) q hdvd
  have hz' : orderOf (z : K) = q := (Subgroup.orderOf_coe z).trans hz
  have hle : Subgroup.zpowers (z : K) ≤ Subgroup.center K := Subgroup.zpowers_le.2 z.2
  have hnorm : (Subgroup.zpowers (z : K)).Normal := Subgroup.normal_of_le_center hle
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z : K))) := by
    rw [Nat.card_zpowers, hz']
    exact (Nat.coprime_primes hp hq).2 (Ne.symm hne)
  have hle2 : Subgroup.zpowers (z : K) ≤ GLAPPrimeCore p K := le_sSup ⟨hnorm, hcop⟩
  rw [hcore] at hle2
  have h1 : (z : K) = 1 := Subgroup.mem_bot.1 (hle2 (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hz'
  exact hq.one_lt.ne hz'

theorem odd_card_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p K = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center K) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  exact hp2 (prime_eq_of_dvd_card_center hp hcore Nat.prime_two h2).symm

theorem isPGroup_center {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p K = ⊥) :
    IsPGroup p (Subgroup.center K) :=
  IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun {_} hd hdd => prime_eq_of_dvd_card_center hp hcore hd hdd))

end Center

theorem subsingleton_alt_of_le_two {n : ℕ} (hn : n ≤ 2) :
    Subsingleton (alternatingGroup (Fin n)) := by
  interval_cases n
  · exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  · exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  · refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := Equiv.Perm.mem_alternatingGroup.1 x.2
    have hy := Equiv.Perm.mem_alternatingGroup.1 y.2
    have : ∀ σ : Equiv.Perm (Fin 2), Equiv.Perm.sign σ = 1 → σ = 1 := by decide
    rw [this _ hx, this _ hy]

section Alt

variable {K : Type} [Group K] [Finite K]

theorem center_eq_bot_of_alt {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Group.IsPerfect K]
    (hcore : GLAPPrimeCore p K = ⊥) (hk : 1 ≤ k)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (k * p + 2))) :
    Subgroup.center K = ⊥ := by
  by_contra hZ
  have hp2' := hp.two_le
  have hp3' : 3 ≤ p := by omega
  have hn5 : 5 ≤ k * p + 2 := by
    have h13 : 1 * 3 ≤ k * p := Nat.mul_le_mul hk hp3'
    omega
  by_cases hp3 : p = 3
  · subst hp3
    rcases CFSG.AGLEmbedding.eq_six_or_seven_of_center hn5 e hp hp2 hZ
        (isPGroup_center hp hcore) with h | h <;> omega
  · have hp5 : 3 < p := by omega
    have hnd := CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn5 e hp hp5
    have hZ1 : Nat.card (Subgroup.center K) ≠ 1 := fun h =>
      hZ (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hZ1
    exact hnd ((prime_eq_of_dvd_card_center hp hcore hq hqd) ▸ hqd)

end Alt

theorem inputPiGen_of_orth (hOrth : InputPiGenOrth) :
    InputPiGen := by
  intro X _ _ p hp hp2 K hK hPi B hB hrank
  have : Fact p.Prime := ⟨hp⟩
  have hcore : GLAPPrimeCore p ↥K = ⊥ := hPi.2.1
  have : Group.IsPerfect ↥K := ⟨hPi.1.1⟩
  have hodd := odd_card_center hp hp2 hcore
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_cases halt : IsAltType p ↥K
  · rcases halt with ⟨k, ⟨e⟩⟩ | ⟨hp3', ⟨e⟩⟩
    · have hk : 1 ≤ k := by
        by_contra hk0
        obtain rfl : k = 0 := by omega
        have hsub := subsingleton_alt_of_le_two (n := 0 * p + 2) (by omega)
        have hnt : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hPi.1.2.toNontrivial
        have h1 : Subsingleton (↥K ⧸ Subgroup.center ↥K) := e.toEquiv.subsingleton
        exact not_subsingleton _ h1
      have hZ := center_eq_bot_of_alt hp hp2 hcore hk e
      have hn6 : k * p + 2 ≠ 6 := by
        intro h
        have hdvd : p ∣ 4 := ⟨k, by have := mul_comm k p; omega⟩
        have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases p
        · exact absurd hdvd (by norm_num)
        · exact absurd hp (by norm_num)
      have hn5 : 5 ≤ k * p + 2 := by
        have h13 : 1 * 3 ≤ k * p := Nat.mul_le_mul hk hp3
        omega
      exact GL83.PiGen.le_glbCore_of_alt hp3 hk rfl hn5 hn6 hB hK hZ e hrank
    · subst hp3'
      exact GL83.PiGen.le_glbCore_of_centGenI hB hK
        (le_centGenI_of_seven (GL83.PiGen.stab_le_normalizer B K)
          (GL83.CompFam.elem_mono hB inf_le_left) hodd e)
  · rcases hPi.2.2 with hA | hO | hS
    · exact absurd (Or.inl hA) halt
    · exact hOrth X p hp hp2 K hK hPi hO halt B hB hrank
    · exact absurd (Or.inr hS) halt

end CFSG.LocalAnalysis.GLTheoremB
