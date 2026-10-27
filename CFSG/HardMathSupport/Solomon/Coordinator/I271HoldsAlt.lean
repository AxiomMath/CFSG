module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltOrb
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltGen
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator GL83 GL83.CompFam GL83.PiGen

section Aux

variable {X : Type} [Group X] [Finite X]

theorem i271h_autOrderIn_dvd_card_mulAut {B K : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hperf : commutator ↥K = ⊤) :
    autOrderIn B K ∣ Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) := by
  let f : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hker : f.ker = (Subgroup.centralizer (K : Set X)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 := Subgroup.normalizerMonoidHom_ker (H := K)
    have h2 : Subgroup.inclusion hBN b ∈ K.normalizerMonoidHom.ker ↔
        ((Subgroup.inclusion hBN b : ↥(Subgroup.normalizer (K : Set X))) : X) ∈
          Subgroup.centralizer (K : Set X) := by
      rw [h1, Subgroup.mem_subgroupOf]
    exact (MonoidHom.mem_ker (f := K.normalizerMonoidHom)
      (x := Subgroup.inclusion hBN b)).symm.trans h2
  have hcard : autOrderIn B K = Nat.card f.range := by
    rw [← Subgroup.index_ker, hker]
    unfold autOrderIn
    rw [inf_of_le_left hBN]
    rfl
  rw [hcard]
  have hinj : Function.Injective ((autCenterQuot ↥K).comp f.range.subtype) :=
    (autCenterQuot_injective_of_perfect hperf).comp f.range.subtype_injective
  exact Subgroup.card_dvd_of_injective _ hinj

theorem i271h_center_eq_bot {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p K = ⊥)
    (hn : 5 ≤ n) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (hnp : ¬ p ∣ n)
    (h73 : ¬ (p = 3 ∧ n = 7)) : Subgroup.center K = ⊥ := by
  by_contra hZ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  by_cases hp3' : p = 3
  · subst hp3'
    rcases CFSG.AGLEmbedding.eq_six_or_seven_of_center hn e hp hp2 hZ (isPGroup_center hp hcore)
      with h | h
    · exact hnp (h ▸ (by norm_num : 3 ∣ 6))
    · exact h73 ⟨rfl, h⟩
  · have hp5 : 3 < p := by omega
    have hnd := CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn e hp hp5
    have hZ1 : Nat.card (Subgroup.center K) ≠ 1 := fun h => hZ (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hZ1
    exact hnd ((prime_eq_of_dvd_card_center hp hcore hq hqd) ▸ hqd)

end Aux

theorem i271AltNdiv_holds : I271AltNdiv := by
  intro X _ _ hXK p K B hH hNorm n hn he hnp
  obtain ⟨hBN, hp2⟩ := hNorm
  have hp : p.Prime := hH.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := hH.odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have h4 := hH.rank_four
  have hrank := hH.rank_local
  have hKc : IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := odd_card_center hp hpodd hOK
  obtain ⟨e0⟩ := he
  have e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n) := e0
  refine ⟨h4, ?_⟩
  by_cases h73 : p = 3 ∧ n = 7
  · obtain ⟨rfl, rfl⟩ := h73
    exact i271h_isInGOne_of_centGenI hBel hBN h4
      (le_centGenI_of_seven (stab_le_normalizer B K) (elem_mono hBel inf_le_left) hodd e)
  · have hZ : Subgroup.center ↥K = ⊥ := i271h_center_eq_bot hp hpodd hOK hn e hnp h73
    have hn6 : n ≠ 6 := by
      intro h6
      subst h6
      have hdvd := i271h_autOrderIn_dvd_card_mulAut hBN hq.1
      rw [Nat.card_congr (MulAut.congr e).toEquiv,
        Proving.AutSixBalance.card_mulAut_alt6] at hdvd
      obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hBN
      have hr2 : 2 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hr ▸ hp2)
      have hp2d : p ^ 2 ∣ 1440 := by
        refine (pow_dvd_pow p hr2).trans ?_
        rw [← hr]
        exact hdvd
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have h34 : p = 3 ∨ p = 4 := by omega
        rcases h34 with h3 | h3
        · exact hnp (h3 ▸ (by norm_num : 3 ∣ 6))
        · exact absurd (h3 ▸ hp) (by norm_num)
      have hle : p ^ 2 ≤ 1440 := Nat.le_of_dvd (by norm_num) hp2d
      have hle' : p ≤ 37 := by nlinarith
      interval_cases p <;> first
        | omega
        | (exfalso; revert hp; norm_num; done)
    have hpn : p ≤ n := by
      have hdvdK := i116e_dvd_card hp hH.core hH.comp
      obtain ⟨φ⟩ := exists_mulEquiv_of_center_eq_bot hZ e
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin] at hdvdK
      have h2 : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
      have : p ∣ Nat.factorial n := hdvdK.trans (Nat.div_dvd_of_dvd h2)
      exact (Nat.Prime.dvd_factorial hp).1 this
    have hk : 1 ≤ n / p := Nat.div_pos hpn hp.pos
    have hcpos : 1 ≤ n % p := Nat.pos_of_ne_zero fun h => hnp (Nat.dvd_of_mod_eq_zero h)
    have hcp : n % p < p := Nat.mod_lt _ hp.pos
    have hnk : n = n / p * p + n % p := by rw [mul_comm]; exact (Nat.div_add_mod n p).symm
    have horb := i271h_orbit_card_le hp3 hk hcpos hcp hnk hn hn6 hBel hKc hZ e hrank
    set π := permHom (stab_le_normalizer B K) hn hn6 e with hπ
    have hApg : IsPGroup p (stab B K) := isPGroup_of_elem (elem_mono hBel inf_le_left)
    have hRpg : IsPGroup p π.range :=
      hApg.of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have hnp' : ¬ p ∣ Fintype.card (Fin n) := by simpa using hnp
    have h3 : 3 ≤ Fintype.card (Fin n) := by simpa using (by omega : 3 ≤ n)
    have hgen := i271h_perm_gen hp3 hRpg hnp' h3 horb
    exact i271h_isInGOne_of_centGenI hBel hBN h4
      (i271h_le_centGenI_of_alt (stab_le_normalizer B K) hZ hn hn6 e hgen)

end CFSG.HardMathSupport.Solomon.Coordinator
