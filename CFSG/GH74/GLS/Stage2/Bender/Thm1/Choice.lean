module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
import CFSG.Adapters.WholeGroupLayer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Access

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem Ctx6.mem (h : Ctx6 G z k S M p) : M ∈ maximalOverCentralizer z := h.choice.adm.1

theorem Ctx6.coatom (h : Ctx6 G z k S M p) : IsCoatom M := h.mem.1

theorem Ctx6.cen_le (h : Ctx6 G z k S M p) : Cen z ≤ M := h.mem.2

theorem Ctx6.z_mem (h : Ctx6 G z k S M p) : z ∈ M := h.cen_le (mem_Cen_self z)

theorem Ctx6.twoPrimes (h : Ctx6 G z k S M p) : TwoPrimes (Fm M) := h.choice.adm.2.1

theorem Ctx6.prime (h : Ctx6 G z k S M p) : p.Prime := h.choice.adm.2.2.1

theorem Ctx6.not_cen (h : Ctx6 G z k S M p) : ¬ Op p M ≤ Cen z := h.choice.adm.2.2.2

theorem Ctx6.orderOf_z (h : Ctx6 G z k S M p) : orderOf z = 2 := h.ctx.orderOf_z

theorem Ctx6.Fs_eq (h : Ctx6 G z k S M p) {N : Subgroup G} (hN : N ∈ maximalOverCentralizer z) :
    Fs N = Fm N := (h.hyp.fitting N hN).1

theorem Ctx6.Fm_eq (h : Ctx6 G z k S M p) {N : Subgroup G} (hN : N ∈ maximalOverCentralizer z) :
    Fm N = pPrimeCoreOf 2 (Fm N) := (h.hyp.fitting N hN).2

end Access

theorem odd_card_Fm {G : Type} [Group G] [Finite G] {z : G} (h : Hyp6A z) {N : Subgroup G}
    (hN : N ∈ maximalOverCentralizer z) : Odd (Nat.card ↥(Fm N)) := by
  have h2 : Fm N = pPrimeCoreOf 2 (Fm N) := (h.fitting N hN).2
  have h3 : Nat.card ↥(Fm N) = Nat.card ↥(pPrimeCore 2 ↥(Fm N)) := by
    conv_lhs => rw [h2]
    exact Subgroup.card_map_of_injective (Fm N).subtype_injective
  rw [h3]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Fm N)))

section PNeTwo

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem Ctx6.p_ne_two (h : Ctx6 G z k S M p) : p ≠ 2 := by
  intro hp2
  subst hp2
  have hodd : Odd (Nat.card ↥(Fm M)) := odd_card_Fm h.hyp h.mem
  have hle : Op 2 M ≤ Fm M := Op_le_Fm 2 Nat.prime_two M
  have hP : IsPGroup 2 ↥(Op 2 M) := isPGroup_Op 2 Nat.prime_two M
  have hdvd : Nat.card ↥(Op 2 M) ∣ Nat.card ↥(Fm M) := Subgroup.card_dvd_of_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have hn0 : n = 0 := by
    by_contra hn0
    have h2 : 2 ∣ Nat.card ↥(Op 2 M) := by rw [hn]; exact dvd_pow_self 2 hn0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  have hbot : Op 2 M = ⊥ := by
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  exact h.not_cen (hbot ▸ bot_le)

end PNeTwo

section SixA

variable {G : Type} [Group G] [Finite G]

theorem isPrimePowerGrp_of_not_twoPrimes {X : Subgroup G} (h : ¬ TwoPrimes X) :
    ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥X := by
  have hfin : (piOf X).Finite := by
    refine (Set.finite_Iic (Nat.card ↥X)).subset ?_
    intro r hr
    exact Nat.le_of_dvd Nat.card_pos hr.2
  have hle : (piOf X).ncard ≤ 1 := by
    unfold TwoPrimes at h
    omega
  have hall := (Set.ncard_le_one hfin).mp hle
  by_cases hex : ∃ q, q ∈ piOf X
  · obtain ⟨q, hq⟩ := hex
    refine ⟨q, hq.1, IsPGroup.of_card (n := (Nat.card ↥X).primeFactorsList.length) ?_⟩
    exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdn => hall d ⟨hd, hdn⟩ q hq)
  · refine ⟨2, Nat.prime_two, IsPGroup.of_card (n := 0) ?_⟩
    have h1 : Nat.card ↥X = 1 := by
      by_contra hne
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
      exact hex ⟨r, hr, hrd⟩
    rw [h1]
    rfl

theorem hyp6A_of_odd {z : G}
    (hodd : ∀ M ∈ maximalOverCentralizer z, Odd (Nat.card ↥(generalizedFitting ↥M)))
    {M₀ : Subgroup G} (hM₀ : M₀ ∈ maximalOverCentralizer z)
    (hnp : ¬ IsPrimePowerGrp ↥(generalizedFitting ↥M₀)) : Hyp6A z := by
  refine ⟨fun N hN => fitting_eq_of_odd (hodd N hN), M₀, hM₀, ?_⟩
  by_contra hnot
  obtain ⟨q, hq, hqp⟩ := isPrimePowerGrp_of_not_twoPrimes hnot
  refine hnp ⟨q, hq, ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hqp
  refine IsPGroup.of_card (n := n) ?_
  have hFs := (fitting_eq_of_odd (hodd M₀ hM₀)).1
  rw [← card_Fs, hFs, hn]

end SixA

section ExistsChoice

variable {G : Type} [Group G] [Finite G]

theorem centralizer_generalizedFitting_le_fitting' (A : Type) [Group A] [Finite A] :
    centralizer ((generalizedFitting A : Subgroup A) : Set A) ≤ fittingSubgroup A :=
  CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup A

theorem mem_Fm_of_centralizes_Fs {M : Subgroup G} {x : G} (hx : x ∈ M)
    (hc : Fs M ≤ centralizer ({x} : Set G)) : x ∈ Fm M := by
  have h1 : (⟨x, hx⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 : (y : G) ∈ centralizer ({x} : Set G) := hc ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h2 x (Set.mem_singleton x)).symm
  exact ⟨⟨x, hx⟩, centralizer_generalizedFitting_le_fitting' ↥M h1, rfl⟩

theorem exists_prime_not_cen {z : G} (hz : orderOf z = 2) (h : Hyp6A z) {M : Subgroup G}
    (hM : M ∈ maximalOverCentralizer z) : ∃ p : ℕ, p.Prime ∧ ¬ Op p M ≤ Cen z := by
  by_contra hno
  push Not at hno
  have hFm : Fm M ≤ Cen z := by
    rw [Fm_def, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore (G := ↥M), Subgroup.map_iSup]
    exact iSup_le fun p => hno p (Nat.prime_of_mem_primeFactors p.2)
  have hzM : z ∈ M := hM.2 (mem_Cen_self z)
  have hc : Fs M ≤ centralizer ({z} : Set G) := by
    rw [(h.fitting M hM).1]
    exact hFm
  have hzF : z ∈ Fm M := mem_Fm_of_centralizes_Fs hzM hc
  have hodd := odd_card_Fm h hM
  have hdvd : orderOf z ∣ Nat.card ↥(Fm M) := by
    have := orderOf_dvd_natCard (⟨z, hzF⟩ : ↥(Fm M))
    rwa [Subgroup.orderOf_mk] at this
  rw [hz] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem exists_choice6 {z : G} (hz : orderOf z = 2) (h : Hyp6A z) :
    ∃ (M : Subgroup G) (p : ℕ), Choice6 z M p := by
  by_cases hex : ∃ (M' : Subgroup G) (p' : ℕ), Adm z M' p' ∧ Inverts z (Op p' M')
  · obtain ⟨M', p', hadm, hinv⟩ := hex
    exact ⟨M', p', ⟨hadm, fun _ => hinv⟩⟩
  · obtain ⟨M, hM, h2⟩ := h.two_primes
    obtain ⟨p, hp, hnc⟩ := exists_prime_not_cen hz h hM
    exact ⟨M, p, ⟨⟨hM, h2, hp, hnc⟩, fun h' => absurd h' hex⟩⟩

end ExistsChoice

end CFSG.GH74.GLS.Stage2.Bender.Thm1
