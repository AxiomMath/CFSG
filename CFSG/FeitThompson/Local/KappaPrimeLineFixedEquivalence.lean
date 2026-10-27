module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

theorem isCyclic_sylow_of_exists [Finite G] [Fact p.Prime]
    (h : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G))
    (S : Sylow p M) : IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G) := by
  obtain ⟨S', hS'⟩ := h
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) S' S
  have h1 : (S' : Subgroup M).map (MulAut.conj m) = (S : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := m) (P := S')
    rw [hm] at h
    exact h.symm
  have h2 : ((S : Subgroup M).map M.subtype : Subgroup G)
      = ((S' : Subgroup M).map M.subtype).map (MulAut.conj (m : G) : G →* G) := by
    rw [← h1, map_subtype_map_conj]
  rw [h2]
  exact (isCyclic_map_conj_iff _ _).2 hS'

theorem exists_mem_map_conj_le_sylow [Finite G] [Fact p.Prime] {X : Subgroup G} (hXM : X ≤ M)
    (hX : IsPGroup p (X.subgroupOf M)) (S : Sylow p M) :
    ∃ m ∈ M, X.map (MulAut.conj m : G →* G) ≤ ((S : Subgroup M).map M.subtype : Subgroup G) := by
  obtain ⟨T, hT⟩ := hX.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) T S
  have h1 : (T : Subgroup M).map (MulAut.conj m) = (S : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := m) (P := T)
    rw [hm] at h
    exact h.symm
  refine ⟨m, m.2, ?_⟩
  have h2 : X.map (MulAut.conj (m : G) : G →* G)
      = ((X.subgroupOf M).map (MulAut.conj m)).map M.subtype := by
    rw [map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le hXM]
  rw [h2, ← h1]
  exact Subgroup.map_mono (Subgroup.map_mono hT)

theorem map_conj_inf_centralizer {N : Subgroup G} (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (N : Set G)) :
    (N ⊓ centralizer (X : Set G)).map (MulAut.conj g : G →* G)
      = N ⊓ centralizer ((X.map (MulAut.conj g : G →* G) : Subgroup G) : Set G) := by
  have hN : N.map (MulAut.conj g : G →* G) = N := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hN,
    map_centralizer_eq_centralizer_image, Subgroup.coe_map]
  rfl

theorem natCard_dvd_of_isCyclic_of_forall_pow_eq_one {C : Type*} [Group C] [IsCyclic C]
    (hexp : ∀ x : C, x ^ p = 1) : Nat.card C ∣ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one (hexp g)

theorem centralizer_singleton_le_centralizer_zpowers_pow (x : G) (n : ℕ) :
    centralizer ({x} : Set G) ≤ centralizer ((zpowers (x ^ n) : Subgroup G) : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]
  intro z hz
  rw [mem_centralizer_singleton_iff] at hz ⊢
  exact ((Commute.symm hz).pow_left n).symm

theorem centralizer_coe_eq_of_zpowers_eq {X : Subgroup G} {x : G} (h : zpowers x = X) :
    centralizer (X : Set G) = centralizer ({x} : Set G) := by
  rw [← h, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem elementaryAbelianPRank_eq_one_of_isCyclic_sylow [Finite G] (hp : p.Prime)
    (hdvd : p ∣ Nat.card M)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G)) :
    elementaryAbelianPRank p M = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (elementaryAbelianPRank_le fun d hd => ?_)
    ((one_le_elementaryAbelianPRank_iff hp).2 hdvd)
  obtain ⟨H, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 hd
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  have hQcyc : IsCyclic (Q : Subgroup M) :=
    (isCyclic_map_subtype_iff _).1 (isCyclic_sylow_of_exists hcyc Q)
  have : IsCyclic H := Subgroup.isCyclic_of_le hQ
  have hdd : p ^ d ∣ p := hcard ▸ natCard_dvd_of_isCyclic_of_forall_pow_eq_one
    (fun x => Subtype.ext (hexp x.1 x.2))
  by_contra hne
  have h2 : 2 ≤ d := by omega
  have : p ^ 2 ≤ p ^ d := Nat.pow_le_pow_right hp.pos h2
  have := Nat.le_of_dvd hp.pos hdd
  nlinarith [hp.two_le]

theorem mem_tau1Primes_union_tau3Primes_of_isCyclic_sylow [Finite G] (hp : p.Prime)
    (hdvd : p ∣ Nat.card M) (hσ : p ∉ sigmaPrimes M)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G)) :
    p ∈ tau1Primes M ∪ tau3Primes M := by
  rw [tau1Primes_union_tau3Primes]
  exact ⟨hp, hdvd, hσ, elementaryAbelianPRank_eq_one_of_isCyclic_sylow hp hdvd hcyc⟩

theorem exists_natCard_eq_of_mem_kappaPrimes [Finite G] (hp : p.Prime) (hmem : p ∈ kappaPrimes M) :
    ∃ (Y : Subgroup G) (S : Sylow p M), Nat.card Y = p ∧
      Y ≤ ((S : Subgroup M).map M.subtype : Subgroup G) ∧
      sigmaCore M ⊓ centralizer (Y : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [mem_kappaPrimes_iff] at hmem
  obtain ⟨-, -, -, S, -, x, hxS, hx1, hne⟩ := hmem
  have hpg : IsPGroup p ((S : Subgroup M).map M.subtype : Subgroup G) :=
    IsPGroup.map S.2 M.subtype
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hpg ⟨x, hxS⟩
  rw [← Subgroup.orderOf_coe ⟨x, hxS⟩] at hk
  simp only at hk
  have hkpos : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero, orderOf_eq_one_iff] at hk
    exact hx1 hk
  have hord : p ∣ orderOf x := hk ▸ dvd_pow_self p hkpos
  refine ⟨zpowers (x ^ (orderOf x / p)), S, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    exact orderOf_pow_orderOf_div (by rw [hk]; exact pow_ne_zero _ hp.pos.ne') hord
  · exact (zpowers_le (H := ((S : Subgroup M).map M.subtype : Subgroup G))).2 (pow_mem hxS _)
  · exact fun h => hne (le_bot_iff.1 (h ▸ inf_le_inf_left _
      (centralizer_singleton_le_centralizer_zpowers_pow x _)))

theorem inf_centralizer_ne_bot_of_mem_kappaPrimes [Finite G] (hp : p.Prime)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G))
    (hmem : p ∈ kappaPrimes M) {X : Subgroup G} (hXM : X ≤ M) (hX : Nat.card X = p) :
    sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y, S, hYcard, hYS, hYne⟩ := exists_natCard_eq_of_mem_kappaPrimes hp hmem
  have hSc : IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G) :=
    isCyclic_sylow_of_exists hcyc S
  have hXp : IsPGroup p (X.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [natCard_subgroupOf hXM, hX, pow_one])
  obtain ⟨m, hmM, hmle⟩ := exists_mem_map_conj_le_sylow hXM hXp S
  have hXm : X.map (MulAut.conj m : G →* G) = Y :=
    eq_of_le_of_natCard_eq_of_isCyclic (A := ((S : Subgroup M).map M.subtype : Subgroup G))
      hmle hYS (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hX, hYcard])
  intro hc
  have hmap := map_conj_inf_centralizer (N := sigmaCore M) X (le_normalizer_sigmaCore M hmM)
  rw [hc, Subgroup.map_bot, hXm] at hmap
  exact hYne hmap.symm

theorem mem_kappaPrimes_of_inf_centralizer_ne_bot [Finite G] (hp : p.Prime)
    (hσ : p ∉ sigmaPrimes M)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G))
    {X : Subgroup G} (hXM : X ≤ M) (hX : Nat.card X = p)
    (hne : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) : p ∈ kappaPrimes M := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxX, hx1, hxgen⟩ := exists_zpowers_eq_of_prime_natCard (by rw [hX]; exact hp)
  have hXp : IsPGroup p (X.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [natCard_subgroupOf hXM, hX, pow_one])
  obtain ⟨T, hT⟩ := hXp.exists_le_sylow
  have hxT : x ∈ ((T : Subgroup M).map M.subtype : Subgroup G) := by
    have hmem : (⟨x, hXM hxX⟩ : M) ∈ (T : Subgroup M) := hT (by
      simpa [Subgroup.mem_subgroupOf] using hxX)
    exact Subgroup.mem_map_of_mem _ hmem
  rw [mem_kappaPrimes_iff]
  refine ⟨hp, hX ▸ Subgroup.card_dvd_of_le hXM, hσ, T, isCyclic_sylow_of_exists hcyc T,
    x, hxT, hx1, ?_⟩
  rwa [← centralizer_coe_eq_of_zpowers_eq hxgen]

theorem mem_kappaPrimes_iff_inf_centralizer_ne_bot [Finite G] (hp : p.Prime)
    (hσ : p ∉ sigmaPrimes M)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G))
    {X : Subgroup G} (hXM : X ≤ M) (hX : Nat.card X = p) :
    p ∈ kappaPrimes M ↔ sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ :=
  ⟨fun h => inf_centralizer_ne_bot_of_mem_kappaPrimes hp hcyc h hXM hX,
    mem_kappaPrimes_of_inf_centralizer_ne_bot hp hσ hcyc hXM hX⟩

theorem mem_tau_union_and_mem_kappaPrimes_iff_of_isCyclic_sylow [Finite G]
    (_hodd : Odd (Nat.card G)) (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (_hM : IsCoatom M)
    (hp : p.Prime) (hdvd : p ∣ Nat.card M) (hσ : p ∉ sigmaPrimes M)
    (hcyc : ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G)) :
    p ∈ tau1Primes M ∪ tau3Primes M ∧
      ∀ X : Subgroup G, X ≤ M → Nat.card X = p →
        (p ∈ kappaPrimes M ↔ sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :=
  ⟨mem_tau1Primes_union_tau3Primes_of_isCyclic_sylow hp hdvd hσ hcyc,
    fun _ hXM hX => mem_kappaPrimes_iff_inf_centralizer_ne_bot hp hσ hcyc hXM hX⟩

end

end CFSG.FeitThompson
