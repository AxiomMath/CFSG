module

public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbit
public import CFSG.ClassicalInvolution.Q3.TL4E3Odd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

theorem E3.commute_of_comm_mem_odd {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hN : Odd (Nat.card N)) {w : G} (hw2 : IsPGroup 2 (Subgroup.zpowers w))
    (hwN : ∀ n ∈ N, w * n = n * w) {a : G} (ha : ⁅w, a⁆ ∈ N) : w * a = a * w := by
  set c := ⁅w, a⁆ with hcdef
  have hwc : w * c = c * w := hwN c ha
  have hwa : w * a = c * a * w := by rw [hcdef, commutatorElement_def]; group
  have hk : ∀ k : ℕ, w ^ k * a = c ^ k * a * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : w * c ^ k = c ^ k * w := (Commute.pow_right hwc k).eq
      calc w ^ (k + 1) * a = w * (w ^ k * a) := by rw [pow_succ', mul_assoc]
        _ = w * (c ^ k * a * w ^ k) := by rw [ih]
        _ = c ^ k * (w * a) * w ^ k := by rw [← mul_assoc, ← mul_assoc, hck]; group
        _ = c ^ (k + 1) * a * w ^ (k + 1) := by rw [hwa]; group
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hw2) ⟨w, Subgroup.mem_zpowers w⟩
  rw [Subgroup.orderOf_mk] at hm
  have hw1 : w ^ 2 ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have hc1 : c ^ 2 ^ m = 1 := by
    have h := hk (2 ^ m)
    rw [hw1, one_mul, mul_one] at h
    exact mul_eq_right.mp h.symm
  have hd1 : orderOf c ∣ Nat.gcd (2 ^ m) (Nat.card N) := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc1) ?_
    have := Subgroup.orderOf_dvd_natCard N ha
    exact this
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left m
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hN.not_two_dvd_nat))] at hd1
  have hc : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  rw [hwa, hc, one_mul]

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.eq_one_of_le_centralizer (hF : E3Frame n R S t J u) {w : Y}
    (h1 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤
      Subgroup.centralizer ({w} : Set Y))
    (h2 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
      Subgroup.centralizer ({w} : Set Y)) : w = 1 := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hFam := hF.graphFam
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hF.large.cls.2.1
  have hY := hF.lemma1710.generate hgen g (by rw [hgJ]; exact mem_orbOf_self _ _)
  have hπ : conjSub g '' orbOf (TC.nbrAdj Ω) (tightCore R) J =
      orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    have h1 := isMaxOrb_conj hFam hF.maxAdj.2 g
    rw [hgJ] at h1
    exact maxOrb_unique hFam hJn.1 h1 (orbOf_mem_maxOrbs hFam hF.maxAdj.1 hF.maxAdj.2)
  have htop : (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({w} : Set Y) := by
    rw [← hY]
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | hM
    · exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) (tightCore R) J) => N)
        M hM).trans h1
    · rw [hπ] at hM
      exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N)
        M hM).trans h2
  have hwZ : w ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top y))
  rw [hF.large.center] at hwZ
  exact hwZ

theorem E3Frame.orbGen_core_le_centralizer (hF : E3Frame n R S t J u) :
    E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤
      Subgroup.centralizer ({t} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hNt : nbrGen (TC.nbrAdj Ω) (tightCore R) ≤ Subgroup.centralizer ({t} : Set Y) :=
    iSup₂_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM.2
      hd.isUniqueInvolution_core
  refine iSup₂_le fun M hM => ?_
  obtain ⟨l, hl, rfl⟩ := hM
  have hlK : conjSub l (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core (hNt hl))
  have h1 := omegaNbr_conj hc hF.maxAdj.1.2 l
  rw [hlK] at h1
  exact hF.le_centralizer_of_mem_omegaNbr hK₀Ω h1 hd.isUniqueInvolution_core

theorem E3Frame.oddCoreOf_orbGen_core_le (hF : E3Frame n R S t J u) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) ≤
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  have hle := hF.orbGen_core_le_centralizer
  have hn : ((E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J).subgroupOf
      (Subgroup.centralizer ({t} : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc =>
      mem_normalizer_of_conjSub_eq (hF.conjSub_orbGen_core hc)
  exact Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_normal_subgroupOf hle hn)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
