module

public import CFSG.GroupTheory.PCore.Defs
public import Mathlib.GroupTheory.FixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Walter.Cited.OddQuotient
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import Mathlib.GroupTheory.IsPerfect
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

section Elementary

theorem exists_mul_commute_of_odd {s y : G} (hs : s * s = 1)
    (hodd : Odd (orderOf (s * (y * s * y⁻¹)))) :
    ∃ v ∈ zpowers (s * (y * s * y⁻¹)), v * y * s = s * (v * y) := by
  set u := s * (y * s * y⁻¹) with hu
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hinv : s * u * s⁻¹ = u⁻¹ := by
    rw [hu, hsinv]
    calc s * (s * (y * s * y⁻¹)) * s = (s * s) * (y * s * y⁻¹) * s := by group
      _ = y * s * y⁻¹ * s := by rw [hs, one_mul]
      _ = y * s⁻¹ * y⁻¹ * s⁻¹ := by rw [hsinv]
      _ = (s * (y * s * y⁻¹))⁻¹ := by group
  obtain ⟨j, hj⟩ := hodd
  have hvv : u ^ (j + 1) * u ^ (j + 1) = u := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf u + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hsv : s * u ^ (j + 1) * s⁻¹ = (u ^ (j + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hvs : u ^ (j + 1) * s = s * (u ^ (j + 1))⁻¹ := by
    rw [← hsv, hsinv]
    calc u ^ (j + 1) * s = (s * s) * u ^ (j + 1) * s := by rw [hs, one_mul]
      _ = s * (s * u ^ (j + 1) * s) := by group
  have hys : y * s = s * u * y := by
    calc y * s = (s * s) * (y * s * y⁻¹) * y := by rw [hs]; group
      _ = s * u * y := by rw [hu]; group
  refine ⟨u ^ (j + 1), mem_zpowers_iff.2 ⟨((j + 1 : ℕ) : ℤ), zpow_natCast u (j + 1)⟩, ?_⟩
  calc u ^ (j + 1) * y * s = u ^ (j + 1) * (y * s) := by group
    _ = u ^ (j + 1) * s * u * y := by rw [hys]; group
    _ = s * (u ^ (j + 1))⁻¹ * (u ^ (j + 1) * u ^ (j + 1)) * y := by rw [hvs, hvv]
    _ = s * (u ^ (j + 1) * y) := by group

theorem conj_mul_mem_of_fixedPointFree {P U : Subgroup G} [Finite P] (hUP : U ≤ P)
    (hUn : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U) (hU : Odd (Nat.card U)) {s : G} (hs : s * s = 1)
    (hsP : ∀ p ∈ P, s * p * s⁻¹ ∈ P) (hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U)
    (hfix : ∀ c ∈ P, c * s = s * c → c ∈ U) :
    ∀ y ∈ P, s * y * s⁻¹ * y ∈ U := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hN : (U.subgroupOf P).Normal := ⟨fun n hn p => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hUn p p.2 n hn⟩
  let σ : P →* P :=
    { toFun := fun y => ⟨s * y * s⁻¹, hsP y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [coe_mul]; group }
  have hσ : ∀ y : P, ((σ y : P) : G) = s * y * s⁻¹ := fun _ => rfl
  have hσU : U.subgroupOf P ≤ (U.subgroupOf P).comap σ := fun n hn => by
    rw [mem_comap, mem_subgroupOf, hσ]
    exact hsU n (mem_subgroupOf.1 hn)
  let τ : P ⧸ U.subgroupOf P →* P ⧸ U.subgroupOf P :=
    QuotientGroup.map (U.subgroupOf P) (U.subgroupOf P) σ hσU
  have hτ : ∀ y : P, τ (y : P ⧸ U.subgroupOf P) = ((σ y : P) : P ⧸ U.subgroupOf P) :=
    fun _ => rfl
  have hσσ : ∀ y : P, σ (σ y) = y := fun y => by
    apply Subtype.ext
    rw [hσ, hσ, hsinv]
    calc s * (s * (y : G) * s) * s = (s * s) * (y : G) * (s * s) := by group
      _ = y := by rw [hs]; group
  have hinvol : Function.Involutive τ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hτ, hτ, hσσ]
  have hfpf : MonoidHom.FixedPointFree τ := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hτ, QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv, hσ] at hq
    have hu : s * ((y : G)⁻¹ * s * (y : G)⁻¹⁻¹) ∈ U := by
      have e : (s * (y : G) * s⁻¹)⁻¹ * y = s * ((y : G)⁻¹ * s⁻¹ * (y : G)⁻¹⁻¹) := by group
      rw [hsinv] at e hq
      rw [← e]; exact hq
    obtain ⟨v, hv, hvc⟩ := exists_mul_commute_of_odd hs
      (hU.of_dvd_nat (U.orderOf_dvd_natCard hu))
    have hvU : v ∈ U := (zpowers_le.2 hu) hv
    have hcU : v * (y : G)⁻¹ ∈ U := hfix _ (P.mul_mem (hUP hvU) (P.inv_mem y.2)) hvc
    have hyU : (y : G) ∈ U := by
      have := U.mul_mem (U.inv_mem hcU) hvU
      have e : (v * (y : G)⁻¹)⁻¹ * v = y := by group
      rwa [e] at this
    exact (QuotientGroup.eq_one_iff y).2 (mem_subgroupOf.2 hyU)
  have key := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinvol
  intro y hy
  have h1 := congrFun key ((⟨y, hy⟩ : P) : P ⧸ U.subgroupOf P)
  rw [hτ, ← QuotientGroup.mk_inv, QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv, coe_inv,
    hσ] at h1
  have h3 := hUn y⁻¹ (P.inv_mem hy) _ (U.inv_mem h1)
  have e : y⁻¹ * ((s * y * s⁻¹)⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ = s * y * s⁻¹ * y := by group
  rwa [e] at h3

private def sectionCentralizer (P U : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (P : Set G) ∧ g ∈ normalizer (U : Set G) ∧
    ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ U}
  mul_mem' := by
    rintro g h ⟨hgP, hgU, hg⟩ ⟨hhP, hhU, hh⟩
    refine ⟨mul_mem hgP hhP, mul_mem hgU hhU, fun y hy => ?_⟩
    have h1 := (mem_normalizer_iff.1 hgU _).1 (hh y hy)
    have := U.mul_mem h1 (hg y hy)
    have e : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) = g * h * y * (g * h)⁻¹ * y⁻¹ := by
      group
    rwa [e] at this
  one_mem' := ⟨one_mem _, one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgP, hgU, hg⟩
    refine ⟨inv_mem hgP, inv_mem hgU, fun y hy => ?_⟩
    have hz : g⁻¹ * y * g ∈ P := by
      have := (mem_normalizer_iff.1 (inv_mem hgP) y).1 hy
      rwa [inv_inv] at this
    have := U.inv_mem (hg _ hz)
    have e : (g * (g⁻¹ * y * g) * g⁻¹ * (g⁻¹ * y * g)⁻¹)⁻¹ = g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ := by group
    rwa [e] at this

private theorem mem_sectionCentralizer {P U : Subgroup G} {g : G} :
    g ∈ sectionCentralizer P U ↔ g ∈ normalizer (P : Set G) ∧ g ∈ normalizer (U : Set G) ∧
      ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ U :=
  Iff.rfl

theorem commute_of_conj_mul_inv_mem {P U : Subgroup G} (hUP : U ≤ P)
    (hUn : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U) (hP : Odd (Nat.card P)) {b : G} {k : ℕ}
    (hb : b ^ 2 ^ k = 1) (hbU : ∀ u ∈ U, b * u = u * b)
    (htriv : ∀ y ∈ P, b * y * b⁻¹ * y⁻¹ ∈ U) : ∀ y ∈ P, b * y = y * b := by
  intro y hy
  have hcU : y⁻¹ * (b * y * b⁻¹) ∈ U := by
    have := hUn y⁻¹ (P.inv_mem hy) _ (htriv y hy)
    have e : y⁻¹ * (b * y * b⁻¹ * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * (b * y * b⁻¹) := by group
    rwa [e] at this
  set c := y⁻¹ * (b * y * b⁻¹) with hc
  have hbc : Commute b c := hbU c hcU
  have hbyb : b * y * b⁻¹ = y * c := by rw [hc]; group
  have hiter : ∀ j : ℕ, b ^ j * y * (b ^ j)⁻¹ = y * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : b * c ^ j * b⁻¹ = c ^ j := by
        rw [(hbc.pow_right j).eq]; group
      calc b ^ (j + 1) * y * (b ^ (j + 1))⁻¹ = b * (b ^ j * y * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = b * (y * c ^ j) * b⁻¹ := by rw [ih]
        _ = (b * y * b⁻¹) * (b * c ^ j * b⁻¹) := by group
        _ = y * c ^ (j + 1) := by rw [hbyb, hcj, mul_assoc, ← pow_succ']
  have hc1 : c ^ 2 ^ k = 1 := by
    have h := hiter (2 ^ k)
    rw [hb, one_mul, inv_one, mul_one] at h
    exact mul_eq_left.mp h.symm
  have hc' : c = 1 := CFSG.Walter.Suzuki.eq_one_of_pow_two_pow_eq_one P hP (hUP hcU) hc1
  calc b * y = b * y * b⁻¹ * b := by group
    _ = y * b := by rw [hbyb, hc', mul_one]

end Elementary

theorem fitting_map_props [Finite G] {N : Subgroup G} [N.Normal] (hsolv : Group.IsSolvable N) :
    (fittingSubgroup N).map N.subtype ≤ N ∧
      Group.IsNilpotent ((fittingSubgroup N).map N.subtype) ∧
      ((fittingSubgroup N).map N.subtype).Normal ∧
      N ⊓ centralizer (((fittingSubgroup N).map N.subtype : Subgroup G) : Set G) ≤
        (fittingSubgroup N).map N.subtype := by
  refine ⟨map_subtype_le _, ?_, ⟨fun x hx g => ?_⟩, ?_⟩
  · exact Group.nilpotent_of_mulEquiv
      ((fittingSubgroup N).equivMapOfInjective N.subtype N.subtype_injective)
  · obtain ⟨z, hz, rfl⟩ := hx
    have h := characteristic_iff_map_eq.mp (fittingSubgroup_characteristic (G := N))
      (MulAut.conjNormal g)
    have hz' : (MulAut.conjNormal g).toMonoidHom z ∈
        (fittingSubgroup N).map (MulAut.conjNormal g).toMonoidHom := mem_map_of_mem _ hz
    rw [h] at hz'
    exact ⟨_, hz', by simp [MulAut.conjNormal_apply]⟩
  · rintro x ⟨hxN, hxC⟩
    have : (⟨x, hxN⟩ : N) ∈ centralizer (fittingSubgroup N : Set N) := by
      rw [mem_centralizer_iff]
      intro z hz
      exact Subtype.ext (mem_centralizer_iff.1 hxC _ ⟨z, hz, rfl⟩)
    exact ⟨_, centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv this, rfl⟩

theorem mem_centralizer_of_two_pow_eq_one_of_fitting [Finite G] {N F : Subgroup G} [hN : N.Normal]
    (hNodd : Odd (Nat.card N)) (hFN : F ≤ N) (hFnil : Group.IsNilpotent F) (hFn : F.Normal)
    (hCF : N ⊓ centralizer (F : Set G) ≤ F) {t : G} (ht : t * t = 1) {A B : Subgroup G}
    (hBA : B ≤ ⁅A, zpowers t⁆) (hAB : A ≤ normalizer (B : Set G))
    (htB : t ∈ normalizer (B : Set G))
    (hC : ∀ c ∈ N, c * t = t * c → c ∈ centralizer (B : Set G)) {b : G} (hb : b ∈ B) {k : ℕ}
    (hbk : b ^ 2 ^ k = 1) : b ∈ centralizer (N : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set S : Set G := {x | x ∈ B ∧ ∃ m : ℕ, x ^ 2 ^ m = 1} with hS
  have hSB : S ⊆ (B : Set G) := fun x hx => hx.1
  set U : Subgroup G := F ⊓ centralizer S with hU
  have hSconj : ∀ g ∈ normalizer (B : Set G), ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    rintro g hg x ⟨hxB, m, hm⟩
    exact ⟨(mem_normalizer_iff.1 hg x).1 hxB, m, by rw [conj_pow, hm, mul_one, mul_inv_cancel]⟩
  have hUconj : ∀ g ∈ normalizer (B : Set G), ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    refine ⟨hFn.conj_mem u hu.1 g, mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 := mem_centralizer_iff.1 hu.2 _ (hSconj g⁻¹ (inv_mem hg) x hx)
    calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * u * g⁻¹ * x := by group
  have hnorm : ∀ {H : Subgroup G} {g : G}, g ∈ normalizer (B : Set G) →
      (∀ g' ∈ normalizer (B : Set G), ∀ h ∈ H, g' * h * g'⁻¹ ∈ H) →
        g ∈ normalizer (H : Set G) := by
    intro H g hg hH
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hH g hg h, fun hh => ?_⟩
    have := hH g⁻¹ (inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this
  have hUnorm : ∀ g ∈ normalizer (B : Set G), g ∈ normalizer (U : Set G) :=
    fun g hg => hnorm hg hUconj
  set P : Subgroup G := F ⊓ normalizer (U : Set G) with hP
  have hUP : U ≤ P := fun u hu => ⟨hu.1, le_normalizer hu⟩
  have hUn : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U := fun p hp u hu =>
    (mem_normalizer_iff.1 hp.2 u).1 hu
  have hPconj : ∀ g ∈ normalizer (B : Set G), ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun g hg p hp =>
    mem_inf.2 ⟨hFn.conj_mem p (mem_inf.1 hp).1 g, (normalizer (U : Set G)).mul_mem
      ((normalizer (U : Set G)).mul_mem (hUnorm g hg) (mem_inf.1 hp).2)
      ((normalizer (U : Set G)).inv_mem (hUnorm g hg))⟩
  have hPnorm : ∀ g ∈ normalizer (B : Set G), g ∈ normalizer (P : Set G) :=
    fun g hg => hnorm hg hPconj
  have hPodd : Odd (Nat.card P) := hNodd.of_dvd_nat (card_dvd_of_le (inf_le_left.trans hFN))
  have hUodd : Odd (Nat.card U) := hPodd.of_dvd_nat (card_dvd_of_le hUP)
  have hCt : ∀ c ∈ F, c * t = t * c → c ∈ U := fun c hc hct =>
    ⟨hc, centralizer_le hSB (hC c (hFN hc) hct)⟩
  have hinv : ∀ a ∈ A, ∀ y ∈ P, a * t * a⁻¹ * y * (a * t * a⁻¹)⁻¹ * y ∈ U := by
    intro a ha
    have haB : a ∈ normalizer (B : Set G) := hAB ha
    have hsB : a * t * a⁻¹ ∈ normalizer (B : Set G) := mul_mem (mul_mem haB htB) (inv_mem haB)
    refine conj_mul_mem_of_fixedPointFree hUP hUn hUodd ?_ (hPconj _ hsB) (hUconj _ hsB) ?_
    · calc a * t * a⁻¹ * (a * t * a⁻¹) = a * (t * t) * a⁻¹ := by group
        _ = 1 := by rw [ht]; group
    · intro c hc hcs
      have hcF : a⁻¹ * c * a ∈ F := by
        have := hFn.conj_mem c hc.1 a⁻¹
        rwa [inv_inv] at this
      have hct : a⁻¹ * c * a * t = t * (a⁻¹ * c * a) := by
        calc a⁻¹ * c * a * t = a⁻¹ * (c * (a * t * a⁻¹)) * a := by group
          _ = a⁻¹ * ((a * t * a⁻¹) * c) * a := by rw [hcs]
          _ = t * (a⁻¹ * c * a) := by group
      have := hUconj a haB _ (hCt _ hcF hct)
      have e : a * (a⁻¹ * c * a) * a⁻¹ = c := by group
      rwa [e] at this
  have hinvt : ∀ y ∈ P, t * y * t⁻¹ * y ∈ U := by
    intro y hy
    have := hinv 1 (one_mem A) y hy
    simpa using this
  have hK : ⁅A, zpowers t⁆ ≤ sectionCentralizer P U := by
    rw [commutator_le]
    intro a ha g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
    have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, ht2, one_zpow, commutatorElement_one_right]
      exact one_mem _
    · rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]
      have haB : a ∈ normalizer (B : Set G) := hAB ha
      have hsB : a * t * a⁻¹ ∈ normalizer (B : Set G) := mul_mem (mul_mem haB htB) (inv_mem haB)
      have hcomm : ⁅a, t⁆ = a * t * a⁻¹ * t := by rw [commutatorElement_def, htinv]
      have hcB : ⁅a, t⁆ ∈ normalizer (B : Set G) := by
        rw [hcomm]; exact mul_mem hsB htB
      refine mem_sectionCentralizer.2 ⟨hPnorm _ hcB, hUnorm _ hcB, fun y hy => ?_⟩
      have h1 := hUconj _ hsB _ (hinvt y hy)
      have h2 := hinv a ha y⁻¹ (P.inv_mem hy)
      have := U.mul_mem h1 h2
      have e : a * t * a⁻¹ * (t * y * t⁻¹ * y) * (a * t * a⁻¹)⁻¹ *
          (a * t * a⁻¹ * y⁻¹ * (a * t * a⁻¹)⁻¹ * y⁻¹) = ⁅a, t⁆ * y * ⁅a, t⁆⁻¹ * y⁻¹ := by
        rw [hcomm]; group
      rwa [e] at this
  have hSP : ∀ x ∈ S, ∀ y ∈ P, x * y = y * x := by
    rintro x ⟨hxB, m, hm⟩ y hy
    have hxK := mem_sectionCentralizer.1 (hK (hBA hxB))
    exact commute_of_conj_mul_inv_mem hUP hUn hPodd hm
      (fun u hu => mem_centralizer_iff.1 hu.2 x ⟨hxB, m, hm⟩) hxK.2.2 y hy
  have hPU : P ≤ U := fun y hy => ⟨hy.1, mem_centralizer_iff.2 fun x hx => hSP x hx y hy⟩
  have hUF : F ≤ U := by
    by_contra hne
    have hlt : U.subgroupOf F < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne fun f hf => ?_
      have : (⟨f, hf⟩ : F) ∈ U.subgroupOf F := htop ▸ mem_top _
      exact mem_subgroupOf.1 this
    obtain ⟨x, hxN, hxU⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    apply hxU
    rw [mem_subgroupOf]
    refine hPU (mem_inf.2 ⟨x.2, ?_⟩)
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := (mem_normalizer_iff.1 hxN ⟨h, (inf_le_left : U ≤ F) hh⟩).1 (mem_subgroupOf.2 hh)
      rw [mem_subgroupOf] at this
      simpa using this
    · intro hh
      have hhF : h ∈ F := by
        have := F.mul_mem (F.mul_mem (F.inv_mem x.2) ((inf_le_left : U ≤ F) hh)) x.2
        have e : (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * x = h := by group
        rwa [e] at this
      have := (mem_normalizer_iff.1 hxN ⟨h, hhF⟩).2 (by rw [mem_subgroupOf]; simpa using hh)
      exact mem_subgroupOf.1 this
  have hbF : ∀ f ∈ F, b * f = f * b := fun f hf =>
    mem_centralizer_iff.1 (hUF hf).2 b ⟨hb, k, hbk⟩
  rw [mem_centralizer_iff]
  intro x hx
  have hyN : x * b * x⁻¹ * b⁻¹ ∈ N := by
    have := N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) b)
    have e : x * (b * x⁻¹ * b⁻¹) = x * b * x⁻¹ * b⁻¹ := by group
    rwa [e] at this
  have hyF : x * b * x⁻¹ * b⁻¹ ∈ F := by
    refine hCF ⟨hyN, mem_centralizer_iff.2 fun f hf => ?_⟩
    have hf' : x⁻¹ * f * x ∈ F := by
      have := hFn.conj_mem f hf x⁻¹
      rwa [inv_inv] at this
    have h1 := hbF _ hf'
    have h2 : f * b⁻¹ = b⁻¹ * f := ((Commute.inv_left (show Commute b f from hbF f hf)).eq).symm
    calc f * (x * b * x⁻¹ * b⁻¹) = x * ((x⁻¹ * f * x) * b) * x⁻¹ * b⁻¹ := by group
      _ = x * (b * (x⁻¹ * f * x)) * x⁻¹ * b⁻¹ := by rw [h1]
      _ = x * b * x⁻¹ * (f * b⁻¹) := by group
      _ = x * b * x⁻¹ * (b⁻¹ * f) := by rw [h2]
      _ = x * b * x⁻¹ * b⁻¹ * f := by group
  have hby : Commute (x * b * x⁻¹ * b⁻¹) b := (hbF _ hyF).symm
  have hy1 : (x * b * x⁻¹ * b⁻¹) ^ 2 ^ k = 1 := by
    have h1 : (x * b * x⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hbk, mul_one, mul_inv_cancel]
    have e : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
    rw [e, hby.mul_pow, hbk, mul_one] at h1
    exact h1
  have hy := CFSG.Walter.Suzuki.eq_one_of_pow_two_pow_eq_one N hNodd hyN hy1
  calc x * b = (x * b * x⁻¹ * b⁻¹) * b * x := by group
    _ = b * x := by rw [hy, one_mul]

theorem mem_centralizer_of_two_pow_eq_one [Finite G] {N : Subgroup G} [N.Normal]
    (hNodd : Odd (Nat.card N)) {t : G} (ht : t * t = 1) {A B : Subgroup G}
    (hBA : B ≤ ⁅A, zpowers t⁆) (hAB : A ≤ normalizer (B : Set G))
    (htB : t ∈ normalizer (B : Set G))
    (hC : ∀ c ∈ N, c * t = t * c → c ∈ centralizer (B : Set G)) {b : G} (hb : b ∈ B) {k : ℕ}
    (hbk : b ^ 2 ^ k = 1) : b ∈ centralizer (N : Set G) := by
  obtain ⟨hFN, hnil, hFn, hCF⟩ := fitting_map_props (N := N) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd)
  exact mem_centralizer_of_two_pow_eq_one_of_fitting hNodd hFN hnil hFn hCF ht hBA hAB htB hC hb
    hbk

theorem le_centralizer_of_le_closure [Finite G] {N : Subgroup G} [N.Normal]
    (hNodd : Odd (Nat.card N)) {t : G} (ht : t * t = 1) {A B : Subgroup G}
    (hBA : B ≤ ⁅A, zpowers t⁆) (hAB : A ≤ normalizer (B : Set G))
    (htB : t ∈ normalizer (B : Set G))
    (hC : ∀ c ∈ N, c * t = t * c → c ∈ centralizer (B : Set G))
    (hB2 : B ≤ closure {b : G | b ∈ B ∧ ∃ k : ℕ, b ^ 2 ^ k = 1}) :
    B ≤ centralizer (N : Set G) :=
  hB2.trans <| (closure_le _).2 fun _ hb =>
    mem_centralizer_of_two_pow_eq_one hNodd ht hBA hAB htB hC hb.1 hb.2.choose_spec

theorem commutator_oddCore_eq_bot [Finite G] {t : G} (ht : orderOf t = 2) {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (htB : t ∈ normalizer (B : Set G))
    (hBA : B ≤ ⁅A, zpowers t⁆) (hB2 : B ≤ closure {b : G | b ∈ B ∧ ∃ k : ℕ, b ^ 2 ^ k = 1})
    (hC : ⁅oddCore G ⊓ centralizer ({t} : Set G), B⁆ = ⊥) : ⁅oddCore G, B⁆ = ⊥ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hOodd : Odd (Nat.card (oddCore G)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  rw [commutator_eq_bot_iff_le_centralizer] at hC ⊢
  rw [← le_centralizer_iff]
  refine le_centralizer_of_le_closure hOodd htt hBA hAB htB (fun c hc hct => ?_) hB2
  exact hC ⟨hc, mem_centralizer_singleton_iff.2 hct⟩

theorem le_closure_two_pow_of_perfect [Finite G] {B : Subgroup G} (hB : ⁅B, B⁆ = B) :
    B ≤ closure {b : G | b ∈ B ∧ ∃ k : ℕ, b ^ 2 ^ k = 1} := by
  set T := closure {b : G | b ∈ B ∧ ∃ k : ℕ, b ^ 2 ^ k = 1} with hT
  have hconj : ∀ x ∈ T, ∀ g ∈ B, g * x * g⁻¹ ∈ T := by
    intro x hx g hg
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨hxB, m, hm⟩ := hx
      exact subset_closure ⟨B.mul_mem (B.mul_mem hg hxB) (B.inv_mem hg), m,
        by rw [conj_pow, hm, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := T.mul_mem hx hy
      have e : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      rwa [e] at this
    | inv x _ hx =>
      have := T.inv_mem hx
      have e : (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := by group
      rwa [e] at this
  have hTn : (T.subgroupOf B).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hconj _ hn _ g.2⟩
  have hQodd : Odd (Nat.card (B ⧸ T.subgroupOf B)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hxmT : ((x ^ m : B) : G) ∈ T := subset_closure ⟨(x ^ m).2, a, by
      rw [← coe_pow, ← pow_mul, mul_comm, ← hxm, pow_orderOf_eq_one, coe_one]⟩
    have h1 : (x : B ⧸ T.subgroupOf B) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hxmT
    have h2 : (x : B ⧸ T.subgroupOf B) ^ 2 = 1 := by
      rw [← hq]; exact pow_orderOf_eq_one _
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    rw [h1, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hsolv : Group.IsSolvable (B ⧸ T.subgroupOf B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
  have hperf : Group.IsPerfect B := isPerfect_iff.mpr hB
  have hsub : Subsingleton (B ⧸ T.subgroupOf B) := by
    rcases subsingleton_or_nontrivial (B ⧸ T.subgroupOf B) with h | h
    · exact h
    · exact absurd hsolv (Group.IsPerfect.not_isSolvable _)
  intro b hb
  have : ((⟨b, hb⟩ : B) : B ⧸ T.subgroupOf B) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at this
  exact this

end CFSG.SeitzReduction.F4Pilot
