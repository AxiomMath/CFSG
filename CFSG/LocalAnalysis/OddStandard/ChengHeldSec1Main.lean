module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Class
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupConj
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupZStar
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.Milestones.SG_two_signalizer_completeness
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open CFSG.OddStandard.ChengHeld.Model (kind0)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mem_of_card_gt {D N : Subgroup G} [Finite D] (F : Fin 4 → Set G)
    (hcov : ∀ x ∈ D, ∃ i, x ∈ F i) (hF : ∀ i, ∀ x ∈ F i, ∀ x' ∈ F i, x * x'⁻¹ ∈ N)
    (hcard : 4 < Nat.card D) : ∃ δ ∈ D, δ ≠ 1 ∧ δ ∈ N := by
  classical
  choose idx hidx using fun x : D => hcov x.1 x.2
  have : Fintype D := Fintype.ofFinite D
  have hlt : Fintype.card (Fin 4) < Fintype.card D := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨x₁, x₂, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt idx hlt
  refine ⟨x₁ * x₂⁻¹, D.mul_mem x₁.2 (D.inv_mem x₂.2), ?_, ?_⟩
  · intro h1
    exact hne (Subtype.ext (mul_inv_eq_one.1 h1))
  · exact hF (idx x₁) x₁ (hidx x₁) x₂ (h ▸ hidx x₂)

omit [Finite G] in
theorem exists_mem_of_card_gt4 {D N : Subgroup G} [Finite D] {F₀ F₁ F₂ F₃ : Set G}
    (hcov : ∀ x ∈ D, x ∈ F₀ ∨ x ∈ F₁ ∨ x ∈ F₂ ∨ x ∈ F₃)
    (h₀ : ∀ x ∈ F₀, ∀ x' ∈ F₀, x * x'⁻¹ ∈ N) (h₁ : ∀ x ∈ F₁, ∀ x' ∈ F₁, x * x'⁻¹ ∈ N)
    (h₂ : ∀ x ∈ F₂, ∀ x' ∈ F₂, x * x'⁻¹ ∈ N) (h₃ : ∀ x ∈ F₃, ∀ x' ∈ F₃, x * x'⁻¹ ∈ N)
    (hcard : 4 < Nat.card D) : ∃ δ ∈ D, δ ≠ 1 ∧ δ ∈ N := by
  refine exists_mem_of_card_gt (D := D) (N := N) ![F₀, F₁, F₂, F₃] ?_ ?_ hcard
  · intro x hx
    rcases hcov x hx with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃

omit [Finite G] in
theorem isConj_cj_self (a c : G) : IsConj a (cj a c) := isConj_iff.2 ⟨c⁻¹, by unfold cj; group⟩

omit [Finite G] in
theorem cj_z_tau {z p t : G} (hz2 : z * z = 1) (ht : cj t z = p * t) (hp : cj p z = p)
    (hpt : p * t = t * p) : cj z t = z * p := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have e1 : z * t * z = p * t := by
    have := ht
    unfold cj at this
    rwa [hzi] at this
  have e3 : z * t = p * t * z := by
    calc z * t = (z * t * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = p * t * z := by rw [e1]
  have e4 : p * z = z * p := by
    have := hp
    unfold cj at this
    rw [hzi] at this
    calc p * z = z * (z * p * z) := by rw [← mul_assoc, ← mul_assoc, hz2, one_mul]
      _ = z * p := by rw [this]
  have e5 : t⁻¹ * p * t = p := by
    calc t⁻¹ * p * t = t⁻¹ * (t * p) := by rw [mul_assoc, ← hpt, ← mul_assoc]
      _ = p := by group
  calc cj z t = t⁻¹ * (z * t) := by unfold cj; group
    _ = t⁻¹ * (p * t * z) := by rw [e3]
    _ = (t⁻¹ * p * t) * z := by group
    _ = p * z := by rw [e5]
    _ = z * p := e4

namespace Cfg

variable {A : Subgroup G} {d : Datum A} (K : Cfg d)

include K

local macro "dnorm " K:term : tactic =>
  `(tactic| simp only [mul_assoc, ($K).sort_pq, ($K).sort_tq, ($K).sort_tp, canc_q,
    ($K).canc_p, ($K).canc_t, ($K).pi_q, ($K).tau_q, ($K).tau_pi, q_mul_self,
    ($K).pi_sq, ($K).tau_sq, one_mul, mul_one])

theorem D_sq {x : G} (hx : x ∈ K.c.D) : x * x = 1 := by
  rcases K.D_cases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dnorm K

theorem three_class_pigeon {w v₁ v₂ v₃ : G} (hw : w ∈ d.X) (hwQS : w ∉ d.QS) (hw2 : w * w = 1)
    (hv₁ : ∃ s ∈ d.S, v₁ = s * w) (hv₂ : ∃ s ∈ d.S, v₂ = s * w) (hv₃ : ∃ s ∈ d.S, v₃ = s * w)
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₃ : v₃ * v₃ = 1)
    (n₁ : ¬ IsConj v₃ v₁) (n₂ : ¬ IsConj v₃ v₂) : IsConj v₁ v₂ := by
  have cl : ∀ v : G, (∃ s ∈ d.S, v = s * w) → v * v = 1 → IsConj v w ∨ IsConj v (d.q * w) := by
    intro v hv hv2
    obtain ⟨s, -, h⟩ := K.coset_classes hw hwQS hw2 hv hv2
    have hc : IsConj v (cj v s) := isConj_iff.2 ⟨s⁻¹, by unfold cj; group⟩
    rcases h with h | h
    · left; rwa [h] at hc
    · right; rwa [h] at hc
  rcases cl v₁ hv₁ h₁ with a | a <;> rcases cl v₂ hv₂ h₂ with b | b <;>
    rcases cl v₃ hv₃ h₃ with c | c
  · exact a.trans b.symm
  · exact a.trans b.symm
  · exact absurd (c.trans a.symm) n₁
  · exact absurd (c.trans b.symm) n₂
  · exact absurd (c.trans b.symm) n₂
  · exact absurd (c.trans a.symm) n₁
  · exact a.trans b.symm
  · exact a.trans b.symm

theorem excl_fu
    (hconj : ∀ k₀ : G, Nonempty (Cfg (d.conj k₀))) {k : Kind}
    (hk : k = Kind.field ∨ k = Kind.unitary) {z : G} (hzX : z ∈ d.X) (hz2 : z * z = 1)
    (hzq : IsConj d.q z)
    (hact : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) : False := by
  obtain ⟨k₀, hq', hX'⟩ := d.exists_conj_datum K.h hzq
  obtain ⟨K'⟩ := hconj k₀
  have hc : ∃ c ∈ d.S, cj c z = c ∧ c * c = K.c.pi := by
    rcases hk with rfl | rfl
    · refine ⟨K.c.mu * K.c.lam * K.c.xi,
        d.S.mul_mem (d.S.mul_mem K.mu_mem_S K.lam_mem_S) K.xi_mem_S, ?_, ?_⟩
      · have hS : K.c.mu * K.c.lam * K.c.xi ∈ d.S :=
          d.S.mul_mem (d.S.mul_mem K.mu_mem_S K.lam_mem_S) K.xi_mem_S
        exact (K.fixed_iff hzX hact hS).2 (mul_mem K.mulam_mem_fixedSub K.xi_mem_fixedSub)
      · have := K.sf.sq_mlx
        rwa [pow_two] at this
    · refine ⟨K.c.mu * K.c.lam * K.c.xi * K.c.tau,
        d.S.mul_mem (d.S.mul_mem (d.S.mul_mem K.mu_mem_S K.lam_mem_S) K.xi_mem_S) K.tau_mem_S,
        ?_, ?_⟩
      · have hS : K.c.mu * K.c.lam * K.c.xi * K.c.tau ∈ d.S :=
          d.S.mul_mem (d.S.mul_mem (d.S.mul_mem K.mu_mem_S K.lam_mem_S) K.xi_mem_S) K.tau_mem_S
        exact (K.fixed_iff hzX hact hS).2 K.c0_mem_fixedSub
      · have := K.c.sq_mlxt K.h K.hP K.hQ
        rwa [pow_two] at this
  obtain ⟨c, hcS, hcz, hcc⟩ := hc
  have hcomm : c * z = z * c := by
    have h1 : z⁻¹ * c * z = c := hcz
    calc c * z = z * (z⁻¹ * c * z) := by group
      _ = z * c := by rw [h1]
  have hcX' : c ∈ (d.conj k₀).X := hX' c (d.S_le_X hcS) hcomm
  have hπQS' : K.c.pi ∈ (d.conj k₀).QS := hcc ▸ K'.sq_mem_QS hcX'
  have hzQS' : z ∈ (d.conj k₀).QS := by
    have := (le_sup_right : (d.conj k₀).S ≤ (d.conj k₀).QS) K'.q_mem_S
    rwa [hq'] at this
  have hzπ : z * K.c.pi ∈ (d.conj k₀).QS := (d.conj k₀).QS.mul_mem hzQS' hπQS'
  have hne : z * K.c.pi ≠ (d.conj k₀).q := by
    rw [hq']
    intro h
    exact K.pi_ne_one (mul_eq_left.1 h)
  have hτ : cj K.c.tau z = K.c.pi * K.c.tau ∧ cj K.c.pi z = K.c.pi := by
    rcases hk with rfl | rfl <;> simp only [Kind.Act2] at hact <;> exact ⟨hact.2.2.1, hact.2.1⟩
  have hzτ := cj_z_tau hz2 hτ.1 hτ.2 K.pi_tau
  have hconj' : IsConj z (z * K.c.pi) := isConj_iff.2 ⟨K.c.tau⁻¹, by rw [← hzτ]; unfold cj; group⟩
  have := K'.iso hzπ hne
  rw [hq'] at this
  exact this hconj'

theorem g_conj : IsConj K.c.pi (d.q * K.c.pi * K.c.tau) ∧ IsConj K.c.tau (d.q * K.c.pi) ∧
    IsConj (d.q * K.c.tau) K.c.pi := by
  have hga := K.g_act
  simp only [GAct, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false] at hga
  obtain ⟨hgq, hgpi, hgtau, -⟩ := hga
  refine ⟨?_, ?_, ?_⟩
  · have := isConj_cj_self K.c.pi K.g
    rwa [hgpi, show K.c.tau * K.c.pi * d.q = d.q * K.c.pi * K.c.tau by dnorm K] at this
  · have := isConj_cj_self K.c.tau K.g
    rwa [hgtau, show K.c.pi * d.q = d.q * K.c.pi by dnorm K] at this
  · have := isConj_cj_self (d.q * K.c.tau) K.g
    rwa [cj_mul, hgq, hgtau, show d.q * (K.c.pi * d.q) = K.c.pi by dnorm K] at this

theorem graph_final {A' : Subgroup G} {d' : Datum A'} (K' : Cfg d') {z : G} (hz2 : z * z = 1)
    (hq' : d'.q = z) (hzq : IsConj d.q z) (hzQS : z ∉ d.QS)
    (hzc : ∀ x ∈ K.c.D, z * x = x * z) (hD' : ∀ x ∈ K.c.D, x ∈ d'.X)
    (o1 : IsConj z (K.c.pi * z)) (o2 : IsConj z (d.q * K.c.tau * z))
    (o3 : IsConj z (d.q * K.c.pi * K.c.tau * z)) : False := by
  have hqD := K.q_mem_D
  have hπD := K.pi_mem_D
  have hτD := K.tau_mem_D
  have hqπD : d.q * K.c.pi ∈ K.c.D := K.c.D.mul_mem hqD hπD
  have hqτD : d.q * K.c.tau ∈ K.c.D := K.c.D.mul_mem hqD hτD
  have hπτD : K.c.pi * K.c.tau ∈ K.c.D := K.c.D.mul_mem hπD hτD
  have hqπτD : d.q * K.c.pi * K.c.tau ∈ K.c.D := K.c.D.mul_mem hqπD hτD
  have hS'z : z ∈ d'.S := hq' ▸ K'.q_mem_S
  have hzN : z ∈ d'.QS := (le_sup_right : d'.S ≤ d'.QS) hS'z
  have hiso : ∀ x ∈ d'.QS, x ≠ z → ¬ IsConj z x := fun x hx hne => by
    have := K'.iso hx (by rw [hq']; exact hne)
    rwa [hq'] at this
  have involz : ∀ x ∈ K.c.D, (x * z) * (x * z) = 1 := fun x hx => by
    calc x * z * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hzc x hx]
      _ = (x * x) * (z * z) := by group
      _ = 1 := by rw [K.D_sq hx, hz2, one_mul]
  have notN : ∀ x ∈ K.c.D, x ≠ 1 → IsConj z (x * z) → x ∉ d'.QS := fun x hx hx1 hxz hxN =>
    hiso (x * z) (d'.QS.mul_mem hxN hzN) (fun h => hx1 (mul_eq_right.1 h)) hxz
  have hπN : K.c.pi ∉ d'.QS := notN _ hπD K.pi_ne_one o1
  have hqτN : d.q * K.c.tau ∉ d'.QS := notN _ hqτD K.q_tau_ne_one o2
  have hqπτN : d.q * K.c.pi * K.c.tau ∉ d'.QS := notN _ hqπτD K.q_pi_tau_ne_one o3
  have hqN : d.q ∉ d'.QS := fun h =>
    hiso _ h (fun h' => hzQS (h' ▸ (le_sup_right : d.S ≤ d.QS) K.q_mem_S)) hzq.symm
  obtain ⟨δ, hδD, hδ1, hδN⟩ := exists_mem_of_card_gt4 (D := K.c.D) (N := d'.QS)
    (F₀ := (d'.QS : Set G))
    (F₁ := {x | ∃ y, K'.c.rep Kind.field = some y ∧ ∃ u ∈ d'.QS, x = u * y})
    (F₂ := {x | ∃ y, K'.c.rep Kind.graph = some y ∧ ∃ u ∈ d'.QS, x = u * y})
    (F₃ := {x | ∃ y, K'.c.rep Kind.unitary = some y ∧ ∃ u ∈ d'.QS, x = u * y})
    (fun x hx => by
      by_cases hxN : x ∈ d'.QS
      · exact Or.inl hxN
      · obtain ⟨k, y, hk, u, hu, rfl⟩ := K'.c.cover x (hD' x hx) hxN
        cases k
        · exact Or.inr (Or.inl ⟨y, hk, u, hu, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨y, hk, u, hu, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨y, hk, u, hu, rfl⟩)))
    (fun x hx x' hx' => d'.QS.mul_mem hx (d'.QS.inv_mem hx'))
    (by
      rintro x ⟨y, hy, u, hu, rfl⟩ x' ⟨y', hy', u', hu', rfl⟩
      obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
      have : u * y * (u' * y)⁻¹ = u * u'⁻¹ := by group
      rw [this]; exact d'.QS.mul_mem hu (d'.QS.inv_mem hu'))
    (by
      rintro x ⟨y, hy, u, hu, rfl⟩ x' ⟨y', hy', u', hu', rfl⟩
      obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
      have : u * y * (u' * y)⁻¹ = u * u'⁻¹ := by group
      rw [this]; exact d'.QS.mul_mem hu (d'.QS.inv_mem hu'))
    (by
      rintro x ⟨y, hy, u, hu, rfl⟩ x' ⟨y', hy', u', hu', rfl⟩
      obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
      have : u * y * (u' * y)⁻¹ = u * u'⁻¹ := by group
      rw [this]; exact d'.QS.mul_mem hu (d'.QS.inv_mem hu'))
    (by rw [K.sf.card_D]; norm_num)
  have invS' : ∀ x ∈ d'.QS, x * x = 1 → x ∈ d'.S := fun x hx hx2 =>
    K'.c.involutions_in_S K'.h K'.sf K'.hc hx hx2
  obtain ⟨gA, gB, gC⟩ := K.g_conj
  have niso : ∀ x ∈ K.c.D, d.q * x ≠ 1 → ¬ IsConj d.q x := fun x hx hne =>
    K.iso ((le_sup_right : d.S ≤ d.QS) (K.D_le_S hx))
      (fun h => hne (by rw [h]; exact (q_mul_self d)))
  have n_t : ¬ IsConj d.q K.c.tau := niso _ hτD K.q_tau_ne_one
  have n_qp : ¬ IsConj d.q (d.q * K.c.pi) :=
    niso _ hqπD (by rw [(canc_q d)]; exact K.pi_ne_one)
  have n_qpt : ¬ IsConj d.q (d.q * K.c.pi * K.c.tau) :=
    niso _ hqπτD (by
      intro h
      apply K.pi_tau_ne_one
      calc K.c.pi * K.c.tau = d.q * (d.q * K.c.pi * K.c.tau) := by dnorm K
        _ = 1 := h)
  have n_qt : ¬ IsConj d.q (d.q * K.c.tau) := niso _ hqτD (by rw [(canc_q d)]; exact K.tau_ne_one)
  rcases K.D_cases hδD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hδ1 rfl
  · exact hqN hδN
  · exact hπN hδN
  ·
    have hδS : d.q * K.c.pi ∈ d'.S := invS' _ hδN (K.D_sq hqπD)
    have hτN : K.c.tau ∉ d'.QS := fun h => hqπτN (d'.QS.mul_mem hδN h)
    have hτX := hD' _ hτD
    have e : z * (d.q * K.c.pi) * K.c.tau = (d.q * K.c.pi * K.c.tau) * z := by
      rw [mul_assoc]; exact hzc _ hqπτD
    have hc3 : IsConj d.q (z * (d.q * K.c.pi) * K.c.tau) := by rw [e]; exact hzq.trans o3
    have hv := K'.three_class_pigeon (w := K.c.tau) (v₁ := K.c.tau)
      (v₂ := d.q * K.c.pi * K.c.tau) (v₃ := z * (d.q * K.c.pi) * K.c.tau) hτX hτN K.tau_sq
      ⟨1, one_mem _, (one_mul _).symm⟩ ⟨d.q * K.c.pi, hδS, rfl⟩
      ⟨z * (d.q * K.c.pi), d'.S.mul_mem hS'z hδS, rfl⟩
      K.tau_sq (K.D_sq hqπτD) (by rw [e]; exact involz _ hqπτD)
      (fun h => n_t (hc3.trans h)) (fun h => n_qpt (hc3.trans h))
    exact K.three_classes.2.2 (gA.trans (hv.symm.trans gB))
  ·
    have hδS : K.c.tau ∈ d'.S := invS' _ hδN K.tau_sq
    have hwN : d.q * K.c.pi ∉ d'.QS := fun h => hqπτN (d'.QS.mul_mem h hδN)
    have hwX := hD' _ hqπD
    have e : z * K.c.tau * (d.q * K.c.pi) = (d.q * K.c.pi * K.c.tau) * z := by
      calc z * K.c.tau * (d.q * K.c.pi) = z * (K.c.tau * (d.q * K.c.pi)) := by rw [mul_assoc]
        _ = (K.c.tau * (d.q * K.c.pi)) * z := hzc _ (K.c.D.mul_mem hτD hqπD)
        _ = (d.q * K.c.pi * K.c.tau) * z := by dnorm K
    have hc3 : IsConj d.q (z * K.c.tau * (d.q * K.c.pi)) := by rw [e]; exact hzq.trans o3
    have hv := K'.three_class_pigeon (w := d.q * K.c.pi) (v₁ := d.q * K.c.pi * K.c.tau)
      (v₂ := d.q * K.c.pi) (v₃ := z * K.c.tau * (d.q * K.c.pi)) hwX hwN (K.D_sq hqπD)
      ⟨K.c.tau, hδS, by dnorm K⟩ ⟨1, one_mem _, (one_mul _).symm⟩
      ⟨z * K.c.tau, d'.S.mul_mem hS'z hδS, rfl⟩
      (K.D_sq hqπτD) (K.D_sq hqπD) (by rw [e]; exact involz _ hqπτD)
      (fun h => n_qpt (hc3.trans h)) (fun h => n_qp (hc3.trans h))
    exact K.three_classes.2.2 (gA.trans hv)
  · exact hqτN hδN
  ·
    have hδS : K.c.pi * K.c.tau ∈ d'.S := invS' _ hδN (K.D_sq hπτD)
    have hwX := hD' _ hqτD
    have e : z * (d.q * K.c.tau) = (d.q * K.c.tau) * z := hzc _ hqτD
    have hc3 : IsConj d.q (z * (d.q * K.c.tau)) := by rw [e]; exact hzq.trans o2
    have hv := K'.three_class_pigeon (w := d.q * K.c.tau) (v₁ := d.q * K.c.tau)
      (v₂ := d.q * K.c.pi) (v₃ := z * (d.q * K.c.tau)) hwX hqτN (K.D_sq hqτD)
      ⟨1, one_mem _, (one_mul _).symm⟩ ⟨K.c.pi * K.c.tau, hδS, by dnorm K⟩
      ⟨z, hS'z, rfl⟩ (K.D_sq hqτD) (K.D_sq hqπD) (by rw [e]; exact involz _ hqτD)
      (fun h => n_qt (hc3.trans h)) (fun h => n_qp (hc3.trans h))
    exact K.three_classes.2.2 (gC.symm.trans hv)
  · exact hqπτN hδN

theorem excl_graph
    (hconj : ∀ k₀ : G, Nonempty (Cfg (d.conj k₀))) {z : G} (hzX : z ∈ d.X) (hz2 : z * z = 1)
    (hzq : IsConj d.q z) (hzQS : z ∉ d.QS)
    (hact : Kind.graph.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) : False := by
  obtain ⟨k₀, hq', hX'⟩ := d.exists_conj_datum K.h hzq
  obtain ⟨K'⟩ := hconj k₀
  have hA := K.c.autFactsG K.h K.hP K.hQ Kind.graph hzX hact
  have hDfix : K.c.D ≤ fixedSubG (kind0 Kind.graph) K.c.famG := by
    unfold fixedSubG kind0 Chart2.D
    simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
    apply Subgroup.closure_mono
    rintro x (rfl | rfl | rfl)
    · simp [Chart2.famG]
    · simp [Chart2.famG]
    · simp [Chart2.famG]
  have hDz : ∀ x ∈ K.c.D, cj x z = x := fun x hx =>
    (K.fixed_iff hzX hact (K.D_le_S hx)).2 (hDfix hx)
  have hzc : ∀ x ∈ K.c.D, z * x = x * z := fun x hx => by
    have h1 : z⁻¹ * x * z = x := hDz x hx
    have : x * z = z * x := by
      calc x * z = z * (z⁻¹ * x * z) := by group
        _ = z * x := by rw [h1]
    exact this.symm
  have hD' : ∀ x ∈ K.c.D, x ∈ (d.conj k₀).X := fun x hx =>
    hX' x (d.S_le_X (K.D_le_S hx)) (hzc x hx).symm
  obtain ⟨⟨s₁, -, e₁⟩, ⟨s₂, -, e₂⟩, ⟨s₃, -, e₃⟩⟩ := hA.graph_orbit hz2 rfl rfl
  have e₁' : s₁⁻¹ * z * s₁ = K.c.pi * z := e₁
  have e₂' : s₂⁻¹ * z * s₂ = d.q * K.c.tau * z := e₂
  have e₃' : s₃⁻¹ * z * s₃ = d.q * K.c.pi * K.c.tau * z := by
    rw [e₃]
    simp [Chart2.famG, mul_assoc]
  exact K.graph_final K' hz2 hq' hzq hzQS hzc hD'
    (isConj_iff.2 ⟨s₁⁻¹, by rw [inv_inv]; exact e₁'⟩)
    (isConj_iff.2 ⟨s₂⁻¹, by rw [inv_inv]; exact e₂'⟩)
    (isConj_iff.2 ⟨s₃⁻¹, by rw [inv_inv]; exact e₃'⟩)

theorem sec1_core (hconj : ∀ k₀ : G, Nonempty (Cfg (d.conj k₀))) : False := by
  obtain ⟨g₀, hg₀X, hg₀ne⟩ := d.exists_conj_ne K.h
  have hz₀conj : IsConj d.q (g₀⁻¹ * d.q * g₀) := isConj_iff.2 ⟨g₀⁻¹, by group⟩
  have hz₀QS : g₀⁻¹ * d.q * g₀ ∉ d.QS := fun h => K.iso h hg₀ne hz₀conj
  have hz₀2 : (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = 1 := by
    calc (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = g₀⁻¹ * (d.q * d.q) * g₀ := by group
      _ = 1 := by rw [(q_mul_self d)]; group
  obtain ⟨k, p, hp, hact⟩ := K.exists_pure_conj hg₀X hz₀QS hz₀2
  have hzX := cj_mem_X d hg₀X hp
  have hz2 : cj (g₀⁻¹ * d.q * g₀) p * cj (g₀⁻¹ * d.q * g₀) p = 1 := by
    rw [← cj_mul, hz₀2]; simp [cj]
  have hzq : IsConj d.q (cj (g₀⁻¹ * d.q * g₀) p) := hz₀conj.trans (isConj_cj_self _ p)
  have hzQS := cj_not_mem_QS d hz₀QS hp
  cases k
  · exact K.excl_fu hconj (Or.inl rfl) hzX hz2 hzq hact
  · exact K.excl_graph hconj hzX hz2 hzq hzQS hact
  · exact K.excl_fu hconj (Or.inr rfl) hzX hz2 hzq hact

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
