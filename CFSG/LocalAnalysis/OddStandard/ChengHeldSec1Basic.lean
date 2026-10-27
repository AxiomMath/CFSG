module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelDerived
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Goldschmidt75.WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Walter.J1
public import Certificates.Certificate8046
public import Certificates.Certificate8049

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem comm_eq_cm {a b : G} (ha : a * a = 1) (hb : b * b = 1) : ⁅a, b⁆ = cm a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  simp only [commutatorElement_def, cm, ha', hb']

structure Cfg (d : Datum A) where
  h : Hyp G A
  hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2
  c : Chart2 d
  g : G
  g_mem : g ∈ A
  g_norm : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S
  g_act : GAct 2 d.q c.pi c.tau c.mu c.lam c.ze c.xi g
  hP : chPresOK = true
  hQ : chPropsOK = true
  hCS : d.X ⊓ centralizer (d.S : Set G) ≤ c.D ⊔ d.Q
  hN : normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ d.X
  invol_conj : ∀ x y : ↥A ⧸ center ↥A, orderOf x = 2 → orderOf y = 2 → IsConj x y
  invol_card : ∀ x : ↥A ⧸ center ↥A, orderOf x = 2 →
    Nat.card {y : ↥A ⧸ center ↥A // IsConj x y} = 315

theorem q_mul_self (d : Datum A) : d.q * d.q = 1 := by
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])

theorem canc_q (d : Datum A) (x : G) :
    d.q * (d.q * x) = x := by rw [← mul_assoc, (q_mul_self d), one_mul]

theorem q_ne_one (d : Datum A) : d.q ≠ 1 := by
  intro h
  have := d.q_ord
  rw [h, orderOf_one] at this
  omega

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

theorem sf : K.c.SFacts := K.c.sFacts K.h K.hP K.hQ

theorem q_mem_S : d.q ∈ d.S := d.q_mem_S K.h

theorem pi_sq : K.c.pi * K.c.pi = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.1

theorem tau_sq : K.c.tau * K.c.tau = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.2.1

theorem mu_sq : K.c.mu * K.c.mu = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.2.2.1

theorem lam_sq : K.c.lam * K.c.lam = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.2.2.2.1

theorem ze_sq : K.c.ze * K.c.ze = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.2.2.2.2.1

theorem xi_sq : K.c.xi * K.c.xi = 1 := by rw [← pow_two]; exact K.c.frame.ord.2.2.2.2.2.2

theorem q_pi : d.q * K.c.pi = K.c.pi * d.q := K.c.frame.q_cent _ (by simp)

theorem q_tau : d.q * K.c.tau = K.c.tau * d.q := K.c.frame.q_cent _ (by simp)

theorem pi_tau : K.c.pi * K.c.tau = K.c.tau * K.c.pi := K.c.frame.R1 _ (by simp) _ (by simp)

theorem q_mem_D : d.q ∈ K.c.D := subset_closure (by simp)

theorem pi_mem_D : K.c.pi ∈ K.c.D := subset_closure (by simp)

theorem tau_mem_D : K.c.tau ∈ K.c.D := subset_closure (by simp)

theorem D_cases {v : G} (hv : v ∈ K.c.D) :
    v = 1 ∨ v = d.q ∨ v = K.c.pi ∨ v = d.q * K.c.pi ∨ v = K.c.tau ∨ v = d.q * K.c.tau ∨
      v = K.c.pi * K.c.tau ∨ v = d.q * K.c.pi * K.c.tau :=
  mem_closure_triple_invol (q_mul_self d) K.pi_sq K.tau_sq K.q_pi K.q_tau K.pi_tau hv

theorem mem_D_of (i j k : ℕ) : d.q ^ i * K.c.pi ^ j * K.c.tau ^ k ∈ K.c.D :=
  mul_mem (mul_mem (pow_mem K.q_mem_D i) (pow_mem K.pi_mem_D j)) (pow_mem K.tau_mem_D k)

theorem D_le_S : K.c.D ≤ d.S := K.sf.center ▸ inf_le_left

theorem D_central {x : G} (hx : x ∈ K.c.D) {s : G} (hs : s ∈ d.S) : s * x = x * s := by
  have : x ∈ d.S ⊓ centralizer (d.S : Set G) := K.sf.center ▸ hx
  exact mem_centralizer_iff.1 this.2 s hs

theorem mem_D_of_central {x : G} (hx : x ∈ d.S) (hc : ∀ s ∈ d.S, s * x = x * s) : x ∈ K.c.D := by
  have : x ∈ d.S ⊓ centralizer (d.S : Set G) := ⟨hx, mem_centralizer_iff.2 hc⟩
  exact K.sf.center ▸ this

theorem D_comm {x y : G} (hx : x ∈ K.c.D) (hy : y ∈ K.c.D) : x * y = y * x :=
  K.D_central hy (K.D_le_S hx)

theorem D_inj : Function.Injective
    (fun v : Fin 2 × Fin 2 × Fin 2 =>
      d.q ^ (v.1 : ℕ) * K.c.pi ^ (v.2.1 : ℕ) * K.c.tau ^ (v.2.2 : ℕ)) := by
  let f : Fin 2 × Fin 2 × Fin 2 → K.c.D := fun v =>
    ⟨d.q ^ (v.1 : ℕ) * K.c.pi ^ (v.2.1 : ℕ) * K.c.tau ^ (v.2.2 : ℕ), K.mem_D_of _ _ _⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rcases K.D_cases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 0, 0), Subtype.ext (by simp [f])⟩
    · exact ⟨(1, 0, 0), Subtype.ext (by simp [f])⟩
    · exact ⟨(0, 1, 0), Subtype.ext (by simp [f])⟩
    · exact ⟨(1, 1, 0), Subtype.ext (by simp [f])⟩
    · exact ⟨(0, 0, 1), Subtype.ext (by simp [f])⟩
    · exact ⟨(1, 0, 1), Subtype.ext (by simp [f])⟩
    · exact ⟨(0, 1, 1), Subtype.ext (by simp [f])⟩
    · exact ⟨(1, 1, 1), Subtype.ext (by simp [f])⟩
  have hcard : Nat.card (Fin 2 × Fin 2 × Fin 2) ≤ Nat.card K.c.D := by
    rw [K.sf.card_D]
    simp
  have hbij := hsurj.bijective_of_nat_card_le hcard
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

theorem cj_D_QS {u : G} (hu : u ∈ d.QS) {e : G} (he : e ∈ K.c.D) : cj e u = e := by
  obtain ⟨a, ha, s, hs, rfl⟩ := d.mem_QS_iff.1 hu
  have h1 : e * a = a * e :=
    mem_centralizer_iff.1 (d.Q_le_centralizer_S ha) e (K.D_le_S he)
  have h2 : e * s = s * e := (K.D_central he hs).symm
  rw [← cj_cj, cj_of_commute (show Commute e a from h1), cj_of_commute (show Commute e s from h2)]

theorem cj_D_QS_mul {u : G} (hu : u ∈ d.QS) (y : G) {e : G} (he : e ∈ K.c.D) :
    cj e (u * y) = cj e y := by
  rw [← cj_cj, K.cj_D_QS hu he]

theorem act_D {x : G} (hx : x ∈ d.X) :
    cj d.q x = d.q ∧ cj K.c.pi x = K.c.pi ∧
      (cj K.c.tau x = K.c.tau ∨ cj K.c.tau x = K.c.pi * K.c.tau) := by
  by_cases hQS : x ∈ d.QS
  · exact ⟨K.cj_D_QS hQS K.q_mem_D, K.cj_D_QS hQS K.pi_mem_D,
      Or.inl (K.cj_D_QS hQS K.tau_mem_D)⟩
  · obtain ⟨k, y, hk, u, hu, rfl⟩ := K.c.cover x hx hQS
    have hact := (K.c.rep_mem k y hk).2.2
    rw [K.cj_D_QS_mul hu y K.q_mem_D, K.cj_D_QS_mul hu y K.pi_mem_D,
      K.cj_D_QS_mul hu y K.tau_mem_D]
    cases k <;> simp only [Kind.Act2] at hact
    · exact ⟨hact.1, hact.2.1, Or.inr hact.2.2.1⟩
    · exact ⟨hact.1, hact.2.1, Or.inl hact.2.2.1⟩
    · exact ⟨hact.1, hact.2.1, Or.inr hact.2.2.1⟩

theorem sq_pure_mem_QS {k : Kind} {y : G} (hk : K.c.rep k = some y) : y * y ∈ d.QS := by
  obtain ⟨hyX, -, hact⟩ := K.c.rep_mem k y hk
  have hA := K.c.autFactsG K.h K.hP K.hQ k hyX hact
  have hcomm : ∀ s ∈ d.S, s * (y * y) = (y * y) * s := by
    intro s hs
    have h1 := hA.invol s hs
    calc s * (y * y) = (y * y) * (y⁻¹ * (y⁻¹ * s * y) * y) := by group
      _ = (y * y) * s := by rw [h1]
  have hmem : y * y ∈ d.X ⊓ centralizer (d.S : Set G) :=
    ⟨d.X.mul_mem hyX hyX, mem_centralizer_iff.2 hcomm⟩
  have hle : K.c.D ⊔ d.Q ≤ d.QS := sup_le (K.D_le_S.trans le_sup_right) le_sup_left
  exact hle (K.hCS hmem)

theorem sq_mem_QS {x : G} (hx : x ∈ d.X) : x * x ∈ d.QS := by
  by_cases hQS : x ∈ d.QS
  · exact d.QS.mul_mem hQS hQS
  · obtain ⟨k, y, hk, u, hu, rfl⟩ := K.c.cover x hx hQS
    have hyX := (K.c.rep_mem k y hk).1
    have h1 : y * u * y⁻¹ ∈ d.QS := by
      have := ChartShape.conj_inv_mem_QS d (d.X.inv_mem hyX) hu
      simpa using this
    have e : u * y * (u * y) = u * (y * u * y⁻¹) * (y * y) := by group
    rw [e]
    exact d.QS.mul_mem (d.QS.mul_mem hu h1) (K.sq_pure_mem_QS hk)

theorem sort_pq (x : G) : K.c.pi * (d.q * x) = d.q * (K.c.pi * x) := by
  rw [← mul_assoc, ← K.q_pi, mul_assoc]

theorem sort_tq (x : G) : K.c.tau * (d.q * x) = d.q * (K.c.tau * x) := by
  rw [← mul_assoc, ← K.q_tau, mul_assoc]

theorem sort_tp (x : G) : K.c.tau * (K.c.pi * x) = K.c.pi * (K.c.tau * x) := by
  rw [← mul_assoc, ← K.pi_tau, mul_assoc]

theorem canc_p (x : G) : K.c.pi * (K.c.pi * x) = x := by rw [← mul_assoc, K.pi_sq, one_mul]

theorem canc_t (x : G) : K.c.tau * (K.c.tau * x) = x := by rw [← mul_assoc, K.tau_sq, one_mul]

theorem pi_q : K.c.pi * d.q = d.q * K.c.pi := K.q_pi.symm

theorem tau_q : K.c.tau * d.q = d.q * K.c.tau := K.q_tau.symm

theorem tau_pi : K.c.tau * K.c.pi = K.c.pi * K.c.tau := K.pi_tau.symm

local macro "dnorm " K:term : tactic =>
  `(tactic| simp only [mul_assoc, ($K).sort_pq, ($K).sort_tq, ($K).sort_tp, canc_q,
    ($K).canc_p, ($K).canc_t, ($K).pi_q, ($K).tau_q, ($K).tau_pi, q_mul_self,
    ($K).pi_sq, ($K).tau_sq, one_mul, mul_one])

theorem D_ne_one {i j k : Fin 2} (hne : (i, j, k) ≠ (0, 0, 0)) :
    d.q ^ (i : ℕ) * K.c.pi ^ (j : ℕ) * K.c.tau ^ (k : ℕ) ≠ 1 := by
  intro h
  have h1 : d.q ^ ((0 : Fin 2) : ℕ) * K.c.pi ^ ((0 : Fin 2) : ℕ) *
      K.c.tau ^ ((0 : Fin 2) : ℕ) = 1 := by
    simp
  exact hne (K.D_inj (a₁ := (i, j, k)) (a₂ := (0, 0, 0)) (by simpa using h.trans h1.symm))

theorem pi_ne_one : K.c.pi ≠ 1 := by simpa using K.D_ne_one (i := 0) (j := 1) (k := 0) (by decide)

theorem tau_ne_one : K.c.tau ≠ 1 := by simpa using K.D_ne_one (i := 0) (j := 0) (k := 1) (by decide)

theorem q_pi_ne_one : d.q * K.c.pi ≠ 1 := by
  simpa using K.D_ne_one (i := 1) (j := 1) (k := 0) (by decide)

theorem q_tau_ne_one : d.q * K.c.tau ≠ 1 := by
  simpa using K.D_ne_one (i := 1) (j := 0) (k := 1) (by decide)

theorem pi_tau_ne_one : K.c.pi * K.c.tau ≠ 1 := by
  simpa using K.D_ne_one (i := 0) (j := 1) (k := 1) (by decide)

theorem q_pi_tau_ne_one : d.q * K.c.pi * K.c.tau ≠ 1 := by
  simpa using K.D_ne_one (i := 1) (j := 1) (k := 1) (by decide)

theorem pi_mem_S : K.c.pi ∈ d.S := K.c.mem.1

theorem tau_mem_S : K.c.tau ∈ d.S := K.c.mem.2.1

theorem mu_mem_S : K.c.mu ∈ d.S := K.c.mem.2.2.1

theorem lam_mem_S : K.c.lam ∈ d.S := K.c.mem.2.2.2.1

theorem ze_mem_S : K.c.ze ∈ d.S := K.c.mem.2.2.2.2.1

theorem xi_mem_S : K.c.xi ∈ d.S := K.c.mem.2.2.2.2.2.1

theorem comm_mem_D {a b : G} (ha : a ∈ d.S) (hb : b ∈ d.S) : ⁅a, b⁆ ∈ K.c.D := by
  rw [← K.sf.derived]
  exact commutator_mem_commutator ha hb

theorem comm_mul_left {a b c : G} (ha : a ∈ d.S) (hb : b ∈ d.S) (hc : c ∈ d.S) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left' a b c]
  have h1 : a * ⁅b, c⁆ = ⁅b, c⁆ * a := K.D_central (K.comm_mem_D hb hc) ha
  have h2 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2]
  exact K.D_comm (K.comm_mem_D hb hc) (K.comm_mem_D ha hc)

theorem not_mem_D_of_comm {x s : G} (hs : s ∈ d.S) (h : ⁅x, s⁆ ≠ 1) : x ∉ K.c.D := by
  intro hD
  apply h
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (K.D_central hD hs).symm

theorem comm_mu_xi : ⁅K.c.mu, K.c.xi⁆ = K.c.pi * K.c.tau := by
  rw [comm_eq_cm K.mu_sq K.xi_sq]; exact K.c.frame.mu_xi

theorem comm_lam_xi : ⁅K.c.lam, K.c.xi⁆ = K.c.tau := by
  rw [comm_eq_cm K.lam_sq K.xi_sq]; exact K.c.frame.lam_xi

theorem comm_mu_ze : ⁅K.c.mu, K.c.ze⁆ = d.q * K.c.pi := by
  rw [comm_eq_cm K.mu_sq K.ze_sq]; exact K.c.frame.mu_ze

theorem comm_lam_ze : ⁅K.c.lam, K.c.ze⁆ = d.q * K.c.pi * K.c.tau := by
  rw [comm_eq_cm K.lam_sq K.ze_sq]; exact K.c.frame.lam_ze

theorem mu_lam : K.c.mu * K.c.lam = K.c.lam * K.c.mu :=
  K.c.frame.R1 _ (by simp) _ (by simp)

theorem ze_xi : K.c.ze * K.c.xi = K.c.xi * K.c.ze :=
  K.c.frame.R2 _ (by simp) _ (by simp)

theorem comm_mu_lam : ⁅K.c.mu, K.c.lam⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 K.mu_lam

theorem comm_ze_xi : ⁅K.c.ze, K.c.xi⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 K.ze_xi

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
