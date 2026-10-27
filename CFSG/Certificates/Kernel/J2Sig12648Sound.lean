module

public import Certificates.Data.Kernel.J2Sig12648
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
import CFSG.Certificates.Kernel.Misc.ArrEnumOps

public section

namespace CFSG.KC.J2Sig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.ConjRec
open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.Monster.B.Mathieu

@[expose] def PR (p : ℕ) (g : GJ) : Prop :=
  permB 315 9 p = true ∧ CFSG.Monster.B.Co2.Rep 315 (unpack 315 9 p) g.1

theorem hw9 : szOK 315 9 = true := by decide

theorem PR_mul {p q : ℕ} {g h : GJ} (hp : PR p g) (hq : PR q h) : PR (m9 p q) (g * h) := by
  refine ⟨permB_pcomp hw9 hp.1 hq.1, ?_⟩
  change CFSG.Monster.B.Co2.Rep 315 (unpack 315 9 (pcomp 315 9 (mask 9) p q)) (g * h).1
  rw [← comp_unpack hw9 hp.1 hq.1]
  exact CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.rep_mul hp.2 hq.2

theorem PR_beq {p q : ℕ} {g h : GJ} (hp : PR p g) (hq : PR q h) : Nat.beq p q = true ↔ g = h := by
  rw [← eqA_unpack hw9 hp.1 hq.1]
  exact ⟨fun e => CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.eq_of_rep hp.2 hq.2 e,
    fun e => (CFSG.Monster.B.Co2.eqA_iff hp.2 hq.2).2 (by rw [e])⟩

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bIf_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp_all

theorem p40_spec {I p : ℕ} {g : GJ} (hI : PR I 1) (hp : PR p g) (h : g ^ 40 = 1) :
    p40 I p = true := by
  unfold p40
  simp only [strictB_eq']
  have h2 : PR (m9 p p) (g ^ 2) := by
    have := PR_mul hp hp
    rwa [← pow_two] at this
  have h4 : PR (m9 (m9 p p) (m9 p p)) (g ^ 4) := by
    have := PR_mul h2 h2
    rwa [← pow_add] at this
  have h5 : PR (m9 (m9 (m9 p p) (m9 p p)) p) (g ^ 5) := by
    have := PR_mul h4 hp
    rwa [← pow_succ] at this
  have h10 := PR_mul h5 h5
  rw [← pow_add] at h10
  have h20 := PR_mul h10 h10
  rw [← pow_add] at h20
  have h40 := PR_mul h20 h20
  rw [← pow_add] at h40
  exact (PR_beq h40 hI).2 h

theorem p4_true {I p : ℕ} {g : GJ} (hI : PR I 1) (hp : PR p g) (h : g ^ 4 = 1) :
    p4 I p = true := by
  unfold p4
  simp only [strictB_eq']
  have h2 : PR (m9 p p) (g ^ 2) := by
    have := PR_mul hp hp
    rwa [← pow_two] at this
  have h4 := PR_mul h2 h2
  rw [← pow_add] at h4
  exact (PR_beq h4 hI).2 h

theorem inVs_spec {V : ℕ → ℕ} {T : ℕ → GJ} {lo p : ℕ} {g : GJ} (hp : PR p g) :
    ∀ {cnt : ℕ}, (∀ j < cnt, PR (V (lo + j)) (T (lo + j))) → inVs V lo cnt p = true →
      ∃ j < cnt, g = T (lo + j)
  | 0, _, h => by simp [inVs] at h
  | cnt + 1, hV, h => by
    change Bool.rec (motive := fun _ => Bool) (inVs V lo cnt p) true
      (Nat.beq p (V (Nat.add lo cnt))) = true at h
    rcases bIf_true h with ⟨hc, -⟩ | ⟨-, he⟩
    · exact ⟨cnt, Nat.lt_succ_self _, (PR_beq hp (hV cnt (Nat.lt_succ_self _))).1 hc⟩
    · obtain ⟨j, hj, e⟩ := inVs_spec hp (fun j hj => hV j (by omega)) he
      exact ⟨j, by omega, e⟩

theorem wst_spec {L0 L1 L2 a d : ℕ} {g0 g1 g2 v : GJ} {H : Subgroup GJ}
    (h0 : PR L0 g0) (h1 : PR L1 g1) (h2 : PR L2 g2) (hm0 : g0 ∈ H) (hm1 : g1 ∈ H) (hm2 : g2 ∈ H)
    (ha : PR a v) (hv : v ∈ H) : ∃ u ∈ H, PR (wst L0 L1 L2 a d) u := by
  unfold wst
  cases e0 : Nat.beq d 0
  · cases e1 : Nat.beq d 1
    · cases e2 : Nat.beq d 2
      · exact ⟨_, H.mul_mem hv hm2, PR_mul ha h2⟩
      · exact ⟨_, H.mul_mem hv hm1, PR_mul ha h1⟩
    · exact ⟨_, H.mul_mem hv hm0, PR_mul ha h0⟩
  · exact ⟨v, hv, ha⟩

theorem wval_spec {L0 L1 L2 I c : ℕ} {g0 g1 g2 : GJ} (hI : PR I 1) (h0 : PR L0 g0)
    (h1 : PR L1 g1) (h2 : PR L2 g2) :
    ∃ v ∈ Subgroup.closure ({g0, g1, g2} : Set GJ), PR (wval L0 L1 L2 I c) v := by
  set H := Subgroup.closure ({g0, g1, g2} : Set GJ)
  have hm0 : g0 ∈ H := Subgroup.subset_closure (by simp)
  have hm1 : g1 ∈ H := Subgroup.subset_closure (by simp)
  have hm2 : g2 ∈ H := Subgroup.subset_closure (by simp)
  unfold wval
  simp only [strictN_eq']
  obtain ⟨u1, hu1, p1⟩ := wst_spec (d := fldO c 0 2) h0 h1 h2 hm0 hm1 hm2 hI H.one_mem
  obtain ⟨u2, hu2, p2⟩ := wst_spec (d := fldO c 2 2) h0 h1 h2 hm0 hm1 hm2 p1 hu1
  obtain ⟨u3, hu3, p3⟩ := wst_spec (d := fldO c 4 2) h0 h1 h2 hm0 hm1 hm2 p2 hu2
  exact wst_spec (d := fldO c 6 2) h0 h1 h2 hm0 hm1 hm2 p3 hu3

theorem witK_spec {X XI X2 X2I I c p : ℕ} {x g : GJ} (hI : PR I 1) (hX : PR X x)
    (hXI : PR XI x⁻¹) (hX2 : PR X2 (x * x)) (hX2I : PR X2I (x * x)⁻¹) (hp : PR p g)
    (h : witK X XI X2 X2I I c p = true) :
    ∃ v ∈ Subgroup.closure ({g, x * g * x⁻¹, (x * x) * g * (x * x)⁻¹} : Set GJ), orderOf v = 3 := by
  have hL1 : PR (m9 X (m9 p XI)) (x * g * x⁻¹) := by
    rw [mul_assoc]
    exact PR_mul hX (PR_mul hp hXI)
  have hL2 : PR (m9 X2 (m9 p X2I)) ((x * x) * g * (x * x)⁻¹) := by
    rw [mul_assoc (x * x)]
    exact PR_mul hX2 (PR_mul hp hX2I)
  obtain ⟨v, hv, hpv⟩ := wval_spec (c := c) hI hp hL1 hL2
  refine ⟨v, hv, ?_⟩
  unfold witK at h
  rw [strictB_eq'] at h
  change Bool.rec (motive := fun _ => Bool) false _ _ = true at h
  cases e1 : Nat.beq (m9 (wval p (m9 X (m9 p XI)) (m9 X2 (m9 p X2I)) I c)
      (m9 (wval p (m9 X (m9 p XI)) (m9 X2 (m9 p X2I)) I c)
        (wval p (m9 X (m9 p XI)) (m9 X2 (m9 p X2I)) I c))) I
  · rw [e1] at h
    exact absurd h (by simp)
  · rw [e1] at h
    have h3 : v * (v * v) = 1 := (PR_beq (PR_mul hpv (PR_mul hpv hpv)) hI).1 e1
    have hne : v ≠ 1 := by
      intro hv1
      have := (PR_beq hpv hI).2 hv1
      rw [this] at h
      exact absurd h (by simp)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ hne
    rw [pow_three]
    exact h3

theorem zK_sound {X XI X2 X2I I W k p : ℕ} {V : ℕ → ℕ} {T : ℕ → GJ} {x g : GJ} (hI : PR I 1)
    (hX : PR X x) (hXI : PR XI x⁻¹) (hX2 : PR X2 (x * x)) (hX2I : PR X2I (x * x)⁻¹)
    (hV : ∀ j < 9, PR (V (9 + j)) (T (9 + j))) (hp : PR p g)
    (h : zK X XI X2 X2I I V W k p = true) (h40 : g ^ 40 = 1) :
    g = 1 ∨ (∃ j < 9, g = T (9 + j)) ∨
      ∃ v ∈ Subgroup.closure ({g, x * g * x⁻¹, (x * x) * g * (x * x)⁻¹} : Set GJ),
        orderOf v = 3 := by
  unfold zK at h
  rw [p40_spec hI hp h40] at h
  change Bool.rec (motive := fun _ => Bool) _ true (Nat.beq p I) = true at h
  cases e1 : Nat.beq p I
  · rw [e1] at h
    change Bool.rec (motive := fun _ => Bool) _ true (inVs V 9 9 p) = true at h
    cases e2 : inVs V 9 9 p
    · rw [e2] at h
      exact Or.inr (Or.inr (witK_spec hI hX hXI hX2 hX2I hp h))
    · exact Or.inr (Or.inl (inVs_spec hp hV e2))
  · exact Or.inl ((PR_beq hp hI).1 e1)

theorem wK_sound {I G GI lo c : ℕ} {V : ℕ → ℕ} {T : ℕ → GJ} {a h : GJ} (hI : PR I 1)
    (hG : PR G a) (hGI : PR GI a⁻¹) (hV : ∀ j < 3, PR (V (lo + j)) (T (lo + j))) (hc : PR c h)
    (hw : wK I G GI V lo c = true) (h4 : h ^ 4 = 1) :
    a * h * a⁻¹ = 1 ∨ ∃ j < 3, a * h * a⁻¹ = T (lo + j) := by
  unfold wK at hw
  rw [p4_true hI hc h4] at hw
  change strictB _ _ = true at hw
  rw [strictB_eq'] at hw
  have hh : PR (m9 G (m9 c GI)) (a * h * a⁻¹) := by
    rw [mul_assoc]
    exact PR_mul hG (PR_mul hc hGI)
  change Bool.rec (motive := fun _ => Bool) _ true (Nat.beq (m9 G (m9 c GI)) I) = true at hw
  cases e1 : Nat.beq (m9 G (m9 c GI)) I
  · rw [e1] at hw
    exact Or.inr (inVs_spec hh hV hw)
  · exact Or.inl ((PR_beq hh hI).1 e1)

end CFSG.KC.J2Sig
