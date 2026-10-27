module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs9
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem normalizer_ne_top9 (hC : Ctx9 G z k S M p) {X : Subgroup G} (hX : X ≠ ⊥) (hXM : X ≤ M) :
    normalizer (X : Set G) ≠ ⊤ := by
  intro htop
  have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hsimple : IsSimpleGroup G := hC.simple
  rcases (haveI := hXn; hsimple.eq_bot_or_eq_top_of_normal X) with h | h
  · exact hX h
  · have : (⊤ : Subgroup G) ≤ M := h ▸ hXM
    exact hC.coatom.1 (top_le_iff.mp this)

theorem exists_coatom9 (hC : Ctx9 G z k S M p) {X : Subgroup G} (hX : X ≠ ⊥) (hXM : X ≤ M) :
    ∃ N : Subgroup G, IsCoatom N ∧ normalizer (X : Set G) ≤ N := by
  rcases eq_top_or_exists_le_coatom (normalizer (X : Set G)) with h | h
  · exact absurd h (normalizer_ne_top9 hC hX hXM)
  · exact h

theorem commutator_eq_self_of_card_inverts {X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Nat.card ↥X = p) (hinv : Inverts z X) : ⁅X, zpowers z⁆ = X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haX, ha1⟩ : ∃ a ∈ X, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : X = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hno x hx)
    rw [this, Subgroup.card_bot] at hX
    exact hp.one_lt.ne hX
  have hap : a ^ p = 1 := by
    have h1 : orderOf (⟨a, haX⟩ : ↥X) ∣ Nat.card ↥X := orderOf_dvd_natCard _
    rw [hX] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hXeq : zpowers a = X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haX) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hap ha1, hX]
  have hza : z * a * z⁻¹ = a⁻¹ := hinv a haX
  rw [← hXeq]
  exact commutator_zpowers_eq_of_inverts hp hp2 hap hza

theorem nn_commutator_QP (h94 : Prop9_4) (hC : Ctx9 G z k S M p) {Q : Subgroup G}
    (hQ : QP z p (Op p M) Q) : NN z p (Op p M) ⁅Q, zpowers z⁆ := by
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op' p M) hQ
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hQp : IsPGroup p ↥Q := hC.P_pgroup.to_le hQ.1
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  have hR0 : ⁅Q, zpowers z⁆ ≠ ⊥ := fun h => hQ.2.2.2.2.2 (commutator_zpowers_eq_bot_iff.mp h)
  have hRC : Cen z ≤ normalizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
    le_normalizer_commutator_zpowers (hQn (hC.cen_le hc)) hc
  have hRc : ⁅⁅Q, zpowers z⁆, zpowers z⁆ = ⁅Q, zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hC.prime hC.odd hQp hzQ
  exact h94 G z k S M p hC _ (hRQ.trans hQ.1) hR0 hRC hRc

end Basic

section Reductions

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem nn_of_Fs_eq (h512 : IG_5_12) (hC : Ctx9 G z k S M p) {X N : Subgroup G} (hXP : X ≤ Op p M)
    (hX0 : X ≠ ⊥) (hzX : z ∈ normalizer (X : Set G)) (hN : IsCoatom N)
    (hXN : normalizer (X : Set G) ≤ N) (hF : Fs N = Op p N) : NN z p (Op p M) X := by
  have hNN : NN z p ⊤ X := by
    by_contra hnot
    exact lemma_9_1 h512 G z p hC.prime N X hN (hC.P_pgroup.to_le hXP) hX0 hzX hXN hnot hF
  exact ⟨hXP, hX0, hzX, hNN.2.2.2⟩

theorem prop9_4_of (h19 : B_signalizer_19_9) (h512 : IG_5_12) : Prop9_4 := by
  intro G _ _ z k S M p hC X hXP hX0 hXC hXc
  have hp := hC.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzX : z ∈ normalizer (X : Set G) := hXC (mem_Cen_self z)
  have hXpg : IsPGroup p ↥X := hC.P_pgroup.to_le hXP
  obtain ⟨N, hN, hXN⟩ := exists_coatom9 hC hX0 (hXP.trans (Op_le' p M))
  have hNmem : N ∈ maximalOverCentralizer z := ⟨hN, hXC.trans hXN⟩
  obtain ⟨r, hr, hr2, hFr⟩ := hC.hyp N hNmem
  have hFN : Fs N = Op p N := by
    by_cases hrp : r = p
    · rw [← hrp]
      exact hFr
    · exfalso
      have hzN : z ∈ N := hXN hzX
      have hXNN : X ≤ N := le_trans Subgroup.le_normalizer hXN
      have hsig : Sig4Sub G z N p X :=
        ⟨hN.1, ⟨hp, hC.odd, hzN, hXNN, hXpg, hX0, fun c _ hc => hXC hc, hXc⟩⟩
      have h1 := (signalizer_sub h19 hC.orderOf_z hsig).1 r hr hr2 hrp
      have hxF : ∀ x ∈ X, x ∈ Op r N := by
        intro x hx
        have hxFm : x ∈ Fm N := by
          refine mem_Fm_of_centralizes_Fs (hXNN hx) ?_
          rw [hFr]
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp (h1 hx) y hy
        rw [← hFr]
        exact Fm_le_Fs N hxFm
      apply hX0
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨a, ha⟩ := exists_orderOf_pow_of_mem_Op hr (hxF x hx)
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hXpg) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hj
      have hcop : Nat.Coprime (r ^ a) (p ^ j) := ((Nat.coprime_primes hr hp).mpr hrp).pow a j
      have h2 : orderOf x ∣ Nat.gcd (r ^ a) (p ^ j) := Nat.dvd_gcd (ha ▸ dvd_rfl) (hj ▸ dvd_rfl)
      rw [hcop.gcd_eq_one] at h2
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)
  exact nn_of_Fs_eq h512 hC hXP hX0 hzX hN hXN hFN

theorem lemma9_16_of (h512 : IG_5_12) (h95 : Prop9_5) : Lemma9_16 := by
  intro G _ _ z k S M p hC Y Y₁ hYP hY0 hYz hYn hY₁ hY₁0 hY₁c hY₁N
  apply hYn
  have hY₁P : Y₁ ≤ Op p M := hY₁.trans inf_le_left
  have hY₁Y : Y₁ ≤ normalizer (Y : Set G) := hY₁.trans inf_le_right
  obtain ⟨N, hN, hYN⟩ := exists_coatom9 hC hY0 (hYP.trans (Op_le' p M))
  have hF : Fs N = Op p N :=
    h95 G z k S M p hC N Y₁ Y hN hY₁P hYP hY₁0 hY0 hY₁N.2.2.1 hYz hY₁c hY₁N hYN (hY₁Y.trans hYN)
  exact nn_of_Fs_eq h512 hC hYP hY0 hYz hN hYN hF

theorem prop9_11c_of (h512 : IG_5_12) (h : Prop9_11) : Prop9_11c := by
  intro G _ _ z k S M p hC V X hV hVe hV2 hv hXP hX0 hXc hVX
  have hzX : z ∈ normalizer (X : Set G) := hVX (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  obtain ⟨N, hN, hXN⟩ := exists_coatom9 hC hX0 (hXP.trans (Op_le' p M))
  have hVN : V ≤ N := (le_sup_left.trans hVX).trans hXN
  have hF : Fs N = Op p N :=
    h G z k S M p hC X V N hXP hX0 hzX hXc hN hXN
      (le_inf (le_inf (hV.trans inf_le_left) hVN) (hV.trans inf_le_right)) hVe hV2 hv
  exact nn_of_Fs_eq h512 hC hXP hX0 hzX hN hXN hF

omit [Finite G] in
theorem exists_minBad9 {M Q : Subgroup G} (hQ : QP z p (Op p M) Q)
    (h : ∃ X : Subgroup G, X ≤ Q ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧ ¬ NN z p (Op p M) X) :
    ∃ X : Subgroup G, MinBad9 z M p Q X := by
  classical
  let T : Subgroup G → Prop := fun X => X ≤ Q ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧ ¬ NN z p (Op p M) X
  have hex : ∃ n, ∃ X, T X ∧ Nat.card ↥X = n := by
    obtain ⟨X, hX⟩ := h
    exact ⟨_, X, hX, rfl⟩
  obtain ⟨X₀, hX₀, hX₀m⟩ := Nat.find_spec hex
  have hmin : ∀ Y, T Y → Nat.find hex ≤ Nat.card ↥Y := fun Y hY => Nat.find_min' hex ⟨Y, hY, rfl⟩
  by_cases hpref : ∃ Y, T Y ∧ Nat.card ↥Y = Nat.find hex ∧ ¬ Y ≤ Cen z
  · obtain ⟨Y, hY, hYm, hYc⟩ := hpref
    exact ⟨Y, hQ, hY.1, hY.2.1, hY.2.2.1, hY.2.2.2,
      fun W hWQ hW0 hWz hWN => hYm ▸ hmin W ⟨hWQ, hW0, hWz, hWN⟩, fun _ => hYc⟩
  · exact ⟨X₀, hQ, hX₀.1, hX₀.2.1, hX₀.2.2.1, hX₀.2.2.2,
      fun W hWQ hW0 hWz hWN => hX₀m ▸ hmin W ⟨hWQ, hW0, hWz, hWN⟩,
      fun ⟨Y, hYQ, hY0, hYz, hYN, hYc, hYnc⟩ =>
        absurd ⟨Y, ⟨hYQ, hY0, hYz, hYN⟩, hX₀m ▸ hYc, hYnc⟩ hpref⟩

end Reductions

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
