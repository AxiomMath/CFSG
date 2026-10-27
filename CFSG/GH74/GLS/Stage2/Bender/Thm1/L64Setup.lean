module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem mem_normalizer_commutator {g : G} {P Q : Subgroup G} (hP : g ∈ normalizer (P : Set G))
    (hQ : g ∈ normalizer (Q : Set G)) : g ∈ normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hP, mem_normalizer_iff_map_conj_eq.mp hQ]

theorem le_normalizer_commutator {H P Q : Subgroup G} (hP : H ≤ normalizer (P : Set G))
    (hQ : H ≤ normalizer (Q : Set G)) : H ≤ normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_commutator (hP hg) (hQ hg)

theorem commutator_le_left_of_le_normalizer {X Y : Subgroup G} (hY : Y ≤ normalizer (X : Set G)) :
    ⁅X, Y⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [show ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) by rw [commutatorElement_def]; group]
  exact X.mul_mem hx ((mem_normalizer_iff.mp (hY hy) x⁻¹).mp (X.inv_mem hx))

theorem commutator_le_right_of_le_normalizer {X Y : Subgroup G} (hX : X ≤ normalizer (Y : Set G)) :
    ⁅X, Y⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [show ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ by rw [commutatorElement_def]]
  exact Y.mul_mem ((mem_normalizer_iff.mp (hX hx) y).mp hy) (Y.inv_mem hy)

theorem commutator_le_of_le {X Y K : Subgroup G} (hX : X ≤ K) (hY : Y ≤ K) : ⁅X, Y⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem (hX hx) (hY hy)) (K.inv_mem (hX hx))) (K.inv_mem (hY hy))

theorem le_commutator_sup_inf_centralizer {p : ℕ} (hp : p.Prime) {P R : Subgroup G} (hP : IsPGroup p ↥P)
    (hPR : P ≤ normalizer (R : Set G)) (hR : ¬ p ∣ Nat.card ↥R) :
    R ≤ ⁅R, P⁆ ⊔ R ⊓ centralizer (P : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := ⁅R, P⁆ with hK
  have hKR : K ≤ R := commutator_le_left_of_le_normalizer hPR
  have hPK : P ≤ normalizer (K : Set G) := le_normalizer_commutator hPR Subgroup.le_normalizer
  intro x hx
  let T : Type := {y : G // y * x⁻¹ ∈ K}
  have hmem : ∀ (a : ↥P) (y : T), (a : G) * y.1 * (a : G)⁻¹ * x⁻¹ ∈ K := by
    intro a y
    have hk : y.1 * x⁻¹ ∈ K := y.2
    have h1 : (a : G) * (y.1 * x⁻¹) * (a : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (hPK a.2) _).mp hk
    have h2 : ⁅(a : G), x⁆ ∈ K := by
      rw [hK, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator a.2 hx
    have h3 : (a : G) * y.1 * (a : G)⁻¹ * x⁻¹ =
        ((a : G) * (y.1 * x⁻¹) * (a : G)⁻¹) * ⁅(a : G), x⁆ := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact K.mul_mem h1 h2
  let act : MulAction ↥P T :=
    { smul := fun a y => ⟨(a : G) * y.1 * (a : G)⁻¹, hmem a y⟩
      one_smul := fun y => by
        apply Subtype.ext
        show ((1 : ↥P) : G) * y.1 * ((1 : ↥P) : G)⁻¹ = y.1
        simp
      mul_smul := fun a b y => by
        apply Subtype.ext
        show ((a * b : ↥P) : G) * y.1 * ((a * b : ↥P) : G)⁻¹ =
          (a : G) * ((b : G) * y.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc] }
  have hcardT : Nat.card T = Nat.card ↥K := by
    refine Nat.card_congr ⟨fun y => ⟨y.1 * x⁻¹, y.2⟩, fun k => ⟨k.1 * x, by simp⟩, ?_, ?_⟩
    · intro y; apply Subtype.ext; simp
    · intro k; apply Subtype.ext; simp
  have hndvd : ¬ p ∣ Nat.card T := by
    rw [hcardT]
    exact fun h => hR (h.trans (Subgroup.card_dvd_of_le hKR))
  obtain ⟨y, hy⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card T hndvd
  have hyP : y.1 ∈ centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ((⟨a, ha⟩ : ↥P) • y).1 = y.1 := by rw [hy ⟨a, ha⟩]
    have h2 : (a : G) * y.1 * (a : G)⁻¹ = y.1 := h1
    calc a * y.1 = (a * y.1 * a⁻¹) * a := by group
      _ = y.1 * a := by rw [h2]
  have hyR : y.1 ∈ R := by
    have h1 : y.1 = (y.1 * x⁻¹) * x := by group
    rw [h1]
    exact R.mul_mem (hKR y.2) hx
  have hx' : x = (y.1 * x⁻¹)⁻¹ * y.1 := by group
  rw [hx']
  exact Subgroup.mul_mem_sup (K.inv_mem y.2) ⟨hyR, hyP⟩

end Gen

section Disj

theorem disjoint_of_isPGroup_of_ne {X : Type} [Group X] [Finite X] {s t : ℕ} (hs : s.Prime) (ht : t.Prime)
    (hst : s ≠ t) {H K : Subgroup X} (hH : IsPGroup s ↥H) (hK : IsPGroup t ↥K) : Disjoint H K := by
  have : Fact s.Prime := ⟨hs⟩
  have : Fact t.Prime := ⟨ht⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hH
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hK
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [ha, hb]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hs ht).mpr hst)

end Disj

section Aut

variable {Y : Type} [Group Y]

theorem le_centralizer_of_coprime_relIndex {K Bb : Subgroup Y} (hBN : Bb ≤ normalizer (K : Set Y))
    (hcop : Nat.Coprime (Nat.card ↥Bb) ((centralizer (K : Set Y)).relIndex (normalizer (K : Set Y)))) :
    Bb ≤ centralizer (K : Set Y) := by
  set C : Subgroup ↥(normalizer (K : Set Y)) :=
    (centralizer (K : Set Y)).subgroupOf (normalizer (K : Set Y)) with hC
  set Bn : Subgroup ↥(normalizer (K : Set Y)) := Bb.subgroupOf (normalizer (K : Set Y)) with hBn
  have hCn : C.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer (K : Set Y)
  have h1 : C.relIndex Bn ∣ C.index := Subgroup.relIndex_dvd_index_of_normal C Bn
  have h2 : C.relIndex Bn ∣ Nat.card ↥Bn := Subgroup.index_dvd_card (C.subgroupOf Bn)
  have h3 : Nat.card ↥Bn ∣ Nat.card ↥Bb :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv).symm ▸ dvd_refl _
  have hcop' : Nat.Coprime (Nat.card ↥Bn) C.index := hcop.coprime_dvd_left h3
  have h4 : C.relIndex Bn = 1 := Nat.eq_one_of_dvd_coprimes hcop' h2 h1
  have h5 : Bn ≤ C := Subgroup.relIndex_eq_one.mp h4
  intro b hb
  exact h5 (show (⟨b, hBN hb⟩ : ↥(normalizer (K : Set Y))) ∈ Bn from hb)

theorem coprime_relIndex_of_alt {K : Subgroup Y} {n : ℕ} (hn : Odd n) (h3 : Nat.Coprime 3 n)
    (h : oddPart (AutOrd ⊤ K) ∣ 9 ∨ NormIso K (Equiv.Perm (Fin 4))) :
    Nat.Coprime n ((centralizer (K : Set Y)).relIndex (normalizer (K : Set Y))) := by
  have hn2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hn
  have hn3 : Nat.Coprime n 3 := h3.symm
  rcases h with h | ⟨_, ⟨e⟩⟩
  · have hA : AutOrd ⊤ K = (centralizer (K : Set Y)).relIndex (normalizer (K : Set Y)) := by
      simp [AutOrd]
    rw [← hA]
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self (AutOrd ⊤ K) 2
    have hodd : Nat.Coprime n (oddPart (AutOrd ⊤ K)) := by
      have h9 : Nat.Coprime n 9 := by
        have := Nat.Coprime.pow_right 2 hn3
        simpa using this
      exact Nat.Coprime.coprime_dvd_right h h9
    rw [← hsplit]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hn2) hodd
  · have h24 : (centralizer (K : Set Y)).relIndex (normalizer (K : Set Y)) = 24 := by
      show ((centralizer (K : Set Y)).subgroupOf (normalizer (K : Set Y))).index = 24
      rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h24]
    have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hn2) hn3

end Aut

section Down

variable {Y : Type} [Group Y]

theorem le_centralizer_commutator_of_map {Q R' P' B' : Subgroup Y} [Q.Normal] [R'.Normal]
    (hQR : Disjoint Q R')
    (h : B'.map (QuotientGroup.mk' Q) ≤
      centralizer ((⁅R'.map (QuotientGroup.mk' Q), P'.map (QuotientGroup.mk' Q)⁆ :
        Subgroup (Y ⧸ Q)) : Set (Y ⧸ Q))) :
    B' ≤ centralizer ((⁅R', P'⁆ : Subgroup Y) : Set Y) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hπw : QuotientGroup.mk' Q w ∈
      ⁅R'.map (QuotientGroup.mk' Q), P'.map (QuotientGroup.mk' Q)⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hw
  have hπb : QuotientGroup.mk' Q b ∈ B'.map (QuotientGroup.mk' Q) := Subgroup.mem_map_of_mem _ hb
  have hc := Subgroup.mem_centralizer_iff.mp (h hπb) _ hπw
  have hcQ : b * w * b⁻¹ * w⁻¹ ∈ Q := by
    rw [← QuotientGroup.ker_mk' Q, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  have hwR : w ∈ R' := Subgroup.commutator_le_left R' P' hw
  have hcR : b * w * b⁻¹ * w⁻¹ ∈ R' :=
    R'.mul_mem (Normal.conj_mem ‹R'.Normal› w hwR b) (R'.inv_mem hwR)
  have h1 : b * w * b⁻¹ * w⁻¹ = 1 := by
    have := hQR.le_bot ⟨hcQ, hcR⟩
    simpa using this
  have h2 : b * w * b⁻¹ = w := mul_inv_eq_one.mp h1
  calc w * b = (b * w * b⁻¹) * b := by rw [h2]
    _ = b * w := by group

end Down


section Setup

variable {G : Type} [Group G]

@[expose] def P1 (z : G) (M N : Subgroup G) (r : ℕ) : Subgroup G := ⁅Op r M ⊓ N, zpowers z⁆

@[expose] def E1 (M N : Subgroup G) (r : ℕ) : Subgroup G := Ep r M ⊓ N

section Plain

variable {z : G} {M N A B : Subgroup G} {r : ℕ}

theorem A_le_P1 (h : Hyp62 z M N A B r) : A ≤ P1 z M N r :=
  calc A = ⁅A, zpowers z⁆ := h.A_comm.symm
    _ ≤ P1 z M N r := Subgroup.commutator_mono (le_inf h.A_le_Or h.A_le) le_rfl

theorem B_le_E1 (h : Hyp62 z M N A B r) : B ≤ E1 M N r := le_inf h.B_le_E h.B_le

theorem P1_le_Op (hz : z ∈ M) : P1 z M N r ≤ Op r M :=
  (Subgroup.commutator_mono inf_le_left le_rfl).trans
    (commutator_le_left_of_le_normalizer (Subgroup.zpowers_le.mpr (le_normalizer_Op r M hz)))

theorem P1_le_N (hz : z ∈ N) : P1 z M N r ≤ N :=
  commutator_le_of_le inf_le_right (Subgroup.zpowers_le.mpr hz)

theorem E1_le_Ep : E1 M N r ≤ Ep r M := inf_le_left

theorem E1_le_N : E1 M N r ≤ N := inf_le_right

theorem E1_le_Fm : E1 M N r ≤ Fm M := E1_le_Ep.trans (Ep_le_Fm r M)

theorem centralizer_P1_le (h : Hyp62 z M N A B r) : centralizer ((P1 z M N r : Subgroup G) : Set G) ≤ M :=
  (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (A_le_P1 h))).trans
    ((Subgroup.centralizer_le_normalizer _).trans h.A_mem.2.2.2)

theorem P1_ne_bot (h : Hyp62 z M N A B r) : P1 z M N r ≠ ⊥ := fun hbot =>
  h.A_mem.2.1 (le_bot_iff.mp (hbot ▸ A_le_P1 h))

theorem mem_normalizer_P1 {c : G} (hcM : c ∈ M) (hcN : c ∈ N) (hcz : c ∈ Cen z) :
    c ∈ normalizer ((P1 z M N r : Subgroup G) : Set G) := by
  have h1 : c ∈ normalizer ((Op r M ⊓ N : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_Op r M hcM, Subgroup.le_normalizer hcN⟩
  have h2 : c ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcz
  exact mem_normalizer_commutator h1 h2

theorem mem_normalizer_E1 {c : G} (hcM : c ∈ M) (hcN : c ∈ N) :
    c ∈ normalizer ((E1 M N r : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_Ep r M hcM, Subgroup.le_normalizer hcN⟩

theorem inf_centralizer_P1_le_normalizer_E1 (h : Hyp62 z M N A B r) {H : Subgroup G} (hHN : H ≤ N) :
    H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G) ≤ normalizer ((E1 M N r : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_E1 (centralizer_P1_le h hc.2) (hHN hc.1)

end Plain

section WithCtx

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M N A B : Subgroup G} {p r : ℕ}

theorem r_ne_two (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) : r ≠ 2 := by
  rintro rfl
  have hodd : Odd (Nat.card ↥(Fm M)) := odd_card_Fm ctx.hyp ctx.mem
  have hAp : IsPGroup 2 ↥A := (isPGroup_Op 2 Nat.prime_two M).to_le h.A_le_Or
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hAp
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h.A_mem.2.1 (Subgroup.eq_bot_of_card_eq A (by rw [hn, pow_zero]))
  have h2 : 2 ∣ Nat.card ↥A := by rw [hn]; exact dvd_pow_self 2 hn0
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le h.A_mem.1)))

theorem isPGroup_P1 (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    IsPGroup r ↥(P1 z M N r) :=
  (isPGroup_Op r h.prime M).to_le (P1_le_Op ctx.z_mem)

theorem P1_le_Fm (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) : P1 z M N r ≤ Fm M :=
  (P1_le_Op ctx.z_mem).trans (Op_le_Fm r h.prime M)

theorem sig4Sub (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    Sig4Sub G z N r (P1 z M N r) := by
  have hr2 : r ≠ 2 := r_ne_two ctx h
  refine ⟨h.maximal.1, ⟨h.prime, hr2, h.z_mem, P1_le_N h.z_mem, isPGroup_P1 ctx h, P1_ne_bot h, ?_, ?_⟩⟩
  · intro c hcN hcz
    exact mem_normalizer_P1 (ctx.cen_le hcz) hcN hcz
  · have hP : IsPGroup r ↥(Op r M ⊓ N) := (isPGroup_Op r h.prime M).to_le inf_le_left
    have hz : z ∈ normalizer ((Op r M ⊓ N : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_Op r M ctx.z_mem, Subgroup.le_normalizer h.z_mem⟩
    exact commutator_zpowers_idem ctx.orderOf_z h.prime hr2 hP hz

theorem inf_Cen_le_normalizer_P1 (ctx : Ctx6 G z k S M p) :
    N ⊓ Cen z ≤ normalizer ((P1 z M N r : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_P1 (ctx.cen_le hc.2) hc.1 hc.2

theorem inf_Cen_le_normalizer_E1 (ctx : Ctx6 G z k S M p) :
    N ⊓ Cen z ≤ normalizer ((E1 M N r : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_E1 (ctx.cen_le hc.2) hc.1

theorem E1_le_centralizer_P1 (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    E1 M N r ≤ centralizer ((P1 z M N r : Subgroup G) : Set G) := by
  have h1 : Op r M ≤ centralizer ((Ep r M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep r h.prime M)
  refine Subgroup.le_centralizer_iff.mp ?_
  exact (P1_le_Op ctx.z_mem).trans (h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr E1_le_Ep)))

theorem B_le_centralizer_P1 (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    B ≤ centralizer ((P1 z M N r : Subgroup G) : Set G) :=
  (B_le_E1 h).trans (E1_le_centralizer_P1 ctx h)

theorem E1_le_inf_centralizer_P1 (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) {H : Subgroup G}
    (hEH : E1 M N r ≤ H) : E1 M N r ≤ H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G) :=
  le_inf hEH (E1_le_centralizer_P1 ctx h)

theorem E1_le_cen_N (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    E1 M N r ≤ N ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G) :=
  E1_le_inf_centralizer_P1 ctx h E1_le_N

theorem normal_E1_of_le (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) {H : Subgroup G}
    (hEH : E1 M N r ≤ H) (hHN : H ≤ N) :
    ((E1 M N r).subgroupOf (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (E1_le_inf_centralizer_P1 ctx h hEH)).mpr
    (inf_centralizer_P1_le_normalizer_E1 h hHN)

theorem normal_E1 (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    ((E1 M N r).subgroupOf (N ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G))).Normal :=
  normal_E1_of_le ctx h E1_le_N le_rfl

theorem coprime_card_Ep (hr : r.Prime) : Nat.Coprime r (Nat.card ↥(Ep r M)) := by
  have : Fact r.Prime := ⟨hr⟩
  have h1 : Nat.card ↥(Ep r M) = Nat.card ↥(pPrimeCore r ↥(Fm M)) :=
    Subgroup.card_map_of_injective (Fm M).subtype_injective
  rw [h1]
  exact pPrimeCore_coprime_card (p := r) (G := ↥(Fm M))

theorem coprime_card_E1 (h : Hyp62 z M N A B r) : Nat.Coprime r (Nat.card ↥(E1 M N r)) :=
  (coprime_card_Ep h.prime).coprime_dvd_right (Subgroup.card_dvd_of_le E1_le_Ep)

theorem odd_card_E1 (ctx : Ctx6 G z k S M p) :
    Odd (Nat.card ↥(E1 M N r)) :=
  Odd.of_dvd_nat (odd_card_Fm ctx.hyp ctx.mem) (Subgroup.card_dvd_of_le E1_le_Fm)

theorem E1_le_pPrimeCoreOf_of_le (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) {H : Subgroup G}
    (hEH : E1 M N r ≤ H) (hHN : H ≤ N) :
    E1 M N r ≤ pPrimeCoreOf r (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)) := by
  have hn := normal_E1_of_le ctx h hEH hHN
  have hle0 := E1_le_inf_centralizer_P1 ctx h hEH
  have hc : Nat.Coprime r (Nat.card ↥((E1 M N r).subgroupOf
      (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)))) := by
    have : Nat.card ↥((E1 M N r).subgroupOf (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G))) =
        Nat.card ↥(E1 M N r) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle0).toEquiv
    rw [this]
    exact coprime_card_E1 h
  have hle : (E1 M N r).subgroupOf (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)) ≤
      pPrimeCore r ↥(H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)) :=
    le_sSup ⟨hn, hc⟩
  calc E1 M N r = ((E1 M N r).subgroupOf
        (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G))).map
          (H ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hle0).symm
    _ ≤ _ := Subgroup.map_mono hle

theorem E1_le_pPrimeCoreOf (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    E1 M N r ≤ pPrimeCoreOf r (N ⊓ centralizer ((P1 z M N r : Subgroup G) : Set G)) :=
  E1_le_pPrimeCoreOf_of_le ctx h E1_le_N le_rfl

end WithCtx

end Setup

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
