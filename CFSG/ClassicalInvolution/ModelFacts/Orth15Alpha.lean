module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Comp

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy
open scoped commutatorElement

section Quasisimple

theorem le_center_of_odd_normal {H : Type*} [Group H] [Finite H]
    (hH : CFSG.Open.IsQuasisimple H) (N : Subgroup H) [N.Normal] (hodd : Odd (Nat.card N)) :
    N ≤ Subgroup.center H := by
  classical
  obtain ⟨hperf, hsimple⟩ := hH
  let π : H →* H ⧸ Subgroup.center H := QuotientGroup.mk' (Subgroup.center H)
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map ‹N.Normal› π (QuotientGroup.mk'_surjective _)
  have := hNn
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · intro x hx
    have h1 : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [hbot] at h1
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp h1)
  · exfalso
    have hcom : N ⊔ Subgroup.center H = ⊤ := by
      have : Subgroup.comap π (N.map π) = N ⊔ Subgroup.center H := by
        rw [sup_comm]
        exact QuotientGroup.comap_map_mk' (Subgroup.center H) N
      rw [← this, htop, Subgroup.comap_top]
    have hle : commutator H ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcom (by infer_instance)
    have hNtop : N = ⊤ := by
      rw [hperf] at hle
      exact eq_top_iff.mpr hle
    have hoddH : Odd (Nat.card H) := by
      have : Nat.card N = Nat.card H := by rw [hNtop]; simp
      rwa [this] at hodd
    have hsolv : Group.IsSolvable H := CFSG.FeitThompson.isSolvable_of_odd_natCard H hoddH
    have : Nontrivial (H ⧸ Subgroup.center H) := hsimple.toNontrivial
    have : Nontrivial H := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : Subsingleton (H ⧸ Subgroup.center H) :=
        (QuotientGroup.mk'_surjective _).subsingleton
      exact not_subsingleton _ ‹_›
    have : Group.IsPerfect H := (Group.isPerfect_def).2 hperf
    exact Group.IsPerfect.not_isSolvable H hsolv

variable {G : Type*} [Group G]

theorem commutator_self_of_perfect {H : Subgroup G} (h : commutator H = ⊤) : ⁅H, H⁆ = H := by
  have h1 : (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H).map H.subtype =
      ⁅(⊤ : Subgroup H).map H.subtype, (⊤ : Subgroup H).map H.subtype⁆ :=
    Subgroup.map_commutator _ _ _
  have h2 : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h2] at h1
  rw [← h1, ← commutator_def, h, h2]

theorem comm_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem commutator_eq_bot_of_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A, B⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (h a ha b hb)

theorem commutator_eq_bot_of_layers [Finite G] (P O : Subgroup G) (𝓗 : Set (Subgroup G))
    (hH : ∀ H ∈ 𝓗, H ≤ P ∧ CFSG.Open.IsQuasisimple ↥H ∧ ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H)
    (hP : P ≤ ⨆ H ∈ 𝓗, H) (hPO : ∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O)
    (hOP : ∀ o ∈ O, ∀ p ∈ P, o * p * o⁻¹ ∈ P) (hodd : Odd (Nat.card O)) : ⁅O, P⁆ = ⊥ := by
  classical
  set M : Subgroup G := O ⊓ P with hM
  have hMn : ∀ p ∈ P, ∀ m ∈ M, p * m * p⁻¹ ∈ M := fun p hp m hm =>
    ⟨hPO p hp m hm.1, P.mul_mem (P.mul_mem hp hm.2) (P.inv_mem hp)⟩
  have hMH : ∀ H ∈ 𝓗, ⁅M, H⁆ = ⊥ := by
    intro H hH'
    obtain ⟨hHP, hHq, hHn⟩ := hH H hH'
    have hMHle : ⁅M, H⁆ ≤ M ⊓ H := by
      rw [Subgroup.commutator_le]
      intro m hm h hh
      refine ⟨?_, ?_⟩
      · have e : (⁅m, h⁆ : G) = m * (h * m⁻¹ * h⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact M.mul_mem hm (hMn h (hHP hh) m⁻¹ (M.inv_mem hm))
      · have e : (⁅m, h⁆ : G) = (m * h * m⁻¹) * h⁻¹ := commutatorElement_def m h
        rw [e]
        exact H.mul_mem (hHn m hm.2 h hh) (H.inv_mem hh)
    have hcentral : ∀ x ∈ M ⊓ H, ∀ h ∈ H, x * h = h * x := by
      let N : Subgroup H := (M ⊓ H).subgroupOf H
      have hNn : N.Normal :=
        ⟨fun n hn g => by
          rw [Subgroup.mem_subgroupOf] at hn ⊢
          exact ⟨hMn g (hHP g.2) n hn.1, H.mul_mem (H.mul_mem g.2 hn.2) (H.inv_mem g.2)⟩⟩
      have hNodd : Odd (Nat.card N) := by
        have h1 : Nat.card ↥N = Nat.card ↥(M ⊓ H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
        have h2 : Nat.card ↥(M ⊓ H) ∣ Nat.card O :=
          Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
        rw [h1]
        exact Odd.of_dvd_nat hodd h2
      have hle := le_center_of_odd_normal hHq N hNodd
      intro x hx h hh
      have hxN : (⟨x, hx.2⟩ : H) ∈ N := Subgroup.mem_subgroupOf.mpr hx
      have := Subgroup.mem_center_iff.mp (hle hxN) ⟨h, hh⟩
      exact (congrArg Subtype.val this).symm
    have h1 : ⁅⁅M, H⁆, H⁆ = ⊥ :=
      commutator_eq_bot_of_comm fun a ha b hb => hcentral a (hMHle ha) b hb
    have h2 : ⁅⁅H, M⁆, H⁆ = ⊥ := by
      rw [Subgroup.commutator_comm H M]
      exact h1
    have h3 : ⁅⁅H, H⁆, M⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [commutator_self_of_perfect hHq.1, Subgroup.commutator_comm] at h3
    exact h3
  have hMP : ⁅M, P⁆ = ⊥ := by
    refine commutator_eq_bot_of_comm fun m hm p hp => ?_
    have hle : (⨆ H ∈ 𝓗, H) ≤ Subgroup.centralizer ({m} : Set G) := by
      refine iSup₂_le fun H hH' h hh => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact comm_of_commutator_eq_bot (hMH H hH') hm hh
    have := hle (hP hp)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this m rfl
  have hperf : P ≤ ⁅P, P⁆ := by
    refine hP.trans (iSup₂_le fun H hH' => ?_)
    obtain ⟨hHP, hHq, -⟩ := hH H hH'
    rw [← commutator_self_of_perfect hHq.1]
    exact Subgroup.commutator_mono hHP hHP
  have hOPM : ⁅O, P⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro o ho p hp
    refine ⟨?_, ?_⟩
    · have e : (⁅o, p⁆ : G) = o * (p * o⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact O.mul_mem ho (hPO p hp o⁻¹ (O.inv_mem ho))
    · have e : (⁅o, p⁆ : G) = (o * p * o⁻¹) * p⁻¹ := commutatorElement_def o p
      rw [e]
      exact P.mul_mem (hOP o ho p hp) (P.inv_mem hp)
  have h1 : ⁅⁅O, P⁆, P⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hOPM le_rfl).trans hMP.le)
  have h2 : ⁅⁅P, O⁆, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm P O]
    exact h1
  have h3 : ⁅⁅P, P⁆, O⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  have h4 : ⁅P, O⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hperf le_rfl).trans h3.le)
  rw [Subgroup.commutator_comm]
  exact h4

end Quasisimple

section Alpha

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mul_self_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) {x : G} (hx : x ∈ A)
    (h : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
  have h2 : orderOf x ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hx
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card A) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card A) = 1 := Nat.coprime_two_left.mpr hA
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Finite G] in
theorem involutionOddCore_le_centralizer' (a : G) :
    involutionOddCore a ≤ Subgroup.centralizer ({a} : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
theorem conj_mem_involutionOddCore (a : G) {x n : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (hn : n ∈ involutionOddCore a) : x * n * x⁻¹ ∈ involutionOddCore a := by
  obtain ⟨y, hy, rfl⟩ := hn
  refine ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, (oddCore_normal _).conj_mem y hy ⟨x, hx⟩, rfl⟩

theorem odd_natCard_involutionOddCore (a : G) : Odd (Nat.card ↥(involutionOddCore a)) :=
  oddCoreOf_odd_natCard (Subgroup.centralizer ({a} : Set G))

theorem alphaOf_eq_bot_of_layers (L : Subgroup G) [L.Normal]
    (hL : ∀ x : G, (∀ y ∈ L, x * y = y * x) → x = 1) (B : Subgroup G) (hBL : B ≤ L)
    (hB2 : ∀ b ∈ B, b * b = 1) (Fam : Set (Subgroup G))
    (hatt : ∀ P ∈ Fam, ∃ a ∈ B, a ≠ 1 ∧ P ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ p ∈ P, x * p * x⁻¹ ∈ P) ∧
      P ≤ ⁅P, P⁆ ∧
      ∀ N : Subgroup G, N ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
        (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        Odd (Nat.card N) → ⁅N, P⁆ = ⊥)
    (hB : ∀ a ∈ B, a ≠ 1 → ∀ N : Subgroup G, N ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
      (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        Odd (Nat.card N) → ⁅N, B⁆ = ⊥)
    (hgen : L ≤ ⨆ P ∈ Fam, P) : alphaOf B = ⊥ := by
  classical
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hB2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hB2 y hy)
    have h := inv_eq_of_mul_eq_one_right (hB2 (x * y) (B.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at h
    exact h.symm
  have hM : ∀ a ∈ B, a ≠ 1 → ∃ M : Subgroup G, M = involutionOddCore a ⊓ L ∧
      M ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ M, x * n * x⁻¹ ∈ M) ∧
      Odd (Nat.card M) := by
    intro a ha ha1
    refine ⟨involutionOddCore a ⊓ L, rfl, ?_, ?_, ?_⟩
    · exact fun x hx => ⟨hx.2, involutionOddCore_le_centralizer' a hx.1⟩
    · intro x hx n hn
      exact ⟨conj_mem_involutionOddCore a hx.2 hn.1,
        L.mul_mem (L.mul_mem hx.1 hn.2) (L.inv_mem hx.1)⟩
    · exact Odd.of_dvd_nat (odd_natCard_involutionOddCore a)
        (Subgroup.card_dvd_of_le inf_le_left)
  refine (alphaOf_eq_bot_iff B).mpr ⟨?_, ?_⟩
  ·
    intro a ha ha1
    obtain ⟨M, rfl, hMle, hMnorm, hModd⟩ := hM a ha ha1
    refine commutator_eq_bot_of_comm fun g hg b hb => ?_
    have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hBcomm y ha b hb
    have hbL : b ∈ L := hBL hb
    have hcN : ⁅g, b⁆ ∈ involutionOddCore a := by
      have e : (⁅g, b⁆ : G) = g * (b * g⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (involutionOddCore a).mul_mem hg
        (conj_mem_involutionOddCore a hbC ((involutionOddCore a).inv_mem hg))
    have hcL : ⁅g, b⁆ ∈ L := by
      have e : (⁅g, b⁆ : G) = (g * b * g⁻¹) * b⁻¹ := commutatorElement_def g b
      rw [e]
      exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› b hbL g) (L.inv_mem hbL)
    have hcM : ⁅g, b⁆ ∈ involutionOddCore a ⊓ L := ⟨hcN, hcL⟩
    have hcb : ⁅g, b⁆ * b = b * ⁅g, b⁆ :=
      comm_of_commutator_eq_bot (hB a ha ha1 _ hMle hMnorm hModd) hcM hb
    have e1 : ⁅g, b⁆ * b = g * b * g⁻¹ := by
      simp only [commutatorElement_def]; group
    have e2 : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
      have : (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      rw [this, hB2 b hb]
      group
    have e3 : ⁅g, b⁆ * ⁅g, b⁆ = 1 := by
      have : (⁅g, b⁆ * b) * (⁅g, b⁆ * b) = ⁅g, b⁆ * ⁅g, b⁆ * (b * b) := by
        calc (⁅g, b⁆ * b) * (⁅g, b⁆ * b) = ⁅g, b⁆ * (b * ⁅g, b⁆) * b := by group
          _ = ⁅g, b⁆ * (⁅g, b⁆ * b) * b := by rw [hcb]
          _ = ⁅g, b⁆ * ⁅g, b⁆ * (b * b) := by group
      rw [e1, e2, hB2 b hb, mul_one] at this
      exact this.symm
    have : ⁅g, b⁆ = 1 := eq_one_of_mul_self_of_odd hModd hcM e3
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  ·
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_bot]
    refine hL x fun y hy => ?_
    have hcent : ∀ P ∈ Fam, ∀ p ∈ P, x * p = p * x := by
      intro P hP p hp
      obtain ⟨a, haB, ha1, hPle, hPnorm, hPperf, hPN⟩ := hatt P hP
      obtain ⟨M, hMe, hMle, hMnorm, hModd⟩ := hM a haB ha1
      have hxa : x ∈ involutionOddCore a := by
        have := Subgroup.mem_iInf.mp hx a
        have := Subgroup.mem_iInf.mp this haB
        exact (Subgroup.mem_iInf.mp this ha1)
      have hNPM : ⁅involutionOddCore a, P⁆ ≤ M := by
        rw [Subgroup.commutator_le]
        intro g hg q hq
        rw [hMe]
        refine ⟨?_, ?_⟩
        · have e : (⁅g, q⁆ : G) = g * (q * g⁻¹ * q⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (involutionOddCore a).mul_mem hg
            (conj_mem_involutionOddCore a (hPle hq).2 ((involutionOddCore a).inv_mem hg))
        · have e : (⁅g, q⁆ : G) = (g * q * g⁻¹) * q⁻¹ := commutatorElement_def g q
          rw [e]
          exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› q (hPle hq).1 g)
            (L.inv_mem (hPle hq).1)
      have hMP : ⁅M, P⁆ = ⊥ := hPN M hMle hMnorm hModd
      have h1 : ⁅⁅involutionOddCore a, P⁆, P⁆ = ⊥ :=
        eq_bot_iff.mpr ((Subgroup.commutator_mono hNPM le_rfl).trans hMP.le)
      have h2 : ⁅⁅P, involutionOddCore a⁆, P⁆ = ⊥ := by
        rw [Subgroup.commutator_comm P (involutionOddCore a)]
        exact h1
      have h3 : ⁅⁅P, P⁆, involutionOddCore a⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
      have h4 : ⁅P, involutionOddCore a⁆ = ⊥ :=
        eq_bot_iff.mpr ((Subgroup.commutator_mono hPperf le_rfl).trans h3.le)
      exact (comm_of_commutator_eq_bot h4 hp hxa).symm
    have hle : (⨆ P ∈ Fam, P) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup₂_le fun P hP p hp => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcent P hP p hp
    have := hle (hgen hy)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this x rfl

end Alpha

end CFSG.ClassicalInvolution.ModelFacts.Orth15
