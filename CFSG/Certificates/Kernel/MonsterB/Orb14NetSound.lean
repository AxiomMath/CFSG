module

public import Certificates.Data.Kernel.MonsterB.Orb14
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound

public section

namespace CFSG.KC.Orb14

open CFSG.KLie.CT CFSG.KC.U6Orb

@[expose] def swp (s m q : ℕ) : ℕ :=
  if m.testBit q then q + s else if s ≤ q ∧ m.testBit (q - s) then q - s else q

@[expose] def Adm (s m : ℕ) : Prop := 0 < s ∧ ∀ q, m.testBit q → m.testBit (q + s) = false

theorem dsw_eq (s m x : ℕ) :
    dsw s m x = x ^^^ (((x >>> s) ^^^ x) &&& m) ^^^ ((((x >>> s) ^^^ x) &&& m) <<< s) := rfl

theorem testBit_dsw {s m : ℕ} (h : Adm s m) (x q : ℕ) :
    (dsw s m x).testBit q = x.testBit (swp s m q) := by
  rw [dsw_eq]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  unfold swp
  by_cases hs : s ≤ q
  · have e : s + (q - s) = q := Nat.add_sub_cancel' hs
    rw [e, decide_eq_true hs, Nat.add_comm s q]
    cases hq : m.testBit q with
    | true =>
      have hm : m.testBit (q - s) = false := by
        cases hm : m.testBit (q - s) with
        | false => rfl
        | true =>
          have := h.2 _ hm
          rw [Nat.sub_add_cancel hs, hq] at this
          exact absurd this (by decide)
      rw [ite_eq_left rfl, hm]
      cases x.testBit q <;> cases x.testBit (q + s) <;> simp
    | false =>
      rw [ite_eq_right (by decide)]
      cases hm : m.testBit (q - s) with
      | true =>
        rw [ite_eq_left ⟨hs, rfl⟩]
        cases x.testBit q <;> cases x.testBit (q - s) <;> simp
      | false =>
        rw [ite_eq_right (fun h' => absurd h'.2 (by decide))]
        cases x.testBit q <;> simp
  · rw [decide_eq_false hs, Nat.add_comm s q]
    cases hq : m.testBit q with
    | true =>
      rw [ite_eq_left rfl]
      cases x.testBit q <;> cases x.testBit (q + s) <;> simp
    | false =>
      rw [ite_eq_right (by decide), ite_eq_right (fun h' => hs h'.1)]
      cases x.testBit q <;> simp

theorem swp_swp {s m : ℕ} (h : Adm s m) (q : ℕ) : swp s m (swp s m q) = q := by
  cases hq : m.testBit q with
  | true =>
    have h1 : m.testBit (q + s) = false := h.2 q hq
    have e1 : swp s m q = q + s := by rw [swp, ite_eq_left hq]
    rw [e1, swp, ite_eq_right (by rw [h1]; decide), ite_eq_left ⟨by omega, by rw [Nat.add_sub_cancel]; exact hq⟩,
      Nat.add_sub_cancel]
  | false =>
    by_cases h3 : s ≤ q ∧ m.testBit (q - s) = true
    · have e1 : swp s m q = q - s := by rw [swp, ite_eq_right (by rw [hq]; decide), ite_eq_left h3]
      rw [e1, swp, ite_eq_left h3.2, Nat.sub_add_cancel h3.1]
    · have e1 : swp s m q = q := by rw [swp, ite_eq_right (by rw [hq]; decide), ite_eq_right h3]
      rw [e1, e1]

theorem swp_lt {s m : ℕ} (hb : m < 2 ^ (1024 - s)) {q : ℕ} (hq : q < 1024) : swp s m q < 1024 := by
  unfold swp
  split
  · next hm =>
    have : q < 1024 - s := by
      by_contra hc
      have hle : 2 ^ (1024 - s) ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)] at hm
      exact absurd hm (by decide)
    omega
  · split <;> omega

@[expose] noncomputable def netF (L : List (ℕ × ℕ)) (x : ℕ) : ℕ := L.foldl (fun acc p => dsw p.1 p.2 acc) x

@[expose] noncomputable def netRF (L : List (ℕ × ℕ)) (x : ℕ) : ℕ := L.foldr (fun p acc => dsw p.1 p.2 acc) x

@[expose] def posF : List (ℕ × ℕ) → ℕ → ℕ
  | [], q => q
  | p :: L, q => swp p.1 p.2 (posF L q)

@[expose] def posR : List (ℕ × ℕ) → ℕ → ℕ
  | [], q => q
  | p :: L, q => posR L (swp p.1 p.2 q)

theorem testBit_netF : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, Adm p.1 p.2) →
    ∀ x q, (netF L x).testBit q = x.testBit (posF L q)
  | [], _, x, q => rfl
  | p :: L, h, x, q => by
    change (netF L (dsw p.1 p.2 x)).testBit q = _
    rw [testBit_netF (fun p' hp => h p' (List.mem_cons_of_mem _ hp)), posF,
      testBit_dsw (h p List.mem_cons_self)]

theorem testBit_netRF : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, Adm p.1 p.2) →
    ∀ x q, (netRF L x).testBit q = x.testBit (posR L q)
  | [], _, x, q => rfl
  | p :: L, h, x, q => by
    change (dsw p.1 p.2 (netRF L x)).testBit q = _
    rw [testBit_dsw (h p List.mem_cons_self), testBit_netRF (fun p' hp => h p' (List.mem_cons_of_mem _ hp)),
      posR]

theorem posR_posF : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, Adm p.1 p.2) → ∀ q, posR L (posF L q) = q
  | [], _, q => rfl
  | p :: L, h, q => by
    rw [posF, posR, swp_swp (h p List.mem_cons_self),
      posR_posF (fun p' hp => h p' (List.mem_cons_of_mem _ hp))]

theorem posF_posR : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, Adm p.1 p.2) → ∀ q, posF L (posR L q) = q
  | [], _, q => rfl
  | p :: L, h, q => by
    rw [posR, posF, posF_posR (fun p' hp => h p' (List.mem_cons_of_mem _ hp)),
      swp_swp (h p List.mem_cons_self)]

theorem posF_lt : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, p.2 < 2 ^ (1024 - p.1)) →
    ∀ q < 1024, posF L q < 1024
  | [], _, _, hq => hq
  | p :: _, h, q, hq => swp_lt (h p List.mem_cons_self)
      (posF_lt (fun p' hp => h p' (List.mem_cons_of_mem _ hp)) q hq)

theorem posR_lt : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, p.2 < 2 ^ (1024 - p.1)) →
    ∀ q < 1024, posR L q < 1024
  | [], _, _, hq => hq
  | p :: _, h, _, hq => posR_lt (fun p' hp => h p' (List.mem_cons_of_mem _ hp)) _
      (swp_lt (h p List.mem_cons_self) hq)

theorem netK_eq (W x : ℕ) : netK W x = netF (stg W) x := rfl

theorem netR_eq (W x : ℕ) : netR W x = netRF (stg W) x := rfl

theorem netOK_spec {W : ℕ} (h : netOK W = true) :
    ∀ p ∈ stg W, Adm p.1 p.2 ∧ p.2 < 2 ^ (1024 - p.1) := by
  intro p hp
  have h' := (allL_iff _ _).1 h p hp
  simp only [andB_eq_true, Nat.blt_eq, Nat.beq_eq, pw2_eq] at h'
  obtain ⟨hs, h0, hb⟩ := h'
  refine ⟨⟨hs, fun q hq => ?_⟩, hb⟩
  have : (p.2 &&& (p.2 <<< p.1)).testBit (q + p.1) = false := by
    change (Nat.land p.2 (Nat.shiftLeft p.2 p.1)).testBit _ = _
    rw [h0, Nat.zero_testBit]
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.add_sub_cancel] at this
  simpa [hq] using this

@[expose] noncomputable def phi (W q : ℕ) : ℕ := posF (stg W) q

@[expose] noncomputable def psi (W q : ℕ) : ℕ := posR (stg W) q

theorem testBit_netK {W : ℕ} (h : netOK W = true) (x q : ℕ) :
    (netK W x).testBit q = x.testBit (phi W q) := by
  rw [netK_eq, testBit_netF (fun p hp => (netOK_spec h p hp).1)]
  rfl

theorem testBit_netR {W : ℕ} (h : netOK W = true) (x q : ℕ) :
    (netR W x).testBit q = x.testBit (psi W q) := by
  rw [netR_eq, testBit_netRF (fun p hp => (netOK_spec h p hp).1)]
  rfl

theorem psi_phi {W : ℕ} (h : netOK W = true) (q : ℕ) : psi W (phi W q) = q :=
  posR_posF (fun p hp => (netOK_spec h p hp).1) q

theorem phi_psi {W : ℕ} (h : netOK W = true) (q : ℕ) : phi W (psi W q) = q :=
  posF_posR (fun p hp => (netOK_spec h p hp).1) q

theorem phi_lt {W : ℕ} (h : netOK W = true) {q : ℕ} (hq : q < 1024) : phi W q < 1024 :=
  posF_lt (fun p hp => (netOK_spec h p hp).2) q hq

theorem phi_inj {W : ℕ} (h : netOK W = true) {a b : ℕ} (e : phi W a = phi W b) : a = b := by
  rw [← psi_phi h a, e, psi_phi h b]

structure NetPerm (g : ℕ → ℕ) (N W : ℕ) : Prop where
  ok : netOK W = true
  lt : ∀ x < N, g x < N
  phi_lt : ∀ q < N, phi W q < N
  g_phi : ∀ q < N, g (phi W q) = q

namespace NetPerm

variable {g : ℕ → ℕ} {N W : ℕ} (h : NetPerm g N W)
include h

theorem phi_g {x : ℕ} (hx : x < N) : phi W (g x) = x := by
  have hsub : (Finset.range N).image (phi W) ⊆ Finset.range N := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (h.phi_lt q (Finset.mem_range.1 hq))
  have hcard : (Finset.range N).card ≤ ((Finset.range N).image (phi W)).card := by
    rw [Finset.card_image_of_injOn (fun a _ b _ e => phi_inj h.ok e)]
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  have : x ∈ (Finset.range N).image (phi W) := by rw [he]; exact Finset.mem_range.2 hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 this
  rw [h.g_phi q (Finset.mem_range.1 hq)]

theorem inj {x y : ℕ} (hx : x < N) (hy : y < N) (e : g x = g y) : x = y := by
  rw [← h.phi_g hx, e, h.phi_g hy]

theorem psi_eq {x : ℕ} (hx : x < N) : psi W x = g x := by
  have e := psi_phi h.ok (g x)
  rwa [h.phi_g hx] at e

theorem netK_mask {R : ℕ} (hR : ∀ x, R.testBit x = true → x < N) (y : ℕ) :
    (netK W R).testBit y = true ↔ ∃ x, R.testBit x = true ∧ g x = y := by
  rw [testBit_netK h.ok]
  constructor
  · intro hb
    have hz := hR _ hb
    refine ⟨_, hb, ?_⟩
    by_cases hy : y < N
    · exact h.g_phi y hy
    · have e2 : g (phi W y) = y := phi_inj h.ok (h.phi_g hz)
      exact absurd (by rw [← e2]; exact h.lt _ hz) hy
  · rintro ⟨x, hb, rfl⟩
    rw [h.phi_g (hR _ hb)]
    exact hb

theorem netR_mask {R : ℕ} (hR : ∀ x, R.testBit x = true → x < N) (y : ℕ) :
    (netR W R).testBit y = true ↔ y < N ∧ R.testBit (g y) = true := by
  rw [testBit_netR h.ok]
  constructor
  · intro hb
    have hz := hR _ hb
    have hy : y < N := by
      have := h.phi_lt _ hz
      rwa [phi_psi h.ok] at this
    exact ⟨hy, by rwa [h.psi_eq hy] at hb⟩
  · rintro ⟨hy, hb⟩
    rwa [h.psi_eq hy]

end NetPerm

end CFSG.KC.Orb14

end
