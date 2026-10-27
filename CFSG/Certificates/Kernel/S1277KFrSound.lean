module

public import Certificates.Data.Kernel.S1277KFr
public import CFSG.Certificates.Kernel.S1277KCandSound

public section

namespace CFSG.KS.S1277Fr

open CFSG.KC.S1277Lat CFSG.KC.S1277Cand CFSG.KC.S1277Mod CFSG.KC.S1277Fr CFSG.KS.S1277Lat
  CFSG.KS.S1277Mod CFSG.KS.S1277Cand CFSG.Quasithin.H13.I1277

theorem beq_false_nat {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

section Fr

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem mem_nodeL {kg gs ts : List ℕ} {m e : ℕ} (hN : nodeChk M kg m gs ts e = true) {x : ℕ}
    (hx : m.testBit x = true) : x ∈ nodeL M ts := by
  rw [nodeChk] at hN
  simp only [Bool.and_eq_true] at hN
  have htree := Nat.eq_of_beq_eq_true hN.1.1.1.2
  rcases ((treeF_bits htree (ne_zero_of_testBit hx)).1 x).1 hx with h | h
  · rw [testBit_idM h]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ h

theorem phi_gens (hκ : MCod K M κ) {Q : Subgroup G} (hQK : Q ≤ K) {m : ℕ}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {pg pr : List ℕ}
    (hlen : pg.length = pr.length)
    (hgen : allL (List.range pg.length) (fun i => m.testBit (pr.getD i 0 % 4096) &&
      m.testBit (pr.getD i 0 >>> 12) && Nat.beq (phiGen M (pr.getD i 0)) (pg.getD i 0)) = true) :
    ∀ g ∈ pg, ∃ r ∈ Phi' Q, κ r = g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have h := (allL_iff.1 hgen) i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, he⟩ := h
  obtain ⟨qa, hqa, hqaκ⟩ := (hQN _).2 ha
  obtain ⟨qb, hqb, hqbκ⟩ := (hQN _).2 hb
  rw [← getD_eq_get 0 hi, ← Nat.eq_of_beq_eq_true he, phiGen]
  cases hab : Nat.beq (pr.getD i 0 % 4096) (pr.getD i 0 >>> 12) with
  | true =>
    refine ⟨qa ^ 2, sq_mem_Phi' hqa, ?_⟩
    rw [cond_true, pow_two, hκ.mul _ (hQK hqa) _ (hQK hqa), hqaκ]
  | false =>
    refine ⟨qa * qb * qa⁻¹ * qb⁻¹, comm_mem_Phi' hqa hqb, ?_⟩
    rw [cond_false, MCod.comm hκ (hQK hqa) (hQK hqb), hqaκ, hqbκ]

theorem fr_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {p TP d : ℕ} {pg pr pt ws : List ℕ}
    (hc : frChk M m gs ts p pg pr pt TP d ws = true) :
    (∀ x ∈ Q, rd6 TP (κ x) < 2 ^ d) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, rd6 TP (κ (x * y)) = rd6 TP (κ x) ^^^ rd6 TP (κ y)) ∧
      (∀ e < 2 ^ d, ∃ x ∈ Q, rd6 TP (κ x) = e) ∧
      (∀ x ∈ Q, rd6 TP (κ x) = 0 ↔ x ∈ Phi' Q) ∧
      (∀ c, p.testBit c = true ↔ ∃ r ∈ Phi' Q, κ r = c) ∧
      (∀ g ∈ pg, ∃ r ∈ Phi' Q, κ r = g) ∧
      treeF M pg pt (idM M) = p ∧ p ≠ 0 := by
  rw [frChk] at hc
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hp1⟩, hpt⟩, hlen⟩, hgen⟩, hel⟩, hwl⟩, hws⟩ := hc
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hpt' := Nat.eq_of_beq_eq_true hpt
  have hp0 : p ≠ 0 := ne_zero_of_testBit hp1
  have hpg := phi_gens hκ hQK hQN hlen' hgen
  have hPK : Phi' Q ≤ K := (Phi'_le Q).trans hQK
  have hpΦ : ∀ c, p.testBit c = true → ∃ r ∈ Phi' Q, κ r = c :=
    tree_sub hκ hPK hpt' hp0 hpg
  have hx : ∀ x ∈ Q, rd6 TP (κ x) < 2 ^ d ∧ (rd6 TP (κ x) = 0 ↔ p.testBit (κ x) = true) ∧
      ∀ g ∈ gs, rd6 TP (M.mul (κ x) g) = rd6 TP (κ x) ^^^ rd6 TP g := by
    intro x hxQ
    have h := (allL_iff.1 hel) _ (mem_nodeL hN ((hQN _).1 ⟨x, hxQ, rfl⟩))
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, ?_, fun g hg => Nat.eq_of_beq_eq_true ((allL_iff.1 h3) g hg)⟩
    rw [← h2, Nat.beq_eq]
  have hone : rd6 TP (κ 1) = 0 := by
    have := (hx 1 Q.one_mem).2.1
    rw [hκ.one] at this ⊢
    exact this.2 hp1
  have hgQ : ∀ g ∈ gs, ∀ r ∈ K, κ r = g → r ∈ Q := by
    intro g hg r hr hrg
    obtain ⟨q, hq, hqκ⟩ := (hQN g).2 (node_gens hN hg)
    rw [← hκ.inj q (hQK hq) r hr (hqκ.trans hrg.symm)]
    exact hq
  have hmul : ∀ x ∈ Q, ∀ y ∈ Q, rd6 TP (κ (x * y)) = rd6 TP (κ x) ^^^ rd6 TP (κ y) := by
    intro x hxQ y hyQ
    have key := node_codes hκ hN (fun y => y ∈ Q ∧ ∀ x ∈ Q,
      rd6 TP (κ (x * y)) = rd6 TP (κ x) ^^^ rd6 TP (κ y))
      ⟨Q.one_mem, fun x _ => by rw [mul_one, hone, Nat.xor_zero]⟩ ?_ y (hQK hyQ)
      ((hQN _).1 ⟨y, hyQ, rfl⟩)
    · exact key.2 x hxQ
    intro y hyK ⟨hyQ', hP⟩ g hg r hr hrg
    have hrQ := hgQ g hg r hr hrg
    refine ⟨Q.mul_mem hyQ' hrQ, fun x hxQ' => ?_⟩
    have hxy : x * y ∈ Q := Q.mul_mem hxQ' hyQ'
    rw [← mul_assoc, hκ.mul _ (hQK hxy) r hr, hrg, (hx _ hxy).2.2 g hg, hP x hxQ',
      hκ.mul y hyK r hr, hrg, (hx _ hyQ').2.2 g hg, Nat.xor_assoc]
  have hinv : ∀ x ∈ Q, rd6 TP (κ x⁻¹) = rd6 TP (κ x) := by
    intro x hxQ
    have h := hmul x hxQ x⁻¹ (Q.inv_mem hxQ)
    rw [mul_inv_cancel, hone] at h
    have := congrArg (rd6 TP (κ x) ^^^ ·) h
    simp only [Nat.xor_zero, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
    exact this.symm
  have hker : ∀ x ∈ Q, rd6 TP (κ x) = 0 ↔ x ∈ Phi' Q := by
    let S : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ rd6 TP (κ x) = 0}
        one_mem' := ⟨Q.one_mem, hone⟩
        mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
          rw [hmul a ha.1 b hb.1, ha.2, hb.2, Nat.xor_zero]⟩
        inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [hinv a ha.1, ha.2]⟩ }
    have hΦS : Phi' Q ≤ S := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (⟨y, hy, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
      · refine ⟨Q.pow_mem hy 2, ?_⟩
        rw [pow_two, hmul y hy y hy, Nat.xor_self]
      · have hab : a * b ∈ Q := Q.mul_mem ha hb
        have haba : a * b * a⁻¹ ∈ Q := Q.mul_mem hab (Q.inv_mem ha)
        refine ⟨Q.mul_mem haba (Q.inv_mem hb), ?_⟩
        rw [hmul _ haba _ (Q.inv_mem hb), hmul _ hab _ (Q.inv_mem ha), hmul a ha b hb,
          hinv a ha, hinv b hb]
        rw [Nat.xor_assoc (rd6 TP (κ a) ^^^ rd6 TP (κ b)), Nat.xor_self]
    intro x hxQ
    constructor
    · intro h0
      obtain ⟨r, hr, hrκ⟩ := hpΦ _ ((hx x hxQ).2.1.1 h0)
      rw [← hκ.inj r (hPK hr) x (hQK hxQ) hrκ]
      exact hr
    · intro hxΦ
      exact (hΦS hxΦ).2
  refine ⟨fun x hxQ => (hx x hxQ).1, hmul, fun e he => ?_, hker, fun c => ⟨hpΦ c, ?_⟩, hpg,
    hpt', hp0⟩
  · have h := (allL_iff.1 hws) e (List.mem_range.2 he)
    rw [Bool.and_eq_true] at h
    obtain ⟨q, hq, hqκ⟩ := (hQN _).2 h.1
    exact ⟨q, hq, by rw [hqκ]; exact Nat.eq_of_beq_eq_true h.2⟩
  · rintro ⟨r, hr, rfl⟩
    exact ((hx r (Phi'_le Q hr)).2.1).1 ((hker r (Phi'_le Q hr)).2 hr)

theorem lab_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {p TP d : ℕ} {pg pr pt ws : List ℕ}
    (hc : frChk M m gs ts p pg pr pt TP d ws = true) {z : G} (hzK : z ∈ K) {typ L : ℕ}
    (hl : labChk M (κ z) ts pg TP typ L = true) {x : G} (hxQ : x ∈ Q) :
    (typ = 0 → (L.testBit (rd6 TP (κ x)) = true ↔ x = z)) ∧
      (typ = 1 → (L.testBit (rd6 TP (κ x)) = true ↔ x * x ≠ 1)) ∧
      (typ ≠ 0 → typ ≠ 1 → (L.testBit (rd6 TP (κ x)) = true ↔ ∀ n ∈ Phi' Q, x * n = n * x)) := by
  obtain ⟨-, -, -, -, hpc, hpg, hpt, hp0⟩ := fr_sound hκ hN hQK hQN hc
  have hxK := hQK hxQ
  have h := (allL_iff.1 hl) _ (mem_nodeL hN ((hQN _).1 ⟨x, hxQ, rfl⟩))
  rw [beq_iff_eq] at h
  rw [h, labK]
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h0 h1 => ?_⟩
  · have : Nat.beq typ 0 = true := by rw [h0]; rfl
    rw [this, cond_true, Nat.beq_eq]
    exact ⟨fun e => hκ.inj x hxK z hzK e, fun e => by rw [e]⟩
  · have a : Nat.beq typ 0 = false := by rw [h1]; rfl
    have b : Nat.beq typ 1 = true := by rw [h1]; rfl
    rw [a, b, cond_false, cond_true, Bool.not_eq_true', ← hκ.mul x hxK x hxK, ← hκ.one]
    constructor
    · intro hne heq
      rw [heq, Nat.beq_refl] at hne
      exact Bool.noConfusion hne
    · intro hne
      cases hb : Nat.beq (κ (x * x)) (κ 1) with
      | false => rfl
      | true => exact absurd (hκ.inj _ (K.mul_mem hxK hxK) _ K.one_mem (Nat.eq_of_beq_eq_true hb)) hne
  · have a : Nat.beq typ 0 = false := beq_false_nat h0
    have b : Nat.beq typ 1 = false := beq_false_nat h1
    rw [a, b, cond_false, cond_false, allL_iff]
    have hPK : Phi' Q ≤ K := (Phi'_le Q).trans hQK
    constructor
    · intro hall n hn
      have key := treeF_closure hpt hp0 (fun c => ∃ y ∈ K, κ y = c ∧ x * y = y * x)
        (fun c hc => ⟨1, K.one_mem, by rw [testBit_idM hc, hκ.one], by group⟩)
        (fun c ⟨y, hy, hyc, hxy⟩ g hg => by
          obtain ⟨r, hr, hrg⟩ := hpg g hg
          have hrK := hPK hr
          have hc' := Nat.eq_of_beq_eq_true (hall g hg)
          rw [← hrg, ← hκ.mul x hxK r hrK, ← hκ.mul r hrK x hxK] at hc'
          have hxr := hκ.inj _ (K.mul_mem hxK hrK) _ (K.mul_mem hrK hxK) hc'
          refine ⟨y * r, K.mul_mem hy hrK, by rw [hκ.mul y hy r hrK, hyc, hrg], ?_⟩
          rw [← mul_assoc, hxy, mul_assoc, hxr, mul_assoc])
      obtain ⟨y, hy, hyn, hxy⟩ := key (κ n) ((hpc _).2 ⟨n, hn, rfl⟩)
      rw [← hκ.inj y hy n (hPK hn) hyn]
      exact hxy
    · intro hall g hg
      obtain ⟨r, hr, rfl⟩ := hpg g hg
      rw [← hκ.mul x hxK r (hPK hr), ← hκ.mul r (hPK hr) x hxK, hall r hr, Nat.beq_refl]

end Fr

theorem frAll_spec {M : Mdl} {z : ℕ} {nm : List ℕ} {ngs nts : List (List ℕ)} {is ps : List ℕ}
    {pgs prs pts : List (List ℕ)} {cs ds : List ℕ} {wss : List (List ℕ)} {ys ls : List ℕ}
    (h : frAll M z nm ngs nts is ps pgs prs pts cs ds wss ys ls = true) {j : ℕ}
    (hj : j < is.length) :
    frChk M (nm.getD (is.getD j 0) 0) (ngs.getD (is.getD j 0) []) (nts.getD (is.getD j 0) [])
        (ps.getD j 0) (pgs.getD j []) (prs.getD j []) (pts.getD j []) (cs.getD j 0) (ds.getD j 0)
        (wss.getD j []) = true ∧
      labChk M z (nts.getD (is.getD j 0) []) (pgs.getD j []) (cs.getD j 0) (ys.getD j 0)
        (ls.getD j 0) = true := by
  have := (allL_iff.1 h) j (List.mem_range.2 hj)
  rwa [Bool.and_eq_true] at this

end CFSG.KS.S1277Fr

end
