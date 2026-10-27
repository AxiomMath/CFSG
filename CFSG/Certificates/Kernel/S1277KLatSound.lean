module

public import Certificates.Data.Kernel.S1277KLat
public import CFSG.Certificates.Kernel.S1277KModSound
public import Mathlib.GroupTheory.PGroup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Lat

open CFSG.KC.S1277Lat

theorem allL_iff {l : List ℕ} {f : ℕ → Bool} : allL l f = true ↔ ∀ a ∈ l, f a = true := by
  induction l with
  | nil => exact ⟨fun _ a ha => absurd ha List.not_mem_nil, fun _ => rfl⟩
  | cons a l ih =>
    change (f a && allL l f) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem comm_of_card_six {Γ : Type} [Group Γ] [Finite Γ] (h6 : Nat.card Γ = 6) {R : Subgroup Γ}
    (hR : R.Normal) (h2 : Nat.card R = 2) (x y : Γ) : x * y = y * x := by
  classical
  obtain ⟨⟨n, hnR⟩, hn1, hnu⟩ := (Nat.card_eq_two_iff' (1 : R)).1 h2
  have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
  have hcen : ∀ g : Γ, g * n * g⁻¹ = n := by
    intro g
    have hm : g * n * g⁻¹ ∈ R := hR.conj_mem n hnR g
    have hne : (⟨g * n * g⁻¹, hm⟩ : R) ≠ 1 := by
      intro h
      apply hn1'
      have h' : g * n * g⁻¹ = 1 := congrArg Subtype.val h
      have : n = g⁻¹ * (g * n * g⁻¹) * g := by group
      rw [this, h']
      group
    have := hnu _ hne
    exact congrArg Subtype.val this
  have hon : orderOf n = 2 := by
    have hdvd : orderOf (⟨n, hnR⟩ : R) ∣ 2 := h2 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hn1'
    · exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 3 (by rw [h6]; norm_num)
  have hcomm : Commute n c := by
    have := hcen c
    rw [Commute, SemiconjBy]
    calc n * c = c * n * c⁻¹ * c := by rw [this]
      _ = c * n := by group
  have hord : orderOf (n * c) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hon, hc]; norm_num), hon, hc]
  have hcyc : IsCyclic Γ := isCyclic_of_orderOf_eq_card (n * c) (by rw [hord, h6])
  exact hcyc.commGroup.mul_comm x y

theorem le_of_index_six {H : Type} [Group H] [Finite H] {N : Subgroup H} [hN : N.Normal]
    (h6 : N.index = 6) {a b : H} (hab : a * b * a⁻¹ * b⁻¹ ∉ N) {Q : Subgroup H} (hQn : Q.Normal)
    (hQ : IsPGroup 2 Q) : Q ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (H ⧸ N) = 6 := h6
  let φ := QuotientGroup.mk' N
  have hQ'n : (Q.map φ).Normal := hQn.map φ (QuotientGroup.mk'_surjective N)
  have hQ'2 : IsPGroup 2 (Q.map φ) := hQ.map φ
  suffices hb : Q.map φ = ⊥ by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    exact hb
  obtain ⟨k, hk⟩ := hQ'2.exists_card_eq
  have hdvd : Nat.card (Q.map φ) ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 h).trans (hk ▸ hdvd)
    norm_num at h4
  interval_cases k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk]; rfl)
  · exfalso
    apply hab
    have hc := comm_of_card_six hcard hQ'n (by rw [hk]; rfl) (φ a) (φ b)
    rw [← QuotientGroup.eq_one_iff]
    change φ (a * b * a⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group

structure MCod {G : Type} [Group G] (K : Subgroup G) (M : Mdl) (κ : G → ℕ) : Prop where
  mul : ∀ x ∈ K, ∀ y ∈ K, κ (x * y) = M.mul (κ x) (κ y)
  inv : ∀ x ∈ K, κ x⁻¹ = M.inv (κ x)
  inj : ∀ x ∈ K, ∀ y ∈ K, κ x = κ y → x = y
  lt : ∀ x ∈ K, κ x < M.nb * 64
  surj : ∀ n < M.nb * 64, ∃ x ∈ K, κ x = n
  one : κ 1 = M.one * 64

theorem treeF_cons (M : Mdl) (gs : List ℕ) (t : ℕ) (ts : List ℕ) (s : ℕ) :
    treeF M gs (t :: ts) s = treeF M gs ts (treeStep M gs s t) := by
  change CFSG.KC.Enum.strictN (treeStep M gs s t) (fun s => treeF M gs ts s) = _
  generalize treeStep M gs s t = y
  cases y <;> rfl

theorem treeF_zero (M : Mdl) (gs : List ℕ) : ∀ ts : List ℕ, treeF M gs ts 0 = 0
  | [] => rfl
  | t :: ts => by
    rw [treeF_cons]
    have e : treeStep M gs 0 t = 0 := by simp [treeStep]
    rw [e]
    exact treeF_zero M gs ts

theorem treeStep_ok {M : Mdl} {gs : List ℕ} {s t : ℕ} (h : treeStep M gs s t ≠ 0) :
    treeStep M gs s t = s ||| 1 <<< (t % 4096) ∧ s.testBit ((t >>> 12) % 4096) = true ∧
      s.testBit (t % 4096) = false ∧ t % 4096 < M.nb * 64 ∧ t >>> 24 < gs.length ∧
      M.mul ((t >>> 12) % 4096) (gs.getD (t >>> 24) 0) = t % 4096 := by
  unfold treeStep at h ⊢
  by_cases hc : (s.testBit ((t >>> 12) % 4096) && !s.testBit (t % 4096) &&
      Nat.blt (t % 4096) (M.nb * 64) && Nat.blt (t >>> 24) gs.length &&
      Nat.beq (M.mul ((t >>> 12) % 4096) (gs.getD (t >>> 24) 0)) (t % 4096)) = true
  · rw [hc]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    exact ⟨rfl, h1, h2, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5⟩
  · rw [Bool.not_eq_true] at hc
    rw [hc] at h
    exact absurd rfl h

theorem testBit_or_one_shiftLeft (s y x : ℕ) :
    (s ||| 1 <<< y).testBit x = (s.testBit x || decide (y = x)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem treeF_closure {M : Mdl} {gs ts : List ℕ} {s m : ℕ} (h : treeF M gs ts s = m) (hm : m ≠ 0)
    (P : ℕ → Prop) (hs : ∀ x, s.testBit x = true → P x)
    (hstep : ∀ x, P x → ∀ g ∈ gs, P (M.mul x g)) : ∀ x, m.testBit x = true → P x := by
  induction ts generalizing s with
  | nil =>
    subst h
    exact hs
  | cons t ts ih =>
    rw [treeF_cons] at h
    have hne : treeStep M gs s t ≠ 0 := by
      intro e
      rw [e, treeF_zero] at h
      exact hm h.symm
    obtain ⟨e, hp, -, -, hg, hmul⟩ := treeStep_ok hne
    refine ih h ?_
    intro x hx
    rw [e, testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with hx | rfl
    · exact hs x hx
    · rw [← hmul]
      refine hstep _ (hs _ hp) _ ?_
      have e' : gs.getD (t >>> 24) 0 = gs[t >>> 24] := by
        simp [List.getD_eq_getElem?_getD, hg]
      rw [e']
      exact List.getElem_mem hg

theorem oxF_cons (M : Mdl) (nm cr : List ℕ) (t : ℕ) (ts : List ℕ) (s : ℕ) :
    oxF M nm cr (t :: ts) s = oxF M nm cr ts (oxStep M nm cr s t) := by
  change CFSG.KC.Enum.strictN (oxStep M nm cr s t) (fun s => oxF M nm cr ts s) = _
  generalize oxStep M nm cr s t = y
  cases y <;> rfl

theorem oxF_mem_aux {M : Mdl} {nm cr : List ℕ} : ∀ (ts : List ℕ) (s x : ℕ),
    (oxF M nm cr ts s >>> 12).testBit x = true → (s >>> 12).testBit x = true ∨
    ∃ t ∈ ts, t % 4096 = x ∧ x < M.nb * 64 ∧ t >>> 24 < M.nb * 64 ∧
      (t >>> 12) % 4096 < cr.length ∧
      M.mul (t >>> 24) (cr.getD ((t >>> 12) % 4096) 0 % 4096) = M.mul x (t >>> 24) ∧
      (nm.getD (cr.getD ((t >>> 12) % 4096) 0 >>> 12) 0).testBit x = true
  | [], s, x, hx => Or.inl hx
  | t :: ts, s, x, hx => by
    rw [oxF_cons] at hx
    rcases oxF_mem_aux ts _ x hx with hx' | ⟨t', ht', hrest⟩
    · unfold oxStep at hx'
      by_cases hc : (Nat.blt (t % 4096) (M.nb * 64) && Nat.ble (s % 4096) (t % 4096) &&
          Nat.blt (t >>> 24) (M.nb * 64) && Nat.blt ((t >>> 12) % 4096) cr.length &&
          Nat.beq (M.mul (t >>> 24) (cr.getD ((t >>> 12) % 4096) 0 % 4096))
            (M.mul (t % 4096) (t >>> 24)) &&
          (nm.getD (cr.getD ((t >>> 12) % 4096) 0 >>> 12) 0).testBit (t % 4096)) = true
      · rw [hc] at hx'
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
        have hy : t % 4096 < 2 ^ (12 + x) :=
          lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
            (by rw [show (4096 : ℕ) = 2 ^ 12 by norm_num]; exact Nat.pow_le_pow_right two_pos (by omega))
        simp only [cond_true] at hx'
        rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_lt_two_pow hy, Bool.or_false,
          Nat.testBit_shiftLeft, Nat.add_sub_cancel_left] at hx'
        simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and] at hx'
        rw [testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_eq] at hx'
        rcases hx' with hx' | rfl
        · exact Or.inl hx'
        · exact Or.inr ⟨t, List.mem_cons_self, rfl, Nat.blt_eq.mp h1, Nat.blt_eq.mp h3,
            Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5, h6⟩
      · rw [Bool.not_eq_true] at hc
        rw [hc] at hx'
        simp at hx'
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hrest⟩

theorem oxF_mem {M : Mdl} {nm cr ts : List ℕ} {x : ℕ}
    (hx : (oxF M nm cr ts 0 >>> 12).testBit x = true) :
    ∃ t ∈ ts, t % 4096 = x ∧ x < M.nb * 64 ∧ t >>> 24 < M.nb * 64 ∧ (t >>> 12) % 4096 < cr.length ∧
      M.mul (t >>> 24) (cr.getD ((t >>> 12) % 4096) 0 % 4096) = M.mul x (t >>> 24) ∧
      (nm.getD (cr.getD ((t >>> 12) % 4096) 0 >>> 12) 0).testBit x = true := by
  rcases oxF_mem_aux ts 0 x hx with h | h
  · simp at h
  · exact h

theorem nodesChk_spec {M : Mdl} {kg : List ℕ} :
    ∀ {ms : List ℕ} {gss tss : List (List ℕ)} {es : List ℕ}, nodesChk M kg ms gss tss es = true →
      ∀ i < ms.length, nodeChk M kg (ms.getD i 0) (gss.getD i []) (tss.getD i []) (es.getD i 0) = true
  | m :: ms, gs :: gss, ts :: tss, e :: es, h, i, hi => by
    rw [nodesChk, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i => exact nodesChk_spec h.2 i (by simpa using hi)
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h, _, _ => by simp [nodesChk] at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp [nodesChk] at h
  | _ :: _, _ :: _, _ :: _, [], h, _, _ => by simp [nodesChk] at h

theorem clsChk_spec {M : Mdl} {nm : List ℕ} :
    ∀ {cs : List ℕ} {gss kss tss : List (List ℕ)}, clsChk M nm cs gss kss tss = true →
      ∀ c < cs.length, clsChk1 M nm (cs.getD c 0) (gss.getD c []) (kss.getD c []) (tss.getD c []) = true
  | c :: cs, gs :: gss, ks :: kss, ts :: tss, h, i, hi => by
    rw [clsChk, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i => exact clsChk_spec h.2 i (by simpa using hi)
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h, _, _ => by simp [clsChk] at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp [clsChk] at h
  | _ :: _, _ :: _, _ :: _, [], h, _, _ => by simp [clsChk] at h

theorem joinRow_spec {M : Mdl} {nm : List ℕ} {ngs : List (List ℕ)} {m : ℕ} :
    ∀ {cs : List ℕ} {ds : List (List ℕ)}, joinRow M nm ngs m cs ds = true →
      ∀ j < cs.length, join1 M nm ngs m (cs.getD j 0) (ds.getD j []) = true
  | c :: cs, d :: ds, h, j, hj => by
    rw [joinRow, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact joinRow_spec h.2 j (by simpa using hj)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => by simp [joinRow] at h

theorem joinChk_spec {M : Mdl} {nm : List ℕ} {ngs : List (List ℕ)} {cr : List ℕ} :
    ∀ {ms : List ℕ} {rs : List (List (List ℕ))}, joinChk M nm ngs cr ms rs = true →
      ∀ i < ms.length, ∀ j < cr.length,
        join1 M nm ngs (ms.getD i 0) (cr.getD j 0) ((rs.getD i []).getD j []) = true
  | m :: ms, r :: rs, h, i, hi, j, hj => by
    rw [joinChk, Bool.and_eq_true] at h
    cases i with
    | zero => exact joinRow_spec h.1 j hj
    | succ i => exact joinChk_spec h.2 i (by simpa using hi) j hj
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _, _, _ => by simp [joinChk] at h

theorem testBit_of_or_eq {a m : ℕ} (h : (a ||| m) = m) {x : ℕ} (hx : a.testBit x = true) :
    m.testBit x = true := by
  rw [← h, Nat.testBit_or, hx, Bool.true_or]

theorem join1_spec {M : Mdl} {nm : List ℕ} {ngs : List (List ℕ)} {m c : ℕ} {d : List ℕ}
    (h : join1 M nm ngs m c d = true) :
    (∀ x, (nm.getD (c >>> 12) 0).testBit x = true → m.testBit x = true) ∨
      ∃ J < nm.length, (∀ x, m.testBit x = true → (nm.getD J 0).testBit x = true) ∧
        (∀ x, (nm.getD (c >>> 12) 0).testBit x = true → (nm.getD J 0).testBit x = true) ∧
        ∀ g ∈ ngs.getD J [], ∃ a b, m.testBit a = true ∧ (nm.getD (c >>> 12) 0).testBit b = true ∧
          M.mul a b = g := by
  unfold join1 at h
  cases hb : Nat.beq (nm.getD (c >>> 12) 0 ||| m) m with
  | true => exact Or.inl fun x hx => testBit_of_or_eq (Nat.eq_of_beq_eq_true hb) hx
  | false =>
    rw [hb, cond_false] at h
    right
    match d, h with
    | J :: ds, h =>
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨⟨⟨hJ, hsup⟩, hlen⟩, hall⟩ := h
      have hsup' := Nat.eq_of_beq_eq_true hsup
      have hlen' := Nat.eq_of_beq_eq_true hlen
      refine ⟨J, hJ, fun x hx => testBit_of_or_eq hsup'
          (by rw [Nat.testBit_or, hx, Bool.true_or]),
        fun x hx => testBit_of_or_eq hsup' (by rw [Nat.testBit_or, hx, Bool.or_true]), ?_⟩
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      have := (allL_iff.1 hall) t (List.mem_range.2 (hlen' ▸ ht))
      simp only [Bool.and_eq_true] at this
      obtain ⟨⟨h1, h2⟩, h3⟩ := this
      refine ⟨_, _, h1, h2, ?_⟩
      rw [Nat.eq_of_beq_eq_true h3, CFSG.KS.S1277Mod.getD_eq_get _ ht]

section Classification

variable {G : Type} [Group G] {K : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem testBit_idM {M : Mdl} {x : ℕ} (h : (idM M).testBit x = true) : x = M.one * 64 := by
  rw [idM, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
  exact (of_decide_eq_true h).symm

theorem tree_sub (hκ : MCod K M κ) {Q : Subgroup G} (hQK : Q ≤ K) {gs ts : List ℕ} {m : ℕ}
    (h : treeF M gs ts (idM M) = m) (hm : m ≠ 0) (hg : ∀ g ∈ gs, ∃ q ∈ Q, κ q = g) :
    ∀ x, m.testBit x = true → ∃ q ∈ Q, κ q = x := by
  refine treeF_closure h hm _ (fun x hx => ⟨1, Q.one_mem, by rw [testBit_idM hx, hκ.one]⟩) ?_
  rintro x ⟨q, hq, rfl⟩ g hgs
  obtain ⟨q', hq', rfl⟩ := hg g hgs
  exact ⟨q * q', Q.mul_mem hq hq', hκ.mul q (hQK hq) q' (hQK hq')⟩

theorem ne_zero_of_testBit {m x : ℕ} (h : m.testBit x = true) : m ≠ 0 := by
  rintro rfl
  simp at h

theorem classificationK (hκ : MCod K M κ) {kg nm nxs cr ox : List ℕ}
    {ngs nts cgs cks cts : List (List ℕ)} {jt : List (List (List ℕ))} {ol : ℕ}
    (hnodes : nodesChk M kg nm ngs nts nxs = true) (hcls : clsChk M nm cr cgs cks cts = true)
    (hox : oxChk M nm cr ox ol = true) (hjoin : joinChk M nm ngs cr nm jt = true)
    (hbot : botChk M nm = true)
    {Q : Subgroup G} (hQK : Q ≤ K) (hQn : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hQO : ∀ q ∈ Q, (nm.getD ol 0).testBit (κ q) = true) :
    ∃ i < nm.length, ∀ n, (∃ q ∈ Q, κ q = n) ↔ (nm.getD i 0).testBit n = true := by
  classical
  have lift : ∀ n < M.nb * 64, ∃ x ∈ K, κ x = n := hκ.surj
  have conj_eq : ∀ k ∈ K, ∀ r ∈ K, ∀ g ∈ K, M.mul (κ k) (κ r) = M.mul (κ g) (κ k) →
      g = k * r * k⁻¹ := by
    intro k hk r hr g hg e
    rw [← hκ.mul k hk r hr, ← hκ.mul g hg k hk] at e
    have := hκ.inj _ (K.mul_mem hk hr) _ (K.mul_mem hg hk) e
    rw [this]
    group
  have hnode : ∀ J < nm.length, treeF M (ngs.getD J []) (nts.getD J []) (idM M) = nm.getD J 0 ∧
      nm.getD J 0 ≠ 0 := by
    intro J hJ
    have h := nodesChk_spec hnodes J hJ
    rw [nodeChk] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩ := h
    exact ⟨Nat.eq_of_beq_eq_true h2, ne_zero_of_testBit h1⟩
  have hcl : ∀ x, (∃ q ∈ Q, κ q = x) → ∃ c < cr.length,
      (nm.getD (cr.getD c 0 >>> 12) 0).testBit x = true ∧
      ∀ y, (nm.getD (cr.getD c 0 >>> 12) 0).testBit y = true → ∃ q ∈ Q, κ q = y := by
    rintro x ⟨q, hq, rfl⟩
    have hxO := hQO q hq
    rw [oxChk] at hox
    rw [← Nat.eq_of_beq_eq_true hox] at hxO
    obtain ⟨t, -, -, hxlt, hklt, hc, he, hxin⟩ := oxF_mem hxO
    set c := (t >>> 12) % 4096
    have h1 := clsChk_spec hcls c hc
    rw [clsChk1] at h1
    simp only [Bool.and_eq_true, Nat.blt_eq] at h1
    obtain ⟨⟨⟨⟨⟨hp, hr⟩, htree⟩, hrin⟩, -⟩, hgen⟩ := h1
    obtain ⟨k, hk, hkκ⟩ := lift _ hklt
    obtain ⟨r, hrK, hrκ⟩ := lift _ hr
    have hrQ : r ∈ Q := by
      have e : M.mul (κ k) (κ r) = M.mul (κ q) (κ k) := by rw [hkκ, hrκ]; exact he
      have := conj_eq k hk r hrK q (hQK hq) e
      have hr' : r = k⁻¹ * q * k⁻¹⁻¹ := by rw [this]; group
      rw [hr']
      exact hQn _ (K.inv_mem hk) q hq
    refine ⟨c, hc, hxin, ?_⟩
    refine tree_sub hκ hQK (Nat.eq_of_beq_eq_true htree) (ne_zero_of_testBit hrin) ?_
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have h2 := (allL_iff.1 hgen) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, Nat.blt_eq] at h2
    obtain ⟨⟨hki, hgi⟩, hei⟩ := h2
    obtain ⟨k', hk', hk'κ⟩ := lift _ hki
    obtain ⟨g', hg', hg'κ⟩ := lift _ hgi
    have e : M.mul (κ k') (κ r) = M.mul (κ g') (κ k') := by
      rw [hk'κ, hrκ, hg'κ]; exact Nat.eq_of_beq_eq_true hei
    refine ⟨g', ?_, by rw [hg'κ, CFSG.KS.S1277Mod.getD_eq_get _ hi]⟩
    rw [conj_eq k' hk' r hrK g' hg' e]
    exact hQn k' hk' r hrQ
  have key : ∀ l : List ℕ, (∀ x ∈ l, ∃ q ∈ Q, κ q = x) → ∃ i < nm.length,
      (∀ x ∈ l, (nm.getD i 0).testBit x = true) ∧
      ∀ y, (nm.getD i 0).testBit y = true → ∃ q ∈ Q, κ q = y := by
    intro l
    induction l with
    | nil =>
      intro _
      have h0 : 0 < nm.length := by
        rcases nm with _ | ⟨a, _⟩
        · rw [botChk] at hbot
          have hb := Nat.eq_of_beq_eq_true hbot
          rw [idM, Nat.one_shiftLeft] at hb
          exact absurd hb.symm (pow_ne_zero _ two_ne_zero)
        · simp
      refine ⟨0, h0, fun x hx => absurd hx List.not_mem_nil, fun y hy => ?_⟩
      rw [botChk] at hbot
      rw [Nat.eq_of_beq_eq_true hbot] at hy
      exact ⟨1, Q.one_mem, by rw [testBit_idM hy, hκ.one]⟩
    | cons x l ih =>
      intro hl
      obtain ⟨i, hi, hli, hiQ⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      obtain ⟨c, hc, hxp, hpQ⟩ := hcl x (hl x List.mem_cons_self)
      rcases join1_spec (joinChk_spec hjoin i hi c hc) with hsub | ⟨J, hJ, hmJ, hpJ, hgJ⟩
      · refine ⟨i, hi, ?_, hiQ⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hsub _ hxp
        · exact hli y hy
      · refine ⟨J, hJ, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hpJ _ hxp
          · exact hmJ _ (hli y hy)
        · refine tree_sub hκ hQK (hnode J hJ).1 (hnode J hJ).2 ?_
          intro g hg
          obtain ⟨a, b, ha, hb, rfl⟩ := hgJ g hg
          obtain ⟨qa, hqa, rfl⟩ := hiQ a ha
          obtain ⟨qb, hqb, rfl⟩ := hpQ b hb
          exact ⟨qa * qb, Q.mul_mem hqa hqb, hκ.mul qa (hQK hqa) qb (hQK hqb)⟩
  obtain ⟨i, hi, hl, hiQ⟩ := key ((List.range (M.nb * 64)).filter fun n => decide (∃ q ∈ Q, κ q = n))
    (fun x hx => of_decide_eq_true (List.mem_filter.1 hx).2)
  refine ⟨i, hi, fun n => ⟨fun hn => hl n ?_, hiQ n⟩⟩
  obtain ⟨q, hq, rfl⟩ := hn
  exact List.mem_filter.2 ⟨List.mem_range.2 (hκ.lt q (hQK hq)), decide_eq_true ⟨q, hq, rfl⟩⟩

end Classification

theorem treeF_bits {M : Mdl} {gs ts : List ℕ} {s m : ℕ} (h : treeF M gs ts s = m) (hm : m ≠ 0) :
    (∀ x, m.testBit x = true ↔ s.testBit x = true ∨ x ∈ ts.map (· % 4096)) ∧
      (ts.map (· % 4096)).Nodup ∧
      ∀ x ∈ ts.map (· % 4096), s.testBit x = false ∧ x < M.nb * 64 := by
  induction ts generalizing s with
  | nil =>
    subst h
    exact ⟨fun x => ⟨Or.inl, fun h => h.elim id (fun h => absurd h List.not_mem_nil)⟩,
      List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩
  | cons t ts ih =>
    rw [treeF_cons] at h
    have hne : treeStep M gs s t ≠ 0 := by
      intro e
      rw [e, treeF_zero] at h
      exact hm h.symm
    obtain ⟨e, -, hy0, hylt, -, -⟩ := treeStep_ok hne
    obtain ⟨i1, i2, i3⟩ := ih h
    rw [e] at i1 i3
    have hb : ∀ x, (s ||| 1 <<< (t % 4096)).testBit x = true ↔
        s.testBit x = true ∨ t % 4096 = x := by
      intro x
      rw [testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨fun x => ?_, ?_, ?_⟩
    · rw [i1, hb, List.map_cons, List.mem_cons]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1.symm)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1.symm)
        · exact Or.inr h1
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, i2⟩
      have h1 := (i3 _ hmem).1
      have h2 := (hb (t % 4096)).2 (Or.inr rfl)
      rw [h1] at h2
      exact Bool.false_ne_true h2
    · intro x hx
      rw [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hy0, hylt⟩
      · obtain ⟨h1, h2⟩ := i3 x hx
        refine ⟨?_, h2⟩
        cases hs : s.testBit x
        · rfl
        · have := (hb x).2 (Or.inl hs)
          rw [h1] at this
          exact absurd this Bool.false_ne_true

section OPart

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem mul_assoc_codes (hκ : MCod K M κ) {a b c : ℕ} (ha : a < M.nb * 64) (hb : b < M.nb * 64)
    (hc : c < M.nb * 64) : M.mul (M.mul a b) c = M.mul a (M.mul b c) := by
  obtain ⟨x, hx, rfl⟩ := hκ.surj a ha
  obtain ⟨y, hy, rfl⟩ := hκ.surj b hb
  obtain ⟨z, hz, rfl⟩ := hκ.surj c hc
  rw [← hκ.mul x hx y hy, ← hκ.mul _ (K.mul_mem hx hy) z hz, ← hκ.mul y hy z hz,
    ← hκ.mul x hx _ (K.mul_mem hy hz), mul_assoc]

theorem node_mul (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {a b : ℕ} (ha : m.testBit a = true)
    (hb : m.testBit b = true) : m.testBit (M.mul a b) = true := by
  rw [nodeChk] at hN
  simp only [Bool.and_eq_true] at hN
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, hg3⟩, hr⟩ := hN
  have htree := Nat.eq_of_beq_eq_true h2
  have hm : m ≠ 0 := ne_zero_of_testBit h1
  obtain ⟨hbits, -, hlt⟩ := treeF_bits htree hm
  have hlt' : ∀ x, m.testBit x = true → x < M.nb * 64 := by
    intro x hx
    rcases (hbits x).1 hx with hx | hx
    · rw [testBit_idM hx, ← hκ.one]
      exact hκ.lt 1 K.one_mem
    · exact (hlt x hx).2
  have hrg : ∀ x, m.testBit x = true → ∀ g ∈ gs, m.testBit (M.mul x g) = true := by
    intro x hx g hg
    have hx' : x ∈ M.one * 64 :: ts.map (· % 4096) := by
      rcases (hbits x).1 hx with hx | hx
      · rw [testBit_idM hx]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hx
    exact (allL_iff.1 ((allL_iff.1 hr) x hx')) g hg
  have hone : ∀ a, a < M.nb * 64 → M.mul a (M.one * 64) = a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hκ.surj a ha
    rw [← hκ.one, ← hκ.mul x hx 1 K.one_mem, mul_one]
  have hgl : ∀ g ∈ gs, g < M.nb * 64 := by
    intro g hg
    have := (allL_iff.1 hg3) g hg
    rw [Bool.and_eq_true] at this
    exact hlt' g this.1
  have hmulc : ∀ x y, x < M.nb * 64 → y < M.nb * 64 → M.mul x y < M.nb * 64 := by
    intro x y hx hy
    obtain ⟨u, hu, rfl⟩ := hκ.surj x hx
    obtain ⟨v, hv, rfl⟩ := hκ.surj y hy
    rw [← hκ.mul u hu v hv]
    exact hκ.lt _ (K.mul_mem hu hv)
  have key := treeF_closure htree hm
    (fun n => n < M.nb * 64 ∧ ∀ a, m.testBit a = true → m.testBit (M.mul a n) = true)
    (fun x hx => by
      rw [testBit_idM hx]
      refine ⟨by rw [← hκ.one]; exact hκ.lt 1 K.one_mem, fun a ha => ?_⟩
      rw [hone a (hlt' a ha)]
      exact ha)
    (fun n ⟨hn, hP⟩ g hg => by
      refine ⟨hmulc n g hn (hgl g hg), fun a ha => ?_⟩
      rw [← mul_assoc_codes hκ (hlt' a ha) hn (hgl g hg)]
      exact hrg _ (hP a ha) g hg)
  exact (key b hb).2 a ha

theorem codes_lt (hκ : MCod K M κ) {gs ts : List ℕ} {m : ℕ} (htree : treeF M gs ts (idM M) = m)
    (hm : m ≠ 0) {x : ℕ} (hx : m.testBit x = true) : x < M.nb * 64 := by
  rcases ((treeF_bits htree hm).1 x).1 hx with hx | hx
  · rw [testBit_idM hx, ← hκ.one]
    exact hκ.lt 1 K.one_mem
  · exact ((treeF_bits htree hm).2.2 x hx).2

theorem node_subgroup (hκ : MCod K M κ) {kg kt nm nxs : List ℕ} {ngs nts : List (List ℕ)}
    (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true) {i : ℕ}
    (hi : i < nm.length) :
    ∃ O : Subgroup K, O.Normal ∧ (∀ x : K, x ∈ O ↔ (nm.getD i 0).testBit (κ x) = true) ∧
      Nat.card O = 2 ^ nxs.getD i 0 := by
  classical
  have hN := nodesChk_spec hnodes i hi
  set m := nm.getD i 0 with hmdef
  set gs := ngs.getD i [] with hgsdef
  set ts := nts.getD i [] with htsdef
  have hN' := hN
  rw [nodeChk] at hN'
  simp only [Bool.and_eq_true] at hN'
  obtain ⟨⟨⟨⟨h1, h2⟩, hcnt⟩, hg3⟩, -⟩ := hN'
  have htree := Nat.eq_of_beq_eq_true h2
  have hm : m ≠ 0 := ne_zero_of_testBit h1
  let O : Subgroup K :=
    { carrier := {x | m.testBit (κ x) = true}
      one_mem' := by
        change m.testBit (κ 1) = true
        rw [hκ.one]; exact h1
      mul_mem' := fun {x y} hx hy => by
        change m.testBit (κ (x.1 * y.1)) = true
        rw [hκ.mul x.1 x.2 y.1 y.2]
        exact node_mul hκ hN hx hy
      inv_mem' := fun {x} hx => by
        have hpow : ∀ n : ℕ, m.testBit (κ (x ^ n).1) = true := by
          intro n
          induction n with
          | zero => rw [pow_zero]; change m.testBit (κ 1) = true; rw [hκ.one]; exact h1
          | succ n ih =>
            rw [pow_succ]
            change m.testBit (κ ((x ^ n).1 * x.1)) = true
            rw [hκ.mul _ (x ^ n).2 _ x.2]
            exact node_mul hκ hN ih hx
        have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ',
            Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        change m.testBit (κ (x⁻¹).1) = true
        rw [hinv]
        exact hpow _ }
  have hOmem : ∀ x : K, x ∈ O ↔ m.testBit (κ x) = true := fun x => Iff.rfl
  have hconjg : ∀ g ∈ kg, ∀ x ∈ K, m.testBit (κ x) = true → ∀ gr ∈ K, κ gr = g →
      m.testBit (κ (gr * x * gr⁻¹)) = true := by
    intro g hg x hxK hx gr hgr hgrκ
    have key := treeF_closure htree hm
      (fun c => ∃ y ∈ K, κ y = c ∧ m.testBit (κ (gr * y * gr⁻¹)) = true)
      (fun c hc => ⟨1, K.one_mem, by rw [testBit_idM hc, hκ.one], by
        rw [mul_one, mul_inv_cancel, hκ.one]; exact h1⟩)
      (fun c ⟨y, hy, hyc, hyb⟩ h hh => by
        have hh3 := (allL_iff.1 hg3) h hh
        rw [Bool.and_eq_true] at hh3
        obtain ⟨hr, hrK, rfl⟩ := hκ.surj h (codes_lt hκ htree hm hh3.1)
        refine ⟨y * hr, K.mul_mem hy hrK, by rw [hκ.mul y hy hr hrK, hyc], ?_⟩
        have e : gr * (y * hr) * gr⁻¹ = (gr * y * gr⁻¹) * (gr * hr * gr⁻¹) := by group
        have hgK : gr⁻¹ ∈ K := K.inv_mem hgr
        rw [e, hκ.mul _ (K.mul_mem (K.mul_mem hgr hy) hgK) _ (K.mul_mem (K.mul_mem hgr hrK) hgK)]
        refine node_mul hκ hN hyb ?_
        have hc := (allL_iff.1 hh3.2) g hg
        rw [hκ.mul _ (K.mul_mem hgr hrK) _ hgK, hκ.mul _ hgr _ hrK, hκ.inv _ hgr, hgrκ]
        exact hc)
    obtain ⟨y, hy, hyx, hyb⟩ := key (κ x) hx
    rw [hκ.inj y hy x hxK hyx] at hyb
    exact hyb
  rw [genChk, Bool.and_eq_true] at hgen
  obtain ⟨hkg, hall⟩ := hgen
  have hall' := Nat.eq_of_beq_eq_true hall
  have hpos : 0 < M.nb * 64 := lt_of_le_of_lt (Nat.zero_le _) (hκ.lt 1 K.one_mem)
  have hfull : (2 ^ (M.nb * 64) - 1 : ℕ) ≠ 0 := by
    have : 2 ≤ 2 ^ (M.nb * 64) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (M.nb * 64) := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hconj : ∀ k ∈ K, ∀ x ∈ K, m.testBit (κ x) = true → m.testBit (κ (k * x * k⁻¹)) = true := by
    have key := treeF_closure hall' hfull
      (fun c => ∃ k ∈ K, κ k = c ∧ ∀ x ∈ K, m.testBit (κ x) = true →
        m.testBit (κ (k * x * k⁻¹)) = true)
      (fun c hc => ⟨1, K.one_mem, by rw [testBit_idM hc, hκ.one], fun x _ hx => by
        rw [one_mul, inv_one, mul_one]; exact hx⟩)
      (fun c ⟨k, hk, hkc, hP⟩ g hg => by
        obtain ⟨gr, hgr, rfl⟩ := hκ.surj g (by have := (allL_iff.1 hkg) g hg; rwa [Nat.blt_eq] at this)
        refine ⟨k * gr, K.mul_mem hk hgr, by rw [hκ.mul k hk gr hgr, hkc], fun x hx hxb => ?_⟩
        have e : k * gr * x * (k * gr)⁻¹ = k * (gr * x * gr⁻¹) * k⁻¹ := by group
        rw [e]
        exact hP _ (K.mul_mem (K.mul_mem hgr hx) (K.inv_mem hgr))
          (hconjg _ hg x hx hxb gr hgr rfl))
    intro k hk x hx hxb
    have hkb : (2 ^ (M.nb * 64) - 1 : ℕ).testBit (κ k) = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true (hκ.lt k hk)
    obtain ⟨k', hk', hk'k, hP⟩ := key (κ k) hkb
    rw [← hκ.inj k' hk' k hk hk'k]
    exact hP x hx hxb
  have hOn : O.Normal := ⟨fun n hn g => hconj g.1 g.2 n.1 n.2 hn⟩
  obtain ⟨hbits, hnd, hnew⟩ := treeF_bits htree hm
  set L := M.one * 64 :: ts.map (· % 4096) with hL
  have hLnd : L.Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
    have := (hnew _ h).1
    rw [idM, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    exact absurd this (by simp)
  have hcardO : Nat.card O = ts.length + 1 := by
    have hbij : Function.Bijective (fun x : O => (⟨κ x.1.1, by
        rw [List.mem_toFinset]
        rcases (hbits _).1 x.2 with h | h
        · rw [testBit_idM h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h⟩ : {n // n ∈ L.toFinset})) := by
      constructor
      · intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext (hκ.inj _ x.1.2 _ y.1.2 this))
      · rintro ⟨n, hn⟩
        rw [List.mem_toFinset] at hn
        have hnb : m.testBit n = true := by
          rcases List.mem_cons.1 hn with rfl | h
          · exact h1
          · exact (hbits n).2 (Or.inr h)
        obtain ⟨x, hx, rfl⟩ := hκ.surj n (codes_lt hκ htree hm hnb)
        exact ⟨⟨⟨x, hx⟩, hnb⟩, rfl⟩
    rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup hLnd, hL, List.length_cons, List.length_map]
  exact ⟨O, hOn, hOmem, by rw [hcardO, Nat.eq_of_beq_eq_true hcnt]⟩

theorem card_K (hκ : MCod K M κ) : Nat.card K = M.nb * 64 := by
  have hbij : Function.Bijective (fun x : K => (⟨κ x.1, hκ.lt x.1 x.2⟩ : Fin (M.nb * 64))) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hκ.inj _ x.2 _ y.2 (congrArg Fin.val hxy))
    · rintro ⟨n, hn⟩
      obtain ⟨x, hx, rfl⟩ := hκ.surj n hn
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem node_subgroupG (hκ : MCod K M κ) {kg kt nm nxs : List ℕ} {ngs nts : List (List ℕ)}
    (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true) {i : ℕ}
    (hi : i < nm.length) :
    ∃ O : Subgroup G, O ≤ K ∧ (∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O) ∧ IsPGroup 2 O ∧
      (∀ x ∈ K, x ∈ O ↔ (nm.getD i 0).testBit (κ x) = true) ∧ Nat.card O = 2 ^ nxs.getD i 0 := by
  obtain ⟨O, hOn, hOmem, hcard⟩ := node_subgroup hκ hgen hnodes hi
  have hc : Nat.card (O.map K.subtype) = 2 ^ nxs.getD i 0 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard]
  refine ⟨O.map K.subtype, fun x hx => ?_, ?_, IsPGroup.of_card hc, ?_, hc⟩
  · obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  · intro k hk o ho
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ho
    exact Subgroup.mem_map.2 ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hOn.conj_mem y hy _, rfl⟩
  · intro x hx
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 h
      exact (hOmem y).1 hy
    · intro h
      exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, (hOmem ⟨x, hx⟩).2 h, rfl⟩

theorem O2_le (hκ : MCod K M κ) {kg kt nm nxs : List ℕ} {ngs nts : List (List ℕ)}
    {ol a b : ℕ} (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true)
    (hq : quotChk M nm nxs ol a b = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQn : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) :
    ∀ q ∈ Q, (nm.getD ol 0).testBit (κ q) = true := by
  classical
  rw [quotChk] at hq
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hq
  obtain ⟨⟨⟨⟨hol, h6⟩, ha⟩, hb⟩, hab⟩ := hq
  obtain ⟨O, hOn, hOmem, hcardO⟩ := node_subgroup hκ hgen hnodes hol
  have hidx : O.index = 6 := by
    have h := O.card_mul_index
    rw [hcardO, card_K hκ, Nat.eq_of_beq_eq_true h6] at h
    have hpos : 0 < 2 ^ nxs.getD ol 0 := by positivity
    have : 2 ^ nxs.getD ol 0 * O.index = 2 ^ nxs.getD ol 0 * 6 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨ar, har, rfl⟩ := hκ.surj a ha
  obtain ⟨br, hbr, rfl⟩ := hκ.surj b hb
  have hab' : (⟨ar, har⟩ : K) * ⟨br, hbr⟩ * (⟨ar, har⟩ : K)⁻¹ * (⟨br, hbr⟩ : K)⁻¹ ∉ O := by
    rw [hOmem]
    change ¬ (nm.getD ol 0).testBit (κ (ar * br * ar⁻¹ * br⁻¹)) = true
    have hK1 : ar * br ∈ K := K.mul_mem har hbr
    have hK2 : ar * br * ar⁻¹ ∈ K := K.mul_mem hK1 (K.inv_mem har)
    rw [hκ.mul _ hK2 _ (K.inv_mem hbr), hκ.mul _ hK1 _ (K.inv_mem har), hκ.mul _ har _ hbr,
      hκ.inv _ har, hκ.inv _ hbr]
    rw [hab]
    simp
  have hQ'n : (Q.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hQn g.1 g.2 n.1 hn⟩
  have hQ'2 : IsPGroup 2 (Q.subgroupOf K) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle := le_of_index_six (N := O) hidx hab' hQ'n hQ'2
  intro q hq
  exact (hOmem ⟨q, hQK hq⟩).1 (hle (by rw [Subgroup.mem_subgroupOf]; exact hq))

theorem normal_two_eq_node (hκ : MCod K M κ) {kg kt nm nxs cr ox : List ℕ}
    {ngs nts cgs cks cts : List (List ℕ)} {jt : List (List (List ℕ))} {ol a b : ℕ}
    (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true)
    (hcls : clsChk M nm cr cgs cks cts = true) (hox : oxChk M nm cr ox ol = true)
    (hjoin : joinChk M nm ngs cr nm jt = true) (hbot : botChk M nm = true)
    (hq : quotChk M nm nxs ol a b = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQn : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) :
    ∃ i < nm.length, ∀ n, (∃ q ∈ Q, κ q = n) ↔ (nm.getD i 0).testBit n = true :=
  classificationK hκ hnodes hcls hox hjoin hbot hQK hQn (O2_le hκ hgen hnodes hq hQK hQn hQ2)

end OPart

end CFSG.KS.S1277Lat

end
