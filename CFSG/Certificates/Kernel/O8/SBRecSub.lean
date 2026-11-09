module

public import CFSG.Certificates.Kernel.O8.SBLowCls

public section

namespace CFSG.KC.SBRec

open CFSG.EvenSmallLie.OmegaEight.SpBranch CFSG.KC.SBCls CFSG.KC.SBLow MulAction

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ} (h0 : mul 0 0 = 0)

include Φ in
theorem mul_lt0 {a b : ℕ} (ha : a < N) (hb : b < N) : mul a b < N := by
  rw [← Φ.f_g ha, ← Φ.f_g hb, ← Φ.map_mul]
  exact Φ.lt _

include Φ h0 in
theorem mul_assoc_c {a b c : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) :
    mul (mul a b) c = mul a (mul b c) := by
  rw [← Φ.f_g ha, ← Φ.f_g hb, ← Φ.f_g hc, ← Φ.map_mul, ← Φ.map_mul, ← Φ.map_mul, ← Φ.map_mul,
    mul_assoc]

include Φ h0 in
theorem foldl_mul_c : ∀ (w : List ℕ) {c : ℕ}, c < N → (∀ a ∈ w, a < N) →
    w.foldl mul c = mul c (w.foldl mul 0) ∧ w.foldl mul c < N
  | [], c, hc, _ => by
    refine ⟨?_, hc⟩
    rw [List.foldl_nil, List.foldl_nil, ← Φ.f_g hc, ← Φ.f_one h0, ← Φ.map_mul, mul_one]
  | a :: w, c, hc, hw => by
    have ha := hw a List.mem_cons_self
    have hw' : ∀ b ∈ w, b < N := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    have h0a : mul 0 a = a := by
      rw [← Φ.f_g ha, ← Φ.f_one h0, ← Φ.map_mul, one_mul]
    obtain ⟨e1, l1⟩ := foldl_mul_c w (mul_lt0 Φ hc ha) hw'
    obtain ⟨e2, -⟩ := foldl_mul_c w ha hw'
    obtain ⟨-, l0⟩ := foldl_mul_c w (Φ.pos) hw'
    refine ⟨?_, by rw [List.foldl_cons]; exact l1⟩
    rw [List.foldl_cons, List.foldl_cons, h0a, e1, e2, mul_assoc_c Φ h0 hc ha l0]

include Φ h0 in
theorem gen_of_words {gs : List ℕ} (hG : Gen mul gens N) (hgs : ∀ g ∈ gs, g < N)
    (hw : ∀ g ∈ gens, ∃ w : List ℕ, (∀ a ∈ w, a ∈ gs) ∧ w.foldl mul 0 = g) : Gen mul gs N := by
  have hreach : ∀ (w : List ℕ) {c : ℕ}, Reach mul gs c → (∀ a ∈ w, a ∈ gs) →
      Reach mul gs (w.foldl mul c) := by
    intro w
    induction w with
    | nil => exact fun h _ => h
    | cons a w ih =>
      intro c hc hw
      rw [List.foldl_cons]
      exact ih (Reach.step hc (hw a List.mem_cons_self)) fun b hb => hw b (List.mem_cons_of_mem _ hb)
  have hlt : ∀ c, Reach mul gs c → c < N := by
    intro c hc
    induction hc with
    | zero => exact Φ.pos
    | step _ hg ih => exact mul_lt0 Φ ih (hgs _ hg)
  intro c hc
  have key : ∀ c, Reach mul gens c → Reach mul gs c := by
    intro c hc
    induction hc with
    | zero => exact Reach.zero
    | @step c g _ hg ih =>
      obtain ⟨w, hwg, hwe⟩ := hw g hg
      have := hreach w ih hwg
      rwa [(foldl_mul_c Φ h0 w (hlt c ih) fun a ha => hgs a (hwg a ha)).1, hwe] at this
  exact key c (hG c hc)

variable (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)

include Φ h0 hinv hgens in
theorem parts_of_sub {gs : List ℕ} (hG : Gen mul gens N) (hgs : ∀ g ∈ gs, g < N)
    (hGs : Gen mul gs N) {r : ℕ × ℕ} (hchk : clsChk mul inv gs N r = true) (hn : r.2 < 130) :
    (decide (r.1 < N) && mul r.1 r.1 == 0 && r.1 != 0 &&
      orbOKM mul inv N r.1 (recM mul inv gens r.1) &&
      orbClosedM mul inv gens r.1 (recM mul inv gens r.1) &&
      (recM mul inv gens r.1).length == r.2 &&
      (recM mul inv gens r.1).all fun p => decide (r.1 ≤ p.1)) = true := by
  have h := clsChk_imp mul inv gs hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨hr, hrr⟩, hr0⟩, hO6⟩, hC6⟩, hl6⟩, hm6⟩ := h
  have hO6' : orbOK mul inv N (Φ.f (Φ.g r.1)) (recM mul inv gs r.1) = true := by
    rw [Φ.f_g hr]
    exact orbOK_of_M mul inv N hO6
  have hC6' : orbClosed mul inv gs (Φ.f (Φ.g r.1)) (recM mul inv gs r.1) = true := by
    rw [Φ.f_g hr]
    exact orbClosed_of_M mul inv gs hC6
  have hcard := Φ.ncard_eq h0 hinv hgs hGs hO6' hC6'
  rw [hl6] at hcard
  obtain ⟨hO, hC⟩ := recM_ok Φ h0 hinv hgens hr (hcard ▸ hn)
  have hO' : orbOK mul inv N (Φ.f (Φ.g r.1)) (recM mul inv gens r.1) = true := by
    rw [Φ.f_g hr]
    exact hO
  have hC' : orbClosed mul inv gens (Φ.f (Φ.g r.1)) (recM mul inv gens r.1) = true := by
    rw [Φ.f_g hr]
    exact hC
  refine ⟨⟨⟨⟨⟨⟨hr, hrr⟩, hr0⟩, ?_⟩, ?_⟩, ?_⟩, fun p hp => ?_⟩
  · exact orbOKM_of hO
  · exact orbClosedM_of hC
  · rw [← Φ.ncard_eq h0 hinv hgens hG hO' hC', hcard]
  · obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv hO' (List.mem_map_of_mem hp)
    have hy : g * Φ.g r.1 * g⁻¹ ∈ orbit (ConjAct H) (Φ.g r.1) := mem_orbit_iff_conj.2 ⟨g, rfl⟩
    rw [Φ.mem_orbit_iff h0 hinv hgs hGs hO6' hC6', hg] at hy
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hy
    rw [← hqe]
    exact hm6 q hq

end CFSG.KC.SBRec

end
