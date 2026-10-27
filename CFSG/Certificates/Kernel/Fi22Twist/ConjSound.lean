module

public import Certificates.Data.Kernel.Fi22Twist.Conj
public import CFSG.Certificates.Kernel.Fi22Twist.PairSound

public section

namespace CFSG.KS.Fi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KS.E27Lie Subgroup

variable {G : Type*} [Group G]

theorem cjFull_spec {g x d : ℕ} (h : cjFull g x d = true) :
    ∀ z < 3510, ap g (ap x z) = ap d (ap g z) := fun z hz =>
  beq_of (CFSG.KS.allN_spec h z hz)

theorem cjRep_spec {K X DF : ℕ → ℕ} {g j row t : ℕ} (h : cjRep K X DF g j row t = true) :
    (t < 3 → cjK row t < 27 ∧ cjFull g (K (cjI row t)) (DF (27 * j + cjK row t)) = true) ∧
    (3 ≤ t → cjK row t % 4 < 3 ∧ cjK row t / 4 < t ∧
      qpMul (K (cjI row (cjK row t % 4))) (X (cjI row t)) (X (cjI row (cjK row t / 4))) = true) := by
  unfold cjRep at h
  rw [sB_eq, sB_eq, bRec_eq] at h
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rw [if_pos (Eq.mpr Nat.blt_eq ht)] at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact ⟨blt_of h1, h2⟩
  · have hn : ¬ (Nat.blt t 3 = true) := by
      rw [Nat.blt_eq]
      omega
    rw [if_neg hn, sB_eq, sB_eq] at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact ⟨blt_of h1, blt_of h2, h3⟩

theorem cjSub_spec {K M X : ℕ → ℕ} {p s row t : ℕ} (h : cjSub K M X p s row t = true) :
    cjK row t < 729 ∧ qpBit (M (730 + p)) (cjK row t) = true ∧
    ∀ l < 6, ap (K (cjK row t)) (qpE (X s) (2 + l)) = ap (K s) (qpE (X (cjI row t)) (2 + l)) := by
  unfold cjSub at h
  rw [sB_eq, sB_eq] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [sB_eq, sB_eq, sB_eq, sB_eq] at h
  exact ⟨blt_of h1, h2, fun l hl => beq_of (allBlk0_spec h l hl)⟩

theorem cjRC_spec {K M X DF CG RC : ℕ → ℕ} {nG c : ℕ} (h : cjRC K M X DF CG RC nG c = true) :
    (∀ t < qpE (RC c) 3, cjI (RC c) t < 729) ∧
    (∀ i < 729, qpBit (M (730 + c)) i = true → ∃ t < qpE (RC c) 3, cjI (RC c) t = i) ∧
    (qpE (RC c) 0 = 0 → qpE (RC c) 1 < nG ∧ qpE (RC c) 2 < 5 ∧
      ∀ t < qpE (RC c) 3, cjRep K X DF (CG (qpE (RC c) 1)) (qpE (RC c) 2) (RC c) t = true) ∧
    (qpE (RC c) 0 ≠ 0 → qpE (RC c) 1 < 81 ∧ qpE (RC c) 2 < 729 ∧
      qpE (RC (qpE (RC c) 1)) 0 < qpE (RC c) 0 ∧
      ∀ t < qpE (RC c) 3, cjSub K M X (qpE (RC c) 1) (qpE (RC c) 2) (RC c) t = true) := by
  unfold cjRC at h
  rw [sB_eq, sB_eq, sB_eq, sB_eq] at h
  obtain ⟨hlt, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hm, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [bRec_eq] at h
  refine ⟨fun t ht => blt_of (CFSG.KS.allN_spec hlt t ht), fun i hi hb => ?_, fun h0 => ?_,
    fun h0 => ?_⟩
  · have hm' : M (730 + c) &&& (qpFull ^^^ cjMask (RC c) (qpE (RC c) 3)) = 0 := beq_of hm
    have hz := congrArg (fun z => z.testBit i) hm'
    rw [qpBit_iff] at hb
    simp only [Nat.testBit_and, Nat.testBit_xor, testBit_qpFull, hb, hi, decide_true,
      Bool.true_and, Bool.true_xor, Nat.zero_testBit, Bool.not_eq_false'] at hz
    have hU : (cjMask (RC c) (qpE (RC c) 3)).testBit i = true := by simpa using hz
    obtain ⟨t, ht, hti⟩ := (testBit_foldOr _ (fun t => 1 <<< cjI (RC c) t) i).1 hU
    rw [testBit_shl1, decide_eq_true_eq] at hti
    exact ⟨t, ht, hti⟩
  · have e0 : Nat.beq (qpE (RC c) 0) 0 = true := by rw [h0]; rfl
    rw [if_pos e0] at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rw [sB_eq] at h
    exact ⟨blt_of h1, blt_of h2, fun t ht => CFSG.KS.allN_spec h t ht⟩
  · have e0 : ¬ (Nat.beq (qpE (RC c) 0) 0 = true) := by
      rw [Nat.beq_eq]
      exact h0
    rw [if_neg e0] at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact ⟨blt_of h1, blt_of h2, blt_of h3, fun t ht => CFSG.KS.allN_spec h t ht⟩

theorem pt_val (ψ : G →* Equiv.Perm (Fin 3510)) (g : G) {z : ℕ} (hz : z < 3510) :
    pt ψ g z = (ψ g ⟨z, hz⟩ : ℕ) := dif_pos hz

theorem conj_of_full {ψ : G →* Equiv.Perm (Fin 3510)} (hψ : Function.Injective ψ)
    {Gk Xk : ℕ} {g x d : G} (hg : PRep 3510 12 ψ Gk g) (hx : PRep 3510 12 ψ Xk x)
    {Dk : ℕ} (hd : ∀ z < 3510, ap Dk z = pt ψ d z) (h : cjFull Gk Xk Dk = true) :
    g * x * g⁻¹ = d := by
  have he : g * x = d * g := by
    refine hψ (Equiv.ext fun z => Fin.ext ?_)
    have hz := z.isLt
    have e1 := cjFull_spec h z hz
    rw [ap_eq hx hz, ap_eq hg (pt_lt ψ _ hz), ap_eq hg hz, hd _ (pt_lt ψ _ hz), ← pt_mul,
      ← pt_mul, pt_val ψ _ hz, pt_val ψ _ hz] at e1
    exact e1
  rw [he, mul_inv_cancel_right]

namespace PairTab

variable {ψ : G →* Equiv.Perm (Fin 3510)} {e : ℕ → G} {T : Subgroup G} {K M X V : ℕ → ℕ}

theorem conj_spec (P : PairTab ψ e T K M X V) {k s i : ℕ} (hk : k < 729) (hs : s < 729)
    (hi : i < 729) (h : ∀ l < 6, ap (K k) (qpE (X s) (2 + l)) = ap (K s) (qpE (X i) (2 + l))) :
    e s * e i * (e s)⁻¹ = e k := by
  have he : e k * e s = e s * e i := by
    refine P.base_eq (mul_mem (P.e_mem hk) (P.e_mem hs)) (mul_mem (P.e_mem hs) (P.e_mem hi))
      fun l hl => ?_
    have h1 := h l hl
    rw [P.img hs l hl, P.img hi l hl, ap_eq (P.key k hk) (pt_lt ψ _ (bp_lt6 l hl)),
      ap_eq (P.key s hs) (pt_lt ψ _ (bp_lt6 l hl))] at h1
    rw [pt_mul, pt_mul, h1]
  rw [← he, mul_inv_cancel_right]

theorem conj_records (P : PairTab ψ e T K M X V) (hψ : Function.Injective ψ)
    {DF CG RC : ℕ → ℕ} {nG : ℕ} {g : ℕ → G} {D : ℕ → Subgroup G}
    (hg : ∀ r < nG, PRep 3510 12 ψ (CG r) (g r))
    (hd : ∀ j < 5, ∀ k < 27, ∃ y ∈ D j, ∀ z < 3510, ap (DF (27 * j + k)) z = pt ψ y z)
    (hc : ∀ c < 81, cjRC K M X DF CG RC nG c = true) {c : ℕ} (hc81 : c < 81) :
    ∃ j < 5, ∃ h ∈ closure {x | (∃ r < nG, g r = x) ∨ ∃ i < 729, e i = x},
      ∀ x ∈ closure {y | ∃ i < 729, qpBit (M (730 + c)) i = true ∧ e i = y},
        h * x * h⁻¹ ∈ D j := by
  suffices H : ∀ dp, ∀ c < 81, qpE (RC c) 0 = dp →
      ∃ j < 5, ∃ h ∈ closure {x | (∃ r < nG, g r = x) ∨ ∃ i < 729, e i = x},
        ∀ x ∈ closure {y | ∃ i < 729, qpBit (M (730 + c)) i = true ∧ e i = y},
          h * x * h⁻¹ ∈ D j from H _ c hc81 rfl
  intro dp
  induction dp using Nat.strong_induction_on with
  | _ dp ih =>
  intro c hc81 hdp
  obtain ⟨hlt, hcov, hrep, hsub⟩ := cjRC_spec (hc c hc81)
  set row := RC c with hrow
  set n := qpE row 3 with hn
  have hS : ∀ (j : ℕ) (h : G), (∀ t < n, h * e (cjI row t) * h⁻¹ ∈ D j) →
      ∀ x ∈ closure {y | ∃ i < 729, qpBit (M (730 + c)) i = true ∧ e i = y},
        h * x * h⁻¹ ∈ D j := by
    intro j h ht x hx
    have hle : closure {y | ∃ i < 729, qpBit (M (730 + c)) i = true ∧ e i = y} ≤
        (D j).comap (MulAut.conj h).toMonoidHom := by
      refine (closure_le _).2 ?_
      rintro _ ⟨i, hi, hb, rfl⟩
      obtain ⟨t, htn, rfl⟩ := hcov i hi hb
      exact ht t htn
    exact hle hx
  by_cases h0 : qpE row 0 = 0
  ·
    obtain ⟨hr, hj, hent⟩ := hrep h0
    refine ⟨_, hj, g (qpE row 1), subset_closure (Or.inl ⟨_, hr, rfl⟩), hS _ _ ?_⟩
    intro t
    induction t using Nat.strong_induction_on with
    | _ t iht =>
    intro htn
    obtain ⟨h3, h4⟩ := cjRep_spec (hent t htn)
    by_cases ht3 : t < 3
    · obtain ⟨hk, hf⟩ := h3 ht3
      obtain ⟨y, hy, hyz⟩ := hd _ hj _ hk
      rw [conj_of_full hψ (hg _ hr) (P.key _ (hlt t htn)) hyz hf]
      exact hy
    · obtain ⟨ha, hu, hm⟩ := h4 (by omega)
      have hat : cjK row t % 4 < n := by omega
      have hut : cjK row t / 4 < n := by omega
      rw [P.mul_spec (hlt _ hat) (hlt t htn) (hlt _ hut) hm]
      have e1 : ∀ a b : G, g (qpE row 1) * (a * b) * (g (qpE row 1))⁻¹ =
          (g (qpE row 1) * a * (g (qpE row 1))⁻¹) * (g (qpE row 1) * b * (g (qpE row 1))⁻¹) :=
        fun a b => by group
      rw [e1]
      exact mul_mem (iht _ (by omega) hat) (iht _ hu hut)
  ·
    obtain ⟨hp, hs, hdep, hent⟩ := hsub h0
    obtain ⟨j, hj, h', hh', hconj⟩ := ih _ (by omega) _ hp rfl
    refine ⟨j, hj, h' * e (qpE row 2), mul_mem hh' (subset_closure (Or.inr ⟨_, hs, rfl⟩)),
      hS _ _ fun t htn => ?_⟩
    obtain ⟨hk, hkb, hbase⟩ := cjSub_spec (hent t htn)
    have e1 := P.conj_spec hk hs (hlt t htn) hbase
    have e2 : h' * e (qpE row 2) * e (cjI row t) * (h' * e (qpE row 2))⁻¹ =
        h' * (e (qpE row 2) * e (cjI row t) * (e (qpE row 2))⁻¹) * h'⁻¹ := by group
    rw [e2, e1]
    exact hconj _ (subset_closure ⟨_, hk, hkb, rfl⟩)

end PairTab

end CFSG.KS.Fi22Twist

end
