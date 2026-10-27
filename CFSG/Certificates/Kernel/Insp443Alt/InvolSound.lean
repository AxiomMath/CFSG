module

public import Certificates.Data.Kernel.Insp443Alt.Invol
public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Certificates.Kernel.Insp443Alt

open Equiv Equiv.Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkEnum CFSG.KC.Enum
  CFSG.SectionRank.QTK.Insp443.Alt CFSG.Quasithin.KGC31

theorem invol_parts {m : Nat} (p : Fin (m + 1)) (e : Perm (Fin m))
    (h : decomposeFin.symm (p, e) * decomposeFin.symm (p, e) = 1) :
    e * e = 1 ∧ ∀ q : Fin m, p = q.succ → e q = q := by
  have hσσ : ∀ i, decomposeFin.symm (p, e) (decomposeFin.symm (p, e) i) = i := fun i => by
    have := congrArg (fun τ : Perm (Fin (m + 1)) => τ i) h
    simpa only [Perm.mul_apply, Perm.one_apply] using this
  have h0 : decomposeFin.symm (p, e) 0 = p := decomposeFin_symm_apply_zero p e
  have hsu : ∀ x, decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ := fun x =>
    decomposeFin_symm_apply_succ e p x
  have hfix : ∀ q : Fin m, p = q.succ → e q = q := by
    intro q hq
    have h1 : decomposeFin.symm (p, e) q.succ = 0 :=
      (congrArg (decomposeFin.symm (p, e)) (hq.symm.trans h0.symm)).trans (hσσ 0)
    rw [hsu, swap_apply_eq_iff, swap_apply_left] at h1
    exact Fin.succ_injective _ (h1.trans hq)
  refine ⟨Equiv.ext fun x => ?_, hfix⟩
  rw [Perm.mul_apply, Perm.one_apply]
  by_cases hp : p = 0
  · have hsu' : ∀ x, decomposeFin.symm (p, e) x.succ = (e x).succ := fun x => by
      rw [hsu, hp, swap_self, refl_apply]
    have h2 := hσσ x.succ
    rw [hsu', hsu'] at h2
    exact Fin.succ_injective _ h2
  · obtain ⟨q, hq⟩ := Fin.exists_succ_eq.2 hp
    have heq : e q = q := hfix q hq.symm
    by_cases hy : e x = q
    · have hx : x = q := e.injective (hy.trans heq.symm)
      rw [hy, heq, hx]
    · have hxq : x ≠ q := fun hx => hy (hx ▸ heq)
      have hne : ∀ z : Fin m, z ≠ q → swap 0 p z.succ = z.succ := fun z hz =>
        swap_apply_of_ne_of_ne (Fin.succ_ne_zero z)
          (fun h => hz (Fin.succ_injective _ (h.trans hq.symm)))
      have h1 : decomposeFin.symm (p, e) x.succ = (e x).succ := by rw [hsu, hne _ hy]
      have h2 := hσσ x.succ
      rw [h1, hsu, swap_apply_eq_iff, hne x hxq] at h2
      exact Fin.succ_injective _ h2

theorem invP_complete : ∀ (m : Nat) (hs : Small m) (σ : Perm (Fin m)), σ * σ = 1 →
    ∃ x ∈ invP m hs, ev x.1 = σ ∧ x.2 = decide (sign σ = -1)
  | 0, hs, σ, _ => by
    refine ⟨(1, false), by simp [invP], Subsingleton.elim _ _, ?_⟩
    rw [Subsingleton.elim σ 1, Perm.sign_one]
    change false = decide ((1 : ℤˣ) = -1)
    decide
  | m + 1, hs, σ, h => by
    have : Small m := small_pred hs
    have hσ : decomposeFin.symm (decomposeFin σ) = σ := decomposeFin.symm_apply_apply σ
    generalize decomposeFin σ = pe at hσ
    obtain ⟨p, e⟩ := pe
    subst hσ
    obtain ⟨he, hfix⟩ := invol_parts p e h
    obtain ⟨x, hx, hxe, hxp⟩ := invP_complete m this e he
    refine ⟨(liftC p x.1, xor (p.1 != 0) x.2), ?_, ?_, ?_⟩
    · rw [invP, forcePL_eq, List.mem_flatMap]
      refine ⟨p, List.mem_finRange p, List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, ?_⟩, rfl⟩⟩
      by_cases hp0 : p.1 = 0
      · simp [hp0]
      · have hq : p.1 - 1 < m := by omega
        have h1 := hfix ⟨p.1 - 1, hq⟩ (Fin.ext (by change p.1 = (p.1 - 1) + 1; omega))
        have hi : img m x.1.1 (p.1 - 1) = p.1 - 1 := by
          have h2 := congrArg Fin.val h1
          rw [← hxe] at h2
          exact h2
        simp [hi]
    · rw [ev_liftC, hxe]
    · rw [hxp]
      exact (par_decomposeFin_symm p e).symm

@[expose] def BadG {G : Type*} [Group G] (p : ℕ) (y s : G) : Prop :=
  y * s * y⁻¹ ≠ s ∧ ∀ j < p, s * (y ^ j * s * (y ^ j)⁻¹) = y ^ j * s * (y ^ j)⁻¹ * s

section Group

variable {G : Type*} [Group G]

theorem pow_eq_pow_mod {c : G} {p : ℕ} (hc : c ^ p = 1) (m : ℕ) : c ^ m = c ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hc, one_pow, one_mul]

theorem conj_pow_eq {c : G} {p : ℕ} (hp : 0 < p) (hc : c ^ p = 1) (s : G) (k j : ℕ) :
    (c ^ k) ^ j * s * ((c ^ k) ^ j)⁻¹ = c ^ (k * j % p) * s * c ^ (p - k * j % p) := by
  have hr : k * j % p ≤ p := (Nat.mod_lt _ hp).le
  have hinv : (c ^ (k * j % p))⁻¹ = c ^ (p - k * j % p) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, Nat.add_sub_cancel' hr, hc])
  rw [← pow_mul, pow_eq_pow_mod hc (k * j), hinv]

theorem badG_iff {c : G} {p : ℕ} (hp : 0 < p) (hc : c ^ p = 1) (s : G) {k : ℕ} (hk : k < p) :
    BadG p (c ^ k) s ↔ c ^ k * s * c ^ (p - k) ≠ s ∧ ∀ j < p,
      s * (c ^ (k * j % p) * s * c ^ (p - k * j % p)) =
        c ^ (k * j % p) * s * c ^ (p - k * j % p) * s := by
  have h1 := conj_pow_eq hp hc s k 1
  rw [pow_one, mul_one, Nat.mod_eq_of_lt hk] at h1
  unfold BadG
  rw [h1]
  simp only [conj_pow_eq hp hc s k]

theorem eElt_hom {H : Type*} [Group H] {m : ℕ} (f : G →* H) (v : Fin m → G)
    (c : Fin m → ZMod 2) : f (eElt v c) = eElt (fun i => f (v i)) c := by
  simp [eElt, map_list_prod, List.map_ofFn, Function.comp_def]

end Group

variable {n : Nat} [Small n]

theorem badG_ev {p : ℕ} (y s : CV n) : BadG p (ev y) (ev s) ↔ BadG p y s := by
  unfold BadG
  simp only [ev_pow', ev_inv', ev_mul', ne_eq, ev_eq_iff]

theorem getD_powL (c : CV n) (p : Nat) {i : Nat} (hi : i ≤ p) : (powL c p).getD i 1 = c ^ i := by
  simp [powL, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hi]

theorem length_conjL (P : List (CV n)) (p : Nat) (s : CV n) : (conjL P p s).length = p := by
  simp [conjL]

theorem getD_conjL (P : List (CV n)) (p : Nat) (s : CV n) {i : Nat} (hi : i < p) :
    (conjL P p s).getD i 1 = P.getD i 1 * s * P.getD (p - i) 1 := by
  simp [conjL, List.getD_eq_getElem?_getD, hi]

theorem getD_commL (s : CV n) (Q : List (CV n)) {i : Nat} (hi : i < Q.length) :
    (commL s Q).getD i false = eq22C s (Q.getD i 1) (Q.getD i 1) s := by
  simp [commL, List.getD_eq_getElem?_getD, hi]

theorem getD_conjL_powL (c s : CV n) {p i : Nat} (hi : i < p) :
    (conjL (powL c p) p s).getD i 1 = c ^ i * s * c ^ (p - i) := by
  rw [getD_conjL _ _ _ hi, getD_powL _ _ hi.le, getD_powL _ _ (Nat.sub_le _ _)]

theorem badB_true {c s : CV n} {p k : Nat} (hp : 0 < p) (hc : c ^ p = 1) (hk : k < p)
    (hb : BadG p (c ^ k) s) :
    badB p s (conjL (powL c p) p s) (commL s (conjL (powL c p) p s)) k = true := by
  rw [badG_iff hp hc s hk] at hb
  obtain ⟨h1, h2⟩ := hb
  rw [badB, Bool.and_eq_true]
  constructor
  · rw [getD_conjL_powL c s hk]
    cases hq : Nat.beq (c ^ k * s * c ^ (p - k)).1 s.1
    · rfl
    · exact absurd (Subtype.ext (Nat.eq_of_beq_eq_true hq)) h1
  · rw [List.all_eq_true]
    intro j hj
    have hr := Nat.mod_lt (k * j) hp
    rw [getD_commL _ _ (by rw [length_conjL]; exact hr), getD_conjL_powL c s hr, eq22C_eq,
      decide_eq_true_iff]
    exact h2 j (List.mem_range.1 hj)

theorem mem_e8 (c : Fin 3 → ZMod 2) : c ∈ e8 := by
  revert c
  decide

theorem card_image_e8 {α : Type*} [DecidableEq α] (g : (Fin 3 → ZMod 2) → α) (v : α → ℕ)
    (h : (e8.map fun c => v (g c)).Nodup) : (Finset.univ.image g).card = 8 := by
  have hinj : Function.Injective g := fun a b hab =>
    List.inj_on_of_nodup_map h (mem_e8 a) (mem_e8 b) (congrArg v hab)
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem eElt_ev (T : Fin 3 → CV n) (c : Fin 3 → ZMod 2) :
    eElt (fun i => ev (T i)) c = ev (eElt T c) :=
  (eElt_hom (evHom n) T c).symm

theorem regular_of [NeZero n] {C s : CV n} (hc : C ^ 7 = 1) {k : Nat} (hk : k < 7)
    (h : regB s (conjL (powL C 7) 7 s) k = true) : Regular (ev C ^ k) (ev s) := by
  have hk2 : k * 2 % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have h1 : ev C ^ k * ev s * (ev C ^ k)⁻¹ = ev ((conjL (powL C 7) 7 s).getD k 1) := by
    rw [getD_conjL_powL C s hk, ev_pow', ev_inv', ev_mul', ev_mul']
    congr 1
    have := conj_pow_eq (by norm_num) hc s k 1
    rwa [pow_one, mul_one, Nat.mod_eq_of_lt hk] at this
  have h2 : (ev C ^ k) ^ 2 * ev s * ((ev C ^ k) ^ 2)⁻¹ =
      ev ((conjL (powL C 7) 7 s).getD (k * 2 % 7) 1) := by
    rw [getD_conjL_powL C s hk2, ev_pow', ev_pow', ev_inv', ev_mul', ev_mul']
    congr 1
    exact conj_pow_eq (by norm_num) hc s k 2
  have hT : tri (ev C ^ k) (ev s) = fun i => ev (![s, (conjL (powL C 7) 7 s).getD k 1,
      (conjL (powL C 7) 7 s).getD (k * 2 % 7) 1] i) := by
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  unfold Regular
  rw [hT]
  simp only [eElt_ev]
  apply card_image_e8 _ Fin.val
  rw [regB] at h
  simpa only [ev_apply, Fin.val_zero] using of_decide_eq_true h

theorem forceBL_eq {β : Sort _} : ∀ (l : List Bool) (k : List Bool → β), forceBL l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forceBL, forceB_eq, forceBL_eq l]

theorem okS_sound [NeZero n] {C5 C7 s : CV n} (h5 : C5 ^ 5 = 1) (h7 : C7 ^ 7 = 1)
    (h : okS (powL C5 5) (powL C7 7) s = true) :
    (∀ k < 5, ¬ BadG 5 (C5 ^ k) s) ∧ ∀ k < 7, BadG 7 (C7 ^ k) s → Regular (ev C7 ^ k) (ev s) := by
  rw [okS, forceCL_eq, forceCL_eq, forceBL_eq, forceBL_eq, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true] at h
  obtain ⟨ha, hb⟩ := h
  refine ⟨fun k hk hbad => ?_, fun k hk hbad => ?_⟩
  · have h1 := ha k (List.mem_range.2 hk)
    rw [badB_true (by norm_num) h5 hk hbad] at h1
    exact absurd h1 (by decide)
  · have h1 := hb k (List.mem_range.2 hk)
    rw [badB_true (by norm_num) h7 hk hbad, Bool.not_true, Bool.false_or] at h1
    exact regular_of h7 hk h1

theorem sok_of_chkI [NeZero n] (h : chkI n = true) (h5 : cyc5 n ^ 5 = 1) (h7 : cyc7 n ^ 7 = 1)
    (s : Perm (Fin n)) : SOK n s := by
  intro hss hsign
  have e5 : ev (cOf (cyc5 n)) = cyc5 n := ev_cOf _
  have e7 : ev (cOf (cyc7 n)) = cyc7 n := ev_cOf _
  have hC5 : cOf (cyc5 n) ^ 5 = 1 := ev_injective (by rw [← ev_pow', e5, h5, ev_one])
  have hC7 : cOf (cyc7 n) ^ 7 = 1 := ev_injective (by rw [← ev_pow', e7, h7, ev_one])
  rw [chkI, forceCL_eq, forceCL_eq, List.all_eq_true] at h
  obtain ⟨x, hx, hxs, hxp⟩ := invP_complete n inferInstance s hss
  have hx2 : x.2 = false := by
    rw [hxp, hsign]
    decide
  have h1 := h x hx
  rw [hx2, Bool.false_or, forceC_eq] at h1
  obtain ⟨A, B⟩ := okS_sound hC5 hC7 h1
  rw [← hxs, ← e5, ← e7]
  refine ⟨fun k hk hbad => A k hk ?_, fun k hk hbad => B k hk ?_⟩
  · rw [ev_pow'] at hbad
    exact (badG_ev _ _).1 hbad
  · rw [ev_pow'] at hbad
    exact (badG_ev _ _).1 hbad

theorem altProp_of_chkI [NeZero n] (h : chkI n = true) (h1 : sign (cyc5 n) = 1)
    (h2 : cyc5 n ^ 5 = 1) (h3 : cyc5 n ≠ 1) (h4 : sign (cyc7 n) = 1) (h5 : cyc7 n ^ 7 = 1)
    (h6 : cyc7 n ≠ 1) : AltProp n :=
  ⟨h1, h2, h3, h4, h5, h6, sok_of_chkI h h2 h5⟩

end CFSG.Certificates.Kernel.Insp443Alt

end
