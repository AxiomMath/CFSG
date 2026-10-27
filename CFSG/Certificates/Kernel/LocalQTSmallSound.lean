module

public import Certificates.Data.Kernel.LocalQT.Small
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSevenInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltPermInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinL42Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.KC.LQT.S

open Equiv Equiv.Perm CFSG.QuasithinUnique.Ch1.AltSeven

@[expose] def code {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => (σ i : ℕ) * 32 ^ (i : ℕ)).sum

theorem code_eq_P {n : ℕ} : (code : Perm (Fin n) → ℕ) = P.code := rfl

theorem allBs_cons (b : Bool) (l : List Bool) : allBs (b :: l) = CFSG.KC.Ord.andB b (allBs l) := rfl

theorem allBs_nil : allBs [] = true := rfl

theorem lenL_eq (l : List ℕ) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenL l) = _
    rw [ih, List.length_cons]

theorem lenRec_eq (l : List ℕ) :
    List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l = l.length := lenL_eq l

theorem memL_iff (s : ℕ) (l : List ℕ) : memL s l = true ↔ s ∈ l := by
  induction l with
  | nil => simp [memL]
  | cons x l ih =>
    change CFSG.KC.Ord.orB (Nat.beq s x) (memL s l) = true ↔ _
    rw [P.orB_iff, P.beq_iff, ih]
    simp

theorem commL_eq (n t : ℕ) (l : List ℕ) : commL n t l = P.allL l (P.comm n t) := rfl

theorem distinctL_map {n : ℕ} (hn : n ≤ 32) (L : List (Perm (Fin n))) :
    distinctL (L.map P.code) = true ↔ L.Nodup := by
  induction L with
  | nil => simp [distinctL]
  | cons g L ih =>
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memL (P.code g) (L.map P.code)))
      (distinctL (L.map P.code)) = true ↔ _
    rw [P.andB_iff, P.notB_iff, memL_iff, P.mem_map_code hn, ih, List.nodup_cons]

theorem s4044 (g5 g3 : Fin 8 → Fin 8 → Perm (Fin 8)) {G5 G3 : ℕ → ℕ → ℕ}
    (hg : ∀ a b : Fin 8, a ≠ b → code (g5 a b) = G5 a b ∧ code (g3 a b) = G3 a b)
    (hk : c4044 G5 G3 = true) :
    ∀ a b : Fin 8, a ≠ b → ∀ τ : Perm (Fin 8), τ * g5 a b = g5 a b * τ →
      τ * g3 a b = g3 a b * τ → τ = 1 ∨ τ = swap a b := by
  have h8 : (8 : ℕ) ≤ 32 := by norm_num
  intro a b hab τ h5 h3
  obtain ⟨e5, e3⟩ := hg a b hab
  have hk' := (P.allN_fin 8 _).1 hk a
  rw [P.allN_fin] at hk'
  have := hk' b
  rw [P.impB_iff, P.notB_iff, P.beq_fin, P.letB_eq, P.letB_eq, ← e5, ← e3, code_eq_P,
    P.allC_iff h8] at this
  have := this hab τ h5
  simp only [P.impB_iff, P.orB_iff, P.comm_code h8, P.code_one, P.code_swap, P.beq_code h8]
    at this
  exact this h3

theorem s4100 (a6 : Perm (Fin 6)) {A : ℕ} (ha : code a6 = A) (hk : c4100 A = true) :
    (∀ t : Perm (Fin 6), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
          ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * a6 * g⁻¹ = t)
    ∧ (∀ g : Perm (Fin 6), g ^ 9 = 1 → g ^ 3 = 1)
    ∧ (∀ a b : Fin 6, a ≠ b → ∃ x : Perm (Fin 6), Perm.sign x = 1 ∧
          (x⁻¹ * (swap a b)⁻¹ * x * swap a b) * (x⁻¹ * (swap a b)⁻¹ * x * swap a b) = 1 ∧
          x⁻¹ * (swap a b)⁻¹ * x * swap a b ≠ 1) := by
  have h6 : (6 : ℕ) ≤ 32 := by norm_num
  subst ha
  unfold c4100 kom at hk
  simp only [P.andB_iff, P.impB_iff, P.notB_iff, P.letB_eq, P.allP_iff, P.anyP_iff,
    P.allN_fin, P.beq_fin, code_eq_P, P.even_code h6, P.code_mul h6, P.code_inv h6,
    P.code_pow h6, P.conj_code h6, P.code_one, P.code_swap, P.beq_code h6] at hk
  obtain ⟨h1, h2, h3⟩ := hk
  exact ⟨h1, h2, h3⟩

theorem s4156 (a7 : Perm (Fin 7)) {A : ℕ} (ha : code a7 = A) {w1 w3 : List ℕ}
    (hk : c4156 A w1 w3 = true) :
    (∀ t : Perm (Fin 7), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
          ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * a7 * g⁻¹ = t)
    ∧ (∀ g : Perm (Fin 7), g ^ 9 = 1 → g ^ 3 = 1)
    ∧ (∀ σ : Perm (Fin 7), σ.cycleType = {2, 2, 2} → σ * σ = 1 ∧
          ∃ x : Perm (Fin 7), Perm.sign x = 1 ∧
            (x⁻¹ * σ⁻¹ * x * σ) * (x⁻¹ * σ⁻¹ * x * σ) = 1 ∧ x⁻¹ * σ⁻¹ * x * σ ≠ 1) := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  subst ha
  unfold c4156 kom at hk
  simp only [P.andB_iff, P.impB_iff, P.notB_iff, P.letB_eq, P.allP_iff, P.allL_iff, P.anyL_iff,
    code_eq_P, P.even_code h7, P.code_mul h7, P.code_pow h7, P.code_one, P.beq_code h7,
    P.fix_code h7, P.beq_iff] at hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk
  refine ⟨fun t ht htt ht1 => ?_, h3, fun σ hσ => ?_⟩
  · obtain ⟨w, hw, e⟩ := h1 t ht htt ht1
    obtain ⟨hp, hev, hc⟩ := h2 w hw
    obtain ⟨g, hg⟩ := P.exists_of_permK hp
    rw [← hg, P.even_code h7] at hev
    rw [← hg] at hc
    rw [P.conj_code h7, e, P.code_eq_iff h7] at hc
    exact ⟨g, hev, hc⟩
  · have ho : orderOf σ = 2 := by
      rw [← Perm.lcm_cycleType, hσ]
      decide
    have hss : σ * σ = 1 := by rw [← pow_two, ← ho, pow_orderOf_eq_one]
    have hfix : (Finset.univ.filter fun i : Fin 7 => σ i = i).card = 1 := by
      have hs : σ.support.card = 6 := by
        rw [← Perm.sum_cycleType, hσ]
        decide
      have : (Finset.univ.filter fun i : Fin 7 => σ i = i) = σ.supportᶜ := by
        ext i
        simp [Perm.mem_support]
      rw [this, Finset.card_compl, hs, Fintype.card_fin]
    obtain ⟨w, hw, e⟩ := h4 σ hss hfix
    obtain ⟨-, -, hp, hev, hc⟩ := h5 w hw
    refine ⟨hss, ?_⟩
    obtain ⟨x, hx⟩ := P.exists_of_permK hp
    rw [← hx] at hev hc
    rw [e] at hc
    simp only [P.even_code h7, P.code_mul h7, P.code_inv h7, P.code_eq_iff h7] at hev hc
    exact ⟨x, hev, hc⟩

theorem s4122 (g1 g2 : Perm (Fin 7)) {C1 C2 : ℕ} (h1 : code g1 = C1) (h2 : code g2 = C2)
    (hk : c4122 C1 C2 = true) :
    ∀ σ : Perm (Fin 7), (∀ g ∈ [g1, g2], σ * g = g * σ) → σ ^ 2 = 1 := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  subst h1 h2
  intro σ hσ
  unfold c4122 at hk
  rw [code_eq_P, P.allC_iff h7] at hk
  have := hk σ (hσ g1 (by simp))
  simp only [P.impB_iff, P.comm_code h7, P.code_pow h7, P.code_one, P.beq_code h7] at this
  exact this (hσ g2 (by simp))

theorem s4129 (c5 c7 : Perm (Fin 7)) {C5 C7 : ℕ} (h5 : code c5 = C5) (h7 : code c7 = C7)
    (hk : c4129 C5 C7 = true) :
    (Perm.sign c5 = 1)
    ∧ (Perm.sign c7 = 1)
    ∧ (c5 ^ 5 = 1)
    ∧ (c7 ^ 7 = 1)
    ∧ (c5 ≠ 1)
    ∧ (c7 ≠ 1)
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧
          g * c5 * g⁻¹ ∈ ({1, c5, c5 ^ 2, c5 ^ 3, c5 ^ 4} : Finset (Perm (Fin 7)))).card = 20)
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧
          g * c7 * g⁻¹ ∈
            ({1, c7, c7 ^ 2, c7 ^ 3, c7 ^ 4, c7 ^ 5, c7 ^ 6} : Finset (Perm (Fin 7)))).card =
            21) := by
  have hn : (7 : ℕ) ≤ 32 := by norm_num
  subst h5 h7
  unfold c4129 at hk
  simp only [P.andB_iff, P.notB_iff, code_eq_P, P.even_code hn, P.code_pow hn, P.conj_code hn,
    P.code_one, P.beq_code hn, P.cntP_eq hn, memL_iff, List.mem_cons, List.not_mem_nil,
    or_false, P.code_eq_iff hn, P.beq_iff] at hk
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hk

private theorem ext_nil' (acc pos : ℕ) : P.ext acc pos [] = acc := by
  rw [P.ext_eq, List.length_nil, P.E_zero, mul_zero, add_zero]

private theorem ext_cons' (acc pos v : ℕ) (l : List ℕ) :
    P.ext acc pos (v :: l) = P.ext (acc + v * 32 ^ pos) (pos + 1) l := by
  rw [P.ext_eq, P.ext_eq, List.length_cons, P.E_succ_left]
  simp only [List.getD_cons_zero, List.getD_cons_succ, pow_succ]
  ring

private def OkO (ok : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | acc, pos, v :: l => ok acc pos v = true ∧ OkO ok (acc + v * 32 ^ pos) (pos + 1) l

private theorem okO_iff (ok : ℕ → ℕ → ℕ → Bool) : ∀ (l : List ℕ) (acc pos : ℕ),
    OkO ok acc pos l ↔ ∀ k (hk : k < l.length), ok (P.ext acc pos (l.take k)) (pos + k) l[k] = true
  | [], acc, pos => by simp [OkO]
  | v :: l, acc, pos => by
    rw [OkO, okO_iff ok l]
    constructor
    · rintro ⟨h0, h⟩ k hk
      cases k with
      | zero => simpa [ext_nil'] using h0
      | succ k =>
        have := h k (by simpa using hk)
        simp only [List.take_succ_cons, ext_cons', List.getElem_cons_succ]
        rwa [show pos + (k + 1) = pos + 1 + k by omega]
    · intro h
      have h0 := h 0 (by simp)
      simp only [List.take_zero, ext_nil', Nat.add_zero, List.getElem_cons_zero] at h0
      refine ⟨h0, fun k hk => ?_⟩
      have := h (k + 1) (by simpa using hk)
      simp only [List.take_succ_cons, ext_cons', List.getElem_cons_succ] at this
      rwa [show pos + (k + 1) = pos + 1 + k by omega] at this

private def clO (n : ℕ) (ok : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, acc => [acc]
  | d + 1, pos, mask, acc => (List.range n).flatMap fun v =>
      if mask.testBit v then [] else
        if ok acc pos v then clO n ok d (pos + 1) (mask ||| 2 ^ v) (acc + v * 32 ^ pos) else []

private def cntO (n : ℕ) (ok : ℕ → ℕ → ℕ → Bool) (d : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ _ => 1)
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => ℕ) 0
        (fun v rest => Nat.add
          (Bool.rec (motive := fun _ => ℕ)
            (Bool.rec (motive := fun _ => ℕ) 0
              (ih (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft 1 v))
                (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))))
              (ok acc pos v))
            0 (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v))))
          rest) n) d

private theorem cntSt_eq (n B C : ℕ) : cntSt n B C = cntO n (stOK B C) n 0 0 0 := rfl

private theorem cntO_eq (n : ℕ) (ok : ℕ → ℕ → ℕ → Bool) : ∀ d pos mask acc,
    cntO n ok d pos mask acc = (clO n ok d pos mask acc).length := by
  intro d
  induction d with
  | zero => intro pos mask acc; rfl
  | succ d ih =>
    intro pos mask acc
    change Nat.rec (motive := fun _ => ℕ) 0 (fun v rest => Nat.add
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 0
          (cntO n ok d (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft 1 v))
            (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))))
          (ok acc pos v))
        0 (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) rest) n = _
    rw [P.rec_add, clO, List.length_flatMap]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    simp only [P.bit_eq, P.lor_eq, P.shl_eq]
    cases mask.testBit v
    · cases ok acc pos v
      · rfl
      · exact ih _ _ _
    · rfl

private theorem mem_clO {n : ℕ} (ok : ℕ → ℕ → ℕ → Bool) : ∀ (d pos mask acc x : ℕ),
    x ∈ clO n ok d pos mask acc ↔
      ∃ l : List ℕ, l.length = d ∧ P.Adm n mask l ∧ OkO ok acc pos l ∧ x = P.ext acc pos l := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc x
    simp only [clO, List.mem_singleton]
    constructor
    · exact fun h => ⟨[], rfl, P.adm_nil n mask, trivial, by rw [ext_nil']; exact h⟩
    · rintro ⟨l, hl, _, _, rfl⟩
      rw [List.length_eq_zero_iff.1 hl, ext_nil']
  | succ d ih =>
    intro pos mask acc x
    rw [clO, List.mem_flatMap]
    constructor
    · rintro ⟨v, hv, hx⟩
      cases hb : mask.testBit v
      · cases hc : ok acc pos v
        · simp [hb, hc] at hx
        · rw [hb, hc] at hx
          obtain ⟨l', hl', hadm', hok', rfl⟩ := (ih _ _ _ _).1 (by simpa using hx)
          exact ⟨v :: l', by simp [hl'], P.adm_cons.2 ⟨List.mem_range.1 hv, hb, hadm'⟩,
            ⟨hc, hok'⟩, (ext_cons' _ _ _ _).symm⟩
      · simp [hb] at hx
    · rintro ⟨l, hl, hadm, hok, rfl⟩
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := P.adm_cons.1 hadm
      obtain ⟨hc, hok'⟩ := hok
      refine ⟨v, List.mem_range.2 hv, ?_⟩
      rw [hb, hc, ext_cons']
      exact (ih _ _ _ _).2 ⟨l', by simpa using hl, hadm', hok', rfl⟩

private theorem nodup_clO {n : ℕ} (hn : n ≤ 32) (ok : ℕ → ℕ → ℕ → Bool) :
    ∀ d pos mask acc, acc < 32 ^ pos → (clO n ok d pos mask acc).Nodup := by
  intro d
  induction d with
  | zero => exact fun _ _ _ _ => List.nodup_singleton _
  | succ d ih =>
    intro pos mask acc hacc
    have hlt : ∀ v < n, acc + v * 32 ^ pos < 32 ^ (pos + 1) := fun v hv => by
      have : v * 32 ^ pos ≤ 31 * 32 ^ pos := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ]
      omega
    rw [clO, List.nodup_flatMap]
    refine ⟨fun v hv => ?_, ?_⟩
    · cases mask.testBit v
      · cases ok acc pos v
        · exact List.nodup_nil
        · exact ih _ _ _ (hlt v (List.mem_range.1 hv))
      · exact List.nodup_nil
    · refine List.nodup_range.pairwise_of_forall_ne fun v hv w hw hvw => ?_
      intro x hx hx'
      have key : ∀ u ∈ List.range n, x ∈ (if mask.testBit u then [] else
          if ok acc pos u then clO n ok d (pos + 1) (mask ||| 2 ^ u) (acc + u * 32 ^ pos)
          else []) → x % 32 ^ (pos + 1) = acc + u * 32 ^ pos := fun u hu hxu => by
        cases hb : mask.testBit u
        · cases hc : ok acc pos u
          · simp [hb, hc] at hxu
          · rw [hb, hc] at hxu
            obtain ⟨l, _, _, _, rfl⟩ := (mem_clO _ _ _ _ _ _).1 (by simpa using hxu)
            exact P.ext_mod l (hlt u (List.mem_range.1 hu))
        · simp [hb] at hxu
      have e := (key v hv hx).symm.trans (key w hw hx')
      exact hvw (Nat.eq_of_mul_eq_mul_right (by positivity) (Nat.add_left_cancel e))

private theorem imgs_length {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) : (P.imgs σ).length = n := by
  classical
  have h : P.allP n (fun x => decide (∃ l : List ℕ, l.length = n ∧ P.Adm n 0 l ∧
      P.ext 0 0 l = x)) = true := by
    rw [P.allP, P.dfs_and]
    exact fun l hl hadm => decide_eq_true ⟨l, hl, hadm, rfl⟩
  obtain ⟨l, hl, hadm, he⟩ := of_decide_eq_true ((P.allP_iff _).1 h σ)
  obtain ⟨τ, rfl⟩ := P.exists_imgs hl hadm
  rw [P.ext_imgs] at he
  rwa [P.code_inj hn he] at hl

open Classical in
private theorem cntO_card {n : ℕ} (hn : n ≤ 32) (ok : ℕ → ℕ → ℕ → Bool) :
    cntO n ok n 0 0 0 =
      (Finset.univ.filter fun σ : Perm (Fin n) => OkO ok 0 0 (P.imgs σ)).card := by
  rw [cntO_eq]
  have hL : (clO n ok n 0 0 0).Nodup := nodup_clO hn ok n 0 0 0 (by norm_num)
  rw [← List.toFinset_card_of_nodup hL,
    ← Finset.card_image_of_injective _ (fun a b h => P.code_inj hn h)]
  congr 1
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_clO]
  constructor
  · rintro ⟨l, hl, hadm, hok, rfl⟩
    obtain ⟨σ, rfl⟩ := P.exists_imgs hl hadm
    exact ⟨σ, hok, (P.ext_imgs σ).symm⟩
  · rintro ⟨σ, hok, rfl⟩
    exact ⟨P.imgs σ, imgs_length hn σ, P.adm_imgs σ, hok, (P.ext_imgs σ).symm⟩

private theorem iffB_iff {a b : Bool} : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

private theorem okO_st {n : ℕ} (hn : n ≤ 32) (B C : ℕ) (σ : Perm (Fin n)) :
    OkO (stOK B C) 0 0 (P.imgs σ) ↔
      (∀ i j : Fin n, P.img B i = P.img B j ↔ P.img B (σ i) = P.img B (σ j)) ∧
        (∀ i j : Fin n, P.img C i = P.img C j ↔ P.img C (σ i) = P.img C (σ j)) := by
  rw [okO_iff]
  have hl : (P.imgs σ).length = n := imgs_length hn σ
  have hget : ∀ k (hk : k < (P.imgs σ).length), (P.imgs σ)[k] = (σ ⟨k, hl ▸ hk⟩ : ℕ) := by
    intro k hk
    have := P.imgs_getD σ (hl ▸ hk)
    rw [List.getD_eq_getElem _ _ hk, P.vals_fin σ ⟨k, hl ▸ hk⟩] at this
    exact this
  have key : ∀ k (hk : k < (P.imgs σ).length),
      stOK B C (P.ext 0 0 ((P.imgs σ).take k)) (0 + k) (P.imgs σ)[k] = true ↔
        ∀ i : Fin n, (i : ℕ) < k →
          (P.img B i = P.img B k ↔ P.img B (σ i) = P.img B (σ ⟨k, hl ▸ hk⟩)) ∧
          (P.img C i = P.img C k ↔ P.img C (σ i) = P.img C (σ ⟨k, hl ▸ hk⟩)) := by
    intro k hk
    have hkn : k < n := hl ▸ hk
    rw [P.ext_take σ hkn.le, zero_add, hget k hk]
    unfold stOK
    rw [P.allN_iff]
    constructor
    · intro h i hi
      have := h i hi
      rw [P.andB_iff, iffB_iff, iffB_iff, P.beq_iff, P.beq_iff, P.beq_iff, P.beq_iff,
        P.img_E hn σ hkn.le i hi] at this
      exact this
    · intro h i hi
      have := h ⟨i, by omega⟩ hi
      rw [P.andB_iff, iffB_iff, iffB_iff, P.beq_iff, P.beq_iff, P.beq_iff, P.beq_iff,
        P.img_E hn σ hkn.le ⟨i, by omega⟩ hi]
      exact this
  have hall : (∀ k (hk : k < (P.imgs σ).length),
      stOK B C (P.ext 0 0 ((P.imgs σ).take k)) (0 + k) (P.imgs σ)[k] = true) ↔
      ∀ i j : Fin n, (i : ℕ) < j →
        (P.img B i = P.img B j ↔ P.img B (σ i) = P.img B (σ j)) ∧
        (P.img C i = P.img C j ↔ P.img C (σ i) = P.img C (σ j)) := by
    constructor
    · intro h i j hij
      exact (key j (hl.symm ▸ j.isLt)).1 (h j _) i hij
    · intro h k hk
      exact (key k hk).2 fun i hi => h i ⟨k, hl ▸ hk⟩ hi
  rw [hall]
  constructor
  · intro h
    have both : ∀ i j : Fin n,
        (P.img B i = P.img B j ↔ P.img B (σ i) = P.img B (σ j)) ∧
        (P.img C i = P.img C j ↔ P.img C (σ i) = P.img C (σ j)) := by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact h i j hij
      · exact ⟨iff_of_true rfl rfl, iff_of_true rfl rfl⟩
      · obtain ⟨h1, h2⟩ := h j i hij
        exact ⟨by rw [eq_comm, h1, eq_comm], by rw [eq_comm, h2, eq_comm]⟩
    exact ⟨fun i j => (both i j).1, fun i j => (both i j).2⟩
  · rintro ⟨h1, h2⟩ i j _
    exact ⟨h1 i j, h2 i j⟩

private theorem card_relStab {n : ℕ} (hn : n ≤ 32) (bx bx' : Fin n → ℕ) {X Y : ℕ}
    (hx : ∀ i, bx i = P.img X i) (hy : ∀ i, bx' i = P.img Y i) :
    Fintype.card {σ : Perm (Fin n) // σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab bx ∧
      σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab bx'} = cntSt n X Y := by
  classical
  rw [cntSt_eq, cntO_card hn, Fintype.card_subtype]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, okO_st hn]
  change ((∀ i j, bx i = bx j ↔ bx (σ i) = bx (σ j)) ∧
    (∀ i j, bx' i = bx' j ↔ bx' (σ i) = bx' (σ j))) ↔ _
  simp only [hx, hy]

theorem s4138 (bx7 by7 : Fin 7 → ℕ) (bx8 by8 : Fin 8 → ℕ) {X7 Y7 X8 Y8 : ℕ}
    (hx7 : ∀ i, bx7 i = P.img X7 i) (hy7 : ∀ i, by7 i = P.img Y7 i)
    (hx8 : ∀ i, bx8 i = P.img X8 i) (hy8 : ∀ i, by8 i = P.img Y8 i)
    (hk : c4138 X7 Y7 X8 Y8 = true) :
    (Fintype.card
        {σ : Perm (Fin 7) // σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab bx7 ∧
          σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab by7} = 48)
    ∧ (Fintype.card
        {σ : Perm (Fin 8) // σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab bx8 ∧
          σ ∈ CFSG.QuasithinUnique.Setup.X3.relStab by8} = 128) := by
  unfold c4138 at hk
  rw [P.andB_iff, P.beq_iff, P.beq_iff] at hk
  exact ⟨by convert (card_relStab (by norm_num) bx7 by7 hx7 hy7).trans hk.1,
    by convert (card_relStab (by norm_num) bx8 by8 hx8 hy8).trans hk.2⟩

theorem s4128 (x y z : Perm (Fin 7)) {X Y Z : ℕ} (hx : code x = X) (hy : code y = Y)
    (hz : code z = Z) (hk : c4128 X Y Z = true) :
    let S : Finset (Perm (Fin 7)) := {1, x, y, x * y, z, x * z, y * z, x * y * z}
    let K : Finset (Perm (Fin 7)) := {1, x, y, x * y}
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    ∧ (∀ a ∈ S, a⁻¹ ∈ S)
    ∧ ((1 : Perm (Fin 7)) ∈ S)
    ∧ (S.card = 8)
    ∧ (∀ a ∈ S, Perm.sign a = 1)
    ∧ (∀ a ∈ K, ∀ b ∈ K, a * b ∈ K)
    ∧ (∀ a ∈ K, a⁻¹ ∈ K)
    ∧ ((1 : Perm (Fin 7)) ∈ K)
    ∧ (K.card = 4)
    ∧ (K ⊆ S)
    ∧ (x ∈ K)
    ∧ (y ∈ K)
    ∧ (z ∈ S)
    ∧ (∀ g : Perm (Fin 7), Perm.sign g = 1 →
          g * x * g⁻¹ ∈ S → g * y * g⁻¹ ∈ S → g * z * g⁻¹ ∈ S → g ∈ S)
    ∧ (∀ c : Perm (Fin 7), Perm.sign c = 1 →
          c * x * c⁻¹ ∈ S → c * y * c⁻¹ ∈ S → (c * x * c⁻¹ ∈ K ∧ c * y * c⁻¹ ∈ K))
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) =>
            Perm.sign g = 1 ∧ g * x * g⁻¹ ∈ K ∧ g * y * g⁻¹ ∈ K).card = 72)
    ∧ (z * y ≠ y * z) := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  subst hx hy hz
  set Ls : List (Perm (Fin 7)) := [1, x, y, x * y, z, x * z, y * z, x * y * z] with hLs
  set Lk : List (Perm (Fin 7)) := [1, x, y, x * y] with hLk
  have hsyl : syl (code x) (code y) (code z) = Ls.map P.code := by
    simp [Ls, syl, code_eq_P, P.code_mul h7, P.code_one]
  have hkle : kle (code x) (code y) = Lk.map P.code := by
    simp [Lk, kle, code_eq_P, P.code_mul h7, P.code_one]
  unfold c4128 at hk
  rw [hsyl, hkle] at hk
  unfold subOK at hk
  simp only [P.andB_iff, P.impB_iff, P.notB_iff, P.allP_iff, P.allL_map, memL_iff,
    P.mem_map_code h7, code_eq_P, P.even_code h7, P.code_mul h7, P.code_inv h7, P.conj_code h7,
    P.code_one, P.cntP_eq h7, P.comm_code h7, lenRec_eq, List.length_map,
    distinctL_map h7, P.beq_iff] at hk
  obtain ⟨⟨s1, s2, s3, s4, s5, s6⟩, ⟨k1, k2, k3, k4, k5, -⟩, hks, hg, hc, hcnt, hzy⟩ := hk
  have hS : ({1, x, y, x * y, z, x * z, y * z, x * y * z} : Finset (Perm (Fin 7))) =
      Ls.toFinset := by simp [Ls]
  have hK : ({1, x, y, x * y} : Finset (Perm (Fin 7))) = Lk.toFinset := by simp [Lk]
  dsimp only
  rw [hS, hK]
  simp only [List.mem_toFinset]
  refine ⟨s1, s2, s3, ?_, s6, k1, k2, k3, ?_, fun a ha => List.mem_toFinset.2
    (hks a (List.mem_toFinset.1 ha)), by simp [Lk], by simp [Lk], by simp [Ls], hg, hc, hcnt,
    hzy⟩
  · rw [List.toFinset_card_of_nodup s5, s4]
  · rw [List.toFinset_card_of_nodup k5, k4]

theorem s4032a {ks : List ℕ} (h : c4032a ks = true) :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 → fixCount σ ∈ ks := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  intro σ h1 h2
  have := (P.allP_iff _).1 h σ
  simp only [P.impB_iff, P.notB_iff, P.code_mul h7, P.code_one, P.beq_code h7, memL_iff,
    P.fix_code h7] at this
  exact this h1 h2

theorem cover_code {k : ℕ} {l : List ℕ} (h : invCover k l = true) :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = k → P.code σ ∈ l := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  intro σ h1 h2
  have := (P.allP_iff _).1 h σ
  simp only [P.impB_iff, P.code_mul h7, P.code_one, P.beq_code h7, memL_iff, P.fix_code h7,
    P.beq_iff] at this
  exact this h1 h2

theorem s4032bc {lb lc : List ℕ} (hb : invCover 3 lb = true) (hb' : ∀ s ∈ lb, p22 s = true)
    (hc : invCover 5 lc = true) (hc' : ∀ s ∈ lc, q2 s = true) :
    (∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = 3 → P22 σ)
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = 5 → Q2 σ) := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  refine ⟨fun σ h1 h2 => ?_, fun σ h1 h2 => ?_⟩
  · have hp := hb' _ (cover_code hb σ h1 h2)
    unfold p22 at hp
    rw [P.anyC_iff h7] at hp
    obtain ⟨c, hc, hp⟩ := hp
    simp only [P.andB_iff, P.notB_iff, P.impB_iff, P.orB_iff, P.even_code h7, P.code_mul h7,
      P.code_inv h7, P.conj_code h7, P.code_one, P.beq_code h7, P.allC_iff h7] at hp
    obtain ⟨hs, hc3, hc1, hall⟩ := hp
    exact ⟨c, hs, hc3, hc1, hc.symm, fun g hg hgs => hall g hgs.symm hg⟩
  · have hq := hc' _ (cover_code hc σ h1 h2)
    unfold q2 at hq
    simp only [P.andB_iff, P.notB_iff, P.impB_iff, P.even_code h7, P.code_mul h7,
      P.code_pow h7, P.conj_code h7, P.code_one, P.beq_code h7, P.allC_iff h7,
      P.anyC_iff h7] at hq
    intro x hx hxs hxx hx1
    obtain ⟨g, hg, hs, h3, h1⟩ := hq x hxs.symm hx hxx hx1
    exact ⟨g, hs, hg.symm, h3, h1⟩

theorem s4032d {k : ℕ} (h : c4032d k = true) :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = k →
      ∃ c : Perm (Fin 7), Perm.sign c = 1 ∧ c ≠ 1 ∧ σ * c = c * σ := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  intro σ h1 h2
  have := (P.allP_iff _).1 h σ
  simp only [P.impB_iff, P.andB_iff, P.notB_iff, P.code_mul h7, P.code_one, P.beq_code h7,
    P.fix_code h7, P.beq_iff, P.anyC_iff h7, P.even_code h7] at this
  obtain ⟨c, hc, hs, hc1⟩ := this h1 h2
  exact ⟨c, hs, hc1, hc.symm⟩

theorem s4032e (L : List (Perm (Fin 7))) {ts : List ℕ} (hL : L.map code = ts)
    (h : c4032e ts = true) : ∀ τ : Perm (Fin 7), (∀ g ∈ L, τ * g = g * τ) → τ = 1 := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  subst hL
  intro τ hτ
  have := (P.allP_iff _).1 h τ
  simp only [P.impB_iff, commL_eq, code_eq_P, P.allL_map, P.comm_code h7, P.code_one,
    P.beq_code h7] at this
  exact this hτ

theorem s4095 (G H U T : List (Perm (Fin 6))) {LG LH LU LT : List ℕ} (hG : G.map code = LG)
    (hH : H.map code = LH) (hU : U.map code = LU) (hT : T.map code = LT)
    (hk : c4095 LG LH LU LT = true) :
    (∀ g ∈ G, ∀ x ∈ H, g * x ∈ H ∧ g⁻¹ * x ∈ H)
    ∧ (∀ g ∈ U, ∀ x ∈ T, g * x ∈ T ∧ g⁻¹ * x ∈ T)
    ∧ (∀ x ∈ H, (∀ t ∈ U, x * t * x⁻¹ ∈ T) → x ∈ T) := by
  have h6 : (6 : ℕ) ≤ 32 := by norm_num
  subst hG hH hU hT
  unfold c4095 at hk
  simp only [P.andB_iff, P.impB_iff, code_eq_P, P.allL_map, P.code_mul h6, P.code_inv h6,
    P.conj_code h6, memL_iff, P.mem_map_code h6] at hk
  exact hk

@[expose] def codeL (l : List ℕ) : ℕ :=
  ((List.range l.length).zip l |>.map fun p => p.2 * 32 ^ p.1).sum

theorem eqLs_iff : ∀ l m : List ℕ, eqLs l m = true ↔ l = m
  | [], [] => by simp [eqLs]
  | [], _ :: _ => by simp [eqLs]
  | _ :: _, [] => by simp [eqLs]
  | x :: l, y :: m => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (eqLs l m) = true ↔ _
    rw [P.andB_iff, P.beq_iff, eqLs_iff l m, List.cons.injEq]

theorem mem_filtL (l : List ℕ) (f : ℕ → Bool) (x : ℕ) : x ∈ filtL l f ↔ x ∈ l ∧ f x = true := by
  induction l with
  | nil => simp [filtL]
  | cons y l ih =>
    change x ∈ Bool.rec (motive := fun _ => List ℕ) (filtL l f) (y :: filtL l f) (f y) ↔ _
    cases hy : f y
    · change x ∈ filtL l f ↔ _
      rw [ih, List.mem_cons]
      constructor
      · exact fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · rw [hy] at h2
          cases h2
        · exact ⟨h1, h2⟩
    · change x ∈ y :: filtL l f ↔ _
      rw [List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        exacts [⟨Or.inl rfl, hy⟩, ⟨Or.inr h1, h2⟩]
      · rintro ⟨rfl | h1, h2⟩
        exacts [Or.inl rfl, Or.inr ⟨h1, h2⟩]

theorem codeL_eq (l : List ℕ) : codeL l = P.E (fun i => l.getD i 0) l.length := by
  have e : ∀ (f : ℕ → ℕ) (m : ℕ), P.E f m = ((List.range m).map fun i => f i * 32 ^ i).sum := by
    intro f m
    induction m with
    | zero => simp [P.E_zero]
    | succ m ih => rw [P.E_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp
  rw [e, codeL]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h2)]

def Tab (n : ℕ) (l : List ℕ) : Prop := l.length = n ∧ ∀ v ∈ l, v < n

theorem tab_getD {n : ℕ} {l : List ℕ} (hl : Tab n l) {i : ℕ} (hi : i < n) : l.getD i 0 < n := by
  rw [List.getD_eq_getElem _ _ (by rw [hl.1]; exact hi)]
  exact hl.2 _ (List.getElem_mem _)

theorem img_codeL {n : ℕ} (hn : n ≤ 32) {l : List ℕ} (hl : Tab n l) {i : ℕ} (hi : i < n) :
    P.img (codeL l) i = l.getD i 0 := by
  rw [P.img_eq, codeL_eq, hl.1, P.E_digit (fun j hj => by have := tab_getD hl hj; omega) hi]

theorem codeL_inj {n : ℕ} (hn : n ≤ 32) {a b : List ℕ} (ha : Tab n a) (hb : Tab n b)
    (h : codeL a = codeL b) : a = b := by
  apply List.ext_getElem (ha.1.trans hb.1.symm)
  intro i h1 h2
  have hi : i < n := ha.1 ▸ h1
  have := img_codeL hn ha hi
  rw [h, img_codeL hn hb hi, List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h1] at this
  exact this.symm

theorem tab_cmul {n : ℕ} {a b : List ℕ} (ha : Tab n a) (hb : Tab n b) :
    Tab n (CFSG.QuasithinUnique.A6Facts.Core.cmul a b) := by
  refine ⟨by simp [CFSG.QuasithinUnique.A6Facts.Core.cmul, hb.1], fun v hv => ?_⟩
  simp only [CFSG.QuasithinUnique.A6Facts.Core.cmul, List.mem_map] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  exact tab_getD ha (hb.2 j hj)

theorem mul_codeL {n : ℕ} (hn : n ≤ 32) {a b : List ℕ} (ha : Tab n a) (hb : Tab n b) :
    P.mul n (codeL a) (codeL b) = codeL (CFSG.QuasithinUnique.A6Facts.Core.cmul a b) := by
  rw [P.mul, P.ofFn_eq, codeL_eq (CFSG.QuasithinUnique.A6Facts.Core.cmul a b), (tab_cmul ha hb).1]
  refine P.E_congr fun i hi => ?_
  have hib : i < b.length := by rw [hb.1]; exact hi
  rw [img_codeL hn hb hi, img_codeL hn ha (tab_getD hb hi), CFSG.QuasithinUnique.A6Facts.Core.cmul,
    List.getD_eq_getElem (List.map (fun j => a.getD j 0) b) 0 (by simpa using hib),
    List.getElem_map, List.getD_eq_getElem b 0 hib]

theorem tab_range (n : ℕ) : Tab n (List.range n) := ⟨by simp, fun v hv => List.mem_range.1 hv⟩

theorem one_codeL (n : ℕ) : P.one n = codeL (List.range n) := by
  rw [P.one, P.ofFn_eq, codeL_eq, List.length_range]
  refine P.E_congr fun i hi => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_range]

theorem tab_cpow {n : ℕ} {a : List ℕ} (ha : Tab n a) (k : ℕ) :
    Tab n (CFSG.QuasithinUnique.A6Facts.Core.cpow a k) := by
  induction k with
  | zero =>
    change Tab n (List.range a.length)
    rw [ha.1]
    exact tab_range n
  | succ k ih => exact tab_cmul ih ha

theorem pow_codeL {n : ℕ} (hn : n ≤ 32) {a : List ℕ} (ha : Tab n a) (k : ℕ) :
    P.pow n (codeL a) k = codeL (CFSG.QuasithinUnique.A6Facts.Core.cpow a k) := by
  induction k with
  | zero =>
    change P.one n = codeL (List.range a.length)
    rw [ha.1, one_codeL]
  | succ k ih =>
    change P.mul n (P.pow n (codeL a) k) (codeL a) = _
    rw [ih, mul_codeL hn (tab_cpow ha k) ha]
    rfl

open CFSG.QuasithinUnique.A6Facts in
theorem s4153 (ls : List (List ℕ)) {L Q : List ℕ} (hc : ls.map codeL = L)
    (hv : ∀ x ∈ ls, x.length = 10 ∧ ∀ v ∈ x, v < 10) (hk : c4153 L Q = true) :
    ls.all (fun x => x == Core.cid || Core.cpow x 45 != Core.cid ||
      ls.all fun u => Core.cmul u x != Core.cmul x u || Core.cpow u 45 == Core.cid) = true := by
  have h10 : (10 : ℕ) ≤ 32 := by norm_num
  have ht : ∀ x ∈ ls, Tab 10 x := hv
  have hid : Tab 10 Core.cid := tab_range 10
  subst hc
  unfold c4153 at hk
  rw [P.andB_iff, eqLs_iff, P.allL_iff] at hk
  obtain ⟨hQ, hall⟩ := hk
  subst hQ
  rw [List.all_eq_true]
  intro x hx
  have h := hall (codeL x) (List.mem_map_of_mem hx)
  simp only [P.orB_iff, P.notB_iff, P.beq_iff, memL_iff, mem_filtL, P.allL_iff, P.comm,
    List.mem_map] at h
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true]
  rcases h with h | h | h
  · left; left
    exact codeL_inj h10 (ht x hx) hid (h.trans (one_codeL 10))
  · left; right
    intro e
    refine h ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [pow_codeL h10 (ht x hx), e, one_codeL]
    rfl
  · right
    intro u hu
    rcases h (codeL u) ⟨u, hu, rfl⟩ with h' | ⟨-, h'⟩
    · left
      intro e
      exact h' (by rw [mul_codeL h10 (ht u hu) (ht x hx), mul_codeL h10 (ht x hx) (ht u hu), e])
    · right
      rw [pow_codeL h10 (ht u hu), one_codeL] at h'
      exact codeL_inj h10 (tab_cpow (ht u hu) 45) hid h'

theorem s4147 (cs : Array ℕ) {L : List ℕ} {k N : ℕ} (hL : cs.toList = L) (hk : cs.size = k)
    (hc : c4147 L k N = true) :
    ∀ l₀ : Fin cs.size, l₀.val = 0 → ∀ U : Finset (Fin cs.size),
      l₀ ∈ U → (∑ l ∈ U, cs[l.val]!) ∣ N → U = {l₀} ∨ U = Finset.univ := by
  subst hL hk
  intro l₀ hl₀ U hU hdvd
  unfold c4147 at hc
  rw [P.andB_iff, P.allN_iff] at hc
  obtain ⟨-, hall⟩ := hc
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = U.image Fin.val := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ∑ i ∈ s, 2 ^ i := ⟨_, rfl⟩
  have hmemU : ∀ i : Fin cs.size, i ∈ U ↔ (i : ℕ) ∈ s := fun i => by
    rw [hs, Finset.mem_image]
    exact ⟨fun h => ⟨i, h, rfl⟩, fun ⟨a, ha, e⟩ => Fin.ext e ▸ ha⟩
  have hbit : ∀ j, m.testBit j = true ↔ j ∈ s := fun j => by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset, hm, Finset.toFinset_bitIndices_sum_two_pow]
  have hsK : ∀ j ∈ s, j < cs.size := fun j hj => by
    rw [hs] at hj
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
    exact a.isLt
  have hK0 : 0 < cs.size := Nat.lt_of_le_of_lt (Nat.zero_le _) l₀.isLt
  have hlt : m < 2 ^ cs.size := Nat.lt_pow_two_of_testBit m fun i hi => by
    cases e : m.testBit i
    · rfl
    · exact absurd (hsK i ((hbit i).1 e)) (by omega)
  have hodd : m % 2 = 1 := by
    have := (hbit 0).2 (by rw [← hl₀]; exact (hmemU l₀).1 hU)
    rw [Nat.testBit_zero, decide_eq_true_iff] at this
    exact this
  have hpow : 2 ^ cs.size = 2 * 2 ^ (cs.size - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsum : sumMask cs.toList m = ∑ l ∈ U, cs[l.val]! := by
    have key : ∀ (l : List ℕ) (i : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
        (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => ℕ) 0 x
          (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) (ih (Nat.succ i))) l i =
        ∑ j ∈ Finset.range l.length, if m.testBit (i + j) then l.getD j 0 else 0 := by
      intro l
      induction l with
      | nil => intro i; rfl
      | cons x l ih =>
        intro i
        change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 x
          (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) (List.rec (motive := fun _ => ℕ → ℕ)
            (fun _ => 0) (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => ℕ) 0 x
              (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) (ih (Nat.succ i))) l (Nat.succ i)) = _
        rw [ih, P.bit_eq, List.length_cons, Finset.sum_range_succ', Nat.add_zero,
          List.getD_cons_zero, Nat.add_eq, Nat.add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [List.getD_cons_succ, Nat.succ_eq_add_one, Nat.add_right_comm, Nat.add_assoc]
        · cases m.testBit i <;> rfl
    change List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
        (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => ℕ) 0 x
          (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) (ih (Nat.succ i))) cs.toList 0 = _
    rw [key, Array.length_toList, ← Finset.sum_filter]
    have hf : (Finset.range cs.size).filter (fun j => m.testBit (0 + j) = true) = s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add, hbit]
      exact ⟨fun h => h.2, fun h => ⟨hsK j h, h⟩⟩
    rw [hf, hs, Finset.sum_image fun a _ b _ e => Fin.ext e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact i.isLt), Array.getElem_toList,
      getElem!_pos cs i.val i.isLt]
  have h2 := hall (m / 2) (by
    rw [show Nat.shiftLeft 1 (Nat.sub cs.size 1) = 2 ^ (cs.size - 1) from Nat.one_shiftLeft _]
    omega)
  rw [P.letB_eq] at h2
  have em : Nat.add (Nat.shiftLeft (m / 2) 1) 1 = m := by
    change (m / 2) <<< 1 + 1 = m
    rw [Nat.shiftLeft_eq, pow_one]
    omega
  rw [em, hsum, P.impB_iff, P.beq_iff, P.orB_iff, P.beq_iff, P.beq_iff] at h2
  have h3 := h2 (Nat.mod_eq_zero_of_dvd hdvd)
  change m = 1 ∨ m = 1 <<< cs.size - 1 at h3
  rw [Nat.one_shiftLeft] at h3
  rcases h3 with h3 | h3
  · left
    ext i
    rw [hmemU, ← hbit, h3, Finset.mem_singleton, Fin.ext_iff, hl₀]
    change (2 ^ 0).testBit i = true ↔ _
    rw [Nat.testBit_two_pow, decide_eq_true_iff, eq_comm]
  · right
    ext i
    rw [hmemU, ← hbit, h3, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    simp [i.isLt]

theorem s4152 (P0l V0l K1l T0l : List (Perm (Fin 7))) (aP bP c1P c2P : Perm (Fin 7))
    {LP LV LK LT : List ℕ} {A B C1 C2 : ℕ} (hP : P0l.map code = LP) (hV : V0l.map code = LV)
    (hK : K1l.map code = LK) (hT : T0l.map code = LT) (ha : code aP = A) (hb : code bP = B)
    (h1 : code c1P = C1) (h2 : code c2P = C2) (hl : c4152l LP LV LK LT A B C1 C2 = true)
    (hs : c4152s LV LK LT C1 C2 = true) :
    ((∀ σ ∈ P0l, Perm.sign σ = 1) ∧
            (∀ σ ∈ V0l, Perm.sign σ = 1) ∧
            (∀ σ ∈ K1l, Perm.sign σ = 1) ∧
            (∀ σ ∈ T0l, Perm.sign σ = 1) ∧
            (Perm.sign aP = 1 ∧ Perm.sign bP = 1 ∧ Perm.sign c1P = 1 ∧ Perm.sign c2P = 1) ∧
            ((1 : Perm (Fin 7)) ∈ P0l) ∧
            (∀ x ∈ P0l, ∀ y ∈ P0l, x * y ∈ P0l) ∧
            (∀ x ∈ P0l, x⁻¹ ∈ P0l) ∧
            ((1 : Perm (Fin 7)) ∈ V0l) ∧
            (∀ x ∈ V0l, ∀ y ∈ V0l, x * y ∈ V0l) ∧
            (∀ x ∈ V0l, x⁻¹ ∈ V0l) ∧
            ((1 : Perm (Fin 7)) ∈ K1l) ∧
            (∀ x ∈ K1l, ∀ y ∈ K1l, x * y ∈ K1l) ∧
            (∀ x ∈ K1l, x⁻¹ ∈ K1l) ∧
            ((1 : Perm (Fin 7)) ∈ T0l) ∧
            (∀ x ∈ T0l, ∀ y ∈ T0l, x * y ∈ T0l) ∧
            (∀ x ∈ T0l, x⁻¹ ∈ T0l) ∧
            (∀ σ ∈ V0l, σ ∈ P0l) ∧
            (∀ σ ∈ P0l, σ ∈ K1l) ∧
            (P0l.toFinset.card = 8) ∧
            (V0l.toFinset.card = 4) ∧
            (K1l.toFinset.card = 24) ∧
            (T0l.toFinset.card = 3) ∧
            (∀ k ∈ K1l, ∀ v ∈ V0l, k * v * k⁻¹ ∈ V0l) ∧
            (∀ k ∈ K1l, (∀ v ∈ V0l, k * v = v * k) → k ∈ V0l) ∧
            (∃ k ∈ K1l, ∃ p ∈ P0l, k * p * k⁻¹ ∉ P0l) ∧
            (∀ τ : Perm (Fin 7), τ ^ 2 = 1 → (Finset.univ.filter fun i => τ i = i).card = 1 →
              ∃ k ∈ K1l, k * τ ≠ τ * k) ∧
            (∀ x : Perm (Fin 7), Perm.sign x = 1 → x ^ 3 = 1 → (∀ v ∈ V0l, x * v = v * x) →
              x ∈ T0l) ∧
            (∀ u₁ ∈ P0l, ∀ u₂ ∈ P0l, u₁ ≠ 1 → u₂ ≠ 1 → u₁ ≠ u₂ → u₁ * u₂ = u₂ * u₁ →
              u₁ * u₁ = 1 → u₂ * u₂ = 1 → (∃ x : Perm (Fin 7), Perm.sign x = 1 ∧ x ≠ 1 ∧
                x ^ 3 = 1 ∧ x * u₁ = u₁ * x ∧ x * u₂ = u₂ * x) → u₁ ∈ V0l ∧ u₂ ∈ V0l) ∧
            (∀ y ∈ T0l, y ≠ 1 → ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y) ∧
            (∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = c1P) ∧
            (∀ y : Perm (Fin 7), Perm.sign y = 1 → y ^ 3 = 1 → y ≠ 1 →
              (∀ v ∈ V0l, y * v * y⁻¹ ∈ V0l) → y ∉ T0l →
              (∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y) → y ∈ K1l) ∧
            (aP ≠ 1) ∧
            (bP ≠ 1) ∧
            (aP ≠ bP) ∧
            (aP * bP = bP * aP) ∧
            (aP * aP = 1) ∧
            (bP * bP = 1) ∧
            (c2P ≠ 1) ∧
            (c2P ^ 3 = 1) ∧
            (c1P ≠ 1) ∧
            (c1P ^ 3 = 1) ∧
            (c2P * aP = aP * c2P) ∧
            (c2P * bP = bP * c2P) ∧
            (c1P ∈ K1l) ∧
            (c1P ∉ T0l) ∧
            (c2P ∈ T0l) ∧
            (aP ∈ V0l) ∧
            (bP ∈ V0l)) := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  subst hP hV hK hT ha hb h1 h2
  unfold c4152l grpL at hl
  unfold c4152s at hs
  simp only [allBs_cons, allBs_nil, P.andB_iff, P.impB_iff, P.notB_iff, P.allP_iff, P.anyP_iff,
    P.allL_map, P.anyL_map, memL_iff, P.mem_map_code h7, code_eq_P, P.even_code h7,
    P.code_mul h7, P.code_inv h7, P.conj_code h7, P.code_pow h7, P.code_one, P.beq_code h7,
    P.comm_code h7, P.anyC_iff h7, lenL_eq, List.length_map, distinctL_map h7, P.fix_code h7,
    P.beq_iff, and_true] at hl hs
  obtain ⟨eP, eV, eK, eT, eA, eB, eC1, eC2, ⟨gP1, gP2, gP3⟩, ⟨gV1, gV2, gV3⟩, ⟨gK1, gK2, gK3⟩,
    ⟨gT1, gT2, gT3⟩, sVP, sPK, dP, lP, dV, lV, dK, lK, dT, lT, cKV, zKV, nKP, a1, b1, ab, cab, aa,
    bb, c21, c23, c11, c13, c2a, c2b, c1K, c1T, c2T, aV, bV, big⟩ := hl
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hs
  exact ⟨eP, eV, eK, eT, ⟨eA, eB, eC1, eC2⟩, gP1, gP2, gP3, gV1, gV2, gV3, gK1, gK2, gK3, gT1,
    gT2, gT3, sVP, sPK, by rw [List.toFinset_card_of_nodup dP, lP],
    by rw [List.toFinset_card_of_nodup dV, lV], by rw [List.toFinset_card_of_nodup dK, lK],
    by rw [List.toFinset_card_of_nodup dT, lT], cKV, zKV, nKP, hs1, hs2,
    fun u₁ hu₁ u₂ hu₂ n₁ n₂ n₁₂ hc s₁ s₂ ⟨x, hx1, hx2, hx3, hx4, hx5⟩ =>
      big u₁ hu₁ u₂ hu₂ n₁ n₂ n₁₂ hc s₁ s₂ ⟨x, hx4, hx1, hx2, hx3, hx5⟩,
    hs3, hs4, hs5, a1, b1, ab, cab, aa, bb, c21, c23, c11, c13, c2a, c2b, c1K, c1T, c2T, aV, bV⟩

section C4046

open CFSG.QuasithinUnique.Unc25G2.Tbl

private theorem getK_cons_zero (x : ℕ) (l : List ℕ) : getK (x :: l) 0 = x := rfl

private theorem getK_one_mem : ∀ {l : List ℕ}, 2 ≤ l.length → getK l 1 ∈ l
  | [], h => by simp at h
  | [_], h => by simp at h
  | _ :: y :: _, _ => by
    change y ∈ _
    simp

private theorem two_le_length {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => simp at ha
  | [x], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

private noncomputable def dedupA (l acc : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun x _ ih acc => ih (Bool.rec (motive := fun _ => List ℕ) (List.cons x acc) acc (memL x acc)))
    l acc

private theorem mem_dedupA (y : ℕ) : ∀ (l acc : List ℕ), y ∈ dedupA l acc ↔ y ∈ l ∨ y ∈ acc
  | [], acc => by simp [dedupA]
  | x :: l, acc => by
    change y ∈ dedupA l (Bool.rec (motive := fun _ => List ℕ) (List.cons x acc) acc (memL x acc)) ↔ _
    rw [mem_dedupA y l]
    cases h : memL x acc
    · change y ∈ l ∨ y ∈ x :: acc ↔ _
      simp only [List.mem_cons]
      tauto
    · change y ∈ l ∨ y ∈ acc ↔ _
      have hx := (memL_iff x acc).1 h
      simp only [List.mem_cons]
      constructor
      · tauto
      · rintro ((rfl | h) | h)
        exacts [Or.inr hx, Or.inl h, Or.inr h]

private theorem mem_dedupL (y : ℕ) (l : List ℕ) : y ∈ dedupL l ↔ y ∈ l := by
  change y ∈ dedupA l [] ↔ _
  rw [mem_dedupA]
  simp

private noncomputable def cmK (n y w : ℕ) : ℕ := P.mul n (P.mul n (P.mul n y w) (P.inv n y)) (P.inv n w)

private noncomputable def commsI (n y : ℕ) (m acc : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) acc (fun w _ ih2 => List.cons (cmK n y w) ih2) m

private noncomputable def commsA (n : ℕ) (l k : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun y _ ih => commsI n y l ih) k

private theorem mem_commsI (n y c : ℕ) (acc : List ℕ) :
    ∀ m : List ℕ, c ∈ commsI n y m acc ↔ (∃ w ∈ m, c = cmK n y w) ∨ c ∈ acc
  | [] => by simp [commsI]
  | w :: m => by
    change c ∈ cmK n y w :: commsI n y m acc ↔ _
    rw [List.mem_cons, mem_commsI n y c acc m]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [or_assoc]

private theorem mem_commsA (n c : ℕ) (l : List ℕ) :
    ∀ k : List ℕ, c ∈ commsA n l k ↔ ∃ y ∈ k, ∃ w ∈ l, c = cmK n y w
  | [] => by simp [commsA]
  | y :: k => by
    change c ∈ commsI n y l (commsA n l k) ↔ _
    rw [mem_commsI, mem_commsA n c l k]
    simp

private theorem mem_commsL (n c : ℕ) (l : List ℕ) :
    c ∈ commsL n l ↔ ∃ y ∈ l, ∃ w ∈ l, c = cmK n y w := mem_commsA n c l l

private def VP (P0 : List (Perm (Fin 8))) (σ : Perm (Fin 8)) : Prop :=
  σ ∈ P0 ∧ ∀ y ∈ P0, ∀ w ∈ P0, σ * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * σ

private theorem cmK_code {y w : Perm (Fin 8)} : cmK 8 (P.code y) (P.code w) = P.code (y * w * y⁻¹ * w⁻¹) := by
  have h8 : (8 : ℕ) ≤ 32 := by norm_num
  simp only [cmK, P.code_inv h8, P.code_mul h8]

private theorem mem_V_iff (P0 : List (Perm (Fin 8))) (s : ℕ) :
    s ∈ filtL (P0.map P.code) (fun x => P.allL (dedupL (commsL 8 (P0.map P.code)))
      fun c => P.comm 8 x c) ↔ ∃ σ, VP P0 σ ∧ P.code σ = s := by
  have h8 : (8 : ℕ) ≤ 32 := by norm_num
  rw [mem_filtL, P.allL_iff]
  constructor
  · rintro ⟨hs, h⟩
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hs
    refine ⟨σ, ⟨hσ, fun y hy w hw => ?_⟩, rfl⟩
    have := h _ ((mem_dedupL _ _).2 ((mem_commsL _ _ _).2
      ⟨_, List.mem_map_of_mem hy, _, List.mem_map_of_mem hw, cmK_code.symm⟩))
    rwa [P.comm_code h8] at this
  · rintro ⟨σ, ⟨hσ, h⟩, rfl⟩
    refine ⟨List.mem_map_of_mem hσ, fun c hc => ?_⟩
    obtain ⟨y', hy', w', hw', e⟩ := (mem_commsL 8 c _).1 ((mem_dedupL c _).1 hc)
    obtain ⟨y, hy, ey⟩ := List.mem_map.1 hy'
    obtain ⟨w, hw, ew⟩ := List.mem_map.1 hw'
    rw [e, ← ey, ← ew, cmK_code, P.comm_code h8]
    exact h y hy w hw

private theorem mem_vTabs_iff (P0 : List (Perm (Fin 8))) (x : List ℕ) :
    x ∈ vTabs 8 (P0.map tbl) ↔ ∃ σ, VP P0 σ ∧ tbl σ = x := by
  unfold vTabs commTabs
  rw [List.mem_filter, List.all_eq_true]
  simp only [List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, h⟩
    refine ⟨σ, ⟨hσ, fun y hy w hw => ?_⟩, rfl⟩
    have := h _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    rwa [← tbl_comm, ← mul_comm_iff_tbl] at this
  · rintro ⟨σ, ⟨hσ, h⟩, rfl⟩
    refine ⟨⟨σ, hσ, rfl⟩, ?_⟩
    rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    rw [← tbl_comm, ← mul_comm_iff_tbl]
    exact h y hy w hw

private theorem exists_tbl {x : List ℕ} (hx : x ∈ (List.range 8).permutations) :
    ∃ σ : Perm (Fin 8), tbl σ = x := by
  rw [List.mem_permutations] at hx
  have hlen : x.length = 8 := by simpa using hx.length_eq
  have hnd : x.Nodup := hx.nodup_iff.2 (List.nodup_range)
  have hlt : ∀ i : Fin 8, x[(i : ℕ)]'(by rw [hlen]; exact i.isLt) < 8 := fun i =>
    List.mem_range.1 (hx.subset (List.getElem_mem _))
  let f : Fin 8 → Fin 8 := fun i => ⟨x[(i : ℕ)]'(by rw [hlen]; exact i.isLt), hlt i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have := (List.Nodup.getElem_inj_iff hnd).1 (congrArg Fin.val hij)
    exact Fin.ext this
  refine ⟨Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩, ?_⟩
  apply List.ext_getElem (by rw [length_tbl, hlen])
  intro i h1 h2
  have hi : i < 8 := by rwa [length_tbl] at h1
  simp [tbl, f]
  rfl

open CFSG.QuasithinUnique.Unc25G2.A8 in
theorem s4046 (P0 : List (Perm (Fin 8))) (t g : Perm (Fin 8)) {LP V : List ℕ} {T0 G0 : ℕ}
    (hp : P0.map code = LP) (ht : code t = T0) (hg : code g = G0)
    (hk : c4046 LP V T0 G0 = true) :
    (List.range 8 ∈ P0.map tbl ∧
          (∀ a ∈ P0.map tbl, ∀ b ∈ P0.map tbl, mulT a b ∈ P0.map tbl) ∧
          (∀ a ∈ P0.map tbl, invT 8 a ∈ P0.map tbl) ∧
          (∀ σ ∈ P0, Perm.sign σ = 1) ∧
          P0.toFinset.card = 64 ∧
          (∀ x ∈ allTabs, (∀ v ∈ vTabs 8 (P0.map tbl), mulT x v = mulT v x) →
            x ∈ vTabs 8 (P0.map tbl)) ∧
          (∀ x ∈ allTabs, x ≠ List.range 8 → (∀ p ∈ P0.map tbl, mulT x p = mulT p x) →
            x = tbl t) ∧
          ((∀ v ∈ vTabs 8 (P0.map tbl), mulT (mulT (tbl g) v) (invT 8 (tbl g)) ∈
              vTabs 8 (P0.map tbl)) ∧
            (∀ v ∈ vTabs 8 (P0.map tbl), mulT (mulT (invT 8 (tbl g)) v) (tbl g) ∈
              vTabs 8 (P0.map tbl)) ∧
            mulT (tbl g) (tbl t) ≠ mulT (tbl t) (tbl g)) ∧
          Perm.sign g = 1) := by
  have h8 : (8 : ℕ) ≤ 32 := by norm_num
  subst hp ht hg
  rw [code_eq_P] at hk
  unfold c4046 c4046v at hk
  rw [P.andB_iff, eqLs_iff] at hk
  obtain ⟨hV, hk⟩ := hk
  have hVm : ∀ s, s ∈ V ↔ ∃ σ, VP P0 σ ∧ P.code σ = s := fun s => by rw [hV, mem_V_iff]
  simp only [allBs_cons, allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, -, k8, -, k10, k11, k12, k13, k14⟩ := hk
  rw [P.code_one, memL_iff, P.mem_map_code h8] at k1
  simp only [P.allL_map, memL_iff, P.code_mul h8, P.code_inv h8, P.mem_map_code h8,
    P.even_code h8] at k2 k3 k4
  rw [distinctL_map h8] at k5
  rw [lenL_eq, List.length_map, P.beq_iff] at k6
  let H : Subgroup (Perm (Fin 8)) :=
    { carrier := {σ | σ ∈ P0}
      mul_mem' := fun ha hb => k2 _ ha _ hb
      one_mem' := k1
      inv_mem' := fun ha => k3 _ ha }
  have hcard : Nat.card H = 2 ^ 6 := by
    have e : Nat.card H = Nat.card P0.toFinset :=
      Nat.card_congr (Equiv.subtypeEquivRight fun σ => (by simp [H] : σ ∈ H ↔ σ ∈ P0.toFinset))
    rw [e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup k5, k6]
    norm_num
  have hpg : IsPGroup 2 H := IsPGroup.of_card hcard
  have : Nontrivial H := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have := hpg.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center H)
  have hzc := Subgroup.mem_center_iff.1 z.2
  have hz1 : ((z : H) : Perm (Fin 8)) ≠ 1 := fun e =>
    hz (Subtype.ext (Subtype.ext e))
  have hzV : VP P0 ((z : H) : Perm (Fin 8)) := by
    refine ⟨(z : H).2, fun y hy w hw => ?_⟩
    have hc : y * w * y⁻¹ * w⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hy hw) (H.inv_mem hy)) (H.inv_mem hw)
    have := congrArg Subtype.val (hzc ⟨_, hc⟩)
    exact this.symm
  have h1V : VP P0 1 := ⟨k1, fun _ _ _ _ => by rw [one_mul, mul_one]⟩
  have hlen : 2 ≤ V.length :=
    two_le_length ((hVm _).2 ⟨_, h1V, rfl⟩) ((hVm _).2 ⟨_, hzV, rfl⟩)
      (fun e => hz1 (P.code_inj h8 e).symm)
  obtain ⟨σ1, hσ1, eσ1⟩ := (hVm _).1 (getK_one_mem hlen)
  have hlenP : 2 ≤ (P0.map P.code).length := by rw [List.length_map, k6]; norm_num
  obtain ⟨p1, hp1, ep1⟩ := List.mem_map.1 (getK_one_mem hlenP)
  rw [← eσ1, P.allC_iff h8] at k8
  rw [← ep1, P.allC_iff h8] at k10
  simp only [P.allL_iff] at k11 k12
  have hVt : ∀ v ∈ vTabs 8 (P0.map tbl), ∃ σ, VP P0 σ ∧ tbl σ = v := fun v hv =>
    (mem_vTabs_iff P0 v).1 hv
  refine ⟨by rw [← tbl_one]; exact List.mem_map_of_mem k1, ?_, ?_, k4, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a' ha' b' hb'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    rw [← tbl_mul]
    exact List.mem_map_of_mem (k2 a ha b hb)
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
    rw [← tbl_inv]
    exact List.mem_map_of_mem (k3 a ha)
  · rw [List.toFinset_card_of_nodup k5, k6]
  · intro x hx hc
    obtain ⟨ξ, rfl⟩ := exists_tbl hx
    have hcv : ∀ σ, VP P0 σ → ξ * σ = σ * ξ := fun σ hσ =>
      (mul_comm_iff_tbl ξ σ).2 (hc _ ((mem_vTabs_iff P0 _).2 ⟨σ, hσ, rfl⟩))
    have := k8 ξ (hcv σ1 hσ1)
    simp only [P.impB_iff, P.allL_iff, memL_iff] at this
    obtain ⟨τ, hτ, e⟩ := (hVm _).1 (this fun v hv => by
      obtain ⟨σ, hσ, rfl⟩ := (hVm v).1 hv
      rw [P.comm_code h8]
      exact hcv σ hσ)
    rw [P.code_inj h8 e] at hτ
    exact (mem_vTabs_iff P0 _).2 ⟨ξ, hτ, rfl⟩
  · intro x hx hx1 hc
    obtain ⟨ξ, rfl⟩ := exists_tbl hx
    have hcp : ∀ p ∈ P0, ξ * p = p * ξ := fun p hp =>
      (mul_comm_iff_tbl ξ p).2 (hc _ (List.mem_map_of_mem hp))
    have := k10 ξ (hcp p1 hp1)
    simp only [P.impB_iff, P.notB_iff, P.allL_map, P.code_one, P.beq_code h8, P.comm_code h8]
      at this
    rw [this (fun e => hx1 (by rw [e, tbl_one])) fun p hp => hcp p hp]
  · intro v hv
    obtain ⟨σ, hσ, rfl⟩ := hVt v hv
    have := k11 _ ((hVm _).2 ⟨σ, hσ, rfl⟩)
    simp only [memL_iff, P.code_mul h8, P.code_inv h8] at this
    obtain ⟨τ, hτ, e⟩ := (hVm _).1 this
    rw [← tbl_inv, ← tbl_mul, ← tbl_mul, ← P.code_inj h8 e]
    exact (mem_vTabs_iff P0 _).2 ⟨τ, hτ, rfl⟩
  · intro v hv
    obtain ⟨σ, hσ, rfl⟩ := hVt v hv
    have := k12 _ ((hVm _).2 ⟨σ, hσ, rfl⟩)
    simp only [memL_iff, P.code_mul h8, P.code_inv h8] at this
    obtain ⟨τ, hτ, e⟩ := (hVm _).1 this
    rw [← tbl_inv, ← tbl_mul, ← tbl_mul, ← P.code_inj h8 e]
    exact (mem_vTabs_iff P0 _).2 ⟨τ, hτ, rfl⟩
  · rw [P.notB_iff, P.comm_code h8] at k13
    exact fun e => k13 ((mul_comm_iff_tbl g t).2 e)
  · rwa [P.even_code h8] at k14

end C4046

end CFSG.KC.LQT.S

end
