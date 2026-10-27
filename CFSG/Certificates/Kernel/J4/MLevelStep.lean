module

public import CFSG.Certificates.Kernel.J4.MLevelSound
import Mathlib.Tactic.Group

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models
open CFSG.Certificates.DceWord (lvE wv)

@[expose] def Pres (d0 n0 : ℕ) (s' : St4) : Prop :=
  (n0 = 0 → s'.2.2.1 = 0) ∧ (s'.2.2.1 = 0 ∨ s'.1 / 65536 = d0 / 65536)

theorem pres_bad (d0 n0 : ℕ) : Pres d0 n0 bad4 := ⟨fun _ => rfl, Or.inl rfl⟩

theorem pres_Ns (SG : ℕ → ℕ) (e d0 p0 n0 c0 : ℕ) : Pres d0 n0 (mNs SG e (d0, p0, n0, c0)) := by
  rcases brec4 (Y := mNs SG e (d0, p0, n0, c0)) rfl with h | ⟨-, h⟩ <;> rw [h]
  · exact pres_bad d0 n0
  · exact ⟨id, Or.inr rfl⟩

theorem pres_Ef (FT : ℕ → ℕ) (S g d0 p0 n0 c0 : ℕ) : Pres d0 n0 (mEfs FT S g (d0, p0, n0, c0)) := by
  rcases brec4 (Y := mEfs FT S g (d0, p0, n0, c0)) rfl with h | ⟨-, h⟩ <;> rw [h]
  · exact pres_bad d0 n0
  · refine ⟨fun h0 => ?_, Or.inr (setD_gen d0 (fDp_lt _))⟩
    subst h0
    change mulF 0 _ = 0
    rw [mulF_eq, mul12_zero]

theorem pres_Eb (FT : ℕ → ℕ) (S g d0 p0 n0 c0 : ℕ) : Pres d0 n0 (mEbs FT S g (d0, p0, n0, c0)) := by
  rcases brec4 (Y := mEbs FT S g (d0, p0, n0, c0)) rfl with h | ⟨-, h⟩ <;> rw [h]
  · exact pres_bad d0 n0
  · refine ⟨fun h0 => ?_, Or.inr (setD_gen d0 (fD_lt _))⟩
    subst h0
    change mulF 0 _ = 0
    rw [mulF_eq, mul12_zero]

theorem pres_Tf (FT OT : ℕ → ℕ) (TH S g h PP d0 p0 n0 c0 : ℕ) :
    Pres d0 n0 (mTfs FT OT TH S g h PP (d0, p0, n0, c0)) := by
  rcases brec4 (Y := mTfs FT OT TH S g h PP (d0, p0, n0, c0)) rfl with h | ⟨-, h⟩ <;> rw [h]
  · exact pres_bad d0 n0
  · refine ⟨fun h0 => ?_, Or.inr (setD_gen d0 (fDp_lt _))⟩
    subst h0
    change mulF 0 _ = 0
    rw [mulF_eq, mul12_zero]

theorem pres_Tb (FT OT : ℕ → ℕ) (TH S g h PP RR d0 p0 n0 c0 : ℕ) :
    Pres d0 n0 (mTbs FT OT TH S g h PP RR (d0, p0, n0, c0)) := by
  rcases brec4 (Y := mTbs FT OT TH S g h PP RR (d0, p0, n0, c0)) rfl with h | ⟨-, h⟩ <;> rw [h]
  · exact pres_bad d0 n0
  · refine ⟨fun h0 => ?_, Or.inr (setD_gen d0 (fD_lt _))⟩
    subst h0
    change mulF 0 _ = 0
    rw [mulF_eq, mul12_zero]

section Next

variable {d : MD} {LET TH : ℕ} {G : Type} [Group G] {φ : Nhat LET →* G} {x y t : G}
  {w : ℕ → G} {R W n K D p nn i f : ℕ}

theorem next_Ef (hRK : R / 65536 % 4294967296 = K)
    (hFB : ∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hK : f = 0 → RecV d (d.FT K))
    (hW : W < 256 ^ n) (hD : D < 65536) (hi : i ≤ n) (hf : f ≤ 1) {S g : ℕ} (hS : S ≤ 1) :
    Next d φ x y t w R W n K D p nn i f (mEfs d.FT S g (D + 65536 * R, p, nn, cur W n i f)) := by
  rcases brec4 (Y := mEfs d.FT S g (D + 65536 * R, p, nn, cur W n i f)) rfl with h | ⟨hc, h⟩
  · exact Or.inl (by rw [h]; rfl)
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, h4⟩ := andB_eq_true.1 hc
  obtain ⟨hin, hl⟩ := letAt_lt hW hf hi (beq_eq_true.1 h1) (by decide)
  rw [dK_eq R hD, hRK] at h2
  rw [dD_eq R hD] at h3
  have e3 := beq_eq_true.1 h3
  have e4 := beq_eq_true.1 h4
  have hl' : fv x y t (wLet W i) = 1 := by rw [hl]; exact fv_eps x y t
  rw [mulF_eq, mulF_eq, setD_eq R hD (fDp_lt _), adv_cur hf hS hin] at h
  subst e3
  rcases refS_spec h2 with ⟨hS0, hg⟩ | ⟨hS1, rfl, hc0⟩
  · have hS0' : S = 0 := by omega
    subst hS0'
    obtain ⟨hrec, hπ, hnF, hM⟩ := hFB g hg
    rw [lor_zero'] at h
    exact Or.inr (Or.inl ⟨_, _, _, _, h, hrec.2.1, hin, InN_mul_left hπ, InN_mul_right hnF,
      fun hp hn => (core_Ef hp hn hπ hnF e4 hl').2 hM⟩)
  · subst hS1
    rw [cur_bit hf] at hc0
    subst hc0
    have hrec := hK rfl
    exact Or.inr (Or.inr ⟨rfl, _, _, _, _, h, hrec.2.1, hin, fun hp hn =>
      ⟨InN_mul_right hp, InN_mul_left hn, fun hπ hnF => core_Ef hp hn hπ hnF e4 hl'⟩⟩)

theorem next_Eb (hRK : R / 65536 % 4294967296 = K)
    (hFB : ∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hK : f = 0 → RecV d (d.FT K))
    (hW : W < 256 ^ n) (hD : D < 65536) (hi : i ≤ n) (hf : f ≤ 1) {S g : ℕ} (hS : S ≤ 1) :
    Next d φ x y t w R W n K D p nn i f (mEbs d.FT S g (D + 65536 * R, p, nn, cur W n i f)) := by
  rcases brec4 (Y := mEbs d.FT S g (D + 65536 * R, p, nn, cur W n i f)) rfl with h | ⟨hc, h⟩
  · exact Or.inl (by rw [h]; rfl)
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, h4⟩ := andB_eq_true.1 hc
  obtain ⟨hin, hl⟩ := letAt_lt hW hf hi (beq_eq_true.1 h1) (by decide)
  rw [dK_eq R hD, hRK] at h2
  rw [dD_eq R hD] at h3
  have e3 := beq_eq_true.1 h3
  have e4 := beq_eq_true.1 h4
  have hl' : fv x y t (wLet W i) = 1 := by rw [hl]; exact fv_eps x y t
  rw [mulF_eq, mulF_eq, setD_eq R hD (fD_lt _), adv_cur hf hS hin] at h
  subst e3
  rcases refS_spec h2 with ⟨hS0, hg⟩ | ⟨hS1, rfl, hc0⟩
  · have hS0' : S = 0 := by omega
    subst hS0'
    obtain ⟨hrec, hπ, hnF, hM⟩ := hFB g hg
    rw [lor_zero'] at h
    exact Or.inr (Or.inl ⟨_, _, _, _, h, hrec.1, hin, InN_mul_left (InN_inv hπ hrec.2.2.2.1),
      InN_mul_right (InN_inv hnF hrec.2.2.2.2),
      fun hp hn => (core_Eb hp hn hrec hπ hnF e4 hl').2 hM⟩)
  · subst hS1
    rw [cur_bit hf] at hc0
    subst hc0
    have hrec := hK rfl
    exact Or.inr (Or.inr ⟨rfl, _, _, _, _, h, hrec.1, hin, fun hp hn =>
      ⟨(InN_mul_right hp).trans (InN_inv_iff hrec.2.2.2.1).symm,
        (InN_mul_left hn).trans (InN_inv_iff hrec.2.2.2.2).symm,
        fun hπ hnF => core_Eb hp hn hrec hπ hnF e4 hl'⟩⟩)

theorem next_Tf (E : Env d φ x y t TH) (hRK : R / 65536 % 4294967296 = K)
    (hFB : ∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hK : f = 0 → RecV d (d.FT K))
    (hW : W < 256 ^ n) (hD : D < 65536) (hi : i ≤ n) (hf : f ≤ 1) {S g h PP : ℕ} (hS : S ≤ 1) :
    Next d φ x y t w R W n K D p nn i f
      (mTfs d.FT d.OT TH S g h PP (D + 65536 * R, p, nn, cur W n i f)) := by
  rcases brec4 (Y := mTfs d.FT d.OT TH S g h PP (D + 65536 * R, p, nn, cur W n i f)) rfl with
    h | ⟨hc, h⟩
  · exact Or.inl (by rw [h]; rfl)
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h4, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h5, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h6, hpt⟩ := andB_eq_true.1 hc
  obtain ⟨hin, hl⟩ := letAt_lt hW hf hi (beq_eq_true.1 h1) (by decide)
  rw [dK_eq R hD, hRK] at h2
  rw [dD_eq R hD] at h3
  have e3 := beq_eq_true.1 h3
  have hJ0 := blt_eq_true.1 h4
  have hO := beq_eq_true.1 h5
  have e6 := beq_eq_true.1 h6
  have hl' : fv x y t (wLet W i) = t := by rw [hl]; exact fv_t x y t
  rw [mulF_eq, mulF_eq, setD_eq R hD (fDp_lt _), adv_cur hf hS hin] at h
  subst e3 e6
  rcases refS_spec h2 with ⟨hS0, hg⟩ | ⟨hS1, rfl, hc0⟩
  · have hS0' : S = 0 := by omega
    subst hS0'
    obtain ⟨hrec, hπ, hnF, hM⟩ := hFB g hg
    rw [lor_zero'] at h
    exact Or.inr (Or.inl ⟨_, _, _, _, h, hrec.2.1, hin, InN_mul_left hπ, InN_mul_right hnF,
      fun hp hn => (core_Tf hp hn hπ hnF hl' (tconj E hJ0 hrec.2.2.1 hO hp hpt)).2 hM⟩)
  · subst hS1
    rw [cur_bit hf] at hc0
    subst hc0
    have hrec := hK rfl
    exact Or.inr (Or.inr ⟨rfl, _, _, _, _, h, hrec.2.1, hin, fun hp hn =>
      ⟨InN_mul_right hp, InN_mul_left hn,
        fun hπ hnF => core_Tf hp hn hπ hnF hl' (tconj E hJ0 hrec.2.2.1 hO hp hpt)⟩⟩)

theorem next_Tb (E : Env d φ x y t TH) (hRK : R / 65536 % 4294967296 = K)
    (hFB : ∀ g < K, RecV d (d.FT g) ∧ MF d φ t w (d.FT g)) (hK : f = 0 → RecV d (d.FT K))
    (hW : W < 256 ^ n) (hD : D < 65536) (hi : i ≤ n) (hf : f ≤ 1) {S g h PP RR : ℕ}
    (hS : S ≤ 1) :
    Next d φ x y t w R W n K D p nn i f
      (mTbs d.FT d.OT TH S g h PP RR (D + 65536 * R, p, nn, cur W n i f)) := by
  rcases brec4 (Y := mTbs d.FT d.OT TH S g h PP RR (D + 65536 * R, p, nn, cur W n i f)) rfl with
    h | ⟨hc, h⟩
  · exact Or.inl (by rw [h]; rfl)
  obtain ⟨h1, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h3, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h4, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h5, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h6, hc⟩ := andB_eq_true.1 hc
  obtain ⟨h7, hpt⟩ := andB_eq_true.1 hc
  obtain ⟨hin, hl⟩ := letAt_lt hW hf hi (beq_eq_true.1 h1) (by decide)
  rw [dK_eq R hD, hRK] at h2
  rw [dD_eq R hD] at h3
  have e3 := beq_eq_true.1 h3
  have hJ0 := blt_eq_true.1 h4
  have hO := beq_eq_true.1 h5
  have e6 := beq_eq_true.1 h6
  have e7 := beq_eq_true.1 h7
  rw [mulF_eq] at e7
  have hl' : fv x y t (wLet W i) = t := by rw [hl]; exact fv_t x y t
  rw [mulF_eq, setD_eq R hD (fD_lt _), adv_cur hf hS hin] at h
  subst e3 e6 e7
  rcases refS_spec h2 with ⟨hS0, hg⟩ | ⟨hS1, rfl, hc0⟩
  · have hS0' : S = 0 := by omega
    subst hS0'
    obtain ⟨hrec, hπ, hnF, hM⟩ := hFB g hg
    rw [lor_zero'] at h
    have hπi := InN_inv hπ hrec.2.2.2.1
    exact Or.inr (Or.inl ⟨_, _, _, _, h, hrec.1, hin, InN_mul_left hπi,
      InN_mul_right (InN_inv hnF hrec.2.2.2.2), fun hp hn =>
        (core_Tb E.ht hp hn hrec hπ hnF hl'
          (tconj E hJ0 hrec.2.2.1 hO ((InN_mul_left hπi).2 hp) hpt)).2 hM⟩)
  · subst hS1
    rw [cur_bit hf] at hc0
    subst hc0
    have hrec := hK rfl
    exact Or.inr (Or.inr ⟨rfl, _, _, _, _, h, hrec.1, hin, fun hp hn =>
      ⟨(InN_mul_right hp).trans (InN_inv_iff hrec.2.2.2.1).symm,
        (InN_mul_left hn).trans (InN_inv_iff hrec.2.2.2.2).symm,
        fun hπ hnF => core_Tb E.ht hp hn hrec hπ hnF hl'
          (tconj E hJ0 hrec.2.2.1 hO ((InN_mul_left (InN_inv hπ hrec.2.2.2.1)).2 hp) hpt)⟩⟩)

theorem next_Ns (E : Env d φ x y t TH) (hW : W < 256 ^ n) (hD : D < d.ND) (hi : i ≤ n)
    (hf : f ≤ 1) {e : ℕ} :
    Next d φ x y t w R W n K D p nn i f (mNs d.SG e (D + 65536 * R, p, nn, cur W n i f)) := by
  rcases brec4 (Y := mNs d.SG e (D + 65536 * R, p, nn, cur W n i f)) rfl with h | ⟨hc, h⟩
  · exact Or.inl (by rw [h]; rfl)
  obtain ⟨h1, h2⟩ := andB_eq_true.1 hc
  have hm := blt_eq_true.1 h1
  rcases E.seg e with h0 | ⟨hu, hM, hev⟩
  · omega
  obtain ⟨him, hmatch⟩ := seg_match hW hf hi hu (beq_eq_true.1 h2)
  rw [adv_cur hf (Nat.zero_le 1) him, lor_zero'] at h
  refine Or.inr (Or.inl ⟨_, _, _, _, h, hD, him, InN_mul_right hM, Iff.rfl, fun hp _ => ?_⟩)
  unfold Q
  rw [ev_mul φ hp hM, hev, wv_seg _ hmatch]
  group

end Next

end CFSG.KJ4.MLevel

end
