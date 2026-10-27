module

public import CFSG.Certificates.Kernel.S1277KSvSound

public section

namespace CFSG.KS.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Gm
  CFSG.KC.S1277Sv CFSG.KC.Enum CFSG.KS.S1277Lat CFSG.KS.S1277Mod CFSG.KS.S1277Sig
  CFSG.KS.S1277Gm CFSG.KS.S1277Cand CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Surv
  Certificates.Data.S1277Sig

theorem packC_colsQ {g : ℕ} (hg : g < 68719476736) : packC (colsQ g) = g := by
  simp only [packC, colsQ, List.foldr_cons, List.foldr_nil, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem sigQ_mem {L g : ℕ} (h : sigQ L [] g = true) : pkSet (Sig 6 (φL L)) g := by
  rw [sigQ, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨σ, hσ, hσt⟩ := perm_of_tChk h.2
  rw [Gk_zero] at hσ
  refine ⟨σ, hσ, ?_⟩
  have e : colsOf σ = colsQ g := by
    apply List.ext_getElem (by rw [length_colsOf]; rfl)
    intro i h1 h2
    have hi : i < 6 := by simpa [length_colsOf] using h1
    rw [getElem_colsOf σ i hi, hσt]
    exact applyCols_pow _ i h2
  rw [pk_def, e, packC_colsQ h.1]

theorem vgChk_spec {L : ℕ} {vg : List ℕ} (h : vgChk L [] vg = true) :
    vg.length = 130 ∧ ∀ g ∈ vg, pkSet (Sig 6 (φL L)) g := by
  rw [vgChk, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun g hg => sigQ_mem ((allL_iff.1 h.2) g hg)⟩

theorem hpChk_spec {vg sl : List ℕ} {sp36 hp : ℕ} (h : hpChk vg sl sp36 hp = true) :
    (∀ t < 24, rd36 sp36 t = sl.getD t 0) ∧
      ∀ k < 130, ∀ t < 24, rd36 hp (k * 24 + t) = mulQ (vg.getD k 0) (sl.getD t 0) := by
  rw [hpChk, Bool.and_eq_true] at h
  have h1 : ∀ t < 24, rd36 sp36 t = sl.getD t 0 := fun t ht =>
    Nat.eq_of_beq_eq_true ((allLt_iff.1 h.1) t ht)
  refine ⟨h1, fun k hk t ht => ?_⟩
  have h2 := (allLt_iff.1 h.2) k hk
  rw [strictB_eq] at h2
  rw [← h1 t ht]
  exact Nat.eq_of_beq_eq_true ((allLt_iff.1 h2) t ht)

noncomputable def cvQ (sp36 hp r : ℕ) : ℕ := mulQ (rd36 sp36 (r % 24)) (rd36 hp (r / 24))

def cokQ (vt : ℕ) (sl a1 a2 : List ℕ) (r y : ℕ) : Prop :=
  r < 74880 ∧ (rd2 vt (r / 576) = 1 ∨ y ∈ tyL (rd2 vt (r / 576)) sl a1 a2)

section Chunk

variable (sp36 hp vt : ℕ) (sl a1 a2 : List ℕ)

theorem covR_eq (r p : ℕ) :
    covR sp36 hp vt sl a1 a2 r p =
      bif Nat.blt r 74880 && Nat.blt p (cvQ sp36 hp r) &&
          (Nat.beq (rd2 vt (r / 576)) 1 || memL (cvQ sp36 hp r) (tyL (rd2 vt (r / 576)) sl a1 a2))
        then cvQ sp36 hp r else 68719476736 := by
  rw [covR, strictN_eq]
  rfl

theorem covL_cons (r : ℕ) (rs : List ℕ) (p : ℕ) :
    covL sp36 hp vt sl a1 a2 (r :: rs) p =
      covL sp36 hp vt sl a1 a2 rs (covR sp36 hp vt sl a1 a2 r p) := by
  have e : covL sp36 hp vt sl a1 a2 (r :: rs) p =
      strictN (covR sp36 hp vt sl a1 a2 r p) (covL sp36 hp vt sl a1 a2 rs) := rfl
  rw [e, strictN_eq]

theorem covL_big : ∀ (rs : List ℕ) (p : ℕ), 68719476736 ≤ p →
    68719476736 ≤ covL sp36 hp vt sl a1 a2 rs p
  | [], _, h => h
  | r :: rs, p, h => by
    rw [covL_cons]
    apply covL_big rs
    rw [covR_eq, cond_eq_if]
    split_ifs with hc
    · simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      omega
    · exact le_rfl

theorem covL_spec : ∀ (rs : List ℕ) (p : ℕ), covL sp36 hp vt sl a1 a2 rs p < 68719476736 →
    p ≤ covL sp36 hp vt sl a1 a2 rs p ∧
      (∀ r ∈ rs, p < cvQ sp36 hp r ∧ cvQ sp36 hp r ≤ covL sp36 hp vt sl a1 a2 rs p ∧
        cokQ vt sl a1 a2 r (cvQ sp36 hp r)) ∧
      (rs.map (cvQ sp36 hp)).Nodup
  | [], p, _ => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | r :: rs, p, h => by
    rw [covL_cons] at h ⊢
    have hlt : covR sp36 hp vt sl a1 a2 r p < 68719476736 := by
      by_contra hc
      exact absurd h (not_lt.2 (covL_big sp36 hp vt sl a1 a2 rs _ (not_lt.1 hc)))
    have hc : (Nat.blt r 74880 && Nat.blt p (cvQ sp36 hp r) &&
        (Nat.beq (rd2 vt (r / 576)) 1 ||
          memL (cvQ sp36 hp r) (tyL (rd2 vt (r / 576)) sl a1 a2))) = true := by
      by_contra hc
      rw [covR_eq, cond_eq_if, if_neg hc] at hlt
      exact lt_irrefl _ hlt
    have hv : covR sp36 hp vt sl a1 a2 r p = cvQ sp36 hp r := by
      rw [covR_eq, cond_eq_if, if_pos hc]
    rw [hv] at h ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, memL_iff] at hc
    obtain ⟨⟨hr, hpv⟩, hty⟩ := hc
    obtain ⟨h1, h2, h3⟩ := covL_spec rs _ h
    refine ⟨hpv.le.trans h1, fun r' hr' => ?_, ?_⟩
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨hpv, h1, hr, hty⟩
      · obtain ⟨a, b, c⟩ := h2 r' hr'
        exact ⟨hpv.trans a, b, c⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, h3⟩
      obtain ⟨r', hr', he⟩ := List.mem_map.1 hm
      have := (h2 r' hr').1
      omega

end Chunk

theorem cover_sound {L : ℕ} {sl vg : List ℕ} {sp36 hp vt : ℕ} {a1 a2 : List ℕ}
    {vr : List (List ℕ)} {vb : List ℕ}
    (hsl : ∀ y ∈ sl, pkSet (Sig 6 (φL L)) y) (hsll : sl.length = 24)
    (hvg : vgChk L [] vg = true) (hhp : hpChk vg sl sp36 hp = true)
    (hcnt : cntChk vr vb = true) (hvr : vr.length = 40)
    (hcov : ∀ c < 40, covChk sp36 hp vt sl a1 a2 vr vb c = true)
    (hsig : Nat.card (Sig 6 (φL L)) = 40320) :
    ∀ σ ∈ Sig 6 (φL L), ∃ r < 74880,
      pk σ = mulQ (sl.getD (r % 24) 0) (mulQ (vg.getD (r / 576) 0) (sl.getD (r / 24 % 24) 0)) ∧
      (rd2 vt (r / 576) = 1 ∨ pk σ ∈ tyL (rd2 vt (r / 576)) sl a1 a2) := by
  classical
  obtain ⟨hvgl, hvgS⟩ := vgChk_spec hvg
  obtain ⟨hp1, hp2⟩ := hpChk_spec hhp
  have hle : Sig 6 (φL L) ≤ Sig 6 (φL L) := le_rfl
  have cv_eq : ∀ r < 74880, cvQ sp36 hp r =
      mulQ (sl.getD (r % 24) 0) (mulQ (vg.getD (r / 576) 0) (sl.getD (r / 24 % 24) 0)) := by
    intro r hr
    have e : r / 576 * 24 + r / 24 % 24 = r / 24 := by omega
    have h2 := hp2 (r / 576) (by omega) (r / 24 % 24) (by omega)
    rw [e] at h2
    rw [cvQ, hp1 _ (by omega), h2]
  have hslS : ∀ i < 24, pkSet (Sig 6 (φL L)) (sl.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hsl _ (List.getElem_mem _)
  have hvgS' : ∀ k < 130, pkSet (Sig 6 (φL L)) (vg.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hvgS _ (List.getElem_mem _)
  have cv_mem : ∀ r < 74880, pkSet (Sig 6 (φL L)) (cvQ sp36 hp r) := fun r hr => by
    rw [cv_eq r hr]
    exact pkSet_mulQ hle (hslS _ (by omega))
      (pkSet_mulQ hle (hvgS' _ (by omega)) (hslS _ (by omega)))
  have hch : ∀ c < 40, vb.getD c 0 ≤ vb.getD (c + 1) 0 ∧
      (∀ r ∈ vr.getD c [], vb.getD c 0 < cvQ sp36 hp r ∧ cvQ sp36 hp r ≤ vb.getD (c + 1) 0 ∧
        cokQ vt sl a1 a2 r (cvQ sp36 hp r)) ∧
      ((vr.getD c []).map (cvQ sp36 hp)).Nodup := by
    intro c hc
    have h := hcov c hc
    rw [covChk, Bool.and_eq_true, Nat.blt_eq] at h
    have he := Nat.eq_of_beq_eq_true h.2
    have := covL_spec sp36 hp vt sl a1 a2 (vr.getD c []) (vb.getD c 0) (by rw [he]; exact h.1)
    rw [he] at this
    exact this
  have hmono : ∀ a b, a ≤ b → b ≤ 40 → vb.getD a 0 ≤ vb.getD b 0 := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact (ih (by omega)).trans (hch b (by omega)).1
  let vals := (List.range 40).flatMap fun c => (vr.getD c []).map (cvQ sp36 hp)
  have hnd : vals.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun c hc => (hch c (List.mem_range.1 hc)).2.2, ?_⟩
    refine (List.pairwise_lt_range (n := 40)).imp_of_mem fun {c c'} hc hc' hlt => ?_
    have hc1 := List.mem_range.1 hc
    have hc2 := List.mem_range.1 hc'
    intro x hx hx'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hx'
    have a := ((hch c hc1).2.1 r hr).2.1
    have b := ((hch c' hc2).2.1 r' hr').1
    have m := hmono (c + 1) c' (by omega) (by omega)
    omega
  have hlen : vals.length = 40320 := by
    rw [cntChk, Bool.and_eq_true] at hcnt
    have h := Nat.eq_of_beq_eq_true hcnt.1
    rw [hvr] at h
    simp only [vals, List.length_flatMap, List.length_map]
    exact h
  have hvalS : ∀ y ∈ vals, pkSet (Sig 6 (φL L)) y := by
    intro y hy
    obtain ⟨c, hc, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
    exact cv_mem r ((hch c (List.mem_range.1 hc)).2.1 r hr).2.2.1
  intro σ hσ
  have hin : pk σ ∈ vals := by
    by_contra hn
    have := card_le_of_pkSet hle (pk σ :: vals) (List.nodup_cons.2 ⟨hn, hnd⟩)
      (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨σ, hσ, rfl⟩
        · exact hvalS y hy)
    rw [List.length_cons, hlen, hsig] at this
    omega
  obtain ⟨c, hc, hy⟩ := List.mem_flatMap.1 hin
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hy
  obtain ⟨-, -, hr1, hty⟩ := (hch c (List.mem_range.1 hc)).2.1 r hr
  refine ⟨r, hr1, ?_, ?_⟩
  · rw [← he, cv_eq r hr1]
  · rw [← he]
    exact hty

end CFSG.KS.S1277Sv

end
