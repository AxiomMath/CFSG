module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Fast

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def eqPF (x y : FW) : Prop := x = y ∨ x = mulF y piF

instance (x y : FW) : Decidable (eqPF x y) := by unfold eqPF; infer_instance

theorem eqP_iff {x y : Wr 8} : eqP x y ↔ eqPF (ofWr x) (ofWr y) := by
  unfold eqP eqPF
  constructor
  · rintro (h | h)
    · left; rw [h]
    · right; rw [h, ofWr_mul, ofWr_allOnes]
  · rintro (h | h)
    · left; exact ofWr_inj h
    · right
      rw [← ofWr_allOnes, ← ofWr_mul] at h
      exact ofWr_inj h

namespace PairData

variable (D : PairData)

@[expose] def gensF (x : FW) : List FW :=
  [ofWr D.a, ofWr D.b, ofWr D.c, ofWr D.d, x]

@[expose] def candsF : List (FW × List ℕ) := D.cands.map fun e => (ofWr e.1, e.2)

@[expose] def lookF (t : FW) : List ℕ :=
  match D.candsF.find? (fun e => decide (eqPF e.1 t)) with
  | some e => e.2
  | none => []

@[expose] def stepF (c1 t : FW) : FW := evalF (D.gensF c1) (D.lookF t)

@[expose] def inSF (t : FW) : Prop := ∃ e ∈ D.candsF, eqPF e.1 t

instance (t : FW) : Decidable (D.inSF t) := by unfold PairData.inSF; infer_instance

theorem gensF_map (x : Wr 8) : (D.gens x).map ofWr = D.gensF (ofWr x) := rfl

theorem ofWr_evalW_gens (x : Wr 8) (w : List ℕ) :
    ofWr (evalW (D.gens x) w) = evalF (D.gensF (ofWr x)) w := by
  rw [ofWr_evalW, gensF_map]

theorem look_eq (t : Wr 8) : D.look t = D.lookF (ofWr t) := by
  unfold PairData.look PairData.lookF PairData.candsF
  rw [List.find?_map]
  have : ((fun e : FW × List ℕ => decide (eqPF e.1 (ofWr t))) ∘
      fun e : Wr 8 × List ℕ => (ofWr e.1, e.2)) =
      fun e : Wr 8 × List ℕ => decide (eqP e.1 t) := by
    funext e
    simp only [Function.comp, decide_eq_decide]
    exact eqP_iff.symm
  rw [this]
  cases D.cands.find? (fun e : Wr 8 × List ℕ => decide (eqP e.1 t)) <;> rfl

theorem ofWr_step (c1 t : Wr 8) : ofWr (D.step c1 t) = D.stepF (ofWr c1) (ofWr t) := by
  unfold PairData.step PairData.stepF
  rw [ofWr_evalW_gens, look_eq]

theorem inS_of_inSF {t : Wr 8} (h : D.inSF (ofWr t)) : D.inS t := by
  obtain ⟨e, he, hee⟩ := h
  unfold PairData.candsF at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  exact ⟨e0, he0, eqP_iff.mpr hee⟩

end PairData

structure PairData.FastOk (D : PairData) : Prop where
  ha : D.a ∈ aeSubOver agl32
  hb : D.b ∈ aeSubOver agl32
  hc : D.c ∈ aeSubOver agl32
  hd : D.d ∈ aeSubOver agl32
  hh : D.h ∈ aeSubOver agl32
  rels_h : ∀ r ∈ D.rels, eqPF (evalF (D.gensF (ofWr D.h)) r) oneF
  rels_cands : ∀ e ∈ D.cands, ∀ r ∈ D.rels, eqPF (evalF (D.gensF (ofWr e.1)) r) oneF
  cand_words : ∀ e ∈ D.cands, eqPF (evalF (D.gensF (ofWr D.h)) e.2) (ofWr e.1)
  dyn : ∀ e ∈ D.cands, D.inSF (ofWr e.1) ∧ D.inSF (D.stepF (ofWr e.1) (ofWr e.1)) ∧
    D.inSF (D.stepF (ofWr e.1) (D.stepF (ofWr e.1) (ofWr e.1))) ∧
    eqPF (D.stepF (ofWr e.1) (D.stepF (ofWr e.1) (D.stepF (ofWr e.1) (ofWr e.1)))) (ofWr D.h)
  perm_filter : ∀ t ∈ D.permWords,
    (∀ r ∈ D.rels, (evalF (D.gensF (ofWr (⟨0, pc t.1⟩ : Wr 8))) r).p = oneF.p) →
      ∃ g ∈ D.goodPerms, gp g = pc t.1
  filter_ok : ∀ g ∈ D.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ D.rels, eqPF (evalF (D.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r)
      oneF) →
      ∃ e ∈ D.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩
  perm_chk : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList D.permWords = true
  permWords_ok : ∀ t ∈ D.permWords,
    eqPF (evalF (D.gensF (ofWr D.h)) t.2) (ofWr (⟨0, pc t.1⟩ : Wr 8))
  pairWords_ok : ∀ t ∈ D.pairWords,
    eqPF (evalF (D.gensF (ofWr D.h)) t.2.2) (ofWr (ofVec (vecOf [t.1, t.2.1])))
  pairs_cov : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∀ q ∈ pairUp8 (supp8 v),
    ∃ t ∈ D.pairWords, t.1 = q.1 ∧ t.2.1 = q.2

theorem masksN_ok : ∀ l ∈ masksN, tab (fun i => (vecOfN l i).val) = l := by decide +kernel

theorem tab_val : tab (fun i : Fin 8 => i.val) = List.range 8 := by
  unfold tab
  rw [← List.map_id (List.range 8)]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < 8 := List.mem_range.mp hk
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt hk']

theorem PairData.Ok_of_fast {D : PairData} (h : D.FastOk) : D.Ok where
  ha := h.ha
  hb := h.hb
  hc := h.hc
  hd := h.hd
  hh := h.hh
  rels_h r hr := by
    apply eqP_iff.mpr
    rw [PairData.ofWr_evalW_gens, ofWr_one]
    exact h.rels_h r hr
  rels_cands e he r hr := by
    apply eqP_iff.mpr
    rw [PairData.ofWr_evalW_gens, ofWr_one]
    exact h.rels_cands e he r hr
  cand_words e he := by
    apply eqP_iff.mpr
    rw [PairData.ofWr_evalW_gens]
    exact h.cand_words e he
  dyn e he := by
    obtain ⟨d1, d2, d3, d4⟩ := h.dyn e he
    refine ⟨D.inS_of_inSF d1, D.inS_of_inSF ?_, D.inS_of_inSF ?_, eqP_iff.mpr ?_⟩
    · rw [PairData.ofWr_step]; exact d2
    · rw [PairData.ofWr_step, PairData.ofWr_step]; exact d3
    · rw [PairData.ofWr_step, PairData.ofWr_step, PairData.ofWr_step]; exact d4
  perm_filter t ht hperm := by
    refine h.perm_filter t ht fun r hr => ?_
    have hmap := map_evalW (permHom 8) (D.gens (⟨0, pc t.1⟩ : Wr 8)) r
    have h1 : (evalW (D.gens (⟨0, pc t.1⟩ : Wr 8)) r).perm = 1 := by
      have := hmap.trans (by simpa [PairData.gens, PairData.pgens, permHom] using hperm r hr)
      simpa [permHom] using this
    rw [← PairData.ofWr_evalW_gens]
    show tab (fun i => ((evalW (D.gens (⟨0, pc t.1⟩ : Wr 8)) r).perm i).val) = List.range 8
    rw [h1]
    exact tab_val
  filter_ok g hg l hl hrels := by
    have hof : ofWr (⟨vecOfN l, gp g⟩ : Wr 8) =
        ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ := by
      simp only [ofWr]
      rw [masksN_ok l hl]
    obtain ⟨e, he, hee⟩ := h.filter_ok g hg l hl fun r hr => by
      have := eqP_iff.mp (hrels r hr)
      rwa [PairData.ofWr_evalW_gens, ofWr_one, hof] at this
    unfold PairData.candsF at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact ⟨e0, he0, eqP_iff.mpr (by rw [hof]; exact hee)⟩
  perm_chk := h.perm_chk
  permWords_ok t ht := by
    apply eqP_iff.mpr
    rw [PairData.ofWr_evalW_gens]
    exact h.permWords_ok t ht
  pairWords_ok t ht := by
    apply eqP_iff.mpr
    rw [PairData.ofWr_evalW_gens]
    exact h.pairWords_ok t ht
  pairs_cov := h.pairs_cov

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
