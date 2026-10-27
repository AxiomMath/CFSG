module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2FilterE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2PermE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DecompE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_S_of {w : Wr 7} (h : wsum w = 0 ∧ Equiv.Perm.sign w.perm = 1 ∧
    ∀ s ∈ fanoLines, s.map w.perm.toEmbedding ∈ fanoLines ∧ s.map w.perm⁻¹.toEmbedding ∈ fanoLines) :
    w ∈ aeSubOver l32 := ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem mem_dec_a : wsum aW = 0 ∧ Equiv.Perm.sign aW.perm = 1 ∧
    ∀ s ∈ fanoLines, s.map aW.perm.toEmbedding ∈ fanoLines ∧ s.map aW.perm⁻¹.toEmbedding ∈ fanoLines := by
  decide +kernel

theorem mem_dec_b : wsum bW = 0 ∧ Equiv.Perm.sign bW.perm = 1 ∧
    ∀ s ∈ fanoLines, s.map bW.perm.toEmbedding ∈ fanoLines ∧ s.map bW.perm⁻¹.toEmbedding ∈ fanoLines := by
  decide +kernel

theorem mem_dec_h : wsum hW = 0 ∧ Equiv.Perm.sign hW.perm = 1 ∧
    ∀ s ∈ fanoLines, s.map hW.perm.toEmbedding ∈ fanoLines ∧ s.map hW.perm⁻¹.toEmbedding ∈ fanoLines := by
  decide +kernel

@[expose] def eH (w : Wr 7) (hw : w ∈ aeSubOver l32) : ↥e64Sub := ⟨mkQ 7 w, ⟨w, hw, rfl⟩⟩

@[expose] def aH : ↥e64Sub := eH aW (mem_S_of mem_dec_a)
@[expose] def bH : ↥e64Sub := eH bW (mem_S_of mem_dec_b)
@[expose] def hH : ↥e64Sub := eH hW (mem_S_of mem_dec_h)

@[expose] def Rep (x : ↥e64Sub) (t : Wr 7) : Prop := (x : AEQ 7) = mkQ 7 t

theorem val_evalW (a b x : ↥e64Sub) (aw bw xw : Wr 7) (ha : Rep a aw) (hb : Rep b bw)
    (hx : Rep x xw) (w : List ℕ) :
    ((evalW [a, b, x] w : ↥e64Sub) : AEQ 7) = mkQ 7 (evalW [aw, bw, xw] w) := by
  have h1 : ((evalW [a, b, x] w : ↥e64Sub) : AEQ 7) = evalW [(a : AEQ 7), (b : AEQ 7), (x : AEQ 7)] w := by
    have := map_evalW e64Sub.subtype [a, b, x] w
    simpa using this
  have h2 : mkQ 7 (evalW [aw, bw, xw] w) = evalW [mkQ 7 aw, mkQ 7 bw, mkQ 7 xw] w := by
    have := map_evalW (mkQ 7) [aw, bw, xw] w
    simpa using this
  rw [h1, h2, ha, hb, hx]

theorem rep_aH : Rep aH aW := rfl
theorem rep_bH : Rep bH bW := rfl
theorem rep_hH : Rep hH hW := rfl

theorem rep_eq {x y : ↥e64Sub} {t : Wr 7} (hx : Rep x t) (hy : Rep y t) : x = y :=
  Subtype.ext (hx.trans hy.symm)

theorem rep_of_eqπ {x : ↥e64Sub} {t t' : Wr 7} (hx : Rep x t) (h : eqπ t t') : Rep x t' := by
  unfold Rep at *
  rw [hx]
  rcases h with h | h
  · rw [h]
  · rw [h]
    have : mkQ 7 (allOnes 7) = 1 := (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
    rw [map_mul, this, mul_one]

theorem relOK_h : ∀ r ∈ relsW, evalW [aH, bH, hH] r = 1 := by
  intro r hr
  apply Subtype.ext
  rw [val_evalW aH bH hH aW bW hW rep_aH rep_bH rep_hH, rels_ok r hr]
  simp

theorem rep_mul {x y : ↥e64Sub} {s t : Wr 7} (hx : Rep x s) (hy : Rep y t) : Rep (x * y) (s * t) := by
  unfold Rep at *
  show (x : AEQ 7) * (y : AEQ 7) = mkQ 7 (s * t)
  rw [hx, hy, map_mul]

theorem rep_one : Rep (1 : ↥e64Sub) 1 := by
  unfold Rep
  show (1 : AEQ 7) = mkQ 7 1
  rw [map_one]

theorem eqπ_of_mkQ_eq {a b : Wr 7} (h : mkQ 7 a = mkQ 7 b) : eqπ a b := by
  rcases mkQ_eq_iff.mp h with h | h
  · left; exact (inv_mul_eq_one.mp h)
  · right
    have h1 : b = a * allOnes 7 := by
      calc b = a * (a⁻¹ * b) := by group
        _ = a * allOnes 7 := by rw [h]
    have h2 : a = b * allOnes 7 := by
      rw [h1, mul_assoc, allOnes_mul_self, mul_one]
    exact h2

theorem exists_rep (x : ↥e64Sub) : ∃ (v : Fin 7 → ZMod 2) (p : Equiv.Perm (Fin 7)), ∑ i, v i = 0 ∧
    (∀ s ∈ fanoLines, s.map p.toEmbedding ∈ fanoLines ∧ s.map p⁻¹.toEmbedding ∈ fanoLines) ∧
      Equiv.Perm.sign p = 1 ∧ Rep x ⟨v, p⟩ := by
  obtain ⟨w, hw, hwx⟩ := x.2
  refine ⟨w.vec, w.perm, hw.1.1, hw.2, hw.1.2, ?_⟩
  unfold Rep
  rw [← hwx]

theorem lemmaS (x : ↥e64Sub) (hx : ∀ r ∈ relsW, evalW [aH, bH, x] r = 1) :
    ∃ e ∈ s32, Rep x e.1 := by
  obtain ⟨v, p, hv, hp, hs, hrep⟩ := exists_rep x
  obtain ⟨t, ht, htp⟩ := perm_cover p hp hs
  have hrels : ∀ r ∈ relsW, eqπ (evalW [aW, bW, (⟨v, pc t.1⟩ : Wr 7)] r) 1 := by
    intro r hr
    have h1 := val_evalW aH bH x aW bW ⟨v, p⟩ rep_aH rep_bH hrep r
    rw [hx r hr] at h1
    rw [htp]
    apply eqπ_of_mkQ_eq
    rw [map_one, ← h1]
    rfl
  have hperm : ∀ r ∈ relsW, evalW [aW.perm, bW.perm, pc t.1] r = 1 := by
    intro r hr
    have h := hrels r hr
    have hmap := map_evalW (permHom 7) [aW, bW, (⟨v, pc t.1⟩ : Wr 7)] r
    have h1 : (evalW [aW, bW, (⟨v, pc t.1⟩ : Wr 7)] r).perm = 1 := by
      rcases h with h | h
      · rw [h]; rfl
      · rw [h]; rfl
    exact hmap.symm.trans h1
  obtain ⟨e0, he0, hpe0⟩ := perm_filter t ht hperm
  obtain ⟨e, he, hee⟩ := filter_ok t ht ⟨e0, he0, hpe0⟩ v hv hrels
  refine ⟨e, he, ?_⟩
  rw [htp] at hee
  unfold Rep at *
  rw [hrep, hee]

theorem step_rep (σ : ↥e64Sub →* ↥e64Sub) (ha : σ aH = aH) (hb : σ bH = bH) {x : ↥e64Sub}
    {t c1w : Wr 7} (hx : Rep x t) (ht : inS t) (hc1 : Rep (σ hH) c1w) :
    Rep (σ x) (stepW c1w t) := by
  have hw := look_spec ht
  have hxe : x = evalW [aH, bH, hH] (look t) :=
    rep_eq hx (rep_of_eqπ (val_evalW aH bH hH aW bW hW rep_aH rep_bH rep_hH (look t)) hw)
  have h1 : σ x = evalW [aH, bH, σ hH] (look t) := by
    rw [hxe]
    have := map_evalW σ [aH, bH, hH] (look t)
    simpa [ha, hb] using this
  rw [h1]
  exact val_evalW aH bH (σ hH) aW bW c1w rep_aH rep_bH hc1 (look t)

theorem relOK_map (σ : ↥e64Sub →* ↥e64Sub) (ha : σ aH = aH) (hb : σ bH = bH) {x : ↥e64Sub}
    (hx : ∀ r ∈ relsW, evalW [aH, bH, x] r = 1) : ∀ r ∈ relsW, evalW [aH, bH, σ x] r = 1 := by
  intro r hr
  have := map_evalW σ [aH, bH, x] r
  simp only [List.map_cons, List.map_nil, ha, hb] at this
  rw [← this, hx r hr, map_one]

theorem gen_e64 (x : ↥e64Sub) : x ∈ Subgroup.closure {y | y ∈ [aH, bH, hH]} := by
  obtain ⟨v, p, hv, hp, hs, hrep⟩ := exists_rep x
  obtain ⟨t, ht, htp⟩ := perm_cover p hp hs
  have hperm : ∃ y ∈ Subgroup.closure {y | y ∈ [aH, bH, hH]}, Rep y ⟨0, p⟩ := by
    refine ⟨evalW [aH, bH, hH] t.2, evalW_mem_closure _ _, ?_⟩
    have := val_evalW aH bH hH aW bW hW rep_aH rep_bH rep_hH t.2
    unfold Rep
    rw [this, permWords_ok t ht, htp]
  obtain ⟨hdec, hpairs⟩ := decomp_ok v hv
  have hvec : ∀ l : List (Fin 7 × Fin 7), (∀ q ∈ l, ∃ t ∈ pairWords, t.1 = q.1 ∧ t.2.1 = q.2) →
      ∃ y ∈ Subgroup.closure {y | y ∈ [aH, bH, hH]},
        Rep y ((l.map fun q => ofVec (vecOf [q.1, q.2])).prod) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1, Subgroup.one_mem _, rep_one⟩
    | cons q l ih =>
      intro hl
      obtain ⟨y, hy, hyr⟩ := ih fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')
      obtain ⟨t, ht, h1, h2⟩ := hl q List.mem_cons_self
      have hq : Rep (evalW [aH, bH, hH] t.2.2) (ofVec (vecOf [q.1, q.2])) := by
        have := val_evalW aH bH hH aW bW hW rep_aH rep_bH rep_hH t.2.2
        unfold Rep
        rw [this, pairWords_ok t ht, h1, h2]
      refine ⟨evalW [aH, bH, hH] t.2.2 * y, (Subgroup.closure _).mul_mem (evalW_mem_closure _ _) hy, ?_⟩
      simpa using rep_mul hq hyr
  obtain ⟨y1, hy1, hr1⟩ := hvec _ hpairs
  rw [hdec] at hr1
  obtain ⟨y2, hy2, hr2⟩ := hperm
  have hxy : x = y1 * y2 := by
    refine rep_eq hrep ?_
    have := rep_mul hr1 hr2
    have e : (ofVec v * (⟨0, p⟩ : Wr 7)) = ⟨v, p⟩ := by
      refine Wr.ext (funext fun i => ?_) (by simp [mul_perm, ofVec])
      show v i + 0 = v i
      simp
    rw [e] at this
    exact this
  rw [hxy]
  exact (Subgroup.closure _).mul_mem hy1 hy2

theorem fix_core_e64 (σ : ↥e64Sub →* ↥e64Sub) (hσ : ∃ a : ℕ, ∀ r, σ^[3 ^ a] r = r)
    (ha : σ aH = aH) (hb : σ bH = bH) : ∀ r, σ r = r := by
  obtain ⟨N0, hN⟩ := hσ
  obtain ⟨e, he, hc1⟩ := lemmaS (σ hH) (relOK_map σ ha hb relOK_h)
  obtain ⟨hs1, hs2, hs3, hs4⟩ := dyn_ok e he
  have x2 := step_rep σ ha hb hc1 hs1 hc1
  have x3 := step_rep σ ha hb x2 hs2 hc1
  have x4 := step_rep σ ha hb x3 hs3 hc1
  have h4 : σ (σ (σ (σ hH))) = hH := rep_eq (rep_of_eqπ x4 hs4) rep_hH
  have h4' : (⇑σ)^[4] hH = hH := by simpa using h4
  have hσh : σ hH = hH := by
    have hmod : 3 ^ N0 % 4 = 1 ∨ 3 ^ N0 % 4 = 3 := by
      clear hN
      induction N0 with
      | zero => left; rfl
      | succ k ih => rw [pow_succ]; omega
    have hN' : (⇑σ)^[3 ^ N0] hH = hH := hN hH
    have hfix : ∀ m : ℕ, (⇑σ)^[4 * m] hH = hH := fun m => by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed h4' m
    have hdecomp : 3 ^ N0 = (3 ^ N0 % 4) + 4 * (3 ^ N0 / 4) := (Nat.mod_add_div _ _).symm
    rw [hdecomp, Function.iterate_add_apply, hfix] at hN'
    rcases hmod with h1 | h3
    · rw [h1] at hN'; simpa using hN'
    · rw [h3] at hN'
      have : (⇑σ)^[4] hH = σ hH := by
        have e : (⇑σ)^[4] hH = σ ((⇑σ)^[3] hH) := Function.iterate_succ_apply' σ 3 hH
        rw [e, hN']
      rw [← this]; exact h4'
  intro r
  have hgen := gen_e64 r
  have hle : Subgroup.closure {y | y ∈ [aH, bH, hH]} ≤ MonoidHom.eqLocus σ (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hσh
  exact hle hgen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
