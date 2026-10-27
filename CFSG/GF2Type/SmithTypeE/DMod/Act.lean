module

public import CFSG.GF2Type.SmithTypeE.DMod.Points
public import CFSG.GF2Type.SmithTypeE.DMod.Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

theorem lineOfPair_map (g : V12 ≃ₗ[ZMod 2] V12) (u w : V12) :
    (lineOfPair u w).map g.toEquiv.toEmbedding = lineOfPair (g u) (g w) := by
  simp [lineOfPair, Finset.map_insert, Finset.map_singleton]

theorem isTsLine_map {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q12 (g x) = q12 x) {s : Finset V12}
    (hs : IsTsLine s) : IsTsLine (s.map g.toEquiv.toEmbedding) := by
  obtain ⟨u, w, hu, hw, huw, hts, rfl⟩ := hs
  exact ⟨g u, g w, fun h => hu (g.map_eq_zero_iff.mp h), fun h => hw (g.map_eq_zero_iff.mp h),
    fun h => huw (g.injective h), tsPair_map hg hts, lineOfPair_map g u w⟩

theorem siegelEquiv_eq_of_lineOfPair_eq {u w u' w' : V12} (h : TsPair u w) (h' : TsPair u' w')
    (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w) (hu' : u' ≠ 0) (hw' : w' ≠ 0) (huw' : u' ≠ w')
    (e : lineOfPair u w = lineOfPair u' w') : siegelEquiv u w = siegelEquiv u' w' := by
  have hu'mem : u' ∈ lineOfPair u w := by
    rw [e]; simp [lineOfPair]
  have hw'mem : w' ∈ lineOfPair u w := by
    rw [e]; simp [lineOfPair]
  simp only [lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hu'mem hw'mem
  rcases hu'mem with h1 | h1 | h1 <;> rcases hw'mem with h2 | h2 | h2 <;> subst u' w'
  · exact (huw' rfl).elim
  · rfl
  · exact (siegelEquiv_add_right h).symm
  · exact (siegelEquiv_swap h).symm
  · exact (huw' rfl).elim
  · rw [add_comm u w, siegelEquiv_add_right (tsPair_swap h), siegelEquiv_swap h]
  · exact (siegelEquiv_add_right h).symm.trans (siegelEquiv_swap h')
  · rw [← siegelEquiv_swap h', add_comm u w, siegelEquiv_add_right (tsPair_swap h),
      siegelEquiv_swap h]
  · exact (huw' rfl).elim

theorem qf_of_q12 {c : ℕ} (h : q12 (dec12 c) = 0) : qf c = false := by
  rw [q12_dec12] at h
  cases hc : qf c
  · rfl
  · rw [hc] at h
    simp [bit] at h

theorem bf_of_B12 {a b : ℕ} (h : B12 (dec12 a) (dec12 b) = 0) : bf a b = false := by
  rw [B12_dec12] at h
  cases hc : bf a b
  · rfl
  · rw [hc] at h
    simp [bit] at h

theorem sgl_lt {u w x : ℕ} (hu : u < 4096) (hw : w < 4096) (hx : x < 4096) : sgl u w x < 4096 := by
  unfold sgl
  refine xor_lt_4096 (xor_lt_4096 hx ?_) ?_
  · split <;> omega
  · split <;> omega

abbrev IsoGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := CFSG.Open.timmesfeldIsometries q12

theorem mem_isoGrp {g : V12 ≃ₗ[ZMod 2] V12} : g ∈ IsoGrp ↔ ∀ x, q12 (g x) = q12 x := Iff.rfl

@[expose] def lineAct (g : IsoGrp) (L : TsLine) : TsLine :=
  ⟨L.1.map g.1.toEquiv.toEmbedding, isTsLine_map g.2 L.2⟩

noncomputable instance : MulAction IsoGrp TsLine where
  smul := lineAct
  one_smul L := by
    apply Subtype.ext
    have hemb : (1 : IsoGrp).1.toEquiv.toEmbedding = Function.Embedding.refl _ :=
      Function.Embedding.ext fun x => rfl
    change L.1.map (1 : IsoGrp).1.toEquiv.toEmbedding = L.1
    rw [hemb, Finset.map_refl]
  mul_smul g h L := by
    apply Subtype.ext
    have hemb : (g * h : IsoGrp).1.toEquiv.toEmbedding =
        h.1.toEquiv.toEmbedding.trans g.1.toEquiv.toEmbedding :=
      Function.Embedding.ext fun x => rfl
    change L.1.map (g * h : IsoGrp).1.toEquiv.toEmbedding =
      (L.1.map h.1.toEquiv.toEmbedding).map g.1.toEquiv.toEmbedding
    rw [hemb, Finset.map_map]

section Certified

@[expose] noncomputable def actPerm : IsoGrp →* Equiv.Perm (Fin 365211) where
  toFun g := lineEquiv.symm.permCongr (MulAction.toPerm g)
  map_one' := Equiv.ext fun k => by
    simp [Equiv.permCongr_apply]
  map_mul' g h := Equiv.ext fun k => by
    simp [Equiv.permCongr_apply, mul_smul]

theorem lineEquiv_actPerm (g : IsoGrp) (k : Fin 365211) :
    lineEquiv (actPerm g k) = g • lineEquiv k := by
  simp [actPerm, Equiv.permCongr_apply]

theorem lineSet_actPerm (g : IsoGrp) (k : Fin 365211) :
    lineSet (actPerm g k).val = (lineSet k.val).map g.1.toEquiv.toEmbedding := by
  have h := congrArg Subtype.val (lineEquiv_actPerm g k)
  exact h

@[expose] noncomputable def siegelK (k : ℕ) : V12 ≃ₗ[ZMod 2] V12 :=
  siegelEquiv (dec12 (linePair k).1) (dec12 (linePair k).2)

theorem tsPair_linePair {k : ℕ} (hk : k < 365211) :
    TsPair (dec12 (linePair k).1) (dec12 (linePair k).2) := by
  obtain ⟨-, -, -, -, hq1, hq2, hb, -⟩ := lineFacts.entry k hk
  exact tsPair_dec12 hq1 hq2 hb

theorem linePair_ne {k : ℕ} (hk : k < 365211) :
    dec12 (linePair k).1 ≠ 0 ∧ dec12 (linePair k).2 ≠ 0 ∧
      dec12 (linePair k).1 ≠ dec12 (linePair k).2 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := lineFacts.entry k hk
  refine ⟨dec12_ne_zero (by omega) (by omega), dec12_ne_zero (by omega) (by omega), fun h => ?_⟩
  have := eq_of_dec12_eq (by omega) (by omega) h
  omega

theorem siegelK_mem_iso {k : ℕ} (hk : k < 365211) : siegelK k ∈ IsoGrp :=
  siegelEquiv_mem_isometries (tsPair_linePair hk)

theorem siegelK_mem_omega {k : ℕ} (hk : k < 365211) :
    siegelK k ∈ CFSG.Open.timmesfeldOmegaPlus 6 :=
  siegelEquiv_mem_omega (tsPair_linePair hk) (linePair_ne hk).1

theorem siegelK_mul_self {k : ℕ} (hk : k < 365211) : siegelK k * siegelK k = 1 :=
  siegelEquiv_mul_self (tsPair_linePair hk)

theorem conj_siegelK {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q12 (g x) = q12 x) {k l : ℕ}
    (hk : k < 365211) (hl : l < 365211)
    (h : lineSet l = (lineSet k).map g.toEquiv.toEmbedding) :
    g * siegelK k * g⁻¹ = siegelK l := by
  unfold siegelK
  rw [conj_siegelEquiv hg (tsPair_linePair hk)]
  obtain ⟨hu, hw, huw⟩ := linePair_ne hk
  obtain ⟨hu', hw', huw'⟩ := linePair_ne hl
  refine siegelEquiv_eq_of_lineOfPair_eq (tsPair_map hg (tsPair_linePair hk))
    (tsPair_linePair hl) (fun h0 => hu (g.map_eq_zero_iff.mp h0))
    (fun h0 => hw (g.map_eq_zero_iff.mp h0)) (fun h' => huw (g.injective h')) hu' hw' huw' ?_
  rw [← lineOfPair_map]
  exact h.symm

theorem tvImg_spec {j a : ℕ} (hj : j < 365211) (ha : a < 365211) :
    tvImg j a < 365211 ∧
      lineSet (tvImg j a) = (lineSet a).map (siegelK j).toEquiv.toEmbedding := by
  obtain ⟨hj0, hj1, hj2, hj3, hqj1, hqj2, hbj, -⟩ := lineFacts.entry j hj
  obtain ⟨ha0, ha1, ha2, ha3, hqa1, hqa2, hba, -⟩ := lineFacts.entry a ha
  have hTj := tsPair_linePair hj
  have hTa := tsPair_linePair ha
  obtain ⟨hu, hw, huw⟩ := linePair_ne ha
  have hS1 : siegelK j (dec12 (linePair a).1) = dec12 (sgl (linePair j).1 (linePair j).2 (linePair a).1) :=
    siegelEquiv_dec12 hqj1 hqj2 hbj _
  have hS2 : siegelK j (dec12 (linePair a).2) = dec12 (sgl (linePair j).1 (linePair j).2 (linePair a).2) :=
    siegelEquiv_dec12 hqj1 hqj2 hbj _
  set x1 := sgl (linePair j).1 (linePair j).2 (linePair a).1 with hx1def
  set x2 := sgl (linePair j).1 (linePair j).2 (linePair a).2 with hx2def
  have hx1 : x1 < 4096 := sgl_lt (by omega) (by omega) (by omega)
  have hx2 : x2 < 4096 := sgl_lt (by omega) (by omega) (by omega)
  have hx10 : x1 ≠ 0 := by
    intro h0
    apply hu
    apply (siegelK j).injective
    rw [hS1, h0, dec12_zero, map_zero]
  have hx20 : x2 ≠ 0 := by
    intro h0
    apply hw
    apply (siegelK j).injective
    rw [hS2, h0, dec12_zero, map_zero]
  have hx12 : x1 ≠ x2 := by
    intro h0
    apply huw
    apply (siegelK j).injective
    rw [hS1, hS2, h0]
  have hqx1 : qf x1 = false := qf_of_q12 (by
    rw [← hS1, siegelK, q12_siegelEquiv hTj]
    exact hTa.1)
  have hqx2 : qf x2 = false := qf_of_q12 (by
    rw [← hS2, siegelK, q12_siegelEquiv hTj]
    exact hTa.2.1)
  have hbx : bf x1 x2 = false := bf_of_B12 (by
    rw [← hS1, ← hS2, siegelK, B12_siegelEquiv hTj]
    exact hTa.2.2)
  obtain ⟨hlt, hset⟩ := lineSet_lineIdx3 hx1 hx2 hx10 hx20 hqx1 hqx2 hx12 hbx
  have hk : tvImg j a = lineIdx3 x1 x2 (x1 ^^^ x2) := rfl
  rw [hk]
  refine ⟨hlt, ?_⟩
  rw [hset, ← hS1, ← hS2, lineSet, ← lineOfPair_map]

end Certified

end CFSG.GF2Type.SmithTypeE.DMod
