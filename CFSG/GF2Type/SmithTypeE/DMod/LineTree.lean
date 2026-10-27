module

public import Certificates.Certificate38701
public import CFSG.GF2Type.SmithTypeE.DMod.GensV

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.KD.SmithD6 CFSG.KC.SmithD6T2

theorem lineTreeCheck_holds :
    (∀ g < 13, gensArr[g]! = lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2) ∧
    ∀ a b : ℕ, a < 4096 → b < 4096 → a ≠ 0 → b ≠ 0 → a ≠ b → qf a = false → qf b = false →
      bf a b = false →
        Relation.ReflTransGen (fun x y : ℕ × ℕ => ∃ g < 13, d6Step g x.1 = y.1 ∧ d6Step g x.2 = y.2)
          (a, b) (1, 2) :=
  Certificates.certificate38701

theorem d6GenPair_eq : ∀ g < 13, d6GenPair g = gensV.getD g (0, 0) := by
  decide +kernel

theorem gensArr_lt {g : ℕ}
    (hg : g < 13) : gensArr[g]! < 365211 := by
  rw [lineTreeCheck_holds.1 g hg]
  exact (lineOf_gensV hg).1

theorem siegelK_gensArr {g : ℕ}
    (hg : g < 13) :
    siegelK gensArr[g]! = siegelEquiv (dec12 (d6GenPair g).1) (dec12 (d6GenPair g).2) := by
  rw [lineTreeCheck_holds.1 g hg, siegelK_lineOf_gensV hg, d6GenPair_eq g hg]

@[expose] def PairOK (x : ℕ × ℕ) : Prop :=
  x.1 < 4096 ∧ x.2 < 4096 ∧ x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 ≠ x.2 ∧ qf x.1 = false ∧ qf x.2 = false ∧
    bf x.1 x.2 = false

theorem lineOf_spec {x : ℕ × ℕ} (h : PairOK x) :
    lineOf x.1 x.2 < 365211 ∧ lineSet (lineOf x.1 x.2) = lineOfPair (dec12 x.1) (dec12 x.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact lineSet_lineIdx3 h1 h2 h3 h4 h6 h7 h5 h8

theorem pairOK_step {g : ℕ} (hg : g < 13) {x : ℕ × ℕ} (h : PairOK x) :
    PairOK (d6Step g x.1, d6Step g x.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨d6Step_lt hg h1, d6Step_lt hg h2, d6Step_ne_zero hg h1 h3, d6Step_ne_zero hg h2 h4,
    fun e => h5 (d6Step_inj hg h1 h2 e), ?_, ?_, ?_⟩
  · rw [d6Step_qf hg]
    exact h6
  · rw [d6Step_qf hg]
    exact h7
  · rw [d6Step_bf hg]
    exact h8

theorem tvImg_lineOf {g : ℕ}
    (hg : g < 13) {x : ℕ × ℕ} (h : PairOK x) :
    tvImg gensArr[g]! (lineOf x.1 x.2) = lineOf (d6Step g x.1) (d6Step g x.2) := by
  obtain ⟨hlx, hsx⟩ := lineOf_spec h
  obtain ⟨hly, hsy⟩ := lineOf_spec (pairOK_step hg h)
  obtain ⟨hlt, hset⟩ := tvImg_spec (gensArr_lt hg) hlx
  apply lineSet_injective hlt hly
  obtain ⟨hu, hw, huw, -, -⟩ := d6GenPair_ts g hg
  rw [hset, hsx, hsy, lineOfPair_map, siegelK_gensArr hg, siegelEquiv_dec12 hu hw huw,
    siegelEquiv_dec12 hu hw huw]
  rfl

theorem lineOf_linePair {k : ℕ} (hk : k < 365211) :
    PairOK (linePair k) ∧ lineOf (linePair k).1 (linePair k).2 = k := by
  obtain ⟨h0, h1, h2, h3, hq1, hq2, hb, -⟩ := lineFacts.entry k hk
  have hP : PairOK (linePair k) := ⟨by omega, by omega, by omega, by omega, by omega, hq1, hq2, hb⟩
  refine ⟨hP, ?_⟩
  obtain ⟨hl, hs⟩ := lineOf_spec hP
  exact lineSet_injective hl hk hs

theorem lineTree_induct_from
    (Q : ℕ → Prop) {k₀ : ℕ} (hk₀ : k₀ < 365211) (h0 : Q k₀)
    (hstep : ∀ g < 13, ∀ p < 365211, ∀ v < 365211, tvImg gensArr[g]! p = v → Q p → Q v) :
    ∀ v < 365211, Q v := by
  let R := fun x y : ℕ × ℕ => ∃ g < 13, d6Step g x.1 = y.1 ∧ d6Step g x.2 = y.2
  have hbwd : ∀ x y, Relation.ReflTransGen R x y → PairOK x → Q (lineOf y.1 y.2) →
      Q (lineOf x.1 x.2) := by
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ hQ => hQ
    | head hxz _ ih =>
      intro hx hQ
      obtain ⟨g, hg, e1, e2⟩ := hxz
      have hz := pairOK_step hg hx
      rw [e1, e2] at hz
      have hQz := ih hz hQ
      have he := tvImg_lineOf hg hz
      rw [← e1, ← e2, d6Step_step hg hx.1, d6Step_step hg hx.2.1] at he
      have := hstep g hg _ (lineOf_spec hz).1 _ (lineOf_spec hx).1 ?_ hQz
      · exact this
      · rw [← he, ← e1, ← e2]
  have hfwd : ∀ x y, Relation.ReflTransGen R x y → PairOK x → Q (lineOf x.1 x.2) →
      PairOK y ∧ Q (lineOf y.1 y.2) := by
    intro x y hxy
    induction hxy with
    | refl => exact fun h hQ => ⟨h, hQ⟩
    | tail _ hyz ih =>
      intro hx hQ
      obtain ⟨hy, hQy⟩ := ih hx hQ
      obtain ⟨g, hg, e1, e2⟩ := hyz
      have hz := pairOK_step hg hy
      refine ⟨by rw [e1, e2] at hz; exact hz, ?_⟩
      have := hstep g hg _ (lineOf_spec hy).1 _ (lineOf_spec hz).1 (tvImg_lineOf hg hy) hQy
      rwa [e1, e2] at this
  have hreach : ∀ k < 365211, Relation.ReflTransGen R (linePair k) (1, 2) := fun k hk => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (lineOf_linePair hk).1
    exact lineTreeCheck_holds.2 _ _ h1 h2 h3 h4 h5 h6 h7 h8
  have hb : Q (lineOf 1 2) := by
    obtain ⟨hP0, e0⟩ := lineOf_linePair hk₀
    exact (hfwd _ _ (hreach k₀ hk₀) hP0 (by rw [e0]; exact h0)).2
  intro v hv
  obtain ⟨hPv, ev⟩ := lineOf_linePair hv
  have := hbwd _ _ (hreach v hv) hPv hb
  rwa [ev] at this

theorem lineTree_induct
    (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ g < 13, ∀ p < 365211, ∀ v < 365211, tvImg gensArr[g]! p = v → Q p → Q v) :
    ∀ v < 365211, Q v :=
  lineTree_induct_from Q (by norm_num) h0 hstep

theorem size_tvCols (k : ℕ) : (tvCols k).size = 32 := by
  simp [tvCols]

@[expose] noncomputable def tvLin (k : ℕ) : V →ₗ[ZMod 2] V := colsLin (tvCols k)

theorem tvLin_decode (k c : ℕ) : tvLin k (decode32 c) = decode32 (applyCols (tvCols k) c) :=
  (decode32_applyCols (size_tvCols k) c).symm

theorem tvLin_single (k : ℕ) (m : Fin 32) :
    tvLin k (Pi.single m 1) = decode32 (tvCols k)[m.val]! :=
  colsLin_single _ m

theorem tvLin_tvImg {g p : ℕ} (hg : g < 365211)
    (hp : p < 365211) (x : V) :
    tvLin (tvImg g p) x = tvLin g (tvLin p (tvLin g x)) := by
  obtain ⟨hv, hset⟩ := tvImg_spec hg hp
  unfold tvLin
  refine colsLin_tvCols_conj ?_ x
  have hT := tsPair_linePair hg
  rw [tlift_conj hT]
  have hq : ∀ y, q12 (siegelK g y) = q12 y := fun y => q12_siegelEquiv hT y
  have e : lineSet (tvImg g p) =
      lineOfPair (siegelK g (dec12 (linePair p).1)) (siegelK g (dec12 (linePair p).2)) := by
    rw [hset, lineSet, lineOfPair_map]
  exact tlift_eq_of_line_eq (tsPair_linePair hv) (tsPair_map hq (tsPair_linePair hp))
    (linePair_ne hv).2.2 (fun h => (linePair_ne hp).2.2 ((siegelK g).injective h)) e

end CFSG.GF2Type.SmithTypeE.DMod
