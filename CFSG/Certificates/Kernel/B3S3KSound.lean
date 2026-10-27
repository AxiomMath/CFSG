module

public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.B3Spor3Checks
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.ChainTailSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.Misc.ChainTail
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CFSG.Monster.B.Co2 (allLt_iff)

@[expose] def BindA (n w : ℕ) (a : Array (Array ℕ)) (m : ℕ) (F : ℕ → ℕ) : Prop :=
  a.size = m ∧ ∀ j < m, a[j]! = unpack n w (F j)

theorem any_range_congr {m : ℕ} {f g : ℕ → Bool} (h : ∀ j < m, f j = g j) :
    (List.range m).any f = (List.range m).any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨j, hj, e⟩ => ⟨j, hj, (h j hj) ▸ e⟩, fun ⟨j, hj, e⟩ => ⟨j, hj, (h j hj).symm ▸ e⟩⟩

theorem toList_of {a : Array (Array ℕ)} {N : ℕ} {F : ℕ → Array ℕ} (hs : a.size = N)
    (h : ∀ i < N, a[i]! = F i) : a.toList = (List.range N).map F := by
  apply List.ext_getElem
  · simp [hs]
  · intro i h1 h2
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
      ← h i (by simpa [hs] using h1), getElem!_pos a i (by simpa using h1)]

section Codes

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem permB_id : permB n w (pidn n w) = true := permB_of_pp (PP.id hw)

omit hw in
theorem validA_of {p : ℕ} (hp : permB n w p = true) : validA n (unpack n w p) = true :=
  validA_unpack hp

theorem eqA_id {p : ℕ} (hp : permB n w p = true) :
    eqA n (unpack n w p) (idA n) = Nat.beq p (pidn n w) := by
  rw [idA_eq hw, eqA_unpack' hw hp (permB_id hw)]

theorem powEq_id {p : ℕ} (hp : permB n w p = true) (e : ℕ) :
    eqA n (powArr n (unpack n w p) e) (idA n) = Nat.beq (pw n w p e) (pidn n w) := by
  rw [pow_unpack' hw hp, eqA_id hw (permB_ppow hw hp e)]
  rfl

omit hw in
theorem enum_of {gs : Array (Array ℕ)} {ng N fuel : ℕ} {G T E S : ℕ → ℕ} {SK ps : List ℕ}
    (hg : BindA n w gs ng G) (hp : ∀ k < ng, permB n w (G k) = true)
    (hk : bfsK n w ng G N T E S = true) (hps : ∀ p ∈ ps, p < n)
    (hK : keysSK n w ps N T SK = true) (hf : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧ (enumBfs n gs ps fuel).pts.size = N ∧
      ∀ i < N, (enumBfs n gs ps fuel).pts[i]! = unpack n w (T i) := by
  have hpts := enumBfs_pts_base hg.1 hg.2 hk hps hK hf
  refine ⟨enumOK_of_bfsK_base hg.1 hg.2 hp hk hps hK hf, by rw [hpts]; simp, fun i hi => ?_⟩
  rw [hpts, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem linesOK3_of {p N r : ℕ} {gs xs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    {T LX : ℕ → ℕ} (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hx : BindA n w xs r LX) (h : linesK n w p N r T LX = true) :
    linesOK3 p N r n gs ps c xs = true := by
  unfold linesK at h
  rw [Bool.and_eq_true, Orb.allN_iff, Orb.allN_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hLp : ∀ j < r, permB n w (LX j) = true := fun j hj => by
    have := h2 j hj
    rw [Bool.and_eq_true] at this
    exact this.1
  unfold linesOK3
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, allLt_iff, allLt_iff]
  refine ⟨⟨⟨hc, hN⟩, fun k hk => ?_⟩, fun j hj => ?_⟩
  · rw [hT k hk, powEq_id hw (hTp k hk), eqA_id hw (hTp k hk)]
    rw [← h1 k hk, anyNP_eq]
    congr 1
    apply any_range_congr
    intro j hj
    rw [anyNP_eq, hx.2 j hj]
    apply any_range_congr
    intro e _
    rw [pow_unpack' hw (hLp j hj), eqA_unpack' hw (hTp k hk) (permB_ppow hw (hLp j hj) e)]
    rfl
  · rw [hx.2 j hj, validA_of (hLp j hj), powEq_id hw (hLp j hj), Bool.true_and]
    have := h2 j hj
    rw [Bool.and_eq_true] at this
    exact this.2

omit hw in
theorem siftA_of {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (n * w)) 0 = true ∧
      allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) = true :=
  siftK_soundR hb hp hl rfl (Nat.eq_of_beq_eq_true h.1) h.2.1 h.2.2

theorem transOK2_of {r nc : ℕ} {H X L : Array (Array ℕ)} {rec : List ℕ} {RL : Array Level}
    {Rb : Array ℕ} {HC XC LC : ℕ → ℕ} (hH : BindA n w H r HC) (hX : BindA n w X nc XC)
    (hXp : ∀ c < nc, permB n w (XC c) = true) (hL : BindA n w L r LC)
    (hLp : ∀ j < r, permB n w (LC j) = true)
    (hrec : ∀ j < r, rec.getD j 0 < nc) (hsift : ∀ j < r, siftA n RL Rb 0 H[j]! = true)
    (h : transK n w r HC XC LC rec = true) : transOK2 r n H X L rec RL Rb = true := by
  unfold transK at h
  rw [Orb.allN_iff] at h
  unfold transOK2
  rw [allLt_iff]
  intro j hj
  have hj' := h j hj
  rw [Bool.and_eq_true] at hj'
  have hc : permB n w (cj n w (HC j) (XC (rec.getD j 0))) = true :=
    permB_pcomp hw hj'.1 (permB_pcomp hw (hXp _ (hrec j hj)) (permB_pinvS hw hj'.1))
  rw [hsift j hj, hH.2 j hj, validA_of hj'.1, hX.2 _ (hrec j hj), hL.2 j hj,
    conj_unpack' hw hj'.1 (hXp _ (hrec j hj))]
  change (true && true && eqA n (unpack n w (cj n w (HC j) (XC (rec.getD j 0))))
    (unpack n w (LC j))) = true
  rw [eqA_unpack' hw hc (hLp j hj)]
  exact hj'.2

theorem relsOKP_of {p nb BP X : ℕ} {base : Array ℕ} {rels : List (ℕ × ℕ × ℕ)}
    (hb : base.size = nb) (hbp : ∀ t < nb, base[t]! = pg w (mask w) BP t)
    (hbn : ∀ t < nb, pg w (mask w) BP t < n) (hX : permB n w X = true)
    (h : relsK n w p BP X nb rels = true) :
    relsOKP p n base (unpack n w X) rels = true := by
  rw [relsOKP, List.all_eq_true]
  rw [relsK, List.all_eq_true] at h
  intro r hr
  have hr' := h r hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hr'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hb]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [pow_unpack' hw hX, hbp _ h2, hbp _ h3, Orb.unpack_get (hbn _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem powPA_get {p X : ℕ} (hX : permB n w X = true) :
    ∀ e < (powPA p n (unpack n w X)).size,
      (powPA p n (unpack n w X))[e]! = unpack n w (pw n w X e) := by
  intro e he
  rw [getElem!_pos _ e he]
  simp only [powPA, Array.getElem_ofFn]
  exact pow_unpack' hw hX e

theorem centOKP_of {p N kS nb BP ng : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {X : ℕ} (hX : permB n w X = true)
    {rels : List (ℕ × ℕ × ℕ)} (hr : relsK n w p BP X nb rels = true)
    {gs : Array (Array ℕ)} {GC : ℕ → ℕ} (hg : BindA n w gs ng GC)
    (hcomm : commK n w ng X GC = true)
    (hsift : ∀ k < ng, siftA n (rawLevels n S base) base 0 (unpack n w (GC k)) = true)
    {ps : List ℕ} {c : ArrCert} {T : ℕ → ℕ} (hc : enumOK n gs ps c = true)
    (hN : c.pts.size = N) (hT : ∀ i < N, c.pts[i]! = unpack n w (T i))
    (hTp : ∀ i < N, permB n w (T i) = true) (hnb : 0 < nb)
    (htail : allN (rcnt (LR 0)) (ptailBranchK n w LR TR BP X (pw n w X) rels N T nb) = true) :
    centOKP p n S base (unpack n w X) rels gs ps c N = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbp : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbn : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hbp t ht]
    exact Orb.base_lt_of_levels hb hl t ht
  have hrel := relsOKP_of hw hbs hbp hbn hX hr
  have hrels : ∀ r ∈ rels, r.2.2 < (powPA p n (unpack n w X)).size := by
    intro r hr'
    rw [relsK, List.all_eq_true] at hr
    have := hr r hr'
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    simpa [powPA] using this.1.1.1
  have htl := ptailK_sound hb hp hl rfl hX (powPA_get hw hX) hrels
    (toList_of hN hT) hTp hnb (Orb.allN_iff.1 htail)
  unfold commK at hcomm
  rw [Orb.allN_iff] at hcomm
  unfold centOKP
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hrel, hc⟩, hN⟩, ?_⟩, ?_⟩, by rw [hbs]; exact htl⟩
  · rw [allLt_iff]
    intro k hk
    rw [hg.1] at hk
    have hk' := hcomm k hk
    rw [Bool.and_eq_true] at hk'
    rw [hg.2 k hk, commA, comp_unpack' hw hk'.1 hX, comp_unpack' hw hX hk'.1,
      eqA_unpack' hw (permB_pcomp hw hk'.1 hX) (permB_pcomp hw hX hk'.1)]
    exact hk'.2
  · rw [allLt_iff]
    intro k hk
    rw [hg.1] at hk
    rw [hg.2 k hk]
    exact hsift k hk

theorem convProdOK_of {N : ℕ} {pts : Array (Array ℕ)} {T WJ WR : ℕ → ℕ} {qs rs : List ℕ}
    (hN : pts.size = N) (hT : ∀ i < N, pts[i]! = unpack n w (T i))
    (hTp : ∀ i < N, permB n w (T i) = true)
    (h : allN N (convAt n w N T qs rs WJ WR) = true) : convProdOK n pts qs rs = true := by
  rw [Orb.allN_iff] at h
  unfold convProdOK
  rw [allLt_iff]
  intro i hi
  rw [hN] at hi
  have hi' := h i hi
  unfold convAt at hi'
  have hP := hTp i hi
  have hq : (qs.any fun q => eqA n (powArr n pts[i]! q) (idA n)) =
      qs.any fun q => Nat.beq (pw n w (T i) q) (pidn n w) := by
    congr 1
    funext q
    rw [hT i hi, powEq_id hw hP]
  rw [hq, hT i hi, eqA_id hw hP]
  cases h1 : (!(qs.any fun q => Nat.beq (pw n w (T i) q) (pidn n w)) ||
    Nat.beq (T i) (pidn n w))
  · rw [h1, Bool.false_or] at hi'
    rw [Bool.false_or]
    simp only [Bool.and_eq_true, Nat.blt_eq, List.any_eq_true] at hi'
    obtain ⟨⟨hj, r, hr, hre⟩, hz⟩ := hi'
    have hre' : WR i = r := Nat.eq_of_beq_eq_true hre
    rw [List.any_eq_true]
    refine ⟨WJ i, by rw [hN]; exact List.mem_range.2 hj, ?_⟩
    rw [List.any_eq_true]
    refine ⟨r, hr, ?_⟩
    have hPj := hTp _ hj
    have hc : permB n w (cj n w (T (WJ i)) (T i)) = true :=
      permB_pcomp hw hPj (permB_pcomp hw hP (permB_pinvS hw hPj))
    have hm : permB n w (cm n w (T i) (cj n w (T (WJ i)) (T i))) = true :=
      permB_pcomp hw hP hc
    have hcj : conjA n (unpack n w (T (WJ i))) (unpack n w (T i)) =
        unpack n w (cj n w (T (WJ i)) (T i)) := conj_unpack' hw hPj hP
    rw [hT _ hj, hcj, comp_unpack' hw hP hc]
    change (!(eqA n (powArr n (unpack n w (cm n w (T i) (cj n w (T (WJ i)) (T i)))) r)
      (idA n)) && eqA n (powArr n (powArr n (unpack n w (cm n w (T i) (cj n w (T (WJ i))
        (T i)))) r) 3) (idA n)) = true
    rw [pow_unpack' hw hm, powEq_id hw (permB_ppow hw hm r), eqA_id hw (permB_ppow hw hm r)]
    rw [← hre']
    exact hz
  · rfl

omit hw in
theorem mem_base_lt {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) : ∀ q ∈ base.toList, q < n := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := Orb.base_lt_of_levels hb hl
  intro q hq
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hq
  have ht' : t < nb := by simpa [hbs] using ht
  have := hbl t ht'
  rw [getElem!_pos base t (by simpa using ht)] at this
  simpa using this

theorem caseOK_of {D : Data} {k : Case} {x : Array ℕ} (hD : D.n = n) {PA PB X : ℕ}
    (hA : D.A = unpack n w PA) (hB : D.B = unpack n w PB) (hPA : permB n w PA = true)
    (hPB : permB n w PB = true) (hx : x = unpack n w X) (hX : permB n w X = true)
    (hX3 : Nat.beq (pw n w X 3) (pidn n w) = true)
    {kS nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Dw : List (List ℤ)}
    (hb : Binds n w PS kS nb BP k.S k.base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS 2 Dw nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 kS Dw = k.W)
    (h0 : Nat.beq (PS 0) PA = true) (h1 : Nat.beq (PS 1) PB = true) (hk2 : 2 ≤ kS)
    (hnd : k.base.toList.Nodup) (hnb : 0 < nb)
    {ng N : ℕ} {GC T E S : ℕ → ℕ} {SK : List ℕ} (hg : BindA n w k.gens ng GC)
    (hcomm : commK n w ng X GC = true)
    (hsift : ∀ j < ng, Nat.beq (Nat.shiftRight (GC j) (n * w)) 0 = true ∧
      allN n (fun i => Nat.blt (pg w (mask w) (GC j) i) n) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 (GC j) = true)
    (hk : bfsK n w ng GC N T E S = true) (hK : keysSK n w k.base.toList N T SK = true)
    (hTp : allN N (fun i => permB n w (T i)) = true) (hcard : N = k.card)
    (hr : relsK n w 3 BP X nb k.rels = true)
    (htail : allN (rcnt (LR 0)) (ptailBranchK n w LR TR BP X (pw n w X) k.rels N T nb) = true)
    (hcrit : ∀ pts : Array (Array ℕ), pts.size = N → (∀ i < N, pts[i]! = unpack n w (T i)) →
      critOK n pts k.card k.crit = true) :
    caseOK D k x = true := by
  subst hcard
  have hTp' : ∀ i < k.card, permB n w (T i) = true := Orb.allN_iff.1 hTp
  have hps : ∀ q ∈ k.base.toList, q < n := mem_base_lt hb hl
  have hcomm' := Orb.allN_iff.1 hcomm
  have hGp : ∀ j < ng, permB n w (GC j) = true := fun j hj => by
    have := hcomm' j hj
    rw [Bool.and_eq_true] at this
    exact this.1
  obtain ⟨he1, he2, he3⟩ := enum_of hg hGp hk hps hK (by omega : k.card ≤ k.card + 1)
  have hPS : ∀ j < kS, permB n w (PS j) = true := fun j hj =>
    permB_of_pp (pp_of_permOK hw (Orb.allN_iff.1 hp j hj))
  have hchain := rawChainK_sound (chunks := 1) hb hh hl hNS hs
  rw [hW] at hchain
  have hS0 : k.S[0]! = unpack n w (PS 0) := hb.2.2.2.2.1 0 (by omega)
  have hS1 : k.S[1]! = unpack n w (PS 1) := hb.2.2.2.2.1 1 (by omega)
  have hsz : k.S.size = kS := hb.2.2.2.1
  have hcent := centOKP_of (p := 3) hw hb hp hl hX hr hg hcomm
    (fun j hj => siftA_of hb hp hl (hsift j hj)) he1 he2 he3 hTp' hnb htail
  have hn1 : 1 ≤ n := hb.1
  unfold caseOK
  simp only [hD]
  rw [hA, hB, hx, validA_of hPA, validA_of hPB, validA_of hX, caseChainOK2P, hchain, hS0, hS1,
    eqA_unpack' hw (hPS 0 (by omega)) hPA, eqA_unpack' hw (hPS 1 (by omega)) hPB,
    h0, h1, hcent, powEq_id hw hX, hX3, hcrit _ (by rw [he2]) he3]
  simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hnd, hps⟩, hn1⟩, by omega⟩

end Codes

theorem check_of {D : Data} (h0 : 0 < D.cases.size)
    (horb : (rawOrbitSizes D.n D.cases[0]!.S D.cases[0]!.base).prod = D.ord)
    (hord : D.ord = 3 ^ D.k3 * D.m3) (hm3 : D.m3 % 3 ≠ 0) (hN3 : D.N3 = 3 ^ D.k3)
    (hlines : linesOK3 3 D.N3 D.lines.size D.n D.QGens D.cases[0]!.base.toList
      (enumBfs D.n D.QGens D.cases[0]!.base.toList (D.N3 + 1)) D.lines = true)
    (hq : ∀ l < D.QGens.size,
      siftA D.n (rawLevels D.n D.cases[0]!.S D.cases[0]!.base) D.cases[0]!.base 0 D.QGens[l]! =
        true)
    (htr : transOK2 D.lines.size D.n D.trans D.caseX D.lines D.recs
      (rawLevels D.n D.cases[0]!.S D.cases[0]!.base) D.cases[0]!.base = true)
    (hrec : ∀ j < D.lines.size, D.recs.getD j 0 < D.cases.size)
    (hcx : D.caseX.size = D.cases.size)
    (hc : ∀ c < D.cases.size, caseOK D D.cases[c]! D.caseX[c]! = true) : check D = true := by
  unfold check
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allLt_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, horb⟩, hord⟩, hm3⟩, hN3⟩, hlines⟩, hq⟩, htr⟩, hrec⟩, hcx⟩, hc⟩

end CFSG.KC.B3S3K

end
