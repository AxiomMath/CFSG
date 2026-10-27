module

public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.RankThree.Native.ChainCentralizerOrb
public import CFSG.Certificates.NativeSchreierCard
public import Certificates.Data.Kernel.Misc.ChainTailOrb
import CFSG.Certificates.NativeSchreierArrays
import CFSG.Certificates.Kernel.Spor.RawOrbSize
import CFSG.Certificates.Kernel.Spor.RawAgree
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.KC.BfsPin (PP)

theorem relOKK0_of {w BP : ℕ} {XP : ℕ → ℕ} {rels : List (ℕ × ℕ × ℕ)}
    (hr0 : ∀ r ∈ rels, Nat.max r.1 r.2.1 ≠ 0) (ACC q : ℕ) :
    relOKK w (mask w) BP XP rels 0 ACC q = true := by
  unfold relOKK
  rw [List.all_eq_true]
  intro r hr
  cases hm : Nat.beq (Nat.max r.1 r.2.1) 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hm) (hr0 r hr)

theorem relOK0_eq {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    (hxs : ∀ e < xs.size, xs[e]! = unpack n w (XP e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size) (hnb : 0 < nb) {k : ℕ} (hk : k < rcnt (LR 0)) :
    relOK base xs rels 0 (idA n) ((rawLevels n S base)[0]!).pts[k]! =
      relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k) := by
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hw2 : n + 1 < 2 ^ w := hb.2.1
  have hsz : szOK n w = true := (Orb.levelK_facts (hl 0 hnb)).1
  have hbl := Orb.base_lt_of_levels hb hl
  have hbase : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbn : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hbase t ht]
    exact hbl t ht
  obtain ⟨A, -⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hnb (hl 0 hnb)
  obtain ⟨-, -, hR, -, -, -⟩ := Orb.levelK_facts (hl 0 hnb)
  have hI : PP n w (pidn n w) := CFSG.KC.BfsPin.PP.id hsz
  have hacc0 : Ag n w (idA n) (pidn n w) := fun y hy => by rw [idA_get hy, PF.pg_pidn hn24 hw2 hy]
  have hpt : ((rawLevels n S base)[0]!).pts[k]! = rpt w (mask w) (LR 0) k :=
    (A.pt k (by rw [← A.cnt]; exact hk)).symm
  rw [hpt, relOK_eq hbase hbn hxs hrels hnb hacc0 hI.2.1 (hR.pt k hk).1]

theorem ptailBranchK_soundR {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {x : Array ℕ} {X : ℕ}
    (hx : x = unpack n w X) (hX : permB n w X = true) {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    (hxs : ∀ e < xs.size, xs[e]! = unpack n w (XP e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size) {E : List (Array ℕ)} {NE : ℕ} {EP : ℕ → ℕ}
    (hE : E = (List.range NE).map fun e => unpack n w (EP e))
    (hEp : ∀ e < NE, permB n w (EP e) = true) (hnb : 0 < nb) {k : ℕ} (hk : k < rcnt (LR 0))
    (hrel0 : relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k) = true)
    (h : ptailBranchK n w LR TR BP X XP rels NE EP nb k = true) :
    ptailOK n (rawLevels n S base) base x xs rels E (nb - 1) 1
      (compA n (idA n) ((rawLevels n S base)[0]!).tr[k]!) = true := by
  have hn : n < 2 ^ 32 := by have := hb.2.2.1; omega
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hw2 : n + 1 < 2 ^ w := hb.2.1
  have hsz : szOK n w = true := (Orb.levelK_facts (hl 0 hnb)).1
  have hbl := Orb.base_lt_of_levels hb hl
  have hbase : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbn : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hbase t ht]
    exact hbl t ht
  have hXP : PP n w X := pp_of_permB hsz hX
  have hxa : Ag n w x X := by
    rw [hx]
    exact ag_unpack n w X
  have hlev : ∀ i < nb, ((rawLevels n S base)[i]!).pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), ((rawLevels n S base)[i]!).pts[k]! = rpt w (mask w) (LR i) k ∧
        rpt w (mask w) (LR i) k < n ∧ PP n w (TR (roff n (n * w) (LR i) + k)) ∧
        Ag n w (((rawLevels n S base)[i]!).tr[k]!) (TR (roff n (n * w) (LR i) + k)) := by
    intro i hi
    obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    obtain ⟨-, -, hR, -, -, hperm⟩ := Orb.levelK_facts (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨(A.pt k (by rw [← A.cnt]; exact hk)).symm, (hR.pt k hk).1,
      pp_of_permOK hsz (hperm k hk), fun y hy => ?_⟩⟩
    have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨y, hy⟩
    rw [(P k hk).1 ⟨y, hy⟩]
    exact R
  have key : ∀ fuel i, i + fuel = nb → ∀ (acc : Array ℕ) (ACC : ℕ), PP n w ACC →
      Ag n w acc ACC → ptailK n w LR TR BP X XP rels NE EP fuel i ACC = true →
      ptailOK n (rawLevels n S base) base x xs rels E fuel i acc = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro i _ acc ACC hA hacc hk
      have hc : commA n acc x =
          Nat.beq (pcomp n w (mask w) ACC X) (pcomp n w (mask w) X ACC) :=
        eqA_ag (ag_compA hn hacc hxa hXP.2.1) (ag_compA hn hxa hacc hA.2.1) (hA.mul hXP)
          (hXP.mul hA)
      have he : E.any (eqA n acc) = CFSG.KC.LQT.P.anyN NE fun e => Nat.beq ACC (EP e) := by
        rw [hE, anyNP_eq]
        apply Bool.eq_iff_iff.2
        simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
        constructor
        · rintro ⟨e, he, h⟩
          exact ⟨e, he, by
            rwa [eqA_ag hacc (ag_unpack n w (EP e)) hA (pp_of_permB hsz (hEp e he))] at h⟩
        · rintro ⟨e, he, h⟩
          exact ⟨e, he, by
            rwa [eqA_ag hacc (ag_unpack n w (EP e)) hA (pp_of_permB hsz (hEp e he))]⟩
      rw [ptailOK, hc, he]
      exact hk
    | succ fuel ih =>
      intro i hif acc ACC hA hacc hk
      have hi : i < nb := by omega
      obtain ⟨hsz', hpt⟩ := hlev i hi
      have e : ptailK n w LR TR BP X XP rels NE EP (fuel + 1) i ACC = strictB (LR i) fun R =>
          allN (rcnt R) fun k => !(relOKK w (mask w) BP XP rels i ACC (rpt w (mask w) R k)) ||
            ptailK n w LR TR BP X XP rels NE EP fuel (i + 1)
              (pcomp n w (mask w) ACC (TR (roff n (n * w) R + k))) := rfl
      rw [e, Orb.strictB_eq] at hk
      rw [ptailOK, allLt_iff]
      intro k hkc
      rw [hsz'] at hkc
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hpt k hkc
      have hk' := Orb.allN_iff.1 hk k hkc
      rw [hp1, relOK_eq hbase hbn hxs hrels hi hacc hA.2.1 hp2]
      cases hr : relOKK w (mask w) BP XP rels i ACC (rpt w (mask w) (LR i) k)
      · rfl
      · rw [hr, Bool.not_true, Bool.false_or] at hk'
        rw [Bool.not_true, Bool.false_or]
        exact ih (i + 1) (by omega) _ _ (hA.mul hp3) (ag_compA hn hacc hp4 hp3.2.1) hk'
  obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := ⟨nb - 1, by omega⟩
  obtain ⟨-, hpt0⟩ := hlev 0 (by omega)
  obtain ⟨-, -, hp3, hp4⟩ := hpt0 k hk
  unfold ptailBranchK at h
  rw [hrel0, Bool.not_true, Bool.false_or] at h
  have hag : Ag n w (compA n (idA n) (((rawLevels n S base)[0]!).tr[k]!))
      (TR (roff n (n * w) (LR 0) + k)) := fun y hy => by
    rw [compA_get hy, hp4 y hy, idA_get (hp3.2.1 y hy)]
  have e : Nat.sub (m + 1) 1 = m := Nat.add_sub_cancel m 1
  rw [e] at h
  exact key m 1 (by omega) _ _ hp3 hag h

theorem ptailBranchK_sound1 {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {x : Array ℕ} {X : ℕ}
    (hx : x = unpack n w X) (hX : permB n w X = true) {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    (hxs : ∀ e < xs.size, xs[e]! = unpack n w (XP e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size) (hr0 : ∀ r ∈ rels, Nat.max r.1 r.2.1 ≠ 0)
    {E : List (Array ℕ)} {NE : ℕ} {EP : ℕ → ℕ}
    (hE : E = (List.range NE).map fun e => unpack n w (EP e))
    (hEp : ∀ e < NE, permB n w (EP e) = true) (hnb : 0 < nb) {k : ℕ} (hk : k < rcnt (LR 0))
    (h : ptailBranchK n w LR TR BP X XP rels NE EP nb k = true) :
    ptailOK n (rawLevels n S base) base x xs rels E (nb - 1) 1
      (compA n (idA n) ((rawLevels n S base)[0]!).tr[k]!) = true :=
  ptailBranchK_soundR hb hp hl hx hX hxs hrels hE hEp hnb hk (relOKK0_of hr0 _ _) h

end CFSG.KC.Misc.ChainTail

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.Misc.ChainTail
open CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CFSG.Monster.B.Co2 (allLt_iff permOfArr)
open CFSG.Certificates.ChainArrays (lev levPts)

section Codes

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem centOKP_of_orbR {p N kS nb BP ng : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {Q : RawSchreierDatum n}
    {O : Array (Array ℕ)} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hch : 0 < chunks) (hcOK : rawChainOK n O S base W chunks = true) {X : ℕ}
    (hX : permB n w X = true) {rels : List (ℕ × ℕ × ℕ)} (hr : relsK n w p BP X nb rels = true)
    {gs : Array (Array ℕ)} {GC : ℕ → ℕ}
    (hg : BindA n w gs ng GC) (hcomm : commK n w ng X GC = true)
    (hsift : ∀ k < ng, siftA n (rawLevels n S base) base 0 (unpack n w (GC k)) = true)
    {ps : List ℕ} {c : ArrCert} {T : ℕ → ℕ} (hps : ∀ q ∈ ps, q < n)
    (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hnb : 0 < nb) {RK EK : ℕ → ℕ}
    (horb : ∀ k < rcnt (LR 0),
      relOKK w (mask w) BP (pw n w X) rels 0 (pidn n w) (rpt w (mask w) (LR 0) k) = false ∨
      RK k < rcnt (LR 0) ∧ EK k < N ∧
      pg w (mask w) (T (EK k)) (rpt w (mask w) (LR 0) (RK k)) = rpt w (mask w) (LR 0) k ∧
      relOKK w (mask w) BP (pw n w X) rels 0 (pidn n w) (rpt w (mask w) (LR 0) (RK k)) = true ∧
      ptailBranchK n w LR TR BP X (pw n w X) rels N T nb (RK k) = true) :
    centOKP p n S base (unpack n w X) rels gs ps c N = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbp : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbl := Orb.base_lt_of_levels hb hl
  have hbn : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hbp t ht]
    exact hbl t ht
  have hrel := relsOKP_of hw hbs hbp hbn hX hr
  have hrels : ∀ r ∈ rels, r.2.2 < (powPA p n (unpack n w X)).size := by
    intro r hr'
    rw [relsK, List.all_eq_true] at hr
    have := hr r hr'
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    simpa [powPA] using this.1.1.1
  have hQ := (validSchreier_of_chainOK hA hch hcOK).1
  have hF := chainCheckFacts hcOK
  have hnbQ : nb = Q.baseCount := hbs.symm.trans hA.base_size
  have hx := rep_of_validA (validA_of hX)
  unfold commK at hcomm
  rw [Orb.allN_iff] at hcomm
  have hcommA : ∀ k < gs.size, commA n gs[k]! (unpack n w X) = true := by
    intro k hk
    rw [hg.1] at hk
    have hk' := hcomm k hk
    rw [Bool.and_eq_true] at hk'
    rw [hg.2 k hk, commA, comp_unpack' hw hk'.1 hX, comp_unpack' hw hX hk'.1,
      eqA_unpack' hw (permB_pcomp hw hk'.1 hX) (permB_pcomp hw hX hk'.1)]
    exact hk'.2
  have hsiftA : ∀ k < gs.size, siftA n (rawLevels n S base) base 0 gs[k]! = true := by
    intro k hk
    rw [hg.1] at hk
    rw [hg.2 k hk]
    exact hsift k hk
  have hK : Subgroup.closure (permsA n gs) ≤
      Subgroup.centralizer {permOfArr n (unpack n w X)} ⊓ Q.originalSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hc hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (hcommA k hk)
    · exact (siftA_iff_mem_originalSubgroup hA hch hcOK hrep).1 (hsiftA k hk)
  have hKE : ∀ g ∈ Subgroup.closure (permsA n gs), ∃ e ∈ c.pts.toList,
      CFSG.Monster.B.Co2.Rep n e g := by
    intro g hg'
    obtain ⟨i, hi, hre⟩ := enumOK_exists_rep hps hc hg'
    refine ⟨c.pts[i]!, ?_, hre⟩
    rw [getElem!_pos c.pts i hi, ← Array.getElem_toList]
    exact List.getElem_mem _
  have hEK : ∀ e ∈ c.pts.toList, ∃ g ∈ Subgroup.closure (permsA n gs),
      CFSG.Monster.B.Co2.Rep n e g := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i < c.pts.size := by simpa using hi
    have hv : validA n c.pts.toList[i] = true := by
      rw [Array.getElem_toList, ← getElem!_pos c.pts i hi']
      exact (enumOK_spec hps hc).2.2 i hi'
    exact ⟨_, enumOK_mem_of_mem hps hc (rep_of_validA hv) (List.getElem_mem _), rep_of_validA hv⟩
  obtain ⟨A0, -⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hnb (hl 0 hnb)
  obtain ⟨-, -, hR0, -, -, -⟩ := Orb.levelK_facts (hl 0 hnb)
  have h0 : 0 < Q.baseCount := by
    rw [← hnbQ]
    exact hnb
  have horb' : ∀ k < (lev n S base 0).pts.size,
      relOK base (powPA p n (unpack n w X)) rels 0 (idA n)
        ((rawLevels n S base)[0]!).pts[k]! = false ∨
      ∃ r < (lev n S base 0).pts.size,
      ∃ g ∈ Subgroup.closure (permsA n gs), g (levPts Q S base 0 r) = levPts Q S base 0 k ∧
      ptailOK n (rawLevels n S base) base (unpack n w X) (powPA p n (unpack n w X)) rels
        c.pts.toList (Q.baseCount - 1) 1
        (compA n (idA n) ((rawLevels n S base)[0]!).tr[r]!) = true := by
    intro k hk
    have hk' : k < rcnt (LR 0) := by rw [A0.cnt]; exact hk
    rcases horb k hk' with hf | ⟨hR, hE, hpg, hrr, hbr⟩
    · left
      rw [relOK0_eq hb hp hl (powPA_get hw hX) hrels hnb hk']
      exact hf
    right
    have hRl : RK k < (lev n S base 0).pts.size := by rw [← A0.cnt]; exact hR
    have hEv : EK k < c.pts.size := hN ▸ hE
    have hrepE := rep_of_validA (validA_of (hTp _ hE))
    refine ⟨RK k, hRl, permOfArr n (unpack n w (T (EK k))), enumOK_mem hps hc hEv ?_, ?_, ?_⟩
    · rw [hT _ hE]
      exact hrepE
    · apply Fin.ext
      have hq : ((levPts Q S base 0 (RK k) : Fin n) : ℕ) = rpt w (mask w) (LR 0) (RK k) := by
        rw [hA.levPts_val hF h0 hRl]
        exact (A0.pt _ hRl).symm
      rw [hA.levPts_val hF h0 hk, ← hrepE (levPts Q S base 0 (RK k)), hq,
        Orb.unpack_get (hR0.pt _ hR).1, hpg]
      exact A0.pt k hk
    · have := ptailBranchK_soundR hb hp hl rfl hX (powPA_get hw hX) hrels (toList_of hN hT)
        hTp hnb hR hrr hbr
      rw [hnbQ] at this
      exact this
  have htl := ptailOK_of_orbits_rel hA hF hQ hx (rep_powPA hx) (relsOKP_spec hrel) hK hKE hEK h0
    horb'
  unfold centOKP
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hrel, hc⟩, hN⟩, allLt_iff.2 hcommA⟩, allLt_iff.2 hsiftA⟩, by
    rw [hA.base_size]
    exact htl⟩

theorem centOKP_of_orb {p N kS nb BP ng : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {Q : RawSchreierDatum n}
    {O : Array (Array ℕ)} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hch : 0 < chunks) (hcOK : rawChainOK n O S base W chunks = true) {X : ℕ}
    (hX : permB n w X = true) {rels : List (ℕ × ℕ × ℕ)} (hr : relsK n w p BP X nb rels = true)
    (hr0 : ∀ r ∈ rels, Nat.max r.1 r.2.1 ≠ 0) {gs : Array (Array ℕ)} {GC : ℕ → ℕ}
    (hg : BindA n w gs ng GC) (hcomm : commK n w ng X GC = true)
    (hsift : ∀ k < ng, siftA n (rawLevels n S base) base 0 (unpack n w (GC k)) = true)
    {ps : List ℕ} {c : ArrCert} {T : ℕ → ℕ} (hps : ∀ q ∈ ps, q < n)
    (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hnb : 0 < nb) {RK EK : ℕ → ℕ}
    (horb : ∀ k < rcnt (LR 0), RK k < rcnt (LR 0) ∧ EK k < N ∧
      pg w (mask w) (T (EK k)) (rpt w (mask w) (LR 0) (RK k)) = rpt w (mask w) (LR 0) k ∧
      ptailBranchK n w LR TR BP X (pw n w X) rels N T nb (RK k) = true) :
    centOKP p n S base (unpack n w X) rels gs ps c N = true :=
  centOKP_of_orbR hw hb hp hl hA hch hcOK hX hr hg hcomm hsift hps hc hN hT hTp hnb fun k hk =>
    have h := horb k hk
    Or.inr ⟨h.1, h.2.1, h.2.2.1, relOKK0_of hr0 _ _, h.2.2.2⟩

theorem centOKP_of_orbT {p N kS nb BP ng : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {Q : RawSchreierDatum n}
    {O : Array (Array ℕ)} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hch : 0 < chunks) (hcOK : rawChainOK n O S base W chunks = true) {X : ℕ}
    (hX : permB n w X = true) {rels : List (ℕ × ℕ × ℕ)} (hr : relsK n w p BP X nb rels = true)
    {gs : Array (Array ℕ)} {GC : ℕ → ℕ}
    (hg : BindA n w gs ng GC) (hcomm : commK n w ng X GC = true)
    (hsift : ∀ k < ng, siftA n (rawLevels n S base) base 0 (unpack n w (GC k)) = true)
    {ps : List ℕ} {c : ArrCert} {T : ℕ → ℕ} (hps : ∀ q ∈ ps, q < n)
    (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hnb : 0 < nb) {NR : ℕ} {RB RI EK : ℕ → ℕ}
    (hrep : ∀ j < NR, repBranchK n w LR TR BP X (pw n w X) rels N T nb (RB j) = true)
    (horb : ∀ k < rcnt (LR 0), orbRelK n w LR BP (pw n w X) rels N T NR RB RI EK k = true) :
    centOKP p n S base (unpack n w X) rels gs ps c N = true := by
  refine centOKP_of_orbR hw hb hp hl hA hch hcOK hX hr hg hcomm hsift hps hc hN hT hTp hnb
    (RK := fun k => RB (RI k)) (EK := EK) fun k hk => ?_
  have h := horb k hk
  unfold orbRelK at h
  cases hr0 : relOKK w (mask w) BP (pw n w X) rels 0 (pidn n w) (rpt w (mask w) (LR 0) k)
  · exact Or.inl rfl
  · rw [hr0, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hb' := hrep _ h1
    unfold repBranchK at hb'
    rw [Bool.and_eq_true] at hb'
    exact Or.inr ⟨h2, h3, Nat.eq_of_beq_eq_true h4, hb'.1, hb'.2⟩

theorem centOKP_of_orbS {p N kS nb BP ng : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {k : ℕ} (hk : k ≤ S.size)
    (hnd : base.toList.Nodup) {W : Array (List ℤ)} {chunks : ℕ}
    (hch : 0 < chunks) (hcOK : rawChainOK n (S.extract 0 k) S base W chunks = true) {X : ℕ}
    (hX : permB n w X = true) {rels : List (ℕ × ℕ × ℕ)} (hr : relsK n w p BP X nb rels = true)
    {gs : Array (Array ℕ)} {GC : ℕ → ℕ}
    (hg : BindA n w gs ng GC) (hcomm : commK n w ng X GC = true)
    (hsift : ∀ k < ng, siftA n (rawLevels n S base) base 0 (unpack n w (GC k)) = true)
    {ps : List ℕ} {c : ArrCert} {T : ℕ → ℕ} (hps : ∀ q ∈ ps, q < n)
    (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hnb : 0 < nb) {NR : ℕ} {RB RI EK : ℕ → ℕ}
    (hrep : ∀ j < NR, repBranchK n w LR TR BP X (pw n w X) rels N T nb (RB j) = true)
    (horb : ∀ k < rcnt (LR 0), orbRelK n w LR BP (pw n w X) rels N T NR RB RI EK k = true) :
    centOKP p n S base (unpack n w X) rels gs ps c N = true := by
  have hlt : ∀ q ∈ base.toList, q < n := mem_base_lt hb hl
  have hn1 : 1 ≤ n := hb.1
  have hLv : (base.toList.attach.map fun q => (⟨q.1, hlt q.1 q.2⟩ : Fin n)).map Fin.val =
      base.toList := by
    simp
  have hLnd : (base.toList.attach.map fun q => (⟨q.1, hlt q.1 q.2⟩ : Fin n)).Nodup :=
    List.Nodup.of_map Fin.val (by rw [hLv]; exact hnd)
  have hA := chainArrays_ofArrays (n := n) (hn := hn1) (k := k) (hk := hk) (hb := hLnd) (W := W)
    (Orb.isInv_of hb hp)
  have hL : ((base.toList.attach.map fun q => (⟨q.1, hlt q.1 q.2⟩ : Fin n)).map Fin.val).toArray =
      base := by
    rw [hLv, Array.toArray_toList]
  rw [hL] at hA
  exact centOKP_of_orbT hw hb hp hl hA hch hcOK hX hr hg hcomm hsift hps hc hN hT hTp hnb hrep horb

theorem caseOK_of_orb {D : Data} {k : Case} {x : Array ℕ} (hD : D.n = n) {PA PB X : ℕ}
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
    (hr : relsK n w 3 BP X nb k.rels = true) {NR : ℕ} {RB RI EK : ℕ → ℕ}
    (hrep : ∀ j < NR, repBranchK n w LR TR BP X (pw n w X) k.rels N T nb (RB j) = true)
    (horb : ∀ q < rcnt (LR 0), orbRelK n w LR BP (pw n w X) k.rels N T NR RB RI EK q = true)
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
  have hcent := centOKP_of_orbS (p := 3) hw hb hp hl (by omega) hnd (by norm_num) hchain hX hr hg
    hcomm (fun j hj => siftA_of hb hp hl (hsift j hj)) hps he1 he2 he3 hTp' hnb hrep horb
  have hn1 : 1 ≤ n := hb.1
  unfold caseOK
  simp only [hD]
  rw [hA, hB, hx, validA_of hPA, validA_of hPB, validA_of hX, caseChainOK2P, hchain, hS0, hS1,
    eqA_unpack' hw (hPS 0 (by omega)) hPA, eqA_unpack' hw (hPS 1 (by omega)) hPB,
    h0, h1, hcent, powEq_id hw hX, hX3, hcrit _ (by rw [he2]) he3]
  simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hnd, hps⟩, hn1⟩, by omega⟩

end Codes

end CFSG.KC.B3S3K
