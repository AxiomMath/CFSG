module

public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.RawCard
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.Misc.ChainTail
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CFSG.Monster.B.Co2 (permOfArr)

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem perm_of_bfsK {ng N : ℕ} {G T E S : ℕ → ℕ} (hp : ∀ k < ng, permB n w (G k) = true)
    (hk : bfsK n w ng G N T E S = true) : allN N (fun i => permB n w (T i)) = true :=
  Orb.allN_iff.2 (bfsK_points (fun y => permB n w y = true) (permB_id hw)
    (fun _ hy k hk' => permB_pcomp hw (hp k hk') hy) hk).2.2.1

theorem caseOK_of_card {D : Data} {k : Case} {x : Array ℕ} (hD : D.n = n) {PA PB X : ℕ}
    (hA : D.A = unpack n w PA) (hB : D.B = unpack n w PB) (hPA : permB n w PA = true)
    (hPB : permB n w PB = true) (hx : x = unpack n w X) (hX : permB n w X = true)
    (hX3 : Nat.beq (pw n w X 3) (pidn n w) = true)
    {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Dw : List (List ℤ)}
    (hb : Binds n w PS kS nb BP k.S k.base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS 2 Dw nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hord : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 => permOfArr n k.S[j.val]!)) ≤
      (rawOrbitSizes n k.S k.base).prod)
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
  have hchain := rawChainK_of_card (chunks := 1) hb hh hl hord
  rw [hW] at hchain
  have hS0 : k.S[0]! = unpack n w (PS 0) := hb.2.2.2.2.1 0 (by omega)
  have hS1 : k.S[1]! = unpack n w (PS 1) := hb.2.2.2.2.1 1 (by omega)
  have hcent := centOKP_of (p := 3) hw hb hp hl hX hr hg hcomm
    (fun j hj => siftA_of hb hp hl (hsift j hj)) he1 he2 he3 hTp' hnb htail
  have hsz : k.S.size = kS := hb.2.2.2.1
  have hn1 : 1 ≤ n := hb.1
  unfold caseOK
  simp only [hD]
  rw [hA, hB, hx, validA_of hPA, validA_of hPB, validA_of hX, caseChainOK2P, hchain, hS0, hS1,
    eqA_unpack' hw (hPS 0 (by omega)) hPA, eqA_unpack' hw (hPS 1 (by omega)) hPB,
    h0, h1, hcent, powEq_id hw hX, hX3, hcrit _ (by rw [he2]) he3]
  simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hnd, hps⟩, hn1⟩, by omega⟩

end CFSG.KC.B3S3K

end
