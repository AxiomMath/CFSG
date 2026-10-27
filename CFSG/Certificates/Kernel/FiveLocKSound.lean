module

public import Certificates.Data.Kernel.FiveLocK
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.FiveLocK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.K426K
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2 (allLt_iff)

theorem caseChainOK_eq (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (a b u : Array ℕ) : caseChainOK n S base W a b u = caseChainOK3 n S base W a b u := rfl

theorem centOK_eq (n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ) (rels : List (ℕ × ℕ × ℕ))
    (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) (N : ℕ) :
    centOK n S base x rels gs ps c N = centOKP 5 n S base x rels gs ps c N := rfl

theorem normalOK_eq (n : ℕ) (gC gA : Array (Array ℕ)) (ps : List ℕ) (cC cA : ArrCert) (N : ℕ)
    (PL : Array Level) (Pb : Array ℕ) :
    normalOK n gC gA ps cC cA N PL Pb = normalOKP 5 n gC gA ps cC cA N PL Pb := rfl

theorem selfCentOK_eq (n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) :
    selfCentOK n gA cC cA = selfCentOKG n gA cC cA := rfl

theorem zCentOK_eq (n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) (x : Array ℕ) :
    zCentOK n gA cC cA x = zCentOKP 5 n gA cC cA x := rfl

theorem derivedOK_eq (n : ℕ) (gC gD : Array (Array ℕ)) (ps : List ℕ) (cC cD : ArrCert)
    (c d x : Array ℕ) (PL : Array Level) (Pb : Array ℕ) :
    derivedOK n gC gD ps cC cD c d x PL Pb = derivedOKP 5 60 n gC gD ps cC cD c d x PL Pb := rfl

theorem allLt_eq_allN {m : ℕ} {f g : ℕ → Bool} (h : ∀ i < m, f i = g i) : allLt m f = allN m g := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, Orb.allN_iff]
  exact ⟨fun H i hi => (h i hi) ▸ H i hi, fun H i hi => (h i hi).symm ▸ H i hi⟩

section Codes

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem commA_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    commA n (unpack n w p) (unpack n w q) = commK n w p q := by
  rw [commA, comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]
  rfl

theorem linesOK_of {gs xs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {T S LX : ℕ → ℕ}
    (hc : enumOK n gs ps c = true) (hN : c.pts.size = 125)
    (hT : ∀ i < 125, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < 125, permB n w (T i) = true)
    (hx : BindA n w xs 31 LX) (h : lines5K n w 125 31 T S LX = true) :
    linesOK n gs ps c xs = true := by
  unfold lines5K at h
  simp only [Bool.and_eq_true, Orb.allN_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hLp : ∀ j < 31, permB n w (LX j) = true := fun j hj => (h4 j hj).1.1.1
  unfold linesOK
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨hc, hN⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩
  · rw [hT k hk, powEq_id hw (hTp k hk)]
    exact h1 k hk
  · rw [hT k hk, eqA_id hw (hTp k hk), ← h2 k hk, anyNP_eq]
    congr 1
    apply any_range_congr
    intro j hj
    rw [anyNP_eq, hx.2 j hj]
    apply any_range_congr
    intro e _
    rw [pow_unpack' hw (hLp j hj), eqA_unpack' hw (hTp k hk) (permB_ppow hw (hLp j hj) e)]
    rfl
  · intro j' hj'
    have hd := h3 j hj j' hj'
    rw [Bool.or_eq_true] at hd ⊢
    rcases hd with hd | hd
    · exact Or.inl (by rw [Nat.eq_of_beq_eq_true hd]; exact beq_self_eq_true j')
    · right
      rw [allLt_iff]
      intro e he
      rw [hx.2 j hj, hx.2 j' hj', pow_unpack' hw (hLp j' hj'),
        eqA_unpack' hw (hLp j hj) (permB_ppow hw (hLp j' hj') e)]
      exact Orb.allN_iff.1 hd e he
  · obtain ⟨⟨⟨hp, hp5⟩, hne⟩, hm⟩ := h4 j hj
    rw [hx.2 j hj]
    refine ⟨⟨⟨validA_of hp, by rw [powEq_id hw hp]; exact hp5⟩, by rw [eqA_id hw hp]; exact hne⟩,
      any_of_memIdxK hw hN hT hTp hm⟩

theorem transOK_of {H L : Array (Array ℕ)} {rec : List ℕ} {RL : Array Level} {Rb : Array ℕ}
    {HC LC : ℕ → ℕ} (hH : BindA n w H 31 HC) (hL : BindA n w L 31 LC)
    (hLp : ∀ j < 31, permB n w (LC j) = true) (hsift : ∀ j < 31, siftA n RL Rb 0 H[j]! = true)
    (h : transFK n w 31 HC LC rec = true) : transOK n H L rec RL Rb = true := by
  unfold transFK at h
  rw [Orb.allN_iff] at h
  unfold transOK
  rw [allLt_iff]
  intro j hj
  have hj' := h j hj
  rw [Bool.and_eq_true] at hj'
  have hm : rec.getD j 0 % 31 < 31 := Nat.mod_lt _ (by norm_num)
  have hc : permB n w (cj n w (HC j) (LC (rec.getD j 0 % 31))) = true :=
    permB_pcomp hw hj'.1 (permB_pcomp hw (hLp _ hm) (permB_pinvS hw hj'.1))
  rw [hsift j hj, hH.2 j hj, validA_of hj'.1, hL.2 _ hm, hL.2 j hj,
    conj_unpack' hw hj'.1 (hLp _ hm)]
  change (true && true && eqA n (unpack n w (cj n w (HC j) (LC (rec.getD j 0 % 31))))
    (unpack n w (LC j))) = true
  rw [eqA_unpack' hw hc (hLp j hj)]
  exact hj'.2

theorem zPart_of {g : Array (Array ℕ)} {cC : ArrCert} {NC ng X : ℕ} {TC G : ℕ → ℕ}
    (hNC : cC.pts.size = NC) (hTC : ∀ i < NC, cC.pts[i]! = unpack n w (TC i))
    (hTCp : ∀ i < NC, permB n w (TC i) = true) (hg : BindA n w g ng G)
    (hGp : ∀ l < ng, permB n w (G l) = true) (hX : permB n w X = true)
    (h : zPartK n w NC ng X TC G = true) :
    allLt cC.pts.size (fun k => !(allLt g.size fun l => commA n cC.pts[k]! g[l]!) ||
      (List.range 5).any fun e => eqA n cC.pts[k]! (powArr n (unpack n w X) e)) = true := by
  unfold zPartK at h
  rw [Orb.allN_iff] at h
  rw [allLt_iff]
  intro k hk
  rw [hNC] at hk
  rw [← h k hk, hg.1, hTC k hk, anyNP_eq]
  congr 1
  · congr 1
    apply allLt_eq_allN
    intro l hl
    rw [hg.2 l hl, commA_unpack hw (hTCp k hk) (hGp l hl)]
  · apply any_range_congr
    intro e _
    rw [pow_unpack' hw hX, eqA_unpack' hw (hTCp k hk) (permB_ppow hw hX e)]
    rfl

theorem zCentOK_of {gA : Array (Array ℕ)} {cC cA : ArrCert} {NC NA ngA X : ℕ}
    {TC TA SA GA : ℕ → ℕ} (hNA : cA.pts.size = NA) (hTA : ∀ i < NA, cA.pts[i]! = unpack n w (TA i))
    (hTAp : ∀ i < NA, permB n w (TA i) = true) (hNC : cC.pts.size = NC)
    (hTC : ∀ i < NC, cC.pts[i]! = unpack n w (TC i)) (hTCp : ∀ i < NC, permB n w (TC i) = true)
    (hgA : BindA n w gA ngA GA) (hGAp : ∀ l < ngA, permB n w (GA l) = true)
    (hX : permB n w X = true) (hm : memIdxK NA TA SA X = true)
    (h : zPartK n w NC ngA X TC GA = true) :
    zCentOK n gA cC cA (unpack n w X) = true := by
  unfold zCentOK
  rw [any_of_memIdxK hw hNA hTA hTAp hm, Bool.true_and]
  exact zPart_of hw hNC hTC hTCp hgA hGAp hX h

theorem selfCentOK_of {gA : Array (Array ℕ)} {cC cA : ArrCert} {NC NA ngA : ℕ}
    {TC TA SA GA : ℕ → ℕ} (hNA : cA.pts.size = NA) (hTA : ∀ i < NA, cA.pts[i]! = unpack n w (TA i))
    (hTAp : ∀ i < NA, permB n w (TA i) = true) (hNC : cC.pts.size = NC)
    (hTC : ∀ i < NC, cC.pts[i]! = unpack n w (TC i)) (hTCp : ∀ i < NC, permB n w (TC i) = true)
    (hgA : BindA n w gA ngA GA) (hGAp : ∀ l < ngA, permB n w (GA l) = true)
    (h : selfCentK n w ngA NC NA GA TC TA SA = true) :
    selfCentOK n gA cC cA = true := by
  unfold selfCentK at h
  rw [Bool.and_eq_true, Orb.allN_iff, Orb.allN_iff] at h
  obtain ⟨h1, h2⟩ := h
  unfold selfCentOK
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  refine ⟨fun l hl => ?_, fun k hk => ?_⟩
  · rw [hgA.1] at hl
    rw [hgA.1, allLt_eq_allN (g := fun l' => commK n w (GA l) (GA l')) fun l' hl' => by
      rw [hgA.2 l hl, hgA.2 l' hl', commA_unpack hw (hGAp l hl) (hGAp l' hl')]]
    exact h1 l hl
  · rw [hNC] at hk
    have hk' := h2 k hk
    rw [Bool.or_eq_true] at hk' ⊢
    rcases hk' with hk' | hk'
    · left
      rw [hgA.1, hTC k hk, allLt_eq_allN (g := fun l => commK n w (TC k) (GA l)) fun l hl => by
        rw [hgA.2 l hl, commA_unpack hw (hTCp k hk) (hGAp l hl)]]
      exact hk'
    · right
      rw [hTC k hk]
      exact any_of_memIdxK hw hNA hTA hTAp hk'

end Codes

theorem derivedOK_of {n : ℕ} {gC gD : Array (Array ℕ)} {ps : List ℕ} {cC cD : ArrCert}
    {c d x : Array ℕ} {PL : Array Level} {Pb : Array ℕ}
    (hle : derivedLeOK n gC gD ps cD 60 = true) (hc : validA n c = true) (hd : validA n d = true)
    (hcm : cC.pts.toList.any (eqA n c) = true) (hdm : cC.pts.toList.any (eqA n d) = true)
    (hcd : eqA n gC[2]! (commutatorA n c d) = true) (hnc : commA n gD[0]! gD[1]! = false)
    (hs : conjSimpleOK n ps cD = true)
    (hz : allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range 5).any fun e => eqA n cC.pts[k]! (powArr n x e)) = true)
    (hsift : allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!) = true) :
    derivedOK n gC gD ps cC cD c d x PL Pb = true := by
  unfold derivedLeOK at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hle
  unfold derivedOK
  rw [h1, h2, hc, hd, hcm, hdm, hcd, h3, h4, hnc, hs, hz, hsift]
  rfl

end CFSG.KC.FiveLocK

end
