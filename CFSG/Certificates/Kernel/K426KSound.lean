module

public import Certificates.Data.Kernel.K426K
public import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

namespace CFSG.KC.K426K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2 (allLt_iff)

private theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem memIdxK_spec {N : ℕ} {T S : ℕ → ℕ} {x : ℕ} (h : memIdxK N T S x = true) :
    ∃ j < N, x = T j := by
  unfold memIdxK at h
  rw [strictB_eq'] at h
  generalize idxK N T S x = j at h
  cases hj : Nat.blt j N
  · rw [hj] at h
    exact absurd (h : false = true) Bool.false_ne_true
  · rw [hj] at h
    exact ⟨j, by simpa [Nat.blt_eq] using hj, Nat.eq_of_beq_eq_true h⟩

theorem allN_of_blocks {f : ℕ → Bool} {L K : ℕ}
    (h : ∀ s < K, allN L (fun j => f (Nat.add (Nat.mul L s) j)) = true) :
    allN (L * K) f = true := by
  rw [Orb.allN_iff]
  intro a ha
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by simp [h0] at ha
  have hs : a / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at ha)
  have := Orb.allN_iff.1 (h (a / L) hs) (a % L) (Nat.mod_lt a hL)
  change f (L * (a / L) + a % L) = true at this
  rwa [Nat.div_add_mod] at this

theorem siftA_of_siftOK {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {G : ℕ}
    (h : siftOK n w nb LR TRI BP G = true) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) = true := by
  unfold siftOK at h
  rw [bAnd_iff, bAnd_iff] at h
  exact siftA_of hb hp hl ⟨h.1, h.2.1, h.2.2⟩

section Codes

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem any_of_memIdxK {N : ℕ} {T S : ℕ → ℕ} {pts : Array (Array ℕ)} (hN : pts.size = N)
    (hT : ∀ i < N, pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true) {x : ℕ}
    (h : memIdxK N T S x = true) : pts.toList.any (eqA n (unpack n w x)) = true := by
  obtain ⟨j, hj, rfl⟩ := memIdxK_spec h
  rw [List.any_eq_true]
  refine ⟨pts[j]!, ?_, ?_⟩
  · rw [getElem!_pos pts j (by omega)]
    exact Array.getElem_mem_toList _
  · rw [hT j hj, eqA_unpack' hw (hTp j hj) (hTp j hj)]
    exact Nat.beq_refl _

omit hw in
theorem ptailIdxK_le {LR TR : ℕ → ℕ} {BP X : ℕ} {XP : ℕ → ℕ} {rels : List (ℕ × ℕ × ℕ)}
    {NE : ℕ} {EP ES : ℕ → ℕ} :
    ∀ f i acc, ptailIdxK n w LR TR BP X XP rels NE EP ES f i acc = true →
      ptailK n w LR TR BP X XP rels NE EP f i acc = true := by
  intro f
  induction f with
  | zero =>
    intro i acc h
    change (!(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) ||
      memIdxK NE EP ES acc) = true at h
    change (!(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) ||
      CFSG.KC.LQT.P.anyN NE fun e => Nat.beq acc (EP e)) = true
    rw [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨j, hj, e⟩ := memIdxK_spec h
      rw [anyNP_eq, List.any_eq_true]
      exact ⟨j, List.mem_range.2 hj, by rw [e]; exact Nat.beq_refl _⟩
  | succ f ih =>
    intro i acc h
    change strictB (LR i) (fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
        ptailIdxK n w LR TR BP X XP rels NE EP ES f (Nat.succ i)
          (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k)))) = true at h
    change strictB (LR i) (fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
        ptailK n w LR TR BP X XP rels NE EP f (Nat.succ i)
          (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k)))) = true
    rw [strictB_eq', Orb.allN_iff] at h ⊢
    intro k hk
    have hk' := h k hk
    rw [Bool.or_eq_true] at hk' ⊢
    rcases hk' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (ih _ _ h1)

omit hw in
theorem ptailBranchIdxK_le {LR TR : ℕ → ℕ} {BP X : ℕ} {XP : ℕ → ℕ} {rels : List (ℕ × ℕ × ℕ)}
    {NE : ℕ} {EP ES : ℕ → ℕ} {nb m : ℕ}
    (h : allN m (ptailBranchIdxK n w LR TR BP X XP rels NE EP ES nb) = true) :
    allN m (ptailBranchK n w LR TR BP X XP rels NE EP nb) = true := by
  rw [Orb.allN_iff] at h ⊢
  intro k hk
  have hk' := h k hk
  unfold ptailBranchIdxK at hk'
  unfold ptailBranchK
  rw [Bool.or_eq_true] at hk' ⊢
  rcases hk' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (ptailIdxK_le _ _ _ h1)

theorem normalOKP_of {p N NC NA ngC ngA : ℕ} {gC gA : Array (Array ℕ)} {ps : List ℕ}
    {cC cA : ArrCert} {PL : Array Level} {Pb : Array ℕ} {TC SC TA SA GC GA : ℕ → ℕ}
    (hcA : enumOK n gA ps cA = true) (hNA : cA.pts.size = NA)
    (hTA : ∀ i < NA, cA.pts[i]! = unpack n w (TA i)) (hTAp : ∀ i < NA, permB n w (TA i) = true)
    (hNC : cC.pts.size = NC) (hTC : ∀ i < NC, cC.pts[i]! = unpack n w (TC i))
    (hTCp : ∀ i < NC, permB n w (TC i) = true) (hgC : BindA n w gC ngC GC)
    (hGCp : ∀ k < ngC, permB n w (GC k) = true) (hgA : BindA n w gA ngA GA)
    (hGAp : ∀ l < ngA, permB n w (GA l) = true)
    (hsift : ∀ l < ngA, siftA n PL Pb 0 (unpack n w (GA l)) = true) (hN : NA = N)
    (h : normalK n w p NC NA ngC ngA TC SC TA SA GC GA = true) :
    normalOKP p n gC gA ps cC cA N PL Pb = true := by
  subst hN
  unfold normalK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [Orb.allN_iff] at h1 h2 h3
  unfold normalOKP
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hcA, hNA⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hNA] at hk
    rw [hTA k hk, powEq_id hw (hTAp k hk)]
    exact h1 k hk
  · rw [allLt_iff]
    intro l hl
    rw [hgA.1] at hl
    rw [hgA.2 l hl]
    exact any_of_memIdxK hw hNC hTC hTCp (h2 l hl)
  · rw [allLt_iff]
    intro k hk
    rw [hgC.1] at hk
    rw [allLt_iff]
    intro l hl
    rw [hgA.1] at hl
    rw [hgC.2 k hk, hgA.2 l hl, conj_unpack' hw (hGCp k hk) (hGAp l hl)]
    have := Orb.allN_iff.1 (h3 k hk) l hl
    exact any_of_memIdxK hw hNA hTA hTAp this
  · rw [allLt_iff]
    intro l hl
    rw [hgA.1] at hl
    rw [hgA.2 l hl]
    exact hsift l hl

theorem derivedLeOK_of {M ND ngC ngD : ℕ} {gC gD : Array (Array ℕ)} {ps : List ℕ}
    {cD : ArrCert} {TD SD GC GD : ℕ → ℕ}
    (hcD : enumOK n gD ps cD = true) (hND : cD.pts.size = ND)
    (hTD : ∀ i < ND, cD.pts[i]! = unpack n w (TD i)) (hTDp : ∀ i < ND, permB n w (TD i) = true)
    (hgC : BindA n w gC ngC GC) (hGCp : ∀ k < ngC, permB n w (GC k) = true)
    (hgD : BindA n w gD ngD GD) (hGDp : ∀ l < ngD, permB n w (GD l) = true) (hM : ND = M)
    (h : derivedLeK n w ND ngC ngD TD SD GC GD = true) :
    derivedLeOK n gC gD ps cD M = true := by
  subst hM
  unfold derivedLeK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Orb.allN_iff] at h1 h2
  unfold derivedLeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hcD, hND⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hgC.1] at hk
    rw [allLt_iff]
    intro l hl
    rw [hgD.1] at hl
    rw [hgC.2 k hk, hgD.2 l hl, conj_unpack' hw (hGCp k hk) (hGDp l hl)]
    exact any_of_memIdxK hw hND hTD hTDp (Orb.allN_iff.1 (h1 k hk) l hl)
  · rw [allLt_iff]
    intro k hk
    rw [hgC.1] at hk
    rw [allLt_iff]
    intro l hl
    rw [hgC.1] at hl
    have pk := hGCp k hk
    have pl := hGCp l hl
    rw [hgC.2 k hk, hgC.2 l hl, commutatorA, inv_unpack hw pk, inv_unpack hw pl,
      comp_unpack' hw pk pl, comp_unpack' hw (permB_pinvS hw pk) (permB_pinvS hw pl),
      comp_unpack' hw (permB_pcomp hw pk pl) (permB_pcomp hw (permB_pinvS hw pk)
        (permB_pinvS hw pl))]
    exact any_of_memIdxK hw hND hTD hTDp (Orb.allN_iff.1 (h2 k hk) l hl)

end Codes

end CFSG.KC.K426K

end
