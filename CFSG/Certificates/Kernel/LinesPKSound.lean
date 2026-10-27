module

public import Certificates.Data.Kernel.LinesPK
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.K426KSound

public section

namespace CFSG.KC.LinesPK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.K426K
  CFSG.KC.FiveLocK
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2 (allLt_iff)

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem linesOKG_of {p N r : ℕ} {gs xs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    {T S LX : ℕ → ℕ} (hc : enumOK n gs ps c = true) (hN : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack n w (T i)) (hTp : ∀ i < N, permB n w (T i) = true)
    (hx : BindA n w xs r LX) (h : linesPK n w p N r T S LX = true) :
    linesOKG p N r n gs ps c xs = true := by
  unfold linesPK at h
  simp only [Bool.and_eq_true, Orb.allN_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hLp : ∀ j < r, permB n w (LX j) = true := fun j hj => (h4 j hj).1.1.1
  unfold linesOKG
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
  · obtain ⟨⟨⟨hp, hpp⟩, hne⟩, hm⟩ := h4 j hj
    rw [hx.2 j hj]
    refine ⟨⟨⟨validA_of hp, by rw [powEq_id hw hp]; exact hpp⟩, by rw [eqA_id hw hp]; exact hne⟩,
      any_of_memIdxK hw hN hT hTp hm⟩

theorem transOKG_of {r : ℕ} {H L : Array (Array ℕ)} {rec : List ℕ} {RL : Array Level}
    {Rb : Array ℕ} {HC LC : ℕ → ℕ} (hr : 0 < r) (hH : BindA n w H r HC) (hL : BindA n w L r LC)
    (hLp : ∀ j < r, permB n w (LC j) = true) (hsift : ∀ j < r, siftA n RL Rb 0 H[j]! = true)
    (h : transFK n w r HC LC rec = true) : transOKG r n H L rec RL Rb = true := by
  unfold transFK at h
  rw [Orb.allN_iff] at h
  unfold transOKG
  rw [allLt_iff]
  intro j hj
  have hj' := h j hj
  rw [Bool.and_eq_true] at hj'
  have hm : rec.getD j 0 % r < r := Nat.mod_lt _ hr
  have hc : permB n w (cj n w (HC j) (LC (rec.getD j 0 % r))) = true :=
    permB_pcomp hw hj'.1 (permB_pcomp hw (hLp _ hm) (permB_pinvS hw hj'.1))
  rw [hsift j hj, hH.2 j hj, validA_of hj'.1, hL.2 _ hm, hL.2 j hj,
    conj_unpack' hw hj'.1 (hLp _ hm)]
  change (true && true && eqA n (unpack n w (cj n w (HC j) (LC (rec.getD j 0 % r))))
    (unpack n w (LC j))) = true
  rw [eqA_unpack' hw hc (hLp j hj)]
  exact hj'.2

end CFSG.KC.LinesPK

end
