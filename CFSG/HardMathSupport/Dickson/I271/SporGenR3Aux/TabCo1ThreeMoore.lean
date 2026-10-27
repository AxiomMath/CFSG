module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Gen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeQuasi
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeDRoot
public import Certificates.Certificate17331

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Matrix

section Data


noncomputable def mooreM (j : ℕ) : GL24 := kG TabCo1ThreeMoore.ext (87 + j)

theorem mooreM_mem (j : ℕ) : mooreM j ∈ GA := kG_mem _ _

theorem moore_data {x : GL24} (hx : MRep (rootRows3D ()) x) :
    x ≠ 1 ∧ x ^ 3 = 1 ∧ (∀ j, 1 ≤ j → j ≤ 7 → x * mooreM j = mooreM j * x) ∧
      CFSG.Sporadic.SchreierLemmas.IsMooreFamily 7 mooreM ∧ mooreM 1 ≠ 1 := by
  have h := (Certificates.certificate17331 : mooreCheck () = true)
  simp only [mooreCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc, List.all_eq_true, List.mem_range] at h
  obtain ⟨hD, hwx, hw1, hx1, hx3, hcomm, hwm, hm3, hm1, hsq, hcube, hdist⟩ := h
  have rm : ∀ j, MRep (nd (kDag TabCo1ThreeMoore.ext) (87 + j)) (mooreM j) := fun j =>
    rep_nd (ext := TabCo1ThreeMoore.ext) hD (87 + j)
  refine ⟨ne_one_of_rep hx hwx hw1 hx1, (hx.pow 3).eq (by rw [hx3]; exact MRep.one), ?_,
    ⟨?_, ?_, ?_, ?_⟩, ne_one_of_rep (rm 1) hwm hw1 hm1⟩
  · intro j hj1 hj7
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (hx.mul (rm (k + 1))).eq (by rw [hcomm k (by omega)]; exact (rm (k + 1)).mul hx)
  · exact ((rm 1).pow 3).eq (by rw [hm3]; exact MRep.one)
  · intro j hj2 hj7
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    exact ((rm (k + 2)).pow 2).eq (by rw [hsq k (by omega)]; exact MRep.one)
  · intro j hj2 hj7
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have e : k + 2 - 1 = k + 1 := by omega
    rw [e]
    exact (((rm (k + 1)).mul (rm (k + 2))).pow 3).eq
      (by rw [hcube k (by omega)]; exact MRep.one)
  · intro i j hi hij hj7
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
    exact (((rm (a + 1)).mul (rm (b + 1))).pow 2).eq
      (by rw [hdist a (by omega) b (by omega) (by omega)]; exact MRep.one)

end Data

section Final


theorem tabCo1_threeD
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group))
    (x : ↥GA) (hx : MRep (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 2)
      (x : GL24)) :
    ShapeRkAt 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) x := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨hx1, hx3, hxy, hM, hy1⟩ := moore_data (x := (x : GL24)) hx
  have hpres := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
    (by norm_num) mooreM hM).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hy1⟩
  obtain ⟨-, ⟨e⟩⟩ := hpres
  set L : Subgroup GL24 := Subgroup.closure (mooreM '' Set.Icc 1 (9 - 2)) with hL
  have hLC : L ≤ Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hxy j hj1 (by omega)).symm, mooreM_mem j⟩
  obtain ⟨hs, hnab, hcardL⟩ := alt9_subgroup_data e
  have hbound : Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) ≤
      3 * Nat.card ↥L := by
    rw [← card_centralizer_GA_eq_inf GA x, hcardL]
    exact TabCo1ThreeDRoot.card_cent_threeD_root_le x hx
  exact shapeRkAt_of_bound Nat.prime_three (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) GA x L hLC hs hnab (by rw [hcardL]; norm_num)
    hx1 hx3 hbound (GoodSpor.of_equiv e goodSpor_three_alt9)
    (RkSpor.of_equiv e (rkSpor_Suz_alt9 hb))

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
