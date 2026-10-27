module

public import Certificates.Data.Kernel.J2ModelK
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.J2ModelK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.KC.Odd87CCK CFSG.Sporadic.Th.Native CFSG.Quasithin.Kleidman.ThreeLocal.J2Model
open CFSG.KC.Child3 (tabP tabP_size)

variable {n w A B : Nat}

theorem beq_tabP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    (tabP n w a == tabP n w b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · cases e : (tabP n w a == tabP n w b)
    · rfl
    · have he : tabP n w a = tabP n w b := eq_of_beq e
      obtain ⟨-, hw, sa, -⟩ := PF.canon_facts ha.1
      obtain ⟨-, -, sb, -⟩ := PF.canon_facts hb.1
      have hab : a = b := PF.eq_of_fields (PF.w_pos hw) sa sb fun i hi => by
        rw [← ap_tabP' ha hi, ← ap_tabP' hb hi, he]
      rw [hab, Nat.beq_refl] at h
      exact absurd h (by decide)
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem wordT_tabP_of (hsz : szOK n w = true) {gens : ℤ → Table} {G : ℤ → Nat} :
    ∀ wd : List ℤ, (∀ l ∈ wd, gens l = tabP n w (G l) ∧ PP n w (G l)) →
      wordT n gens wd = tabP n w (pword n w G wd) ∧ PP n w (pword n w G wd)
  | [], _ => ⟨idT_tabP hsz, PP.id hsz⟩
  | l :: wd, h => by
    obtain ⟨ih, ihp⟩ := wordT_tabP_of hsz wd fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hl, hlp⟩ := h l List.mem_cons_self
    have e : wordT n gens (l :: wd) = (wordT n gens wd).map (fun t => (gens l)[t.toNat]!) := rfl
    refine ⟨?_, hlp.pc ihp⟩
    rw [e, ih, map_eq_compT (tabP_size n w _), hl, compT_tabP' hlp ihp]
    rfl

theorem PP_genK (hA : PP n w A) (hB : PP n w B) (z : ℤ) : PP n w (genK n w A B z) := by
  unfold genK
  split_ifs
  · exact hA
  · exact hA.pinv
  · exact hB
  · exact hB.pinv

theorem PP_uK (hsz : szOK n w = true) (hA : PP n w A) (hB : PP n w B) (k : Nat) :
    PP n w (uK n w A B k) := PP_pword hsz (PP_genK hA hB) _

theorem PP_letK (hsz : szOK n w = true) (hA : PP n w A) (hB : PP n w B) (z : ℤ) :
    PP n w (letK n w A B z) := by
  unfold letK
  split
  · exact PP_uK hsz hA hB _
  · exact (PP_uK hsz hA hB _).pinv

theorem range_map_get {f : Nat → Table} {k : Nat} (hk : k < 7) :
    ((Array.range 7).map f)[k]! = f k := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, Array.getElem_range]

theorem ap_tabP_eq {X : Nat} (hX : PP n w X) {i : Nat} (hi : i < n) : ap (tabP n w X) i = papK w X i :=
  ap_tabP' hX hi

theorem movesSome_tabP {X : Nat} (hX : PP n w X) : movesSome n (tabP n w X) = movesK n w X := by
  unfold movesSome movesK
  exact any_congr' fun i hi => by rw [ap_tabP_eq hX (List.mem_range.1 hi)]

theorem differSome_tabP {X Y : Nat} (hX : PP n w X) (hY : PP n w Y) :
    differSome n (tabP n w X) (tabP n w Y) = differK n w X Y := by
  unfold differSome differK
  exact any_congr' fun i hi => by
    rw [ap_tabP_eq hX (List.mem_range.1 hi), ap_tabP_eq hY (List.mem_range.1 hi)]

theorem lettersOK_spec {wd : List ℤ} (h : lettersOK wd = true) :
    ∀ z ∈ wd, z ≠ 0 ∧ z.natAbs ≤ 7 := by
  intro z hz
  have := List.all_eq_true.1 h z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem modelCheckAt_of_modelK (hsz : szOK n w = true) {gen : ℤ → Table}
    (hgen : ∀ z, gen z = tabP n w (genK n w A B z)) (h : modelK n w A B = true) :
    modelCheckAt n gen = true := by
  unfold modelK at h
  simp only [Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  obtain ⟨hpA, hpB, lf, lt, lt', la, lb, lr, hr, ha7, hb7, htt, htt', hcomm, hm1, hm2, hdiff, hf5,
    hmf, hc1, hc2⟩ := h
  have hA := pp_of_permB hsz hpA
  have hB := pp_of_permB hsz hpB
  have hG := PP_genK hA hB
  have hTu : modelTu n gen = (Array.range 7).map fun k => tabP n w (uK n w A B k) := by
    unfold modelTu uTab2 uK
    exact Array.map_congr_left fun k _ => wordT_tabP hsz hgen hG _
  have hTui : modelTui n gen = (Array.range 7).map fun k => tabP n w (pinv n w (uK n w A B k)) := by
    unfold modelTui
    rw [hTu, Array.map_map]
    exact Array.map_congr_left fun k _ => invT_tabP (PP_uK hsz hA hB k)
  have hL : ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ 7 →
      letTab (modelTu n gen) (modelTui n gen) z = tabP n w (letK n w A B z) := by
    intro z hz0 hz7
    unfold letTab letK
    rw [hTu, hTui]
    split
    · rw [range_map_get (by omega)]
    · rw [range_map_get (by omega)]
  have hW : ∀ wd, lettersOK wd = true →
      wordT n (letTab (modelTu n gen) (modelTui n gen)) wd = tabP n w (pword n w (letK n w A B) wd) ∧
        PP n w (pword n w (letK n w A B) wd) := fun wd hl =>
    wordT_tabP_of hsz wd fun l hlw =>
      ⟨hL l (lettersOK_spec hl l hlw).1 (lettersOK_spec hl l hlw).2, PP_letK hsz hA hB l⟩
  obtain ⟨ef, pf⟩ := hW _ lf
  obtain ⟨et, pt⟩ := hW _ lt
  obtain ⟨et', pt'⟩ := hW _ lt'
  obtain ⟨ea, pa⟩ := hW _ la
  obtain ⟨eb, pb⟩ := hW _ lb
  have pI := PP.id hsz
  unfold modelCheckAt
  simp only [Bool.and_eq_true, List.all_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk7 : k < 7 := List.mem_range.1 hk
    rw [hTu, hTui, range_map_get hk7, range_map_get hk7, ← invT_tabP (PP_uK hsz hA hB k)]
    exact invOK_tabP (PP_uK hsz hA hB k)
  · intro r hr'
    obtain ⟨e, p⟩ := hW _ (lr r hr')
    rw [e, idT_tabP hsz, beq_tabP p pI]
    exact hr r hr'
  · rw [ea, hgen, beq_tabP pa (hG 1)]
    exact ha7
  · rw [eb, hgen, beq_tabP pb (hG 2)]
    exact hb7
  · rw [et, compT_tabP' pt pt, idT_tabP hsz, beq_tabP (pt.pc pt) pI]
    exact htt
  · rw [et', compT_tabP' pt' pt', idT_tabP hsz, beq_tabP (pt'.pc pt') pI]
    exact htt'
  · rw [et, et', compT_tabP' pt pt', compT_tabP' pt' pt, beq_tabP (pt.pc pt') (pt'.pc pt)]
    exact hcomm
  · rw [et, movesSome_tabP pt]
    exact hm1
  · rw [et', movesSome_tabP pt']
    exact hm2
  · rw [et, et', differSome_tabP pt pt']
    exact hdiff
  · rw [ef, powT_tabP pf, idT_tabP hsz, beq_tabP (PP_ppw pf 5) pI]
    exact hf5
  · rw [ef, movesSome_tabP pf]
    exact hmf
  · rw [ef, et, compT_tabP' pf pt, compT_tabP' pt pf, beq_tabP (pf.pc pt) (pt.pc pf)]
    exact hc1
  · rw [ef, et', compT_tabP' pf pt', compT_tabP' pt' pf, beq_tabP (pf.pc pt') (pt'.pc pf)]
    exact hc2

end CFSG.KC.J2ModelK
