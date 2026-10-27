module

public import CFSG.Certificates.Kernel.U6Sound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data
public import Certificates.Data.Kernel.U6.Sec3K

public section

namespace CFSG.KC.U6Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.KS CFSG.KS.Raw CFSG.KC.Enum CFSG.KC.U6
open CFSG.F4.Native

theorem mulVecC_eq {C : Array ℕ} {M v : ℕ} (hC : C = decA M 2 36) (_hv : v < 4096) :
    mulVecC C v = mvK M v ∧ mvK M v < 4096 := by
  let f : ℕ → ℕ := fun r => CFSG.KC.F4M.xorN 6 fun j =>
    CFSG.KC.F4M.fm (CFSG.KLie.CT.fget M (Nat.add (Nat.mul 6 r) j) 2) (crd v j)
  have hf : ∀ r, f r < 4 := fun r => Snd.xorN_lt _ (fun _ => Snd.fm_lt _ _) 6
  obtain ⟨e, b⟩ := Snd.orN_sum f hf 6
  have hrow : ∀ r < 6, f r = rowC C v r := by
    intro r hr
    have hent : ∀ j < 6, CFSG.KC.F4M.fm (CFSG.KLie.CT.fget M (Nat.add (Nat.mul 6 r) j) 2)
        (crd v j) = f4mul C[6 * r + j]! (coord v j) := by
      intro j hj
      rw [hC, Snd.decA_get M 2 36 _ (by omega), Snd.crd_eq]
      exact Snd.fm_eq (Snd.fget_lt _ _ 2) (Snd.coord_lt v j)
    simp only [f, Snd.xorN_eq, List.range_succ, List.range_zero, List.nil_append,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_xor]
    rw [hent 0 (by norm_num), hent 1 (by norm_num), hent 2 (by norm_num), hent 3 (by norm_num),
      hent 4 (by norm_num), hent 5 (by norm_num)]
    rfl
  have em : mvK M v = (List.range 6).foldl (fun acc i => acc + f i * 4 ^ i) 0 := e
  refine ⟨?_, em ▸ b⟩
  rw [em]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [hrow 0 (by norm_num), hrow 1 (by norm_num), hrow 2 (by norm_num), hrow 3 (by norm_num),
    hrow 4 (by norm_num), hrow 5 (by norm_num), mulVecC]
  ring

theorem normC_eq {c : ℕ} (_hc : c < 4096) : normC c = normK c ∧ normK c < 4096 := by
  obtain ⟨e, b⟩ := Snd.normK_eq c
  exact ⟨e.symm, e ▸ b⟩

theorem tabC_eq {C : Array ℕ} {QM QIM M UP POS P : ℕ} (hQ : qmCodes = decA QM 2 36)
    (hQI : qimCodes = decA QIM 2 36) (hC : C = decA M 2 36) (hu : decA UP 12 693 = uPts)
    (hp : decA POS 10 4096 = uPos) (hk : tabK QM QIM M UP POS P = true) :
    tabC C = unpack 693 10 P := by
  apply Array.ext (by simp [tabC, unpack])
  intro i h1 h2
  have hi : i < 693 := by simpa [tabC] using h1
  simp only [tabC, unpack, Array.getElem_ofFn]
  have hx := Nat.eq_of_beq_eq_true (allN_spec hk i hi)
  have hup : (uPts ())[i]! = up UP i := by
    rw [← hu, decA, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    rfl
  have hu4 : up UP i < 4096 :=
    Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  obtain ⟨e1, b1⟩ := mulVecC_eq hQI hu4
  obtain ⟨e2, b2⟩ := mulVecC_eq hC b1
  obtain ⟨e3, b3⟩ := mulVecC_eq hQ b2
  obtain ⟨e4, b4⟩ := normC_eq b3
  rw [hup, e1, e2, e3, e4, hx]
  have hpos : (uPos ())[normK (mvK QM (mvK M (mvK QIM (up UP i))))]! =
      (uPts ()).toList.idxOf (normK (mvK QM (mvK M (mvK QIM (up UP i))))) := by
    rw [uPos, getElem!_pos _ _ (by simpa using b4), Array.getElem_ofFn]
  rw [← hpos, ← hp, decA, getElem!_pos _ _ (by simpa using b4), Array.getElem_ofFn]
  rfl

end CFSG.KC.U6Sec3

end
