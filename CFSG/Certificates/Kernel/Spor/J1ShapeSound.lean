module

public import Certificates.Data.Kernel.Spor.J1Shape
public import CFSG.Sporadic.Schreier.J1CertCheckInputs
import CFSG.Certificates.Kernel.Spor.ImageListSound

public section

namespace CFSG.KS.J1Shape

open CFSG.KS CFSG.KS.Co2Shape CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

theorem sylowPrimes_eq : ∀ l : List SylowRecord,
    List.rec (motive := fun _ => List Nat) [] (fun s _ ih => List.cons s.prime ih) l =
      l.map (·.prime)
  | [] => rfl
  | s :: l => congrArg (List.cons s.prime) (sylowPrimes_eq l)

theorem isPermList_of_permL {n : Nat} {l : List Nat} (h : permL n l = true) :
    isPermList n l = true :=
  permBody_of_permL h

theorem j1ShapeK_sound {r : J1CertificateFile} (hg : r.group = "J1") (h : j1ShapeK r = true) :
    r.shapeOK = true := by
  unfold j1ShapeK at h
  simp only [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, eqNL_iff, sylowPrimes_eq, List.all_eq_true,
    Nat.ble_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  unfold J1CertificateFile.shapeOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hg⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, ?_⟩, h11⟩, ?_⟩
  · rintro a (ha | ha)
    · exact isPermList_of_permL (h9 a ha)
    · exact isPermList_of_permL (h10 a ha)
  · intro s hs
    obtain ⟨hs1, hs2⟩ := h12 s hs
    exact ⟨fun g hg => isPermList_of_permL (hs1 g hg),
      fun ng hng => ⟨isPermList_of_permL (hs2 ng hng).1, (hs2 ng hng).2⟩⟩

end CFSG.KS.J1Shape

end
