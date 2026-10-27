module

public import CFSG.Sporadic.J4.QT2LocHNative
import CFSG.Certificates.Kernel.J4Q.ConjBFS

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem closure_sound {seeds : List (List Nat)} {fuel n s : Nat} {TS : Nat → List Nat}
    {PAR LAB : Nat → Nat} {TT : Nat → Nat → Nat}
    (_hseeds : seeds.eraseDups = (List.range s).map TS) (_hsn : s ≤ n)
    (_hdist : ∀ i < n, ∀ j < n, TS i = TS j → i = j)
    (_htree : ∀ k, s ≤ k → k < n → PAR k < k ∧ LAB k < 6 ∧
      TS k = letConj (letters.getD (LAB k) 0) (TS (PAR k)))
    (_hclos : ∀ k < n, ∀ g < 6, TT k g < n ∧ letConj (letters.getD g 0) (TS k) = TS (TT k g))
    (_hord : ∀ k, s ≤ k → k + 1 < n → PAR k * 6 + LAB k < PAR (k + 1) * 6 + LAB (k + 1))
    (_hfirst : ∀ k < n, ∀ g < 6, TT k g < s ∨ PAR (TT k g) * 6 + LAB (TT k g) ≤ k * 6 + g)
    (_hfuel : n ≤ fuel) :
    (closureConjT seeds fuel).toList = (List.range n).map TS := by
  rw [ConjBFS.closureConjT_eq, ConjBFS.gbfs_sound (key := id) (mkSeed := id)
    (mkNew := fun u _ _ => u) (fun _ => rfl) (fun _ _ _ => rfl) _hseeds _hsn _hdist _htree _hclos
    _hord _hfirst _hfuel]
  apply List.map_congr_left
  intro k _
  unfold ConjBFS.entry
  split <;> rfl

end CFSG.KC.J4Q

end
