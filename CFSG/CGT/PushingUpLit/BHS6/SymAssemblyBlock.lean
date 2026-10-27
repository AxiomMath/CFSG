module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.NatQuot
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] {n : ℕ}

@[expose] def altRestrict {G E : Subgroup Γ} (φ : ↥G →* Equiv.Perm (Fin n)) (hEG : E ≤ G)
    (hEA : ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ alternatingGroup (Fin n)) :
    ↥E →* alternatingGroup (Fin n) where
  toFun e := ⟨φ ⟨e, hEG e.2⟩, hEA e e.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' x y := Subtype.ext (map_mul φ ⟨x, hEG x.2⟩ ⟨y, hEG y.2⟩)

theorem mem_centralizer_of_mem {V : Subgroup Γ} (hV : IsElemAbelian 2 V) {v : Γ} (hv : v ∈ V) :
    v ∈ Subgroup.centralizer (V : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := hV.1.is_comm.comm (⟨w, hw⟩ : ↥V) ⟨v, hv⟩
  exact congrArg Subtype.val h

end CFSG.CGT.PushingUpLit.BHS6
