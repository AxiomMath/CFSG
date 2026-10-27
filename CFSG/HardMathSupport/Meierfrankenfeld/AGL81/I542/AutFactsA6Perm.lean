module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Equiv Subgroup

@[expose] noncomputable def permAut : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
  (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range

theorem conjNormal_injective_alt6 :
    Function.Injective (MulAut.conjNormal :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))) :=
  CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)

noncomputable def permAutEquiv : Perm (Fin 6) ≃* permAut :=
  MonoidHom.ofInjective conjNormal_injective_alt6

theorem conj_injective_alt6 :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  intro a b h
  apply Subtype.ext
  apply conjNormal_injective_alt6
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val]
  exact h

theorem inn_le_permAut :
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤ permAut := by
  rintro _ ⟨a, rfl⟩
  exact ⟨(a : Perm (Fin 6)), MulAut.conjNormal_val⟩

theorem relIndex_inn_permAut :
    ((MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range).relIndex
      permAut = 2 := by
  have h1 := Subgroup.relIndex_mul_card
    (H := (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range)
    (K := permAut)
  rw [inf_eq_left.2 inn_le_permAut] at h1
  have hI : Nat.card (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
      = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective conj_injective_alt6).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hP : Nat.card permAut = 720 := by
    rw [← Nat.card_congr permAutEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  rw [hI, hP] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (by rw [h1])

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
