module

public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique.Setup.Lift

section Direct

variable {H : Type*} [Group H] {ι : Type*} [Fintype ι] (L : ι → Subgroup H)

theorem natCard_iSup_eq_prod [Finite H]
    (hcomm : Pairwise fun i j => ∀ x y : H, x ∈ L i → y ∈ L j → Commute x y)
    (hind : iSupIndep L) : Nat.card ↥(⨆ i, L i) = ∏ i, Nat.card ↥(L i) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm),
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]

variable [DecidableEq ι]

theorem noncommPiCoprod_eq_mul_update
    (hcomm : Pairwise fun i j => ∀ x y : H, x ∈ L i → y ∈ L j → Commute x y)
    (x : ∀ i, L i) (i : ι) :
    Subgroup.noncommPiCoprod hcomm x =
      (x i : H) * Subgroup.noncommPiCoprod hcomm (Function.update x i 1) := by
  have hx : Pi.mulSingle i (x i) * Function.update x i 1 = x := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
  conv_lhs => rw [← hx]
  rw [map_mul]
  congr 1
  exact Subgroup.noncommPiCoprod_mulSingle _ _

theorem commute_noncommPiCoprod_update
    (hcomm : Pairwise fun i j => ∀ x y : H, x ∈ L i → y ∈ L j → Commute x y)
    (x : ∀ i, L i) (i : ι) {k : H} (hk : k ∈ L i) :
    Commute k (Subgroup.noncommPiCoprod hcomm (Function.update x i 1)) := by
  have h : Subgroup.noncommPiCoprod hcomm (Function.update x i 1) ∈ Subgroup.centralizer {k} := by
    rw [Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self]
    · rw [Function.update_of_ne hj, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm hj _ _ (x j).2 hk).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

end Direct

end CFSG.QuasithinUnique.Setup.Lift
