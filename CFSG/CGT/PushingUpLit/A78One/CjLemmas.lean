module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.T2K.FourSevenA

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G]

theorem cjx_mem (g : G) (X : Subgroup G) (x : G) : x ∈ cj g X ↔ g⁻¹ * x * g ∈ X :=
  mem_map_conj_iff g X x

theorem cjx_cj (a b : G) (Y : Subgroup G) : cj a (cj b Y) = cj (a * b) Y := by
  ext y
  rw [cjx_mem, cjx_mem, cjx_mem]
  have e : (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
  rw [e]

theorem cjx_one (Y : Subgroup G) : cj (1 : G) Y = Y := by
  ext y
  rw [cjx_mem]
  simp

theorem cjx_inv_cj (g : G) (Y : Subgroup G) : cj g⁻¹ (cj g Y) = Y := by
  rw [cjx_cj, inv_mul_cancel, cjx_one]

theorem cjx_cj_inv (g : G) (Y : Subgroup G) : cj g (cj g⁻¹ Y) = Y := by
  rw [cjx_cj, mul_inv_cancel, cjx_one]

theorem cjx_mono {X Y : Subgroup G} (g : G) (h : X ≤ Y) : cj g X ≤ cj g Y :=
  Subgroup.map_mono h

theorem cjx_card (g : G) (X : Subgroup G) : Nat.card ↥(cj g X) = Nat.card ↥X :=
  card_map_conj X g

theorem cjx_isElemAbelian {X : Subgroup G} (hX : IsElemAbelian 2 X) (g : G) :
    IsElemAbelian 2 (cj g X) :=
  isElemAbelian_map_conj hX g

theorem cjx_isMax {Y A : Subgroup G} (g : G) (hA : IsMaxElemAbelian Y A) :
    IsMaxElemAbelian (cj g Y) (cj g A) := by
  refine ⟨cjx_mono g hA.1, cjx_isElemAbelian hA.2.1 g, fun B hB hBe => ?_⟩
  have hB' : cj g⁻¹ B ≤ Y := by
    have := cjx_mono g⁻¹ hB
    rwa [cjx_inv_cj] at this
  have h1 := hA.2.2 (cj g⁻¹ B) hB' (cjx_isElemAbelian hBe g⁻¹)
  rw [cjx_card] at h1
  rw [cjx_card]
  exact h1

theorem cjx_isMax_of_normalizer {Q A : Subgroup G} (hA : IsMaxElemAbelian Q A) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : IsMaxElemAbelian Q (cj g A) :=
  isMaxElemAbelian_map_conj hA hg

theorem cjx_centralizer (g : G) (S : Subgroup G) :
    cj g (Subgroup.centralizer (S : Set G)) =
      Subgroup.centralizer ((cj g S : Subgroup G) : Set G) := by
  ext y
  rw [cjx_mem, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have hs' : g⁻¹ * s * g ∈ S := (cjx_mem g S s).1 hs
    have h1 := h (g⁻¹ * s * g) hs'
    calc s * y = g * (g⁻¹ * s * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = y * s := by group
  · intro h s hs
    have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    have hs' : g * s * g⁻¹ ∈ cj g S := by
      rw [cjx_mem, e]
      exact hs
    have h1 := h (g * s * g⁻¹) hs'
    calc s * (g⁻¹ * y * g) = g⁻¹ * (g * s * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * s * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * y * g * s := by group

theorem cjx_inf (g : G) (X Y : Subgroup G) : cj g (X ⊓ Y) = cj g X ⊓ cj g Y :=
  Subgroup.map_inf X Y _ (MulAut.conj g).injective

theorem cjx_sup (g : G) (X Y : Subgroup G) : cj g (X ⊔ Y) = cj g X ⊔ cj g Y :=
  Subgroup.map_sup _ _ _

theorem cjx_le_normalizer {L X : Subgroup G} {g : G} (hL : L ≤ Subgroup.normalizer (X : Set G))
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : cj g L ≤ Subgroup.normalizer (X : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hL hl)) (Subgroup.inv_mem _ hg)

theorem cjx_bGrp (g : G) (L A : Subgroup G) :
    cj g (Hyp45.bGrp L A) =
      (cj g A ⊓ Subgroup.centralizer ((cj g (blockU L) : Subgroup G) : Set G)) ⊔
        cj g (blockU L) := by
  unfold Hyp45.bGrp
  rw [cjx_sup, cjx_inf, cjx_centralizer]


end CFSG.CGT.PushingUpLit.A78One
