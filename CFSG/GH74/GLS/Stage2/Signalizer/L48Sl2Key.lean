module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2KeyPSL

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem sl2Key : SL2Key := by
  intro F _ _ hodd L _ he a ha2 ha1 p hp hp2 Y hY hN y hy
  obtain ⟨e⟩ := he
  have : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h
    have h1 := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  let e' : L ≃* SL(2, F) := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  let φ : L ⧸ center L ≃* PSL(2, F) :=
    QuotientGroup.congr (center L) (Subgroup.center SL(2, F)) e' (Subgroup.map_center_eq e')
  have hY' : IsPGroup p (Y.map φ.toMonoidHom) :=
    hY.of_equiv (Y.equivMapOfInjective φ.toMonoidHom φ.injective)
  have hN' : ∀ c : PSL(2, F), c * φ a = φ a * c →
      c ∈ normalizer (Y.map φ.toMonoidHom : Set PSL(2, F)) := by
    intro c hc
    obtain ⟨c, rfl⟩ := φ.surjective c
    rw [← map_mul, ← map_mul] at hc
    rw [CFSG.GH74.GLS.IVK.L2Borel.normalizer_map_equiv, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
    exact hN c (φ.injective hc)
  have key := psl2Key hp hp2 hF (by rw [← map_mul, ha2, map_one])
    (fun h => ha1 (φ.injective (by rw [h, map_one]))) hY' hN' (φ y)
    (Subgroup.mem_map_of_mem _ hy)
  rw [← map_mul, ← map_mul] at key
  exact φ.injective key

end CFSG.GH74.GLS.Stage2.Signalizer.L48
