module

import CFSG.GH74.KGroups.L33
import CFSG.GH74.SmallRanks.PSL
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.PSLN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Matrix

abbrev SL33 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

@[expose] def uniM (x y z : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![1, x, z; 0, 1, y; 0, 0, 1]

theorem det_uniM (x y z : ZMod 3) : (uniM x y z).det = 1 := by
  rw [uniM, Matrix.det_fin_three]; simp <;> decide

@[expose] def uni (x y z : ZMod 3) : SL33 := ⟨uniM x y z, det_uniM x y z⟩

theorem uniM_mul (x y z x' y' z' : ZMod 3) :
    uniM x y z * uniM x' y' z' = uniM (x + x') (y + y') (z + z' + x * y') := by
  simp only [uniM, Matrix.mul_fin_three]
  congr 1 <;> ring_nf

theorem uni_mul (x y z x' y' z' : ZMod 3) :
    uni x y z * uni x' y' z' = uni (x + x') (y + y') (z + z' + x * y') :=
  Subtype.ext (uniM_mul x y z x' y' z')

theorem uni_zero : uni 0 0 0 = 1 := by
  apply Subtype.ext
  show uniM 0 0 0 = 1
  rw [uniM, Matrix.one_fin_three]

theorem uni_eq {x y z x' y' z' : ZMod 3} (h1 : x = x') (h2 : y = y') (h3 : z = z') :
    uni x y z = uni x' y' z' := by rw [h1, h2, h3]

theorem uni_inv (x y z : ZMod 3) : uni x y z * uni (-x) (-y) (x * y - z) = 1 := by
  rw [uni_mul, ← uni_zero]
  refine uni_eq ?_ ?_ ?_ <;> revert x y z <;> decide

theorem uni_injective {x y z x' y' z' : ZMod 3} (h : uni x y z = uni x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have h1 := congrArg (fun g : SL33 => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1) h
  have h2 := congrArg (fun g : SL33 => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2) h
  have h3 := congrArg (fun g : SL33 => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2) h
  simp only [uni, uniM] at h1 h2 h3
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

@[expose] def unitri : Subgroup SL33 where
  carrier := {g | ∃ x y z : ZMod 3, uni x y z = g}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, rfl⟩ ⟨x', y', z', rfl⟩
    exact ⟨_, _, _, (uni_mul x y z x' y' z').symm⟩
  one_mem' := ⟨0, 0, 0, uni_zero⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, rfl⟩
    exact ⟨-x, -y, x * y - z, eq_inv_of_mul_eq_one_right (uni_inv x y z)⟩

theorem y_eq_zero {x y z : ZMod 3} (h : uni 1 0 0 * uni x y z = uni x y z * uni 1 0 0) :
    y = 0 := by
  rw [uni_mul, uni_mul] at h
  have h3 := (uni_injective h).2.2
  clear h
  revert x y z h3; decide

theorem x_eq_zero {x y z : ZMod 3} (h : uni 0 1 0 * uni x y z = uni x y z * uni 0 1 0) :
    x = 0 := by
  rw [uni_mul, uni_mul] at h
  have h3 := (uni_injective h).2.2
  clear h
  revert x y z h3; decide

theorem comm_center (z : ZMod 3) : uni 0 1 0 * uni 0 0 z = uni 0 0 z * uni 0 1 0 := by
  rw [uni_mul, uni_mul]
  refine uni_eq ?_ ?_ ?_ <;> revert z <;> decide

theorem card_unitri : Nat.card unitri = 27 := by
  have hbij : Function.Bijective
      (fun v : ZMod 3 × ZMod 3 × ZMod 3 => (⟨uni v.1 v.2.1 v.2.2, ⟨_, _, _, rfl⟩⟩ : unitri)) := by
    refine ⟨fun v w h => ?_, fun ⟨g, x, y, z, hg⟩ => ⟨(x, y, z), Subtype.ext hg⟩⟩
    obtain ⟨h1, h2, h3⟩ := uni_injective (congrArg Subtype.val h)
    exact Prod.ext h1 (Prod.ext h2 h3)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp [Nat.card_prod, Nat.card_zmod]

theorem not_three_dvd_index_unitri : ¬ 3 ∣ unitri.index := by
  have h := unitri.card_mul_index
  rw [card_unitri, CFSG.GH74.SmallRanks.card_sl3] at h
  have : unitri.index = 208 := by omega
  rw [this]
  norm_num

@[expose] def wM : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 0, 0; 0, 0, 1; 0, 2, 0]

theorem det_wM : wM.det = 1 := by decide

@[expose] def wmat : SL33 := ⟨wM, det_wM⟩

theorem wM_mul (z : ZMod 3) : wM * uniM 0 0 z = uniM z 0 0 * wM := by
  simp only [wM, uniM, Matrix.mul_fin_three]
  congr 1 <;> first | rfl | ring | (ring_nf; done) | simp

theorem wmat_conj (z : ZMod 3) : wmat * uni 0 0 z * wmat⁻¹ = uni z 0 0 := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (wM_mul z)

theorem nonempty_equiv_sl33 {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ d.1 = .A 2 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : Nonempty (K ≃* SL33) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  simp only at hd1
  subst hd1
  have h := CFSG.Models.lieModel_A 2 q hv e
  rw [hqp, hqe] at h
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    CFSG.GH74.KGroups.L33.card_F (CFSG.Models.LieModel.toBlueprint (by decide) h)
  exact ⟨e1.trans ((QuotientGroup.quotientMulEquivOfEq CFSG.GH74.KGroups.L33.center_bot).trans
    QuotientGroup.quotientBot)⟩

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
