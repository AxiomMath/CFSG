module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact34Holds
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (IsPStar PstarSet)

variable {W : Type} [CommGroup W]

theorem card_mul_card_inf_centSec_le [Finite W] {X A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender X A) (U : Subgroup W) :
    Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U) := by
  set B : Subgroup (MulAut W) := A ⊓ centSec U ⊥ with hB
  have hBA : B ≤ A := by
    rw [hB]
    exact inf_le_left
  have hoff : Nat.card B * Nat.card (fixV B) ≤ Nat.card A * Nat.card (fixV A) :=
    hA.2.2.2 B hBA
  have hUfix : U ≤ fixV B := by
    intro u hu b hb
    rw [hB] at hb
    have hcent := (mem_centSec.mp (Subgroup.mem_inf.mp hb).2).2 u hu
    rw [Subgroup.mem_bot] at hcent
    exact mul_inv_eq_one.mp hcent
  have hFix : fixV A ≤ fixV B := B1.fixV_le_fixV hBA
  have hsup : U ⊔ fixV A ≤ fixV B := sup_le hUfix hFix
  have hcard : Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(U ⊓ fixV A) =
      Nat.card U * Nat.card (fixV A) :=
    (card_sup_mul_card_inf_of_commute U (fixV A) (fun _ _ _ _ => mul_comm _ _)).1
  have hsupcard : Nat.card ↥(U ⊔ fixV A) ≤ Nat.card (fixV B) :=
    Subgroup.card_le_of_le hsup
  have hmain : Nat.card B * Nat.card U * Nat.card (fixV A) ≤
      Nat.card A * Nat.card ↥(fixV A ⊓ U) * Nat.card (fixV A) := by
    calc Nat.card B * Nat.card U * Nat.card (fixV A)
        = Nat.card B * (Nat.card U * Nat.card (fixV A)) := by ring
      _ = Nat.card B * (Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(U ⊓ fixV A)) := by
          rw [← hcard]
      _ ≤ Nat.card B * (Nat.card (fixV B) * Nat.card ↥(U ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsupcard)
      _ = Nat.card B * Nat.card (fixV B) * Nat.card ↥(U ⊓ fixV A) := by ring
      _ ≤ Nat.card A * Nat.card (fixV A) * Nat.card ↥(U ⊓ fixV A) :=
          Nat.mul_le_mul_right _ hoff
      _ = Nat.card A * Nat.card ↥(fixV A ⊓ U) * Nat.card (fixV A) := by
          rw [inf_comm (fixV A) U]
          ring
  have hFpos : 0 < Nat.card (fixV A) := Nat.card_pos
  simpa [mul_comm] using Nat.le_of_mul_le_mul_right hmain hFpos

theorem GomiFact36Hyp.exists_offender [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) :
    ∃ A : Subgroup (MulAut W), A ≤ S ∧ A ≤ Subgroup.normalizer (L : Set (MulAut W)) ∧
      IsElemAbelian2 A ∧ IsQuadratic A ∧ ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) ∧
      ∀ U : Subgroup W,
        Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U) := by
  have hex : ∃ A : Subgroup (MulAut W), IsPStar S A ∧
      ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    by_contra hno
    push Not at hno
    have hsup : sSup (PstarSet S) ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
      sSup_le fun A hA => hno A hA
    have hbot : ⁅sSup (PstarSet S), L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hsup
    have hbot' : ⁅L, sSup (PstarSet S)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hbot
    exact h.2.2.2.1 hbot'
  obtain ⟨A, hAP, hAnC⟩ := hex
  have hA_S : IsFFStarOffender S A := hAP.1
  have hA_Y : IsFFStarOffender Y A :=
    ⟨hA_S.1.trans h.1.le, hA_S.2.1, hA_S.2.2.1, hA_S.2.2.2⟩
  have hMin : IsFFStarMin S A :=
    ⟨hA_S, fun B hB hFF => hAP.2 B hB hFF.2.2.1 hFF.2.2.2.symm⟩
  have hquad : IsQuadratic A := B1_4_3 hW hMin
  have hN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    le_normalizer_of_offender_component (fun w => by simpa [pow_two] using hW w)
      h.2.1 h.2.2.1 hA_Y
  exact ⟨A, hA_S.1, hN, hA_S.2.2.1, hquad, hAnC,
    fun U => card_mul_card_inf_centSec_le hA_S U⟩

private theorem submoduleClosure_map_le {X : Subgroup (MulAut W)} {U : Subgroup W}
    {a : MulAut W} (ha : a ∈ X) :
    (G6.submoduleClosure X U).map a.toMonoidHom ≤ G6.submoduleClosure X U := by
  rw [G6.submoduleClosure, Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg => ?_
  rw [Subgroup.map_map]
  have e : a.toMonoidHom.comp (g : MulAut W).toMonoidHom = (a * g).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [e]
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ X) => U.map (g : MulAut W).toMonoidHom) (a * g)
    (X.mul_mem ha hg) le_rfl

theorem submoduleClosure_fixV_le_fixV {S L K : Subgroup (MulAut W)} (hKS : K ≤ S)
    (hKL : K ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    G6.submoduleClosure L (fixV S) ≤ fixV K := by
  rw [G6.submoduleClosure]
  refine iSup_le fun g => iSup_le fun hg => ?_
  rintro w ⟨v, hv, rfl⟩
  rw [mem_fixV]
  intro k hk
  have hkv : k v = v := (mem_fixV.mp hv) k (hKS hk)
  have hcomm : k * g = g * k :=
    (Subgroup.mem_centralizer_iff.mp (hKL hk) g hg).symm
  calc k (g v) = g (k v) := by rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
    _ = g v := by rw [hkv]

theorem sup_le_stabSub_submoduleClosure_fixV (S L : Subgroup (MulAut W)) :
    L ⊔ (S ⊓ Subgroup.normalizer (L : Set (MulAut W))) ≤
      stabSub (G6.submoduleClosure L (fixV S)) := by
  refine sup_le (B1.le_stabSub_of_invariant ?_) (B1.le_stabSub_of_invariant ?_)
  · intro l hl w hw
    exact submoduleClosure_map_le (X := L) (U := fixV S) hl ⟨w, hw, rfl⟩
  · intro s hs w hw
    exact apply_mem_submoduleClosure_fixV_of_mem_normalizer (Subgroup.mem_inf.mp hs).1
      (Subgroup.mem_inf.mp hs).2 hw

end CFSG.GroupTheory
