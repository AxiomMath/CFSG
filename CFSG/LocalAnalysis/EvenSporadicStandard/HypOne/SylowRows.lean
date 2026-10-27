module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Models
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.SmallOddCore (GroupData tp rep_tp rep_invT mem_R_of_sift commTT_iff permOK
  commTT mem_sup_zpowers_iff)

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem fourClassesLarge_row_P (hD : GroupData n P pg gg sift) {t : Table}
    (ht : permOK n t = true) {capS capC : ℕ} {cg sg : Array Table} {ord : ℕ}
    (hcard : ord = 2 ^ (Nat.card ↥(centralizerIn P (tp n t))).factorization 2)
    (h : sylowFourOK n capS capC (fun T => sift T && commTT n T t) cg sg ord = true) :
    FourClassesLarge ↥(centralizerIn P (tp n t)) := by
  have rt := rep_tp ht
  refine fourClassesLarge_of_sylowFourOK hD.lt (fun T g hT hm => ?_) hcard h
  rw [Bool.and_eq_true] at hm
  exact mem_centralizerIn.2 ⟨(hD.sift T g hT).1 hm.1, (commTT_iff hT rt).1 hm.2⟩

theorem index_two_of_normalizing {U : Equiv.Perm (Fin n)} (hU2 : U ^ 2 = 1)
    (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) :
    ∀ x ∈ P ⊔ zpowers U, x ∉ P → ∀ y ∈ P ⊔ zpowers U, y ∉ P → x⁻¹ * y ∈ P := by
  intro x hx hxP y hy hyP
  have hx' := ((mem_sup_zpowers_iff hU2 hUn).1 hx).resolve_left hxP
  have hy' := ((mem_sup_zpowers_iff hU2 hUn).1 hy).resolve_left hyP
  have h1 := hUn _ (P.mul_mem (P.inv_mem hx') hy')
  have : x⁻¹ * y = U * ((x * U)⁻¹ * (y * U)) * U⁻¹ := by group
  rw [this]
  exact h1

theorem fourClassesLarge_row_R (hD : GroupData n P pg gg sift) {u : Table}
    (hu : Rep n u (tp n u)) (hU2 : tp n u ^ 2 = 1) (hUn : ∀ p ∈ P, tp n u * p * (tp n u)⁻¹ ∈ P)
    {t : Table} (ht : permOK n t = true) {capS capC : ℕ} {cg sg : Array Table} {ord : ℕ}
    (hcard : ord = 2 ^ (Nat.card ↥(centralizerIn (P ⊔ zpowers (tp n u)) (tp n t))).factorization 2)
    (h : sylowFourOK n capS capC
      (fun T => (sift T || sift (compT n T u)) && commTT n T t) cg sg ord = true) :
    FourClassesLarge ↥(centralizerIn (P ⊔ zpowers (tp n u)) (tp n t)) := by
  have rt := rep_tp ht
  refine fourClassesLarge_of_sylowFourOK hD.lt (fun T g hT hm => ?_) hcard h
  rw [Bool.and_eq_true] at hm
  exact mem_centralizerIn.2 ⟨mem_R_of_sift hD hU2 hUn hu hT hm.1, (commTT_iff hT rt).1 hm.2⟩

@[expose] def zOK (n : ℕ) (sift : Table → Bool) (u t z : Table) : Bool :=
  permOK n z && !sift z && (sift z || sift (compT n z u)) && commTT n z t

theorem card_centralizerIn_R_of_z (hD : GroupData n P pg gg sift) {u : Table}
    (hu : Rep n u (tp n u)) (hU2 : tp n u ^ 2 = 1) (hUn : ∀ p ∈ P, tp n u * p * (tp n u)⁻¹ ∈ P)
    {t z : Table} (ht : permOK n t = true) (hz : zOK n sift u t z = true) :
    Nat.card ↥(centralizerIn (P ⊔ zpowers (tp n u)) (tp n t)) =
      2 * Nat.card ↥(centralizerIn P (tp n t)) := by
  simp only [zOK, Bool.and_eq_true, Bool.not_eq_true'] at hz
  obtain ⟨⟨⟨hzp, hzs⟩, hzR⟩, hzc⟩ := hz
  have rt := rep_tp ht
  have rz := rep_tp hzp
  refine card_centralizerIn_eq_two_mul le_sup_left (index_two_of_normalizing hU2 hUn) (tp n t)
    (tp n z) (mem_centralizerIn.2 ⟨mem_R_of_sift hD hU2 hUn hu rz hzR, (commTT_iff rz rt).1 hzc⟩)
    fun hP => ?_
  rw [← hD.sift z _ rz] at hP
  rw [hP] at hzs
  exact Bool.noConfusion hzs

@[expose] def e8Rows (n : ℕ) (sift : Table → Bool) (a b c : Table) : Bool :=
  permOK n a && permOK n b && permOK n c && sift a && sift b && sift c && e8Check n a b c

theorem e8Rows_spec (hD : GroupData n P pg gg sift) {a b c : Table}
    (h : e8Rows n sift a b c = true) : HasElemAbelianEight P := by
  simp only [e8Rows, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hsa⟩, hsb⟩, hsc⟩, he8⟩ := h
  have ra := rep_tp ha
  have rb := rep_tp hb
  have rc := rep_tp hc
  exact hasElemAbelianEight_of_e8Check_rep ra rb rc he8 ((hD.sift a _ ra).1 hsa)
    ((hD.sift b _ rb).1 hsb) ((hD.sift c _ rc).1 hsc)

@[expose] def commTable (n : ℕ) (l t : Table) : Table :=
  compT n (compT n (compT n l t) (invT n l)) (invT n t)

@[expose] def foursWitOK (n : ℕ) (sift : Table → Bool) (l t : Table) : Bool :=
  permOK n l && sift l && invOK n l (invT n l) && permOK n t && invOK n t (invT n t) &&
    ordTest n 2 (commTable n l t)

theorem foursWit_spec (hD : GroupData n P pg gg sift) {l t : Table}
    (h : foursWitOK n sift l t = true) :
    ∃ l' ∈ P, orderOf (l' * tp n t * l'⁻¹ * (tp n t)⁻¹) = 2 := by
  simp only [foursWitOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl, hsl⟩, hli⟩, ht⟩, hti⟩, hord⟩ := h
  have rl := rep_tp hl
  have rt := rep_tp ht
  have rli := rep_invT rl hli
  have rti := rep_invT rt hti
  refine ⟨tp n l, (hD.sift l _ rl).1 hsl, ?_⟩
  exact (ordTest_iff perm_faithful (Rep.compT (Rep.compT (Rep.compT rl rt) rli) rti)
    (by norm_num)).1 hord

end CFSG.EvenSporadicStandard.HypOne
