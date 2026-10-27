module

public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleComponentStructure

public section

namespace CFSG.EvenSporadicStandard.TwoB.Layer54

open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.SemisimpleComponentStructure

variable {H : Type*} [Group H] [Finite H]

theorem map_conj_eq (S : Subgroup H) [Group.IsSolvable S] {t : H} (ht : t * t = 1)
    (hS : ∀ x ∈ Layer.subgroup H, x * t = t * x → x ∈ S) (i : ComponentIndex H) :
    i.val.map (MulAut.conj t).toMonoidHom = i.val := by
  by_contra hne
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hQ : IsComponentOf i.val ⊤ := i.property
  have hQ' : IsComponentOf (i.val.map (MulAut.conj t).toMonoidHom) ⊤ :=
    (LocalComponents.equiv_iff (MulAut.conj t) i.val).mpr hQ
  have hmem : ∀ q ∈ i.val, t * q * t⁻¹ ∈ i.val.map (MulAut.conj t).toMonoidHom := fun q hq => by
    exact ⟨q, hq, by simp [MulAut.conj_apply]⟩
  have hcomm : ∀ q ∈ i.val, ∀ q' ∈ i.val.map (MulAut.conj t).toMonoidHom, q * q' = q' * q := by
    have h := LocalComponents.commute_of_ne i.val (i.val.map (MulAut.conj t).toMonoidHom) hQ hQ'
      (fun h => hne h.symm)
    intro q hq q' hq'
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hq) q' hq').symm
  let d : ↥i.val →* H := MonoidHom.mk' (fun q => (q : H) * (t * (q : H) * t⁻¹)) (by
    intro a b
    have h1 : (b : H) * (t * (a : H) * t⁻¹) = (t * (a : H) * t⁻¹) * (b : H) :=
      hcomm _ b.2 _ (hmem _ a.2)
    show (a : H) * (b : H) * (t * ((a : H) * (b : H)) * t⁻¹) =
      ((a : H) * (t * (a : H) * t⁻¹)) * ((b : H) * (t * (b : H) * t⁻¹))
    calc (a : H) * (b : H) * (t * ((a : H) * (b : H)) * t⁻¹)
        = (a : H) * ((b : H) * (t * (a : H) * t⁻¹)) * (t * (b : H) * t⁻¹) := by group
      _ = (a : H) * ((t * (a : H) * t⁻¹) * (b : H)) * (t * (b : H) * t⁻¹) := by rw [h1]
      _ = ((a : H) * (t * (a : H) * t⁻¹)) * ((b : H) * (t * (b : H) * t⁻¹)) := by group)
  have hdS : ∀ q : ↥i.val, d q ∈ S := by
    intro q
    have hu : t * (q : H) * t⁻¹ ∈ i.val.map (MulAut.conj t).toMonoidHom := hmem _ q.2
    apply hS
    · exact mul_mem (Layer.component_le hQ q.2) (Layer.component_le hQ' hu)
    · have hqu : (q : H) * (t * (q : H) * t⁻¹) = (t * (q : H) * t⁻¹) * (q : H) :=
        hcomm _ q.2 _ hu
      have e1 : (q : H) * (t * (q : H) * t⁻¹) * t = (q : H) * t * q := by
        rw [ht']
        calc (q : H) * (t * (q : H) * t) * t = q * (t * q * (t * t)) := by simp only [mul_assoc]
          _ = (q : H) * t * q := by rw [ht, mul_one, mul_assoc]
      have e2 : t * ((q : H) * (t * (q : H) * t⁻¹)) = (q : H) * t * q := by
        rw [hqu, ht']
        calc t * ((t * (q : H) * t) * q) = (t * t) * q * t * q := by simp only [mul_assoc]
          _ = (q : H) * t * q := by rw [ht, one_mul]
      exact e1.trans e2.symm
  have : Group.IsPerfect ↥i.val := ⟨hQ.2.2.1⟩
  have h1 : d.codRestrict S hdS = 1 := SolvableKernelContainment.hom_eq_one _
  have hdq : ∀ q : ↥i.val, (q : H) * (t * (q : H) * t⁻¹) = 1 := fun q =>
    congrArg Subtype.val (DFunLike.congr_fun h1 q)
  have hle : i.val.map (MulAut.conj t).toMonoidHom ≤ i.val := by
    rintro _ ⟨q, hq, rfl⟩
    have h2 := eq_inv_of_mul_eq_one_right (hdq ⟨q, hq⟩)
    have h3 : (MulAut.conj t).toMonoidHom q = t * q * t⁻¹ := by simp [MulAut.conj_apply]
    rw [h3]
    exact h2 ▸ inv_mem hq
  exact hne (LocalComponents.eq_of_le _ _ hQ' hQ hle)

end CFSG.EvenSporadicStandard.TwoB.Layer54
