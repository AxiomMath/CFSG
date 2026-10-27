module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Lifts

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

theorem cycleType_eq_of_sq_eq_one {g : alternatingGroup (Fin 9)} (hg : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (g : Perm (Fin 9)).cycleType = {2, 2} ∨ (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  have h2 : (g : Perm (Fin 9)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hg, OneMemClass.coe_one]
  have h1 : (g : Perm (Fin 9)) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hsign : Perm.sign (g : Perm (Fin 9)) = 1 := Perm.mem_alternatingGroup.mp g.2
  obtain ⟨k, hk⟩ : ∃ k, (g : Perm (Fin 9)).cycleType = Multiset.replicate k 2 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one h2⟩
  have hsum := Perm.sum_cycleType_le (g : Perm (Fin 9))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1 (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk4 : k ≤ 4 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  rw [hk]
  interval_cases k
  · exact absurd hsign (by decide)
  · exact Or.inl rfl
  · exact absurd hsign (by decide)
  · exact Or.inr rfl

private theorem aNineSylowWordPerm_commute : ∀ v : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenA : Perm (Fin 9)) =
        (aNineSylowGenA : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v * (aNineSylowGenB : Perm (Fin 9)) =
        (aNineSylowGenB : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v * (aNineSylowGenC : Perm (Fin 9)) =
        (aNineSylowGenC : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v * (aNineSylowGenD : Perm (Fin 9)) =
        (aNineSylowGenD : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v * (aNineSylowGenE : Perm (Fin 9)) =
        (aNineSylowGenE : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v * (aNineSylowGenF : Perm (Fin 9)) =
        (aNineSylowGenF : Perm (Fin 9)) * aNineSylowWordPerm v →
    aNineSylowWordPerm v = 1 ∨
      aNineSylowWordPerm v = (aNineSylowGenA : Perm (Fin 9)) * (aNineSylowGenC : Perm (Fin 9)) := by
  decide +kernel

theorem eq_one_or_eq_genAC_of_commute_aNineSylow {s : alternatingGroup (Fin 9)}
    (hs : s ∈ ANineSylow) (hc : ∀ r ∈ ANineSylow, Commute s r) :
    s = 1 ∨ s = aNineSylowGenA * aNineSylowGenC := by
  obtain ⟨v, rfl⟩ := exists_aNineSylowWord_eq hs
  have hcoe : ∀ r ∈ ANineSylow, aNineSylowWordPerm v * (r : Perm (Fin 9)) =
      (r : Perm (Fin 9)) * aNineSylowWordPerm v := fun r hr => by
    rw [← coe_aNineSylowWord, ← Subgroup.coe_mul, ← Subgroup.coe_mul, (hc r hr).eq]
  rcases aNineSylowWordPerm_commute v (hcoe _ aNineSylowGenA_mem) (hcoe _ aNineSylowGenB_mem)
    (hcoe _ aNineSylowGenC_mem) (hcoe _ aNineSylowGenD_mem) (hcoe _ aNineSylowGenE_mem)
    (hcoe _ aNineSylowGenF_mem) with h | h
  · exact Or.inl (Subtype.ext (by rw [coe_aNineSylowWord, h, OneMemClass.coe_one]))
  · exact Or.inr (Subtype.ext (by rw [coe_aNineSylowWord, h, Subgroup.coe_mul]))

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J)
include hJ

theorem cycleType_eq_of_orderOf_eq_two (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {x : J}
    (hx : orderOf x = 2) (hxz : x ≠ zbar J) :
    ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hp1 : proj e x ≠ 1 := fun h =>
    (hJ.mem_center_iff.mp ((proj_eq_one_iff e).mp h)).elim hx1 hxz
  rcases cycleType_eq_of_sq_eq_one (by rw [← map_pow, hx2, map_one]) hp1 with h | h
  · exact absurd (hx2.symm.trans (hJ.sq_eq_zbar_of_cycleType_two_two e h))
      (Ne.symm hJ.zbar_ne_one)
  · exact h

theorem isConj_of_proj_eq_genAC (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {x y : J}
    (hx : orderOf x = 2) (hxz : x ≠ zbar J) (hy : proj e y = aNineSylowGenA * aNineSylowGenC) :
    IsConj x y := by
  obtain ⟨g, c, hc, hg⟩ := exists_conj_eq_mul_of_isConj e (u := x) (v := y) (by
    rw [hy]
    exact (isConj_aNineSylowGenA_mul_genC (hJ.cycleType_eq_of_orderOf_eq_two e hx hxz)).symm)
  rcases hJ.mem_center_iff.mp hc with rfl | rfl
  · exact isConj_iff.mpr ⟨g, by rw [hg, mul_one]⟩
  · obtain ⟨u, hu⟩ := proj_surjective e aNineSylowGenB
    have h := hJ.conj_eq_mul_zbar_of_genB_of_genAC e hu hy
    refine isConj_iff.mpr ⟨u⁻¹ * g, ?_⟩
    calc u⁻¹ * g * x * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * x * g⁻¹) * u := by group
      _ = u⁻¹ * (u * y * u⁻¹) * u := by rw [hg, h]
      _ = y := by group

theorem isConj_of_orderOf_eq_two {x y : J} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxz : x ≠ zbar J) (hyz : y ≠ zbar J) : IsConj x y := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  obtain ⟨w, hw⟩ := proj_surjective e (aNineSylowGenA * aNineSylowGenC)
  exact (hJ.isConj_of_proj_eq_genAC e hx hxz hw).trans
    (hJ.isConj_of_proj_eq_genAC e hy hyz hw).symm

theorem mem_center_of_forall_commute (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {s : J}
    (hs : proj e s ∈ ANineSylow) (hc : ∀ r : J, proj e r ∈ ANineSylow → Commute s r) :
    s ∈ center J := by
  rcases eq_one_or_eq_genAC_of_commute_aNineSylow hs (fun r hr => by
      obtain ⟨r', rfl⟩ := proj_surjective e r
      exact (hc r' hr).map (proj e)) with h | h
  · exact (proj_eq_one_iff e).mp h
  · obtain ⟨u, hu⟩ := proj_surjective e aNineSylowGenB
    have h1 := hJ.conj_eq_mul_zbar_of_genB_of_genAC e hu h
    have h2 : u * s * u⁻¹ = s := by
      rw [← (hc u (by rw [hu]; exact aNineSylowGenB_mem)).eq, mul_inv_cancel_right]
    exact absurd (mul_eq_left.mp (h2.symm.trans h1).symm) hJ.zbar_ne_one

theorem center_le_sylow (T : Sylow 2 J) : center J ≤ T :=
  IsPGroup.le_sylow_of_normal hJ.isPGroup_center T

theorem mem_center_sylow_iff (T : Sylow 2 J) {t : J} (ht : t ∈ T) :
    (⟨t, ht⟩ : (T : Subgroup J)) ∈ center (T : Subgroup J) ↔ t ∈ center J := by
  refine ⟨fun htc => ?_, fun htJ => Subgroup.mem_center_iff.mpr fun r =>
    Subtype.ext (Subgroup.mem_center_iff.mp htJ r)⟩
  have : Finite J := hJ.finite
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  let T₀ : Sylow 2 J := aNineSylowSylow.comapOfKerIsPGroup (proj e) (hJ.isPGroup_ker_proj e)
    (by rw [MonoidHom.range_eq_top.mpr (proj_surjective e)]; exact le_top)
  have hT₀ : ∀ r : J, r ∈ T₀ ↔ proj e r ∈ ANineSylow := fun r => Iff.rfl
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J T₀ T
  have hmem : ∀ r : J, r ∈ T₀ → g * r * g⁻¹ ∈ g • T₀ := fun r hr =>
    Subgroup.smul_mem_pointwise_smul r (MulAut.conj g) (T₀ : Subgroup J) hr
  obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists t (MulAut.conj g)
    (T₀ : Subgroup J)).mp ht
  have hsJ : s ∈ center J := by
    refine hJ.mem_center_of_forall_commute e ((hT₀ s).mp hs) fun r hr => ?_
    have hcomm := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp htc ⟨g * r * g⁻¹, hmem r ((hT₀ r).mpr hr)⟩)
    have hcomm' : g * (r * s) * g⁻¹ = g * (s * r) * g⁻¹ := by
      calc g * (r * s) * g⁻¹ = g * r * g⁻¹ * (MulAut.conj g • s) := by
            rw [MulAut.smul_def, MulAut.conj_apply]; group
        _ = MulAut.conj g • s * (g * r * g⁻¹) := hcomm
        _ = g * (s * r) * g⁻¹ := by rw [MulAut.smul_def, MulAut.conj_apply]; group
    exact (mul_left_cancel (mul_right_cancel hcomm')).symm
  rw [MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_center_iff.mp hsJ g,
    mul_inv_cancel_right]
  exact hsJ

theorem map_subtype_center_sylow (T : Sylow 2 J) :
    (center (T : Subgroup J)).map (T : Subgroup J).subtype = center J := by
  ext t
  refine ⟨?_, fun htJ => ⟨⟨t, hJ.center_le_sylow T htJ⟩,
    (hJ.mem_center_sylow_iff T _).mpr htJ, rfl⟩⟩
  rintro ⟨⟨t, ht⟩, htc, rfl⟩
  exact (hJ.mem_center_sylow_iff T ht).mp htc

theorem card_center_sylow (T : Sylow 2 J) : Nat.card (center (T : Subgroup J)) = 2 := by
  rw [← Subgroup.card_map_of_injective (T : Subgroup J).subtype_injective,
    hJ.map_subtype_center_sylow T, hJ.card_center]

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
