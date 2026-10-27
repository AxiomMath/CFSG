module

public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
open TauCeti CFSG.Open
open CFSG.HardMathSupport.Lang.E6Descent

section Tw243




theorem exists_elemAbelian_243_twistedE6 (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1) :
    ∃ E : Subgroup (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group, IsElemAbelian 3 E ∧
      243 ≤ Nat.card E := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_equiv_graphFixedRootGroup_twistedE6 q hv
  have hℓ : q.p.Prime := q.prime_p
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hQ : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have : Fact q.p.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, hQ, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω q.p := charP_of_injective_algebraMap (algebraMap K Ω).injective q.p
  let Fr : Ω →+* Ω := iterateFrobenius Ω q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ (q.p ^ q.exponent) := fun c => iterateFrobenius_def ..
  have h3' : 3 ∣ q.p ^ q.exponent + 1 := by rwa [hQ] at h3
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, hQ]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, hQ]
  obtain ⟨E, hER, hEab, hEcard⟩ := exists_elemAbelian_three_pow_six_twistedFixed (Fr := Fr) hf hFr h3'
  obtain ⟨-, hle, hnormal, -⟩ :=
    exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK' σ hσ' Ω Fr hFr
  obtain ⟨hfin, -, -, -, -, hRcard, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK' σ hσ' Ω Fr hFr
  set R := twistedFixedGroup TwistTag.E6 Ω Fr with hRdef
  set G0 := graphFixedRootGroup TwistTag.E6 K σ with hG0
  set C := G0.map (baseChangeGL (algebraMap K Ω)) with hCdef
  have hCcard : Nat.card C = ordTwistedE6 (q.p ^ q.exponent) := by
    rw [hCdef, Subgroup.card_map_of_injective (baseChangeGL_injective _)]
    exact CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hf hK' σ hσ'
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h3N : 3 ∣ Nat.card R := by
    rw [hRcard]
    exact (dvd_pow_self 3 (by norm_num : (6 : ℕ) ≠ 0)).trans (three_pow_six_dvd_numerator h3')
  have hC3 : Nat.card C * 3 = Nat.card R := by
    rw [hCcard]
    unfold ordTwistedE6
    rw [Nat.gcd_eq_left h3', ← hRcard]
    exact Nat.div_mul_cancel h3N
  have hidx : (C.subgroupOf R).index = 3 := by
    have h := Subgroup.card_mul_index (C.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    have hC0 : Nat.card C ≠ 0 := by
      intro h0
      rw [h0] at hC3
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hC0) (h.trans hC3.symm)
  have hrel : C.relIndex E ∣ 3 := by
    have h1 : (C.subgroupOf R).relIndex (E.subgroupOf R) = C.relIndex E := by
      have h2 : (E.subgroupOf R).map R.subtype = E := Subgroup.map_subgroupOf_eq_of_le hER
      have := Subgroup.relIndex_comap (H := C) R.subtype (E.subgroupOf R)
      exact this.trans (congrArg C.relIndex h2)
    have := hnormal
    rw [← h1, ← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have hmul : C.relIndex E * Nat.card ↥(C ⊓ E) = 3 ^ 6 :=
    (Subgroup.relIndex_mul_card (H := C) (K := E)).trans hEcard
  have hr3 : C.relIndex E ≤ 3 := Nat.le_of_dvd (by norm_num) hrel
  have hXcard : 243 ≤ Nat.card ↥(C ⊓ E) := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [hmul, hr3]
  have hX : IsElemAbelian 3 (C ⊓ E) := isElemAbelian_mono inf_le_right hEab
  have hinj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp G0.subtype) :=
    (baseChangeGL_injective _).comp Subtype.val_injective
  obtain ⟨E0, hE0, hE0card⟩ := exists_elemAbelian_of_injective_hom _ hinj
    (X := C ⊓ E) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_inf.1 hx).1
      exact ⟨⟨y, hy⟩, rfl⟩) hX
  obtain ⟨E1, hE1, hE1card⟩ := exists_elemAbelian_of_injective_hom e.toMonoidHom e.injective
    (X := E0) (fun x _ => ⟨e.symm x, by simp⟩) hE0
  exact ⟨E1, hE1, by rw [hE1card, hE0card]; exact hXcard⟩


end Tw243

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
