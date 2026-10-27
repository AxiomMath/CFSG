module

public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v w

theorem point_involution_card_comap
    {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) (B : Subgroup H) :
    Nat.card {x : G // x ∈ B.comap e.toMonoidHom ∧ IsInvolution x} =
      Nat.card {x : H // x ∈ B ∧ IsInvolution x} := by
  let f : {x : G // x ∈ B.comap e.toMonoidHom ∧ IsInvolution x} →
      {x : H // x ∈ B ∧ IsInvolution x} := fun x =>
    ⟨e x, x.property.1, IsInvolution.map_of_injective x.property.2 e.toMonoidHom e.injective⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h)
    · intro y
      refine ⟨⟨e.symm y, ?_,
        IsInvolution.map_of_injective y.property.2 e.symm.toMonoidHom e.symm.injective⟩, ?_⟩
      · change e (e.symm y) ∈ B
        simpa only [e.apply_symm_apply] using y.property.1
      · apply Subtype.ext
        exact e.apply_symm_apply y
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem full_model_point_pair_compHom
    {G : Type u} {H : Type v} {Omega : Type w}
    [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (rho : H →* Equiv.Perm Omega) (b : Omega) (B : Subgroup H) (q : ℕ)
    (hdata : letI : MulAction H Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer H b ∧ TwoRankAtLeastTwo H ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive H Omega 2 ∧
      Nat.card {x : H // x ∈ B ∧ IsInvolution x} = q - 1 ∧
      ∃ (a0 b0 : Omega) (w0 : H) (T0 : Subgroup H),
        a0 ≠ b0 ∧ w0 • a0 = b0 ∧ w0 • b0 = a0 ∧
        (T0 : Set H) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = q - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w0 = x⁻¹) :
    let : MulAction G Omega := MulAction.compHom Omega (rho.comp e.toMonoidHom)
    B.comap e.toMonoidHom = MulAction.stabilizer G b ∧
    TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded (B.comap e.toMonoidHom) ∧
    MulAction.IsMultiplyPretransitive G Omega 2 ∧
    Nat.card {x : G // x ∈ B.comap e.toMonoidHom ∧ IsInvolution x} = q - 1 ∧
    ∃ (a0 b0 : Omega) (w0 : G) (T0 : Subgroup G),
      a0 ≠ b0 ∧ w0 • a0 = b0 ∧ w0 • b0 = a0 ∧
      (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
      IsCyclic T0 ∧ Nat.card T0 = q - 1 ∧
      ∀ x ∈ T0, rightConjugateElem x w0 = x⁻¹ := by
  let : MulAction H Omega := MulAction.compHom Omega rho
  let : MulAction G Omega := MulAction.compHom Omega (rho.comp e.toMonoidHom)
  obtain ⟨hB, hrank, hSE, htwo, hcard, a0, b0, w0, T0,
    hab, hwa, hwb, hTset, hTcyclic, hTcard, hinvert⟩ := hdata
  have hmapB : B.map e.symm.toMonoidHom = B.comap e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa only [e.apply_symm_apply, SetLike.mem_coe] using hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hB' : B.comap e.toMonoidHom = MulAction.stabilizer G b := by
    rw [hB]
    ext x
    rfl
  have hSE' : fusionStronglyEmbedded (B.comap e.toMonoidHom) :=
    hmapB ▸ hSE.map_mulEquiv e.symm
  have hrank' : TwoRankAtLeastTwo G :=
    twoRankAtLeastTwo_of_injective e.symm.toMonoidHom e.symm.injective hrank
  have htwo' : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨h, hha, hhb⟩ := MulAction.is_two_pretransitive_iff.mp htwo hab hcd
    refine ⟨e.symm h, ?_, ?_⟩
    · change rho (e (e.symm h)) a = c
      change rho h a = c at hha
      simpa only [e.apply_symm_apply] using hha
    · change rho (e (e.symm h)) b = d
      change rho h b = d at hhb
      simpa only [e.apply_symm_apply] using hhb
  have hcard' := (point_involution_card_comap e B).trans hcard
  let T : Subgroup G := T0.map e.symm.toMonoidHom
  have hTcomap : T = T0.comap e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ T0
      simpa only [e.apply_symm_apply, SetLike.mem_coe] using hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hTset' : (T : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} := by
    ext x
    rw [hTcomap]
    change e x ∈ T0 ↔ rho (e x) a0 = a0 ∧ rho (e x) b0 = b0
    exact Set.ext_iff.mp hTset (e x)
  have hTcyclic' : IsCyclic T := by
    let : IsCyclic T0 := hTcyclic
    exact isCyclic_of_surjective (e.symm.subgroupMap T0) (e.symm.subgroupMap T0).surjective
  have hTcard' : Nat.card T = q - 1 :=
    (Subgroup.card_map_of_injective e.symm.injective).trans hTcard
  refine ⟨hB', hrank', hSE', htwo', hcard', a0, b0, e.symm w0, T, hab, ?_, ?_,
    hTset', hTcyclic', hTcard', ?_⟩
  · change rho (e (e.symm w0)) a0 = b0
    change rho w0 a0 = b0 at hwa
    simpa only [e.apply_symm_apply] using hwa
  · change rho (e (e.symm w0)) b0 = a0
    change rho w0 b0 = a0 at hwb
    simpa only [e.apply_symm_apply] using hwb
  · intro x hx
    apply e.injective
    have hxT : e x ∈ T0 := by
      rw [hTcomap] at hx
      exact hx
    simpa only [rightConjugateElem, map_mul, map_inv, e.apply_symm_apply] using hinvert (e x) hxT

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
