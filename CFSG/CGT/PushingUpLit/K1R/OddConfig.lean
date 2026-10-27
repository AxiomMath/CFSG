module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinear

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.OddClassicalRankOne
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem NoFour.map {G H : Type*} [Group G] [Group H] {X : Subgroup G} (h : NoFour X)
    (f : G →* H) (hf : Function.Injective f) : NoFour (X.map f) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxx hyy hxy
  rw [← map_mul, ← map_one f] at hxx hyy
  rw [← map_mul, ← map_mul] at hxy
  rcases h x hx y hy (hf hxx) (hf hyy) (hf hxy) with h' | h' | h'
  · exact Or.inl (by rw [h', map_one])
  · exact Or.inr (Or.inl (by rw [h', map_one]))
  · exact Or.inr (Or.inr (by rw [h']))

theorem NoFour.of_map {G H : Type*} [Group G] [Group H] {X : Subgroup G} {f : G →* H}
    (h : NoFour (X.map f)) (hf : Function.Injective f) : NoFour X := by
  intro x hx y hy hxx hyy hxy
  rcases h (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩ (by rw [← map_mul, hxx, map_one])
      (by rw [← map_mul, hyy, map_one]) (by rw [← map_mul, ← map_mul, hxy]) with h' | h' | h'
  · exact Or.inl (hf (h'.trans (map_one f).symm))
  · exact Or.inr (Or.inl (hf (h'.trans (map_one f).symm)))
  · exact Or.inr (Or.inr (hf h'))

theorem NoFour.of_map_of_ker {G H : Type*} [Group G] [Group H] {X : Subgroup G} {f : G →* H}
    (h : NoFour (X.map f)) (hk : ∀ x ∈ X, f x = 1 → x = 1) : NoFour X := by
  intro x hx y hy hxx hyy hxy
  rcases h (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩ (by rw [← map_mul, hxx, map_one])
      (by rw [← map_mul, hyy, map_one]) (by rw [← map_mul, ← map_mul, hxy]) with h' | h' | h'
  · exact Or.inl (hk x hx h')
  · exact Or.inr (Or.inl (hk y hy h'))
  · refine Or.inr (Or.inr ?_)
    have h1 := hk (x * y⁻¹) (mul_mem hx (inv_mem hy))
      (by rw [map_mul, map_inv, h', mul_inv_cancel])
    exact mul_inv_eq_one.mp h1

@[expose] def NoFourConfig {P : Type*} [Group P] (β : MulAut P) (K : Type*) [Field K] : Prop :=
  ∃ S : Subgroup (fixedSubgroup β), S.Normal ∧ IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
    NoFour (fixedSubgroup β ⊓ centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) :
      Set P))

theorem NoFourConfig.of_mulEquiv {P P' : Type*} [Group P] [Group P'] {K : Type*} [Field K]
    (e : P ≃* P') {β : MulAut P} {β' : MulAut P'} (hint : ∀ x, e (β x) = β' (e x))
    (h : NoFourConfig β K) : NoFourConfig β' K := by
  obtain ⟨S, hSn, hSs, ⟨a, b, hab⟩, ⟨φ⟩, hr⟩ := h
  have hfix := OddClassSelector.map_fixedSubgroup_of_comm e β β' hint
  let eF : fixedSubgroup β ≃* fixedSubgroup β' :=
    ((fixedSubgroup β).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let eS : S ≃* S.map eF.toMonoidHom := S.equivMapOfInjective eF.toMonoidHom eF.injective
  have hmapS : (S.map eF.toMonoidHom).map (fixedSubgroup β').subtype =
      (S.map (fixedSubgroup β).subtype).map e.toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hinf : fixedSubgroup β' ⊓ centralizer (((S.map eF.toMonoidHom).map
      (fixedSubgroup β').subtype : Subgroup P') : Set P') =
      (fixedSubgroup β ⊓ centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) :
        Set P)).map e.toMonoidHom := by
    rw [hmapS, ← CFSG.LocalAnalysis.SymplecticFourStandard.map_centralizer_mulEquiv, ← hfix,
      ← map_inf_eq _ _ _ e.injective]
  refine ⟨S.map eF.toMonoidHom, hSn.map _ eF.surjective, eS.symm.isSimpleGroup,
    ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩,
    ⟨eS.symm.trans φ⟩, ?_⟩
  rw [hinf]
  exact hr.map e.toMonoidHom e.injective

theorem noFourConfig_of_data {D : Type*} [Group D] {n : ℕ} (hn : 2 ≤ n) {K : Type*} [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) {α : MulAut D} {S : Subgroup D}
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (hnf : NoFour (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D))) :
    NoFourConfig α K := by
  obtain ⟨hSs, hSnab, hSK', hmap⟩ := subgroupOf_fixedRoot_data hn hK hSα hSK
  refine ⟨_, hSn, hSs, hSnab, hSK', ?_⟩
  change NoFour (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer
    (((S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).map
      (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) : Set D))
  rw [hmap]
  exact hnf

end CFSG.CGT.PushingUpLit.K1R
