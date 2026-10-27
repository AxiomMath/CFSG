module

public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi4
public import CFSG.RankThree.PartOne.SEITZQ1.AmbientPlane
public import CFSG.RankThree.PartOne.SEITZQ1.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ7
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZQ1 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)


section Main


theorem reeF4_phi2Ambient_of_card {m : ℕ} (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) : Phi2Ambient m K := by
  intro p hp hp5 hpq
  exact q1_phi2_plane hm hK hp hp5 hpq

theorem reeF4_closure_cenGen_eq_top_of_phi2
    (hamb : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], 1 ≤ m →
      Nat.card K = 2 ^ (2 * m + 1) → Phi2Ambient m K)
    {m : ℕ} {K : Type} [Group K] [Finite K] [IsSimpleGroup K] (hiso : IsoLie K (.reeF4 m))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * m + 1) + 1)
    (E₁ : Subgroup K) (hE₁p : ∀ x ∈ E₁, x ^ p = 1) (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model hiso
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have hshape : SylowShape p 2 ((2 ^ (2 * m + 1) + 1).factorization p) K :=
    (CFSG.RankThree.PartOne.K128.sylowShape_ree_phi2 hX hp hp5 hpq).of_mulEquiv e
  obtain ⟨E, hEΓ, hEp, hEc, hD⟩ := hamb m X hm1 hX p hp hp5 hpq
  have hE'' := reeF4c_closure_cenGen_subgroupOf (F4.reeGamma X m) E hEΓ hD
  have hE''c : Nat.card ↥(E.subgroupOf (F4.reeGamma X m)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv]
    exact hEc
  have hE''p : ∀ x ∈ E.subgroupOf (F4.reeGamma X m), x ^ p = 1 := fun x hx =>
    Subtype.ext (by simpa using hEp x hx)
  have hE₀top : Subgroup.closure
      (cenGen ((E.subgroupOf (F4.reeGamma X m)).map e.symm.toMonoidHom)) = ⊤ :=
    reeF4c_closure_cenGen_map_top e.symm _ hE''
  have hE₀c : Nat.card ↥((E.subgroupOf (F4.reeGamma X m)).map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE''c]
  have hE₀p : ∀ x ∈ (E.subgroupOf (F4.reeGamma X m)).map e.symm.toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    show (e.symm y) ^ p = 1
    rw [← map_pow, hE''p y hy, map_one]
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hE₀c : IsPGroup p ↥((E.subgroupOf
    (F4.reeGamma X m)).map e.symm.toMonoidHom)).exists_le_sylow
  obtain ⟨φ⟩ := hshape _ S.isPGroup' S.not_dvd_index
  exact closure_cenGen_eq_top_of_plane S _ φ hS hE₀p hE₀c hE₀top E₁ hE₁p hE₁c

theorem extSeitzAtInnerFor_reeF4_phi2 (m : ℕ) :
    ExtSeitzAtInnerFor (.reeF4 m) fun p => p ∣ 2 ^ (2 * m + 1) + 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact reeF4_closure_cenGen_eq_top_of_phi2
    (fun _ K _ _ _ hm hK => reeF4_phi2Ambient_of_card hm K hK) hiso hp hp5 hP E₁ hE₁p hcard₁

end Main

end CFSG.LieType.SeitzGeneration
