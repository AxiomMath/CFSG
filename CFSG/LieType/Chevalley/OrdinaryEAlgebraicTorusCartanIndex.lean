module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem mem_torusGroup_iff_existsUnique
    (L : Type) [Field L] [IsAlgClosed L] (h : ModGL τ L) :
    h ∈ torusGroup τ L ↔ ∃! a : Fin τ.rank → Lˣ, rootDiagUnit τ a = h := by
  constructor
  · intro hh
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    exact ⟨a, rfl, fun b hb => rootDiagUnit_injective hb⟩
  · rintro ⟨a, rfl, -⟩
    obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift τ L a
    rw [ht]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨(j, t j), rfl⟩

variable {M : Type} [Field M]

theorem fixedFieldImage_index_dvd_and_card_units
    [Finite M] (σ : M ≃+* M) :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
        τ.cartan.det.natAbs ∧
      ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
        (Nat.card (fixSubfield σ) - 1) ^ τ.rank := by
  classical
  let k := fixSubfield σ
  let ι : k →+* M := k.subtype
  let η : (Fin τ.rank → kˣ) →* ModGL τ M := (rootDiagUnitHom τ M).comp
    (MonoidHom.pi fun i => (Units.map ι.toMonoidHom).comp (Pi.evalMonoidHom (fun _ => kˣ) i))
  have hη : ∀ a, η a = rootDiagUnit τ fun i => Units.map ι.toMonoidHom (a i) := fun _ => rfl
  let μ := CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := kˣ) τ.cartan.transpose
  have hμ : ∀ t : Fin τ.rank → kˣ,
      η (μ t) =
        ((List.finRange τ.rank).map fun j => torusElt τ M j (Units.map ι.toMonoidHom (t j))).prod
      := fun t => by
    rw [hη, list_prod_torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    rw [CFSG.LocalAnalysis.ComponentInitial.monomialHom_apply, cartanChar, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, Matrix.transpose_apply]
  have hμJ : ∀ t : Fin τ.rank → kˣ,
      η (μ t) ∈ fixedFieldImage τ σ := fun t => by
    rw [hμ]
    have hmem : ((List.finRange τ.rank).map fun j => torusElt τ k j (t j)).prod ∈
        adjointGroup τ k := Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      exact torusElt_mem_adjointGroup j _
    refine ⟨_, hmem, ?_⟩
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun j _ => baseChangeGL_torusElt ι j (t j)
  have hμT : ∀ t : Fin τ.rank → kˣ,
      η (μ t) ∈ torusGroup τ M := fun t => by
    rw [hμ]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨(j, _), rfl⟩
  let S := (entrywiseFixedTorus τ σ).comap η
  let I := μ.range
  have hIS : I ≤ S := by
    rintro _ ⟨t, rfl⟩
    exact ⟨hμT t, fixedFieldImage_le (hμJ t)⟩
  let Jg := (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
  let η' : S →* entrywiseFixedGroup τ σ :=
    { toFun := fun a => ⟨η a.1, entrywiseFixedTorus_le a.2⟩
      map_one' := Subtype.ext (map_one η)
      map_mul' := fun a b => Subtype.ext (map_mul η a.1 b.1) }
  let Ψ := (QuotientGroup.mk' Jg).comp η'
  have hΨ : Function.Surjective Ψ := by
    intro y
    induction y using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨h, hh, j, hj, hx⟩ := mem_mul_of_mem_entrywiseFixedGroup x.2
    obtain ⟨hT, hΓ⟩ := hh
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
    have hσb : ∀ i, σ (b i : M) = b i := by
      have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ b) =
          rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom b)
      have h1 := rootDiagUnit_injective (h0.symm.trans hΓ.2)
      intro i
      exact congrArg Units.val (congrFun h1 i)
    let a : Fin τ.rank → kˣ := fun i => Units.mk0 ⟨b i, hσb i⟩ fun h0 =>
      (b i).ne_zero (congrArg Subtype.val h0)
    have ha : η a = rootDiagUnit τ b := by
      rw [hη]
      congr 1
      funext i
      exact Units.ext rfl
    have haS : a ∈ S := by
      change η a ∈ entrywiseFixedTorus τ σ
      rw [ha]
      exact ⟨hT, hΓ⟩
    refine ⟨⟨a, haS⟩, ?_⟩
    change (QuotientGroup.mk (η' ⟨a, haS⟩) : entrywiseFixedGroup τ σ ⧸ Jg) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (η a)⁻¹ * (x : ModGL τ M) ∈ fixedFieldImage τ σ
    rw [ha, ← hx, inv_mul_cancel_left]
    exact hj
  have hker : I.subgroupOf S ≤ Ψ.ker := by
    rintro ⟨_, hs⟩ ⟨t, rfl⟩
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (η' ⟨_, hs⟩) : entrywiseFixedGroup τ σ ⧸ Jg) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hμJ t
  have hJI : Jg.index ∣ I.index := by
    calc Jg.index = Ψ.ker.index := by
          rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΨ, Subgroup.card_top]
          rfl
      _ ∣ (I.subgroupOf S).index := Subgroup.index_dvd_of_le hker
      _ ∣ I.index := Subgroup.relIndex_dvd_index_of_le hIS
  refine ⟨hJI.trans ?_, hJI.trans ?_⟩
  · calc I.index ∣ τ.cartan.transpose.det.natAbs := (index_range_monomialHom_dvd k _).2
      _ = τ.cartan.det.natAbs := by rw [Matrix.det_transpose]
  · have : Finite (Fin τ.rank → kˣ) := inferInstance
    refine (Subgroup.index_dvd_card I).trans ?_
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]

theorem fixedFieldImage_index_dvd
    [Finite M] (σ : M ≃+* M) :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
      τ.cartan.det.natAbs :=
  (fixedFieldImage_index_dvd_and_card_units σ).1

theorem fixedFieldImage_index_dvd_card_units
    [Finite M] (σ : M ≃+* M) :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
      (Nat.card (fixSubfield σ) - 1) ^ τ.rank :=
  (fixedFieldImage_index_dvd_and_card_units σ).2

theorem le_fixedFieldImage_of_isPGroup
    (σ : M ≃+* M) {d : ℕ} (hd0 : d ≠ 0) (hd3 : d ≤ 3)
    (hd : ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ d) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {P : Subgroup (ModGL τ M)} (hPΓ : P ≤ entrywiseFixedGroup τ σ)
    (hP : IsPGroup p P) : P ≤ fixedFieldImage τ σ := by
  have : Fact p.Prime := ⟨hp⟩
  let Jg := (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
  have hfin : Finite (entrywiseFixedGroup τ σ ⧸ Jg) :=
    Nat.finite_of_card_ne_zero fun h0 => hd0 (Nat.eq_zero_of_zero_dvd (by
      change Nat.card (entrywiseFixedGroup τ σ ⧸ Jg) ∣ d at hd
      rwa [h0] at hd))
  let Q := (P.subgroupOf (entrywiseFixedGroup τ σ)).map (QuotientGroup.mk' Jg)
  have hQ : IsPGroup p Q :=
    (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPΓ).symm).map (QuotientGroup.mk' Jg)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := Q)).mp hQ
  have hdvd : p ^ n ∣ d := by
    rw [← hn]
    exact (Subgroup.card_subgroup_dvd_card Q).trans hd
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : p ∣ d := (dvd_pow_self p hne).trans hdvd
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h1
    omega
  rw [hn0, pow_zero, Subgroup.card_eq_one] at hn
  intro x hx
  have hle : P.subgroupOf (entrywiseFixedGroup τ σ) ≤ (QuotientGroup.mk' Jg).ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact hn
  have h1 : (⟨x, hPΓ hx⟩ : entrywiseFixedGroup τ σ) ∈ (QuotientGroup.mk' Jg).ker :=
    hle (Subgroup.mem_subgroupOf.mpr hx)
  rw [QuotientGroup.ker_mk'] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem ordinary_E_algebraic_torus_and_finite_fixed_group_Cartan_index
    (τ : Tag) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) :
    (∀ (L : Type) [Field L] [IsAlgClosed L] (h : ModGL τ L),
      h ∈ torusGroup τ L ↔ ∃! a : Fin τ.rank → Lˣ, rootDiagUnit τ a = h) ∧
    ∀ (M : Type) [Field M] [Finite M] (σ : M ≃+* M),
      fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ ∧
      ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).Normal ∧
      ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ d ∧
      ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ M), P ≤ entrywiseFixedGroup τ σ →
        IsPGroup p P → P ≤ fixedFieldImage τ σ := by
  have hdet : τ.cartan.det.natAbs = d := by
    rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [det_cartan_E6]
      rfl
    · rw [det_cartan_E7]
      rfl
    · rw [det_cartan_E8]
      rfl
  have hd0 : d ≠ 0 := by
    rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hd3 : d ≤ 3 := by
    rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  refine ⟨fun L _ _ h => mem_torusGroup_iff_existsUnique L h, fun M _ _ σ => ?_⟩
  have hidx : ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ d :=
    hdet ▸ fixedFieldImage_index_dvd σ
  exact ⟨fixedFieldImage_le, fixedFieldImage_normal, hidx,
    fun p hp hp3 P hPΓ hP => le_fixedFieldImage_of_isPGroup σ hd0 hd3 hidx hp hp3 hPΓ hP⟩

end CFSG.LieType.Chevalley
