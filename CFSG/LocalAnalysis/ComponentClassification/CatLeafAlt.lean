module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def IsAltType (K : Type) [Group K] : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), 5 ≤ Fintype.card Ω ∧
    Nonempty (K ≃* alternatingGroup Ω)

theorem IsAltType.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsAltType K') : IsAltType K := by
  obtain ⟨Ω, _, _, hΩ, ⟨f⟩⟩ := h
  exact ⟨Ω, _, _, hΩ, ⟨e.trans f⟩⟩

theorem not_isHeldType_of_isAltType {K : Type} [Group K] (h : IsAltType K) :
    ¬ GrSLit.IsHeldType K := by
  rintro ⟨eH⟩
  obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := h
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcard : (Fintype.card Ω).factorial / 2 = 4030387200 := by
    rw [← Sporadic.He.card_He, ← Nat.card_congr eH.toEquiv, Nat.card_congr eA.toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  rcases le_or_gt (Fintype.card Ω) 13 with h13 | h14
  · have h1 := Nat.factorial_le h13
    have h2 : (Fintype.card Ω).factorial / 2 ≤ (13 : ℕ).factorial / 2 := Nat.div_le_div_right h1
    rw [hcard] at h2
    exact absurd h2 (by decide)
  · have h1 := Nat.factorial_le (show 14 ≤ Fintype.card Ω by omega)
    have h2 : (14 : ℕ).factorial / 2 ≤ (Fintype.card Ω).factorial / 2 := Nat.div_le_div_right h1
    rw [hcard] at h2
    exact absurd h2 (by decide)

theorem statedClassicalModel_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ}
    (h : Blueprint.LieModel X .PSL n p f) :
    Assembly.LowTwoRank.StatedClassicalModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem card_of_isL34Type {K : Type} [Group K] (h : GrSLit.IsL34Type K) : Nat.card K = 20160 :=
  (PSL3Four.excludes_alternating_models_stated.{0} K (statedClassicalModel_of_lieModel_psl h)).1

theorem not_isL34Type_of_isAltType {K : Type} [Group K] (h : IsAltType K) :
    ¬ GrSLit.IsL34Type K := by
  intro hL
  obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := h
  obtain ⟨-, -, h⟩ :=
    PSL3Four.excludes_alternating_models_stated K (statedClassicalModel_of_lieModel_psl hL)
  exact (h Ω hΩ).false eA

theorem exists_involution_of_properFixedComponent_alternating {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {σ : MulAut (alternatingGroup (Fin n))} {P : Subgroup (alternatingGroup (Fin n))}
    (h : ProperFixedComponent σ P) :
    ∃ τ : Perm (Fin n), orderOf τ = 2 ∧ σ = MulAut.conjNormal τ ∧
      5 ≤ (Finset.univ.filter fun x => τ x = x).card ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃*
        alternatingGroup ↥(Finset.univ.filter fun x => τ x = x)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hσ1 := h.ne_one
  obtain ⟨hσ, hPF, hP, -⟩ := h
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  obtain ⟨τ, rfl⟩ := hbij.2 σ
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin n), ((c τ x : alternatingGroup (Fin n)) : Perm (Fin n))
      = τ * x * τ⁻¹ := fun x => rfl
  have hττ : τ * τ = 1 := by
    apply hbij.1
    rw [map_mul, map_one]
    ext x
    rw [MulAut.mul_apply, hσ, MulAut.one_apply]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one c)
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set F := fixedSubgroup (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin n), x ∈ F ↔ τ * (x : Perm (Fin n)) = x * τ := by
    intro x
    change c τ x = x ↔ _
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin n)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin n)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = ((y : alternatingGroup (Fin n)) :
        Perm (Fin n)) := congrArg (fun z : N => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hR : R.Normal := inferInstance
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ L hL
  let eL : L₀ ≃* L := (L₀.equivMapOfInjective e₁.toMonoidHom e₁.injective).trans
    ((L₀.map e₁.toMonoidHom).equivMapOfInjective R.subtype R.subtype_injective)
  let eA : L ≃* alternatingGroup (MulAction.fixedPoints Q (Fin n)) :=
    (MulEquiv.subgroupCongr hLeq).trans
      ((alternatingGroup (MulAction.fixedPoints Q (Fin n))).equivMapOfInjective _
        (CatalogueBAlternating.fixedPointsNormalizerHom_injective Q)).symm
  have : IsSimpleGroup (alternatingGroup (MulAction.fixedPoints Q (Fin n))) :=
    alternatingGroup.isSimpleGroup hdeg
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP (eL.trans eA)
  obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  have hfix : ∀ x : Fin n, x ∈ MulAction.fixedPoints Q (Fin n) ↔
      x ∈ (Finset.univ.filter fun x => τ x = x) := by
    intro x
    rw [Finset.mem_filter, MulAction.mem_fixedPoints]
    constructor
    · intro hx
      exact ⟨Finset.mem_univ x, hx ⟨τ, mem_zpowers τ⟩⟩
    · rintro ⟨-, hx⟩ ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact Perm.zpow_apply_eq_self_of_apply_eq_self hx k
  let eΩ := Equiv.subtypeEquivRight hfix
  have hcard : Nat.card (MulAction.fixedPoints Q (Fin n)) =
      (Finset.univ.filter fun x => τ x = x).card := by
    rw [Nat.card_congr eΩ, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact ⟨τ, hτ2, rfl, hcard ▸ hdeg, ⟨(eP.trans eZ).trans eΩ.altCongrHom⟩⟩

theorem isAltType_of_properFixedComponent_alternating {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {σ : MulAut (alternatingGroup (Fin n))} {P : Subgroup (alternatingGroup (Fin n))}
    (h : ProperFixedComponent σ P) : IsAltType (P ⧸ Open.fusionZStar P) := by
  obtain ⟨τ, -, -, hdeg, he⟩ := exists_involution_of_properFixedComponent_alternating hn hn6 h
  exact ⟨_, _, _, by rw [Fintype.card_coe]; exact hdeg, he⟩

theorem not_isHeldType_of_properFixedComponent_alternating {S : Type} [Group S] [Finite S]
    {n : ℕ} (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := by
  by_cases hn6 : n = 6
  · subst hn6
    rintro ⟨eH⟩
    have h1 := card_dvd_of_fusionZStar_equiv eH.toEquiv
    rw [Sporadic.He.card_He, Nat.card_congr θ.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 := Nat.le_of_dvd (by norm_num [Nat.factorial]) h1
    norm_num [Nat.factorial] at h2
  obtain ⟨h', ⟨e⟩⟩ := h.map θ
  exact fun hH => not_isHeldType_of_isAltType
    ((isAltType_of_properFixedComponent_alternating hn hn6 h').of_mulEquiv e) hH

theorem not_isL34Type_of_properFixedComponent_alternating {S : Type} [Group S] [Finite S]
    {n : ℕ} (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ GrSLit.IsL34Type (P ⧸ Open.fusionZStar P) := by
  by_cases hn6 : n = 6
  · subst hn6
    intro hL
    have hc := card_of_isL34Type hL
    have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
    rw [hc, Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    have h2 := Nat.le_of_dvd (by norm_num [Nat.factorial]) h1
    norm_num [Nat.factorial] at h2
  obtain ⟨h', ⟨e⟩⟩ := h.map θ
  exact fun hL => not_isL34Type_of_isAltType
    ((isAltType_of_properFixedComponent_alternating hn hn6 h').of_mulEquiv e) hL

end CFSG.ComponentClassification.CatLeaf
