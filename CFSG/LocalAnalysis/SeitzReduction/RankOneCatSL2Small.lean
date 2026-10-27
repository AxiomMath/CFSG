module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarAutL2
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarGroups
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem nonempty_mulEquiv_psl2Model_of_lieModel {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSL 2 2 f) : Nonempty (X ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  have hadm := F4Pilot.statedLieAdmissible_of_lieModel h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 f (by have := hadm.2.1; omega)]
  exact ⟨e.trans (GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv
    (FiniteField.ringEquivOfCardEq hcard))⟩

theorem card_mulAut_of_center_eq_bot {X : Type*} [Group X] [Finite X] (hZ : center X = ⊥) :
    Nat.card (MulAut X) = Nat.card X * Nat.card (Outer X) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center X := by
      rw [mem_center_iff]
      intro y
      have h1 := congrArg (fun β : MulAut X => β y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = g * y * g⁻¹ * g := by rw [h1]
        _ = g * y := by group
    rw [hZ] at hgZ
    exact mem_bot.mp hgZ
  have hcardInn : Nat.card (MulAut.conj : X →* MulAut X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← (MulAut.conj : X →* MulAut X).range.card_mul_index, hcardInn]
  rfl

theorem card_le_of_isPGroup_of_card_dvd {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) {N u : ℕ} (hu : Odd u) (hN : 0 < N) (hG : Nat.card G ∣ N * u) :
    Nat.card P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : 2 ^ k ∣ N * u := hk ▸ (Subgroup.card_subgroup_dvd_card P).trans hG
  have hcop : Nat.Coprime (2 ^ k) u := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu)
  rw [hk]
  exact Nat.le_of_dvd hN (hcop.dvd_of_dvd_mul_right h1)

theorem eq_one_of_forall_inv_mul_mem_center {D : Type*} [Group D] [Group.IsPerfect D]
    {α : MulAut D} (hα : ∀ d : D, d⁻¹ * α d ∈ center D) : α = 1 := by
  let φ : D →* center D :=
    { toFun := fun d => ⟨d⁻¹ * α d, hα d⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (a * b)⁻¹ * α (a * b) = (a⁻¹ * α a) * (b⁻¹ * α b)
        have ha : ∀ g : D, g * (a⁻¹ * α a) = (a⁻¹ * α a) * g := fun g =>
          mem_center_iff.mp (hα a) g
        rw [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (α a * α b) = b⁻¹ * (a⁻¹ * α a) * α b := by group
          _ = (a⁻¹ * α a) * b⁻¹ * α b := by rw [ha b⁻¹]
          _ = (a⁻¹ * α a) * (b⁻¹ * α b) := by group) }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := D)]
    exact Abelianization.commutator_subset_ker φ
  ext d
  have hd : d ∈ φ.ker := hker ▸ mem_top d
  rw [MonoidHom.mem_ker] at hd
  have hd' : d⁻¹ * α d = 1 := congrArg Subtype.val hd
  rw [MulAut.one_apply]
  calc α d = d * (d⁻¹ * α d) := by group
    _ = d := by rw [hd', mul_one]

@[expose] noncomputable def quotientCenterAutHom (D : Type*) [Group D] :
    MulAut D →* MulAut (D ⧸ center D) where
  toFun α := QuotientGroup.congr (center D) (center D) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem quotientCenterAutHom_mk {D : Type*} [Group D] (α : MulAut D) (d : D) :
    quotientCenterAutHom D α (QuotientGroup.mk d) = QuotientGroup.mk (α d) :=
  rfl

theorem quotientCenterAutHom_injective {D : Type*} [Group D] [Group.IsPerfect D] :
    Function.Injective (quotientCenterAutHom D) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine eq_one_of_forall_inv_mul_mem_center fun d => ?_
  have h := congrArg (fun β : MulAut (D ⧸ center D) => β (QuotientGroup.mk d)) hα
  simp only [quotientCenterAutHom_mk, MulAut.one_apply] at h
  have h1 : (α d)⁻¹ * d ∈ center D := QuotientGroup.eq.mp h
  have h2 := inv_mem h1
  rwa [mul_inv_rev, inv_inv] at h2

theorem card_le_two_of_le_centralizer {J : Type} [Group J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (h2 : FixedCentralizerTwoSmall τ D)
    {U : Subgroup (fixedSubgroup τ)} (hU : IsPGroup 2 U)
    (hUD : U ≤ centralizer (D : Set (fixedSubgroup τ))) : Nat.card U ≤ 2 := by
  have h := h2 (U.map (fixedSubgroup τ).subtype) (hU.map _) ?_ (map_subtype_le U)
  · rwa [card_map_of_injective (fixedSubgroup τ).subtype_injective] at h
  · rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hUD hu) d hd)

theorem normal_of_isComponent_of_twoSmall {J : Type} [Group J] [Finite J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D) (h2 : FixedCentralizerTwoSmall τ D) :
    D.Normal := by
  constructor
  intro d hd c
  set D' : Subgroup (fixedSubgroup τ) := D.map (MulAut.conj c).toMonoidHom with hD'
  have hD'c : IsComponent D' := LocalCores.isComponent_map_mulEquiv (MulAut.conj c) hD
  rcases LocalCores.distinct_components_commute hD hD'c with h | h
  · rw [h]
    exact ⟨d, hd, rfl⟩
  · exfalso
    have hle : D' ≤ centralizer (D : Set (fixedSubgroup τ)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm D' D).trans h)
    have hper : Group.IsPerfect D' := hD'c.1.1
    have hsub := subsingleton_of_perfect_of_two_small hper (fun U hU => by
      have h3 := card_le_two_of_le_centralizer h2 (hU.map D'.subtype) (by
        rintro _ ⟨u, -, rfl⟩
        exact hle u.2)
      rwa [card_map_of_injective D'.subtype_injective] at h3)
    have hnt := LocalCores.isQuasisimple_nontrivial hD'c.1
    exact not_nontrivial_iff_subsingleton.mpr hsub hnt

theorem card_le_of_isPGroup_fixedSubgroup {J : Type} [Group J] [Finite J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D) {n : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 n) (h2 : FixedCentralizerTwoSmall τ D)
    {Q : Subgroup (fixedSubgroup τ)} (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 * (2 ^ n * 2 ^ padicValNat 2 n) := by
  have hn : 2 ≤ n := two_le_of_lieModel_PSL_two_two hDm
  have hN : D.Normal := normal_of_isComponent_of_twoSmall hD h2
  have hQN : Q ≤ normalizer (D : Set (fixedSubgroup τ)) := by
    rw [normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hcard := card_eq_card_inf_centralizer_mul_card_range hQN
  have h1 : Nat.card (Q ⊓ centralizer (D : Set (fixedSubgroup τ)) : Subgroup _) ≤ 2 :=
    card_le_two_of_le_centralizer h2 (hQ.to_le inf_le_left) inf_le_right
  set R := (D.normalizerMonoidHom.comp (inclusion hQN)).range with hR
  have hRp : IsPGroup 2 R := hQ.of_surjective _
    (D.normalizerMonoidHom.comp (inclusion hQN)).rangeRestrict_surjective
  have : Group.IsPerfect D := hD.1.1
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_lieModel hDm
  have h3 := card_le_of_isPGroup_mulAut_psl2 hn e
    (hRp.map (quotientCenterAutHom D))
  rw [card_map_of_injective quotientCenterAutHom_injective] at h3
  rw [hcard]
  exact Nat.mul_le_mul h1 h3

end CFSG.SeitzReduction.RankOne
