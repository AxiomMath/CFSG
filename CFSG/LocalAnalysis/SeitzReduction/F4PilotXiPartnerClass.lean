module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerS

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6SecondGraphFixed (SecondGraphFixedSubgroup)
open CFSG.SeitzReduction.TwistedE6Pilot (relWordTX conj_relWordTX_pinnedX_highRoot)

local instance f4PilotXiPartnerClassNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotXiPartnerClassNeZeroRankE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Class


variable {k : Type} [Field k]

theorem f4OrbitXUnit_one_eq_pinnedX (c : k) :
    f4OrbitXUnit k 1 c = pinnedX TwistTag.E6.tag k (Pi.single 3 1) c := by
  rw [pinnedX_single]
  rfl

theorem exists_conj_e6FixedToF4_highRoot_eq_yRep_t [CharP k 2]
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
      twistedFixedGroup TwistTag.E6 k (RingHom.id k)) :
    ∃ c ∈ adjointGroup Tag.F4 k,
      c * e6FixedToF4 k ⟨_, ht⟩ * c⁻¹ = (yRep k .t : ModGL Tag.F4 k) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  set Γ := twistedFixedGroup TwistTag.E6 k (RingHom.id k) with hΓ
  have hn : twistedE6RelWeyl k relWordTX ∈ Γ :=
    graphFixedRootGroup_le _ _ _ (twistedE6RelWeyl_mem (RingHom.id k) relWordTX)
  have hconj : (⟨_, hn⟩ : Γ) * ⟨_, ht⟩ * (⟨_, hn⟩ : Γ)⁻¹ = ⟨_, f4OrbitXUnit_mem 1 1⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change _ = f4OrbitXUnit k 1 1
    rw [f4OrbitXUnit_one_eq_pinnedX]
    exact conj_relWordTX_pinnedX_highRoot 1
  have hΨ : e6FixedToF4 k ⟨_, hn⟩ * e6FixedToF4 k ⟨_, ht⟩ * (e6FixedToF4 k ⟨_, hn⟩)⁻¹ =
      pinnedX Tag.F4 k (Pi.single 1 1) 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, hconj, e6FixedToF4_f4OrbitXUnit h2, pinnedX_single]
  have hl1 : CFSG.LieType.Steinberg.Adjoint.iform (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ)
      (Pi.single 1 1) = 4 := by decide +kernel
  have hl2 : CFSG.LieType.Steinberg.Adjoint.iform root0122 root0122 = 4 := by decide +kernel
  obtain ⟨w₁, hw₁⟩ := exists_smul_eq_rootR (isRoot_single .F4 (1 : Fin (Tag.rank .F4))) hl1
  obtain ⟨w₂, hw₂⟩ := exists_smul_eq_rootR isRoot_root0122 hl2
  have hw : (w₂⁻¹ * w₁) • (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) = root0122 := by
    rw [mul_smul, hw₁, ← hw₂, inv_smul_smul]
  set n' := canonicalRep (coxeterSystem .F4) k (w₂⁻¹ * w₁) with hn'
  have hW : n' * pinnedX Tag.F4 k (Pi.single 1 1) 1 * n'⁻¹ = pinnedX Tag.F4 k root0122 1 := by
    rw [hn', canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single .F4 _) 1, hw]
  refine ⟨n' * e6FixedToF4 k ⟨_, hn⟩, mul_mem (canonicalRep_mem_adjointGroup _ k _)
    (e6FixedToF4_mem_adjointGroup h2 _), ?_⟩
  calc n' * e6FixedToF4 k ⟨_, hn⟩ * e6FixedToF4 k ⟨_, ht⟩ * (n' * e6FixedToF4 k ⟨_, hn⟩)⁻¹ =
      n' * (e6FixedToF4 k ⟨_, hn⟩ * e6FixedToF4 k ⟨_, ht⟩ * (e6FixedToF4 k ⟨_, hn⟩)⁻¹) * n'⁻¹ := by
        group
    _ = (yRep k .t : ModGL Tag.F4 k) := by rw [hΨ, hW]; rfl

end Class

section Perfect

theorem commutator_fixSubgroup_of_secondGraph {Gm : Type*} [Group Gm] {C J : Subgroup Gm}
    {P t : Gm} {H : Type*} [Group H] {e : J ≃* H} (hsec : SecondGraphFixedSubgroup C J P t e)
    {η : MulAut C} (hη : ∀ g : C, (η g : Gm) = P * g * P⁻¹) (hx : t ∈ C)
    (hperf : ∀ htJ : t ∈ J, ⁅centralizer ({e ⟨t, htJ⟩} : Set H),
      centralizer ({e ⟨t, htJ⟩} : Set H)⁆ = centralizer ({e ⟨t, htJ⟩} : Set H)) :
    ⁅E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η),
      E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η)⁆ =
    E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η) := by
  obtain ⟨htJ, hJC, η₀, hη₀, huniq, -, -, hfix, -, -, hiff1, hiff2⟩ := hsec
  have hηη₀ : η = η₀ := huniq η hη
  subst hηη₀
  set s := e ⟨t, htJ⟩ with hs
  set φ : H →* C := (J.subgroupOf C).subtype.comp
    ((subgroupOfEquivOfLe hJC).symm.toMonoidHom.comp e.symm.toMonoidHom) with hφ
  have hφe : ∀ x : J, ((φ (e x) : C) : Gm) = x := fun x => by
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rfl
  have hfixeq : E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η) =
      (centralizer ({s} : Set H)).map φ := by
    ext g
    constructor
    · intro hg
      have hg' : (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) g = g := hg
      obtain ⟨hgJ, -⟩ := (hfix g).1 hg'
      refine ⟨e ⟨g, hgJ⟩, ?_, Subtype.ext (hφe _)⟩
      exact mem_centralizer_singleton_iff.2 ((hiff1 ⟨g, hgJ⟩).1 ⟨g.2, hg'⟩)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, ⟨hxC, hxfix⟩, rfl⟩ := (hiff2 y).1 (mem_centralizer_singleton_iff.1 hy)
      have h1 : φ (e x) = ⟨x, hxC⟩ := Subtype.ext (hφe x)
      change (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) (φ (e x)) = φ (e x)
      rw [h1]
      exact hxfix
  rw [hfixeq, ← map_commutator, hperf htJ]


theorem commutator_centralizer_of_coe_eq {k : Type} [Field k] [Finite k] [CharP k 2]
    (hq : 4 ≤ Nat.card k)
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
      twistedFixedGroup TwistTag.E6 k (RingHom.id k))
    {s : adjointGroup Tag.F4 k} (hs : (s : ModGL Tag.F4 k) = e6FixedToF4 k ⟨_, ht⟩) :
    ⁅centralizer ({s} : Set (adjointGroup Tag.F4 k)),
      centralizer ({s} : Set (adjointGroup Tag.F4 k))⁆ =
    centralizer ({s} : Set (adjointGroup Tag.F4 k)) := by
  obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
  set c' : adjointGroup Tag.F4 k := ⟨c, hcC⟩
  have hcs : MulAut.conj c'⁻¹ (yRep k .t) = s := by
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, ← hc, hs]
    change c⁻¹ * (c * _ * c⁻¹) * c = _
    group
  have h := commutator_centralizer_map (factF3Perfect hq .t) (MulAut.conj c'⁻¹)
  rwa [hcs] at h

theorem xiFixPerfectE6Input_holds : XiFixPerfectE6Input := by
  intro f K' _ _ hf hK' η hη hx
  have hf1 : 1 ≤ f := by omega
  have := charP_two_of_natCard_eq_two_pow hK'
  have hM' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf1 hK' hM'
  let _ : Algebra K' (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hσM : ∀ c : GaloisField 2 (2 * f), iterateFrobenius (GaloisField 2 (2 * f)) 2 f c =
      c ^ 2 ^ f := fun c => iterateFrobenius_def (p := 2) f c
  obtain ⟨ht, -, -, -, ⟨eJ, -, heJ, hsec⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf1 K' (GaloisField 2 (2 * f)) hK' hM' _ hσM
  have hq : 4 ≤ Nat.card K' := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact commutator_fixSubgroup_of_secondGraph hsec hη hx fun htJ =>
    commutator_centralizer_of_coe_eq hq ht (heJ htJ)

theorem xiFixPerfectTwistedE6Input_holds : XiFixPerfectTwistedE6Input := by
  intro f K₂ _ _ σ hf hK₂ hσ η hη hx
  have hf1 : 1 ≤ f := by omega
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have := charP_two_of_natCard_eq_two_pow hk
  have : Finite (GaloisField 2 f) := finite_of_natCard_eq_two_pow hk
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf1 hk hK₂
  let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
  obtain ⟨ht, -, -, -, -, ⟨eJ, -, heJ, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf1 (GaloisField 2 f) K₂ hk hK₂ σ hσ
  have hq : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact commutator_fixSubgroup_of_secondGraph hsec hη hx fun htJ =>
    commutator_centralizer_of_coe_eq hq ht (heJ htJ)

end Perfect

section Inputs


theorem e6RowXiExclusionInput_of_caseL' (hL : E6RowXiCaseLInput) : E6RowXiExclusionInput :=
  e6RowXiExclusionInput_of_caseL xiFixPerfectE6Input_holds hL

theorem twistedE6RowXiExclusionInput_of_caseL' (hL : TwistedE6RowXiCaseLInput) :
    TwistedE6RowXiExclusionInput :=
  twistedE6RowXiExclusionInput_of_caseL xiFixPerfectTwistedE6Input_holds hL

end Inputs

section MainL


open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput) in
theorem seitzExclusion_highF4_of_caseL (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual)
    (hGr : GraphPieceTablesInput) (hECT : E6RowCTQuotInput) (hEL : E6RowXiCaseLInput)
    (hTCT : TwistedE6RowCTQuotInput) (hTL : TwistedE6RowXiCaseLInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_xiInputs' hGLS hSp6Odd hMinn hMcomp hres hGr hECT
    (e6RowXiExclusionInput_of_caseL' hEL) hTCT (twistedE6RowXiExclusionInput_of_caseL' hTL) h2

end MainL

end CFSG.SeitzReduction.F4Pilot
