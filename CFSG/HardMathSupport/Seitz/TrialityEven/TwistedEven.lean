module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.TwistedThree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoToral

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.ClassicalInvolution.G2D4Models CFSG.HardMathSupport.Seitz.TrialityOdd
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator


section Identification

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def TwistedGroupIdent : Prop :=
  (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype =
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom

variable {σ}

theorem twistedIncl_mem_root_of_eq (hid : TwistedGroupIdent σ) (z : twistedGroup σ.toRingHom) :
    twistedIncl σ.toRingHom z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  rw [← hid]
  exact ⟨(z : adjointGroup d4 K), z.2, rfl⟩

theorem mem_J_iff_of_eq (hid : TwistedGroupIdent σ) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (z : twistedGroup σ.toRingHom) :
    twistedIncl σ.toRingHom z ∈ trialityFieldImage σ σ ↔ z ∈ FixedSub σ := by
  have hC := twistedIncl_mem_root_of_eq hid z
  have h := d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨twistedIncl σ.toRingHom z, hC⟩
  rw [mem_FixedSub]
  refine h.trans ?_
  constructor
  · intro hz
    have := congrArg Subtype.val hz
    rwa [coe_fieldActor] at this
  · intro hz
    refine Subtype.ext ?_
    rw [coe_fieldActor]
    exact hz

def fixedSubEquivJ_of_eq (hid : TwistedGroupIdent σ) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    ↥(FixedSub σ) ≃* ↥(trialityFieldImage σ σ) :=
  MulEquiv.ofBijective
    (((twistedIncl σ.toRingHom).comp (FixedSub σ).subtype).codRestrict (trialityFieldImage σ σ)
      (fun z => (mem_J_iff_of_eq hid hσ3 z.1).2 z.2))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a.1 = twistedIncl σ.toRingHom b.1 :=
        congrArg (Subtype.val : ↥(trialityFieldImage σ σ) → ModGL TwistTag.D4.tag K) h
      exact Subtype.ext (CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1),
      by
      rintro ⟨g, hg⟩
      have hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
        d4_trialityFieldImage_self_le σ hg
      have h := hid
      rw [← h] at hgC
      obtain ⟨a, ha, rfl⟩ := hgC
      exact ⟨⟨⟨a, ha⟩, (mem_J_iff_of_eq hid hσ3 ⟨a, ha⟩).1 hg⟩, rfl⟩⟩

def twistedEquivRoot_of_eq (hid : TwistedGroupIdent σ) :
    twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  MulEquiv.ofBijective
    ((twistedIncl σ.toRingHom).codRestrict (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (fun z => twistedIncl_mem_root_of_eq hid z))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a = twistedIncl σ.toRingHom b :=
        congrArg (Subtype.val : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
          ModGL TwistTag.D4.tag K) h
      exact CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1, by
      rintro ⟨g, hg⟩
      have h := hid
      rw [← h] at hg
      obtain ⟨a, ha, rfl⟩ := hg
      exact ⟨⟨a, ha⟩, rfl⟩⟩

end Identification

open Subgroup CFSG.GH74.GLS.Stage4.Hex in
theorem closure_cenGen_twistedGroup_three_of_eq {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hid : TwistedGroupIdent σ) {q : ℕ} (hq : 3 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (h3q : 3 ∣ q + 1)
    (F : Subgroup (twistedGroup σ.toRingHom)) (hFJ : F ≤ FixedSub σ) (hFp : ∀ x ∈ F, x ^ 3 = 1)
    (hFc : Nat.card F = 3 ^ 2) : Subgroup.closure (cenGen F) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ q := by omega
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hcardF : Nat.card (fixedField σ.toRingHom) = q :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσq
  have hcardX : Nat.card (fixSubfield σ) = q := hcardF
  obtain ⟨M, hM⟩ := exists_sl2_orderOf (fixedField σ.toRingHom) (p := 3)
    (by rw [hcardF]; exact h3q)
  let nh : twistedGroup σ.toRingHom := nHat σ.toRingHom (ng 0) * nHat σ.toRingHom (ng 1)
  let b : twistedGroup σ.toRingHom := slLong σ.toRingHom hσ3' M
  let b₀ : twistedGroup σ.toRingHom := nh * b * nh⁻¹
  let L : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M
  let v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3' L
  have hLfix : Matrix.SpecialLinearGroup.map σ.toRingHom L = L := by
    refine Subtype.ext ?_
    ext i j
    simp only [L, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (M.1 i j).2
  have hnhJ : nh ∈ FixedSub σ :=
    mul_mem (nHat_zero_mem_FixedSub σ hσ3) (nHat_one_mem_FixedSub σ hσ3)
  have hbJ : b ∈ FixedSub σ := slLong_mem_FixedSub σ hσ3 M
  have hb₀J : b₀ ∈ FixedSub σ := mul_mem (mul_mem hnhJ hbJ) (inv_mem hnhJ)
  have hvJ : v ∈ FixedSub σ := slShort_mem_FixedSub σ hσ3 L hLfix
  have hob : orderOf b = 3 := by
    rw [orderOf_injective (slLong σ.toRingHom hσ3') (slLong_injective hσ3') M, hM]
  have hob₀ : orderOf b₀ = 3 := by
    have := orderOf_injective (MulAut.conj nh).toMonoidHom (MulAut.conj nh).injective b
    rw [← hob]
    exact this
  have hoL : orderOf L = 3 := by
    rw [orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (fixedField σ.toRingHom).subtype) (sl_map_injective _) M, hM]
  have hov : orderOf v = 3 := by
    rw [orderOf_injective (slShort σ.toRingHom hσ3') (slShort_injective hσ3') L, hoL]
  have hb₀theta : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    have e : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        (nHatE K (ng 0) * nHatE K (ng 1)) * (b : adjointGroup d4 K) *
          (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ := by
      have hn0 : (nHat σ.toRingHom (ng 0) : adjointGroup d4 K) = nHatE K (ng 0) := nHat_val _ _
      have hn1 : (nHat σ.toRingHom (ng 1) : adjointGroup d4 K) = nHatE K (ng 1) := nHat_val _ _
      simp only [b₀, nh, Subgroup.coe_mul, Subgroup.coe_inv, hn0, hn1, mul_assoc, mul_inv_rev]
    rw [e]
    exact conj_mem_thetaGroup (slLong_coe_mem_central σ.toRingHom hσ3' M)
  have hAb : ∀ a ∈ (slShort σ.toRingHom hσ3').range, a * b₀ = b₀ * a := by
    rintro _ ⟨B, rfl⟩
    refine Subtype.ext ?_
    exact (commute_thetaGroup_outerRankOne hb₀theta
      (slShort_coe_mem_outer σ.toRingHom hσ3' B)).eq.symm
  have hcomm : Commute b₀ v := (hAb v ⟨L, rfl⟩).symm
  have hnot : v ∉ zpowers b₀ := by
    intro hv'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hv'
    have hLc : L ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply slShort_injective hσ3'
      rw [map_mul, map_mul]
      have h1 : Commute b₀ (slShort σ.toRingHom hσ3' B) := (hAb _ ⟨B, rfl⟩).symm
      have h2 := (h1.zpow_left i).eq
      rw [hi] at h2
      exact h2.symm
    have h2 := sq_eq_one_of_mem_center hLc
    have h3 : orderOf L ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hoL] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨E₀, hbE, -, hE₀p, hE₀c, hE₀le⟩ := exists_plane_of_commute hob₀ hov hcomm hnot
  have hE₀J : E₀ ≤ FixedSub σ := hE₀le _ hb₀J hvJ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    have : Finite (fixSubfield σ) := inferInstance
    rw [ENat.card_eq_coe_natCard, hcardX]
    exact_mod_cast hq
  let ε : ↥(FixedSub σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (fixedSubEquivJ_of_eq hid hσ3).trans (trialityFieldImageEquivG2 σ hk3)
  have hkq : 3 ≤ Nat.card (fixSubfield σ) := by rw [hcardX]; exact hq
  have hk1 : 3 ∣ Nat.card (fixSubfield σ) + 1 := by rw [hcardX]; exact h3q
  obtain ⟨hE₀ea, hE₀cd⟩ := isElemAbelian_map_subgroupOf ε hE₀J hE₀p hE₀c
  obtain ⟨hFea, hFcd⟩ := isElemAbelian_map_subgroupOf ε hFJ hFp hFc
  have hJgen : closure (cenGen (E₀.subgroupOf (FixedSub σ))) = ⊤ :=
    closure_cenGen_eq_top_of_map ε _
      (G2Anisotropic.Coordinator.g2NativePlaneGen_three_of_dvd_add_one (fixSubfield σ) hkq hk1
        _ hE₀ea hE₀cd)
  have hJA : FixedSub σ ⊔ (slShort σ.toRingHom hσ3').range = ⊤ := by
    have h := CFSG.ClassicalInvolution.G2D4Models.range_slLong_sup_range_slShort hσ3'
    rw [eq_top_iff, ← h]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨A, rfl⟩
    exact slLong_mem_FixedSub σ hσ3 A
  have hJle : FixedSub σ ≤ closure (cenGen E₀) := by
    have h1 : (closure (cenGen (E₀.subgroupOf (FixedSub σ)))).map (FixedSub σ).subtype ≤
        closure (cenGen E₀) := by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨k, ⟨x, hx, hx1, hk⟩, rfl⟩
      refine ⟨(x : twistedGroup σ.toRingHom), hx, fun h => hx1 (Subtype.ext h), ?_⟩
      exact congrArg Subtype.val hk
    rw [hJgen, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hob₀
    exact absurd hob₀ (by norm_num)
  have hAle : (slShort σ.toRingHom hσ3').range ≤ closure (cenGen E₀) := fun a ha =>
    subset_closure ⟨b₀, hbE, hb₀1, hAb a ha⟩
  have htop₀ : closure (cenGen E₀) = ⊤ := by
    rw [eq_top_iff, ← hJA]
    exact sup_le hJle hAle
  obtain ⟨x, hx⟩ := exists_conj_of_plane_G2 (fixSubfield σ) hkq hk1 _ _ hE₀ea hE₀cd hFea hFcd
  have hFE := eq_map_conj_of_map_subgroupOf ε hE₀J hFJ x hx
  rw [hFE]
  change closure (cenGen (cj E₀ _)) = ⊤
  rw [closure_cenGen_cj, htop₀, Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective]

theorem twistedTorusPlaneGenEvenThree :
    ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (2 ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) → 3 ∣ 2 ^ f + 1 →
      ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
        D4PlaneInTorusMinus 2 f Nat.prime_two K σ E →
        Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
          ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  intro f hf K _ _ hK σ hσ h3q E hEea hEc hT0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, _, _, _, g₀, ⟨-, hg₀P, -⟩, β, hβ⟩ := hT0
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'3 : ∀ y ∈ E', y ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    change (β⁻¹ e) ^ 3 = 1
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian e he, map_one]
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective, hEc]
  have hfix : ∀ y ∈ E', fieldActor (t := TwistTag.D4) σ σ y = y := by
    rintro _ ⟨e, he, rfl⟩
    exact fieldActor_eq_of_twistedTorus σ hσ h3q hg₀P _ (hE'3 _ ⟨e, he, rfl⟩) (hβ e he)
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq3 : 3 ≤ 2 ^ f := by omega
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hid : TwistedGroupIdent σ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.map_twistedGroup_eq_graphFixedRootGroup_two
      (by omega) hK σ hσ
  let eR := twistedEquivRoot_of_eq hid
  set F := E'.map eR.symm.toMonoidHom with hF
  have hFJ : F ≤ FixedSub σ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← mem_J_iff_of_eq hid hσ3]
    have h1 : twistedIncl σ.toRingHom (eR.symm.toMonoidHom y) =
        ((eR (eR.symm y) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
    exact (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ hσ3 y).2
      (hfix y hy)
  have hFp : ∀ x ∈ F, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (eR.symm y) ^ 3 = 1
    rw [← map_pow, hE'3 y hy, map_one]
  have hFc : Nat.card F = 3 ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective eR.symm.injective, hE'c]
  have hgen := closure_cenGen_twistedGroup_three_of_eq σ hσ3 hid hq3 hK hσ h3q F hFJ hFp hFc
  have hE'gen : Subgroup.closure (cenGen E') = ⊤ := closure_cenGen_eq_top_of_map eR.symm E' hgen
  change Subgroup.closure (cenGen E') = ⊤ at hE'gen
  have h := Proving.closure_centralizers_map_mulAut (β⁻¹) E
  change Subgroup.closure (cenGen E') = _ at h
  rw [hE'gen, ← Subgroup.map_top_of_surjective (β⁻¹).toMonoidHom (β⁻¹).surjective] at h
  exact (Subgroup.map_injective (β⁻¹).injective h).symm

end CFSG.HardMathSupport.Seitz.TrialityEven
