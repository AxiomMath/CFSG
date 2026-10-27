module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglFix
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  LangTwistedProof Matrix
open scoped MatrixGroups

section Descent

variable {L : Type} [Field L] [CharP L 2]

theorem twistHom_secZ_even {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) :
    twistHom TwistTag.D4 L Fr (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1) =
      yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 := by
  have hp2 : TwistTag.D4.perm 2 = 2 := by decide
  rw [map_mul, twistHom_xUnit, twistHom_yUnit, hp2, hFr, map_one]

theorem pow_two_pow_even {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {n : ℕ} (hn : Even n) :
    (μ : L) ^ 2 ^ n = (μ : L) := by
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  obtain ⟨k, rfl⟩ := hn
  have hmod : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  rw [← Nat.div_add_mod (2 ^ (k + k)) 3, hmod, pow_add, pow_mul, h3, one_pow, one_mul, pow_one]

end Descent

theorem nonempty_autFix_equiv_secFixE {n : ℕ} (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [CharP (AlgebraicClosure K) 2] {μ : (AlgebraicClosure K)ˣ}
    (hμ : (μ : AlgebraicClosure K) ^ 2 + μ + 1 = 0)
    (hFrμ : iterateFrobenius (AlgebraicClosure K) 2 n (μ : AlgebraicClosure K) =
      (μ : AlgebraicClosure K)) :
    Nonempty (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) ≃*
      secFixE μ (iterateFrobenius (AlgebraicClosure K) 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  set P := diagramMap TwistTag.D4 K with hPdef
  have hσ₀ : ∀ x : C₀, ((σ₀ x : C₀) : ModGL TwistTag.D4.tag K) = P⁻¹ * x * P := by
    intro x
    have hx := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ x.2)).2
    rw [twistHom_apply] at hx
    rw [coe_fieldActor]
    calc Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) =
        P⁻¹ * (P * Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) * P⁻¹) *
          P := by group
      _ = P⁻¹ * x * P := by rw [hx]
  set ι := algebraMap K L with hιdef
  set PL := diagramMap TwistTag.D4 L with hPLdef
  have hιP : baseChangeGL ι P = PL := baseChangeGL_diagramMap ι TwistTag.D4
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι := by
    ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [hFr, hσ, map_pow]
  set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hz
  have hzG : z ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
  have hy0 : d4TrialityY0 L * PL⁻¹ = z * (secElt μ)⁻¹ * z⁻¹ := by
    rw [hz, ← wordUnit_secZWord]
    exact d4TrialityY0_mul_eq_conj h2L hμ
  have hcent : graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) =
      (secM μ).map (MulAut.conj z).toMonoidHom := by
    rw [hy0, graphCentralizer_conj hzG, graphCentralizer_inv, graphCentralizer_secElt_eq h2L hμ]
  have hFz : twistHom TwistTag.D4 L Fr z = z := twistHom_secZ_even hFrμ
  have hrange := CFSG.RankThree.PartOne.KGD.triEmb_range (σ := σ) (L := L) Nat.prime_two hn1 hK
    hσ Fr hFr
  set y₀ := d4TrialityY0Elt K σ with hy₀
  have hιy₀ : baseChangeGL ι (y₀ : ModGL TwistTag.D4.tag K) = d4TrialityY0 L :=
    baseChangeGL_d4TrialityY0 ι
  have key : ∀ x : C₀, (MulAut.conj y₀ * σ₀) x = x ↔
      CFSG.RankThree.PartOne.KGD.triEmb K σ L x ∈
        Subgroup.centralizer {d4TrialityY0 L * PL⁻¹} := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, CFSG.RankThree.PartOne.KGD.triEmb_apply,
      ← hιy₀, ← hιP, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      (baseChangeGL_injective ι).eq_iff]
    rw [MulAut.mul_apply, MulAut.conj_apply]
    constructor
    · intro h
      have h' := congrArg (fun u : C₀ => (u : ModGL TwistTag.D4.tag K)) h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀] at h'
      calc (x : ModGL TwistTag.D4.tag K) * ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹) =
          ((y₀ : ModGL TwistTag.D4.tag K) * (P⁻¹ * x * P) * (y₀ : ModGL TwistTag.D4.tag K)⁻¹) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹) := by rw [h']
        _ = (y₀ : ModGL TwistTag.D4.tag K) * P⁻¹ * x := by group
    · intro h
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀]
      calc (y₀ : ModGL TwistTag.D4.tag K) * (P⁻¹ * x * P) * (y₀ : ModGL TwistTag.D4.tag K)⁻¹ =
          ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹ * x) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)⁻¹ := by group
        _ = ((x : ModGL TwistTag.D4.tag K) * ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)⁻¹ := by rw [h]
        _ = x := by group
  have hF'' : ∀ g, twistHom TwistTag.D4 L Fr (z⁻¹ * g * z) =
      z⁻¹ * twistHom TwistTag.D4 L Fr g * z := by
    intro g
    rw [map_mul, map_mul, map_inv, hFz]
  set X := Sec4.autFix (MulAut.conj y₀ * σ₀)
  set f : X →* ModGL TwistTag.D4.tag L := (MulAut.conj z⁻¹).toMonoidHom.comp
    ((CFSG.RankThree.PartOne.KGD.triEmb K σ L).comp X.subtype) with hf
  have hfx : ∀ x : X, f x = z⁻¹ * CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1 * z := by
    intro x
    change (MulAut.conj z⁻¹) (CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1) = _
    rw [MulAut.conj_apply, inv_inv]
  have hmem : ∀ x : X, f x ∈ secFixE μ Fr := by
    intro x
    rw [hfx]
    set g := CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1
    have hgC : g ∈ graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) :=
      Subgroup.mem_inf.2 ⟨CFSG.RankThree.PartOne.KGD.triEmb_mem_adjointGroup x.1,
        (key x.1).1 x.2⟩
    rw [hcent] at hgC
    obtain ⟨m, hm, hmg⟩ := hgC
    have hmz : z⁻¹ * g * z = m := by
      rw [← hmg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨hmz ▸ hm, ?_⟩
    change twistHom TwistTag.D4 L Fr (z⁻¹ * g * z) = z⁻¹ * g * z
    rw [hF'', CFSG.RankThree.PartOne.KGD.triEmb_fixed Fr hcomm x.1]
  have hfinj : Function.Injective f := by
    intro x x' h
    rw [hfx, hfx] at h
    have h'' := mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (CFSG.RankThree.PartOne.KGD.triEmb_injective h'')
  refine ⟨MulEquiv.ofBijective (f.codRestrict (secFixE μ Fr) hmem) ⟨fun x x' h => hfinj
    (congrArg Subtype.val h), fun m => ?_⟩⟩
  set g := z * (m : ModGL TwistTag.D4.tag L) * z⁻¹ with hg
  have hgC : g ∈ graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) := by
    rw [hcent]
    exact ⟨m, m.2.1, rfl⟩
  have hFg : twistHom TwistTag.D4 L Fr g = g := by
    have hm2 : twistHom TwistTag.D4 L Fr (m : ModGL TwistTag.D4.tag L) = m := m.2.2
    have e : (m : ModGL TwistTag.D4.tag L) = z⁻¹ * g * z := by rw [hg]; group
    rw [e, hF''] at hm2
    calc twistHom TwistTag.D4 L Fr g = z * (z⁻¹ * twistHom TwistTag.D4 L Fr g * z) * z⁻¹ := by
          group
      _ = z * (z⁻¹ * g * z) * z⁻¹ := by rw [hm2]
      _ = g := by group
  have hgr : g ∈ (CFSG.RankThree.PartOne.KGD.triEmb K σ L).range := by
    rw [hrange]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hgC).1, hFg⟩
  obtain ⟨x, hx⟩ := hgr
  have hxX : x ∈ X := (key x).2 (hx ▸ (Subgroup.mem_inf.1 hgC).2)
  refine ⟨⟨x, hxX⟩, Subtype.ext ?_⟩
  change f ⟨x, hxX⟩ = m
  rw [hfx]
  change z⁻¹ * CFSG.RankThree.PartOne.KGD.triEmb K σ L x * z = m
  rw [hx, hg]
  group

theorem card_autFix_y0_even {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ)) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨μ, hμ⟩ := LangTwisted2Proof.exists_cube_root_unit (L := AlgebraicClosure K)
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hFrμ : Fr (μ : AlgebraicClosure K) = (μ : AlgebraicClosure K) := by
    rw [hFr]
    exact pow_two_pow_even hμ hfe
  obtain ⟨e₁⟩ := nonempty_autFix_equiv_secFixE hf hK hσ hμ hFrμ
  have e₂ := secFixEEquiv hμ hFrμ
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let _ := ZMod.algebra (AlgebraicClosure K) 2
  let ι : GaloisField 2 f →+* AlgebraicClosure K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f)
      (M := AlgebraicClosure K)).toRingHom
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨G₀, hG⟩ := exists_secD_fix hq hFr μ
  have e₃ := pglFixEEquiv ι hq hcard hFr μ hG
  have hc := Nat.card_congr (e₁.trans (e₂.trans e₃.symm)).toEquiv
  rw [hc, card_pgl_three, hcard]

theorem pgl_three_card_dvd_ordG2 (q : ℕ) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ CFSG.Open.ordG2 q := by
  obtain ⟨w, hw⟩ := Nat.sub_dvd_pow_sub_pow (q ^ 3) 1 2
  rw [one_pow, ← pow_mul] at hw
  unfold CFSG.Open.ordG2
  exact ⟨q ^ 3 * w, by rw [show q ^ 6 - 1 = (q ^ 3 - 1) * w from hw]; ring⟩

end CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl
