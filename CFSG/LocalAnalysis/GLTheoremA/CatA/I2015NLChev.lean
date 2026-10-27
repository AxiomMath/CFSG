module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLAct
import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.Chevalley.OppositeNoncommutativity
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge
  CFSG.SignalizerFunctorTheorem.NonLocalExc

section Model

set_option linter.unusedSectionVars false


theorem chevWitness_aux {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hNL : NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)))
    (S : (Fin τ.rank → ℤ) → Prop) (hS : S = IsRoot τ) (H : Subgroup (MarkChev.GLS S K))
    (hH : H = MarkChev.chevH τ.cartan S K false) {f : MulAut (↥H ⧸ Subgroup.center ↥H)}
    (hf : ∀ x : ↥H,
      MarkChev.entrywise S K σ (map_zero σ) ((x : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
        ((x : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) →
      f (QuotientGroup.mk x) = QuotientGroup.mk x) : NLWitness f := by
  subst hS
  have hH' : H = adjointGroup τ K := hH.trans (chevH_false_eq_adjointGroup K τ)
  subst hH'
  haveI : Finite (ModGL τ K) := finite_modGL
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e : (↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hJle : fixedFieldImage τ σ ≤ adjointGroup τ K := fixedFieldImage_le.trans inf_le_left
  let D : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥D ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJle).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  have hsD : IsSimpleGroup ↥D := eJ.isSimpleGroup
  have hna : ∃ x y : ↥D, x * y ≠ y * x := by
    obtain ⟨g, h, hgh⟩ := (opposite_simple_root_noncommutativity τ (fixSubfield σ)).2.2.1
    exact ⟨eJ.symm g, eJ.symm h, fun h' => hgh (eJ.symm.injective (by rw [map_mul, map_mul]; exact h'))⟩
  refine nlWitness_of_nonLocalized e hsD hna hNL ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxJ : (x : ModGL τ K) ∈ fixedFieldImage τ σ := hx
  have hfix : Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) = x :=
    (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hxJ)).2
  show f (e.symm x) = e.symm x
  have hex : e.symm x = QuotientGroup.mk x := rfl
  rw [hex]
  exact hf x (congrArg Units.val hfix)

theorem chevWitness_of_fixed {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hNL : NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)))
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : ∀ x : ↥(LargeEvenChevH τ.cartan K false), chevRho τ K σ x = x →
      f (QuotientGroup.mk x) = QuotientGroup.mk x) : NLWitness f := by
  refine chevWitness_aux σ hs hNL (LargeEvenIsRoot τ.cartan) (largeEvenIsRoot_eq_isRoot τ)
    (LargeEvenChevH τ.cartan K false) (largeEvenChevH_eq τ.cartan K false) fun x hx => hf x ?_
  apply Subtype.ext
  apply Units.ext
  show ((chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) : LargeEvenChevGL τ.cartan K) :
    Module.End K (LargeEvenChevModule τ.cartan K)) = _
  rw [chevAct_val]
  exact hx

theorem chevWitness_of_mem {τ : Tag} {K : Type} [Field K] [Finite K]
    (hs : ∀ σ : K ≃+* K, IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hNL : ∀ σ : K ≃+* K, NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)))
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) :
    NLWitness f := by
  obtain ⟨σ, hσ⟩ := hf
  refine chevWitness_of_fixed σ (hs σ) (hNL σ) fun x hx => hσ x x ?_
  have h2 : chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) = (x : LargeEvenChevGL τ.cartan K) :=
    congrArg Subtype.val hx
  exact (congrArg (fun y : LargeEvenChevGL τ.cartan K =>
    (y : Module.End K (LargeEvenChevModule τ.cartan K))) h2).symm

end Model

section Sigma

set_option linter.unusedSectionVars false


theorem chevSigmaZero {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : ℕ}
    (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (hord : orderOf f = p) :
    ∃ σ₀ : K ≃+* K, orderOf σ₀ = p ∧ p ∣ m ∧ Nat.card (fixSubfield σ₀) = 2 ^ (m / p) ∧
      ∀ x : ↥(LargeEvenChevH τ.cartan K false), chevRho τ K σ₀ x = x →
        f (QuotientGroup.mk x) = QuotientGroup.mk x := by
  have hu : 0 < chevExp τ := by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
  haveI : Finite ↥(LargeEvenChevH τ.cartan K false) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_chevH]
    obtain ⟨r, hr, h⟩ := card_adjointGroup_spec hτ hm hK
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  obtain ⟨σ, hσ⟩ := hf
  have hZo : Odd (Nat.card (Subgroup.center ↥(LargeEvenChevH τ.cartan K false))) := by
    rw [card_center_chevH]
    exact odd_one
  have hσ' : ∀ x : ↥(LargeEvenChevH τ.cartan K false),
      f (QuotientGroup.mk x) = QuotientGroup.mk (chevRho τ K σ x) := fun x =>
    hσ x (chevRho τ K σ x) (by
      show ((chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) : LargeEvenChevGL τ.cartan K) :
        Module.End K (LargeEvenChevModule τ.cartan K)) = _
      rw [chevAct_val])
  have hordH : CFSG.LocalAnalysis.GLTheoremA.S10.twoPart
      (Nat.card ↥(LargeEvenChevH τ.cartan K false)) ^ 1 = 2 ^ (m * chevExp τ) := by
    rw [pow_one, card_chevH]
    exact twoPart_card_adjointGroup hτ hm hK
  have hfix : ∀ σ : K ≃+* K, True → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      CFSG.LocalAnalysis.GLTheoremA.S10.twoPart (CFSG.LocalAnalysis.GLTheoremA.FP.fixNum
        (chevRho τ K σ)) ^ 1 = 2 ^ (e * chevExp τ) := by
    intro σ _ e he
    have hk : Nat.card (fixSubfield σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, chevRho, fixNum_chev, fixCountS_eq,
      twoPart_card_entrywiseFixedGroup σ hk (one_le_of_card_fixed he)]
    exact twoPart_card_adjointGroup hτ (one_le_of_card_fixed he) hk
  obtain ⟨σ₀, hσ₀, -, hdvd, hcard, hfixed⟩ := fixed_of_action hm hK
    (Subgroup.center ↥(LargeEvenChevH τ.cartan K false)) le_rfl hZo
    (chevRho τ K) (fun _ => True) (fun _ _ _ => trivial) hu one_pos hordH hfix hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) f σ hσ' hord
  exact ⟨σ₀, hσ₀, hdvd, card_fixF.trans hcard, hfixed⟩

end Sigma

section FamilyFE

set_option linter.unusedSectionVars false


theorem i2015NLOnF4_holds : I2015NLOnF4 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro _ _ _ _ _ _ Q hQ
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ =>
    chevWitness_of_mem (τ := .F4)
      (fun _ => isSimpleGroup_adjointGroup_of_quasisimple
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 _))
      (fun σ => nonLocalized_F4 σ) hf⟩

theorem i2015NLOnE_holds : I2015NLOnE := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_ (fun p _ h => by
    rcases ht with h' | h' | h' <;> (rw [h'] at h; exact absurd h.1 (by decide)))
  intro _ _ _ _ _ _ Q hQ
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  rcases ht with rfl | rfl | rfl
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ =>
      chevWitness_of_mem (τ := .E6)
        (fun _ => isSimpleGroup_adjointGroup_of_quasisimple
          (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 _))
        (fun σ => nonLocalized_E6 σ) hf⟩
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ =>
      chevWitness_of_mem (τ := .E7)
        (fun _ => isSimpleGroup_adjointGroup_of_quasisimple
          (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 _))
        (fun σ => nonLocalized_E7 σ) hf⟩
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ =>
      chevWitness_of_mem (τ := .E8)
        (fun _ => isSimpleGroup_adjointGroup_of_quasisimple
          (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 _))
        (fun σ => nonLocalized_E8 σ) hf⟩

end FamilyFE

section FamilyG2

set_option linter.unusedSectionVars false


theorem i2015NLOnG2_holds : I2015NLOnG2 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp _ _ _ hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht hC
  subst ht
  obtain ⟨-, -, hn2⟩ := hlab
  unfold regN at hC
  dsimp only at hC hn2
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf hord _ _ => ?_⟩
  obtain ⟨σ₀, -, hdvd, hcard, hfix⟩ := chevSigmaZero (τ := .G2) (Or.inl rfl) (by omega) hK hp hf hord
  obtain ⟨c, hc⟩ := hdvd
  have hnc : n / p = c := by rw [hc, Nat.mul_div_cancel_left c hp.pos]
  have hc0 : c ≠ 0 := by
    rintro rfl
    omega
  have hc1 : c ≠ 1 := fun h => hC (by rw [hc, h, mul_one])
  have h3k : 3 ≤ Nat.card (fixSubfield σ₀) := by
    rw [hcard, hnc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact chevWitness_of_fixed (τ := .G2) σ₀
    (isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card _ h3k))
    (nonLocalized_G2 σ₀) hfix

end FamilyG2

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
