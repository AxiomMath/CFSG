module

public import CFSG.ClassicalInvolution.Q3.Q3T7H4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace TwinThmE

section

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
theorem eq_of_conjSub_le_of_l6_7 [Finite G] (h67 : L6_7On Ω)
    (hΩ : HypOmegaGen Ω) {R Y X S : Subgroup G} (hR : R ∈ RSet Ω) (hRY : R ≤ Y)
    (hXn : ∀ y ∈ Y, conjSub y X = X) (hRX : R ⊓ X = ⊥) (hS2 : IsPGroup 2 S)
    (hRS : R ≤ S) (hSH : S ≤ X ⊔ R) {g : G} (hg : g ∈ Y) (hle : conjSub g R ≤ S) :
    conjSub g R = R := by
  by_contra hne
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hR'' : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR g
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hS2
  have hcomm : Commutes R (conjSub g R) :=
    h67 S₀ R hR (conjSub g R) hR'' (hRS.trans hS₀) (hle.trans hS₀) (Ne.symm hne)
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hR''Y : conjSub g R ≤ Y := conjSub_le_of_le_of_mem_left hRY hg
  have hR''N : conjSub g R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hR''Y hx)
  have hR''X : X ⊓ conjSub g R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxR⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSub_iff] at hxR
    have hxX' : g⁻¹ * x * g ∈ X := by
      have := conj_mem_conjSub (n := g⁻¹) hxX
      rwa [hXn g⁻¹ (Y.inv_mem hg), inv_inv] at this
    have h1 : g⁻¹ * x * g ∈ R ⊓ X := ⟨hxR, hxX'⟩
    rw [hRX, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hcard : Nat.card (conjSub g R) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc1 : Nat.card (X ⊔ conjSub g R : Subgroup G) = Nat.card X * Nat.card (conjSub g R) :=
    card_sup_of_le_normalizer hR''N hR''X
  have hc2 : Nat.card (X ⊔ R : Subgroup G) = Nat.card X * Nat.card R :=
    card_sup_of_le_normalizer hRN (by rwa [inf_comm])
  have hle2 : X ⊔ conjSub g R ≤ X ⊔ R := sup_le le_sup_left (hle.trans hSH)
  have heq : X ⊔ conjSub g R = X ⊔ R :=
    Subgroup.eq_of_le_of_card_ge hle2 (by rw [hc1, hc2, hcard])
  have hF : Frame X (conjSub g R) :=
    ⟨hR''N, by rwa [inf_comm], isPGroup_conjSub g hR2⟩
  obtain ⟨a, ha, b, hb, hab⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_not_commute
  apply hab
  have hamem : a ∈ X ⊔ conjSub g R := heq ▸ (le_sup_right : R ≤ X ⊔ R) ha
  obtain ⟨t, ht, c, hc, hr⟩ := hF.mem_sup_iff.mp hamem
  have hcdef : c = t⁻¹ * a := by rw [← hr]; group
  have hct : t⁻¹ * (a * b * a⁻¹) * t = a * b * a⁻¹ := by
    have := hcomm (a * b * a⁻¹) (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) t ht
    rw [mul_assoc, this]
    group
  have hw1 : a * b * a⁻¹ * b⁻¹ ∈ R := R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha))
    (R.inv_mem hb)
  have hw2 : a * b * a⁻¹ * b⁻¹ ∈ X := by
    have e : a * b * a⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by
      calc a * b * a⁻¹ * b⁻¹ = (t⁻¹ * (a * b * a⁻¹) * t) * b⁻¹ := by rw [hct]
        _ = c * (b * c⁻¹ * b⁻¹) := by rw [hcdef]; group
    rw [e]
    refine X.mul_mem hc ?_
    have := conj_mem_conjSub (n := b) (X.inv_mem hc)
    rwa [hXn b (hRY hb)] at this
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ R ⊓ X := ⟨hw1, hw2⟩
  rw [hRX, Subgroup.mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem l6_13_on [Finite G] (hΩ : HypOmegaGen Ω) (h67 : L6_7On Ω) :
    ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
      R ⊓ X = ⊥ →
        (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
            R ⊔ oddCoreOf X ∧
          ⁅R, X⁆ ≤ oddCoreOf X := by
  intro R hR Y X hRY hXY hXn hRX
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hHY : X ⊔ R ≤ Y := sup_le hXY hRY
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le hR2 (le_sup_right : R ≤ X ⊔ R)
  have hclosed : ∀ g ∈ Y, conjSub g R ≤ S → conjSub g R = R := fun g hg hle =>
    eq_of_conjSub_le_of_l6_7 h67 hΩ hR hRY hXn hRX hS.isPGroup hRS hS.le hg hle
  have h42 : Hyp42 X R S :=
    { frame := ⟨hRN, hRX, hR2⟩
      sylow := hS
      le := hRS
      closed := fun g hg hle => hclosed g⁻¹ (Y.inv_mem (hXY hg)) hle }
  have hcomm : ⁅X, R⁆ ≤ oddCoreOf X := lemma_4_2_oddCore h42
  have hcomm' : ⁅R, X⁆ ≤ oddCoreOf X := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  refine ⟨?_, hcomm'⟩
  refine iSup₂_le fun R' hR' => ?_
  obtain ⟨⟨y, hy, hR'eq⟩, hR'le⟩ := hR'
  subst hR'eq
  have hR'2 : IsPGroup 2 (conjSub y R) := isPGroup_conjSub y hR2
  obtain ⟨S', hS', hR'S'⟩ := exists_isSylowOf_le hR'2 (sup_comm R X ▸ hR'le)
  obtain ⟨c, hcH, hconj⟩ := exists_rightConjugate_eq_of_isSylowOf hS' hS
  have hcY : c ∈ Y := hHY hcH
  have hle : conjSub (c * y) R ≤ S := by
    rw [conjSub_mul]
    have h1 : conjSub y R ≤ conjSub c⁻¹ S := by
      have : rightConjugate S c = conjSub c⁻¹ S := rfl
      rw [← this, hconj]
      exact hR'S'
    have h2 := conjSub_mono (n := c) h1
    rwa [conjSub_conjSub_inv] at h2
  have hceq : conjSub (c * y) R = R := hclosed _ (Y.mul_mem hcY hy) hle
  have hyR : conjSub y R = conjSub c⁻¹ R := by
    calc conjSub y R = conjSub (c⁻¹ * (c * y)) R := by rw [inv_mul_cancel_left]
      _ = conjSub c⁻¹ (conjSub (c * y) R) := conjSub_mul _ _ _
      _ = conjSub c⁻¹ R := by rw [hceq]
  have hF : Frame X R := ⟨hRN, hRX, hR2⟩
  obtain ⟨ρ, hρ, x, hx, hρx⟩ := hF.mem_sup_iff.mp (Subgroup.inv_mem _ hcH)
  have hinv : c⁻¹ = (ρ * x * ρ⁻¹) * ρ := by rw [← hρx]; group
  have hxX : ρ * x * ρ⁻¹ ∈ X := by
    have := conj_mem_conjSub (n := ρ) hx
    rwa [hXn ρ (hRY hρ)] at this
  rw [hyR, hinv, conjSub_mul, conjSub_eq_self_of_mem hρ]
  intro u hu
  rw [mem_conjSub_iff] at hu
  have hu' : u = ((ρ * x * ρ⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) * (ρ * x * ρ⁻¹)⁻¹ *
      ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹))⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) := by
    group
  rw [hu', sup_comm]
  refine Subgroup.mul_mem_sup (hcomm (Subgroup.commutator_mem_commutator hxX hu)) hu
end

section Cent

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem normal_two_central_Q8 (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) {Q : Subgroup G} [Q.Normal]
    (hQ2 : IsPGroup 2 ↥Q) {J : Subgroup G} (hJ : J ∈ Ω) (hJQ : J ⊓ Q = ⊥) :
    J ≤ Subgroup.centralizer (Q : Set G) := by
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 J hJ
  obtain ⟨R, hR⟩ := Uniform.exists_isSylow2In J
  have hRΩ : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hR
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hRQ : R ⊓ Q = ⊥ := by
    rw [eq_bot_iff, ← hJQ]
    exact inf_le_inf_right _ hR.1
  have h67 : L6_7On Ω := Q3T8.Asc77.l6_7_proved G Ω hΩ
  have h613 := (TwinThmE.l6_13_on hΩ h67 R hRΩ ⊤ Q le_top le_top
    (fun y _ => AscQuot.conjSub_eq_of_normal Q y) hRQ).2
  rw [AscE186.oddCoreOf_eq_bot_of_isPGroup hQ2, le_bot_iff] at h613
  have hRC : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r := by
    intro r hr q hq
    have hmem : ⁅r, q⁆ ∈ ⁅R, Q⁆ := Subgroup.commutator_mem_commutator hr hq
    rw [h613, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hzR : z ∈ R := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR.1 hR.2.1 (by omega)
  have hQC : Q ≤ Subgroup.centralizer ({z} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRC z hzR q hq).symm
  obtain ⟨z', hz'J, hz'2, hz'sub⟩ := hcls.subnormal J hJ
  have hz'z : z' = z := by
    have h2' := pow_orderOf_eq_one z'
    rw [hz'2, pow_two] at h2'
    have hz'1 : z' ≠ 1 := fun h => by rw [h, orderOf_one] at hz'2; omega
    rcases hz.unique z' hz'J h2' with h | h
    · exact absurd h hz'1
    · exact h
  subst hz'z
  have hJC : J ≤ Subgroup.centralizer ({z'} : Set G) := isSubnormal_le hz'sub
  have hsub : IsSubnormal J (J ⊔ Q) := by
    have := isSubnormal_inf hz'sub (J ⊔ Q)
    rwa [inf_eq_left.mpr le_sup_left, inf_eq_right.mpr (sup_le hJC hQC)] at this
  have hodd : ∀ x ∈ {x : G | x ∈ J ∧ Odd (orderOf x)}, ∀ q ∈ Q, x * q = q * x :=
    fun x hx q hq =>
      Q3T8.Asc77.centralizes_of_isSubnormal hQ2 (T := {x : G | x ∈ J ∧ Odd (orderOf x)})
        (fun x hx => hx.2) hsub (fun x hx => hx.1)
        (fun x _ q hq => by
          have : q = 1 := Subgroup.mem_bot.mp (hJQ ▸ hq)
          rw [this]
          simp) x hx q ⟨(le_sup_right : Q ≤ J ⊔ Q) hq, hq⟩
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨r, hr, o, ho, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow (h2 J hJ) hR k hk
  have hoJ : o ∈ J := (oddCoreOf_le_self J) ho
  have hoodd : Odd (orderOf o) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  have h1 := hodd o ⟨hoJ, hoodd⟩ q hq
  have h2' := hRC r hr q hq
  calc q * (r * o) = (q * r) * o := by group
    _ = (r * q) * o := by rw [h2']
    _ = r * (q * o) := by group
    _ = r * (o * q) := by rw [← h1]
    _ = (r * o) * q := by group

end Cent

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
