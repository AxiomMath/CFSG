module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowA
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi23 CFSG.Blueprint.NativeSporadic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Model

theorem lvl_two_le_Cd : lvl 2 ≤ CFSG.Sporadic.Fi23.Cd :=
  fun _ hg => CFSG.Sporadic.Fi23.mem_Cd.2 (mem_lvl_two_iff.1 hg).1

@[expose] noncomputable def lvlTwoTheta : ↥(lvl 2) →* CFSG.Sporadic.Fi22.J :=
  fi23Kappa.comp (Subgroup.inclusion lvl_two_le_Cd)

theorem lvlTwoTheta_apply (b : ↥(lvl 2)) :
    lvlTwoTheta b = fi23Kappa (Subgroup.inclusion lvl_two_le_Cd b) := rfl

@[expose] noncomputable def d1Cd : ↥CFSG.Sporadic.Fi23.Cd := ⟨CFSG.Sporadic.Fi23.d1, fi23_d1_mem_Cd⟩

@[expose] noncomputable def d1B : ↥(lvl 2) := ⟨CFSG.Sporadic.Fi23.d1, d1_mem_lvl_two⟩

@[expose] noncomputable def dB : ↥(lvl 2) := ⟨CFSG.Sporadic.Fi23.d, d_mem_lvl_two⟩

theorem lvlTwoTheta_eq_one {b : ↥(lvl 2)} (hb : lvlTwoTheta b = 1) :
    (b : CFSG.Sporadic.Fi23.J) = 1 ∨ (b : CFSG.Sporadic.Fi23.J) = CFSG.Sporadic.Fi23.d :=
  fi23Kappa_eq_one (c := Subgroup.inclusion lvl_two_le_Cd b) hb

theorem card_ker_lvlTwoTheta_le : Nat.card lvlTwoTheta.ker ≤ 2 := by
  have h2 : Nat.card fi23Kappa.ker = 2 := by
    rw [ker_fi23Kappa, CFSG.Sporadic.Fi23.card_center_C]
  refine le_of_le_of_eq (Nat.card_le_card_of_injective
    (fun b : lvlTwoTheta.ker => (⟨Subgroup.inclusion lvl_two_le_Cd b.1, b.2⟩ : fi23Kappa.ker))
    ?_) h2
  intro b c h
  have h' : Subgroup.inclusion lvl_two_le_Cd b.1 = Subgroup.inclusion lvl_two_le_Cd c.1 :=
    congrArg Subtype.val h
  exact Subtype.ext (Subgroup.inclusion_injective lvl_two_le_Cd h')

theorem card_range_lvlTwoTheta_ge : 18393661440 ≤ Nat.card lvlTwoTheta.range := by
  have h := CFSG.GH74.Generic.card_eq_card_mul_card_ker lvlTwoTheta.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  rw [MonoidHom.ker_rangeRestrict, card_lvl_two] at h
  have h2 := card_ker_lvlTwoTheta_le
  have hpos : 0 < Nat.card lvlTwoTheta.range := Nat.card_pos
  nlinarith

theorem orderOf_kappa_d1 : orderOf (fi23Kappa d1Cd) = 2 := by
  have hsq : fi23Kappa d1Cd ^ 2 = 1 := by
    rw [← map_pow]
    have : d1Cd ^ 2 = 1 := Subtype.ext (CFSG.Sporadic.Fi23.d1_sq)
    rw [this, map_one]
  refine orderOf_eq_prime hsq fun h1 => ?_
  rcases fi23Kappa_eq_one h1 with h | h
  · have hc : IsConj CFSG.Sporadic.Fi23.d CFSG.Sporadic.Fi23.d1 :=
      (isConj_d_iff _).2 ⟨⟨1, by norm_num⟩, rfl⟩
    have h' : CFSG.Sporadic.Fi23.d1 = 1 := h
    rw [h', isConj_one_left] at hc
    exact CFSG.Sporadic.Fi23.d_ne_one hc
  · exact fi23_d_ne_d1 h.symm

theorem range_lvlTwoTheta_comm :
    ∀ k ∈ lvlTwoTheta.range, k * fi23Kappa d1Cd = fi23Kappa d1Cd * k := by
  rintro _ ⟨b, rfl⟩
  rw [lvlTwoTheta_apply, ← map_mul, ← map_mul]
  exact congrArg fi23Kappa (Subtype.ext (mem_lvl_two_iff.1 b.2).2)

theorem lvlTwoTheta_range_equiv : Nonempty (↥lvlTwoTheta.range ≃* Fi22D) :=
  fi22_pair_equiv (L := ⊤) (u := fi23Kappa d1Cd)
    ⟨Subgroup.topEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm⟩ (Subgroup.mem_top _)
    orderOf_kappa_d1 le_top range_lvlTwoTheta_comm card_range_lvlTwoTheta_ge

theorem exists_cover_of_range_equiv {B G : Type} [Group B] [Finite B] [Group G] (θ : B →* G)
    (e : ↥θ.range ≃* Fi22D) (dB d1B : B) (hcard : Nat.card B = 36787322880)
    (hker : ∀ b, θ b = 1 → b = 1 ∨ b = dB) (hd : dB ∈ center B) (hd1 : d1B ∈ center B)
    (hdc : dB ∈ commutator B) (hu : ∀ k ∈ θ.range, k * θ d1B = θ d1B * k) (hu1 : θ d1B ≠ 1) :
    ∃ p₀ : B →* (Fi22D ⧸ center Fi22D), Function.Surjective p₀ ∧ p₀.ker ≤ center B ∧
      Nat.card p₀.ker = 4 ∧ Group.IsPerfect B := by
  let θ' : B →* ↥θ.range := θ.rangeRestrict
  have hθ's : Function.Surjective θ' := MonoidHom.rangeRestrict_surjective _
  have hθ'v : ∀ b, ((θ' b : θ.range) : G) = θ b := fun b => rfl
  let p₀ : B →* (Fi22D ⧸ center Fi22D) :=
    (QuotientGroup.mk' (center Fi22D)).comp (e.toMonoidHom.comp θ')
  have hp₀s : Function.Surjective p₀ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp hθ's)
  have hcentB : ∀ c : B, (c = 1 ∨ c = dB) → c ∈ center B := by
    rintro c (h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact hd
  have hz0 : e (θ' d1B) ∈ center Fi22D := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hu k.1 k.2))
  have hz0ne : (⟨e (θ' d1B), hz0⟩ : ↥(center Fi22D)) ≠ 1 := by
    intro h
    have h1 : e (θ' d1B) = 1 := congrArg Subtype.val h
    have h2 : θ' d1B = 1 := by
      rw [← map_one e] at h1
      exact e.injective h1
    exact hu1 (congrArg Subtype.val h2)
  have hker0 : p₀.ker ≤ center B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hxc : e (θ' b) ∈ center Fi22D := (QuotientGroup.eq_one_iff _).1 hb
    rcases eq_one_or_eq_of_card_two fi22D_card_center hz0ne ⟨e (θ' b), hxc⟩ with h | h
    · have h1 : e (θ' b) = 1 := congrArg Subtype.val h
      have h2 : θ' b = 1 := by
        rw [← map_one e] at h1
        exact e.injective h1
      exact hcentB b (hker b (congrArg Subtype.val h2))
    · have h1 : e (θ' b) = e (θ' d1B) := congrArg Subtype.val h
      have h2 : θ' b = θ' d1B := e.injective h1
      have h3 : θ (b * d1B⁻¹) = 1 := by
        have : θ' (b * d1B⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
        exact congrArg Subtype.val this
      have h4 := hcentB _ (hker _ h3)
      have h5 : b = b * d1B⁻¹ * d1B := (inv_mul_cancel_right b d1B).symm
      rw [h5]
      exact Subgroup.mul_mem _ h4 hd1
  have hk4 : Nat.card p₀.ker = 4 := by
    have h := CFSG.GH74.Generic.card_eq_card_mul_card_ker p₀ hp₀s
    rw [hcard, fi22D_card_quotient] at h
    omega
  have hperf : Group.IsPerfect B := by
    haveI : Group.IsPerfect Fi22D := fi22D_isQuasisimple.1
    haveI : Group.IsPerfect ↥θ.range :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hK' : commutator ↥θ.range = ⊤ := Group.IsPerfect.commutator_eq_top
    have himg : (commutator B).map θ' = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective θ' hθ's]
      exact hK'
    rw [Group.isPerfect_def, eq_top_iff]
    intro b _
    have hmem : θ' b ∈ (commutator B).map θ' := by
      rw [himg]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcb⟩ := hmem
    have hcb' : θ (c⁻¹ * b) = 1 := by
      have : θ' (c⁻¹ * b) = 1 := by rw [map_mul, map_inv, hcb, inv_mul_cancel]
      exact congrArg Subtype.val this
    rcases hker _ hcb' with h | h
    · have hb : b = c := by
        rw [inv_mul_eq_one] at h
        exact h.symm
      rw [hb]
      exact hc
    · have hb : b = c * dB := by rw [← h, mul_inv_cancel_left]
      rw [hb]
      exact Subgroup.mul_mem _ hc hdc
  exact ⟨p₀, hp₀s, hker0, hk4, hperf⟩

theorem exists_lvlTwo_cover :
    ∃ p₀ : ↥(lvl 2) →* (Fi22D ⧸ center Fi22D), Function.Surjective p₀ ∧
      p₀.ker ≤ center ↥(lvl 2) ∧ Nat.card p₀.ker = 4 ∧ Group.IsPerfect ↥(lvl 2) := by
  obtain ⟨e⟩ := lvlTwoTheta_range_equiv
  refine exists_cover_of_range_equiv lvlTwoTheta e dB d1B card_lvl_two
    (fun b hb => ?_) ?_ ?_ d_mem_commutator_lvl_two range_lvlTwoTheta_comm ?_
  · rcases lvlTwoTheta_eq_one hb with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_lvl_two_iff.1 g.2).1
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_lvl_two_iff.1 g.2).2
  · intro h
    have h4 := orderOf_kappa_d1
    rw [show fi23Kappa d1Cd = 1 from h, orderOf_one] at h4
    omega

end Model

end CFSG.EvenSporadicStandard.Induction.Fi
