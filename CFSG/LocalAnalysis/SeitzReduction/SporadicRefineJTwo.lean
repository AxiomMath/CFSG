module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small
public import CFSG.Sporadic.Recognition.McLCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

abbrev MatThreeTwo : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

abbrev transvThreeTwo : MatThreeTwo := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

theorem mat_three_two_involution_conj : ∀ B : MatThreeTwo, B.det = 1 → B * B = 1 → B ≠ 1 →
    ∃ K : MatThreeTwo, K.det = 1 ∧ K * transvThreeTwo = B * K := by
  decide +kernel

theorem exists_conj_of_SL_three_two {a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) :
    ∃ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), k * a * k⁻¹ = b := by
  have hdet : (transvThreeTwo : MatThreeTwo).det = 1 := by decide
  set t : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨transvThreeTwo, hdet⟩ with ht
  have key : ∀ c : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), c * c = 1 → c ≠ 1 →
      ∃ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), k * t = c * k := by
    intro c hc hc1
    obtain ⟨K, hK, hKc⟩ := mat_three_two_involution_conj (c : MatThreeTwo) c.2
      (by rw [← Matrix.SpecialLinearGroup.coe_mul, hc]; rfl)
      (fun h => hc1 (Subtype.ext h))
    exact ⟨⟨K, hK⟩, Subtype.ext hKc⟩
  obtain ⟨ka, hka⟩ := key a ha ha1
  obtain ⟨kb, hkb⟩ := key b hb hb1
  refine ⟨kb * ka⁻¹, ?_⟩
  have hta : t = ka⁻¹ * a * ka := by
    calc t = ka⁻¹ * (ka * t) := by group
      _ = ka⁻¹ * (a * ka) := by rw [hka]
      _ = ka⁻¹ * a * ka := by group
  calc kb * ka⁻¹ * a * (kb * ka⁻¹)⁻¹ = kb * (ka⁻¹ * a * ka) * kb⁻¹ := by group
    _ = kb * t * kb⁻¹ := by rw [← hta]
    _ = b * kb * kb⁻¹ := by rw [hkb]
    _ = b := by group

theorem nonempty_equiv_SL_three_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two h

theorem exists_conj_of_mulEquiv_SL_three_two {X : Type*} [Group X]
    (φ : X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {a b : X} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) : ∃ k : X, k * a * k⁻¹ = b := by
  obtain ⟨k, hk⟩ := exists_conj_of_SL_three_two (a := φ a) (b := φ b)
    (by rw [← map_mul, ha, map_one]) (fun h1 => ha1 (φ.injective (by rw [h1, map_one])))
    (by rw [← map_mul, hb, map_one]) (fun h1 => hb1 (φ.injective (by rw [h1, map_one])))
  refine ⟨φ.symm k, φ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hk]

section J2

theorem j2_card_centralizer {S : Type} [Group S] (e : S ≃* NativeSporadic.J2) {s : S}
    (hs : orderOf s = 2) :
    Nat.card (centralizer ({s} : Set S)) = 240 ∨ Nat.card (centralizer ({s} : Set S)) = 1920 := by
  set θ : S ≃* ComponentClassification.J2Cover.P :=
    e.trans ComponentClassification.J2Cover.nativeEquivP with hθ
  set ι : S →* Equiv.Perm (Fin 315) :=
    ComponentClassification.J2Cover.P.subtype.comp θ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp θ.injective
  have hrange : ι.range = ComponentClassification.J2Cover.P := by
    rw [hι, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr θ.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hCS : Nat.card (centralizer ({s} : Set S)) =
      Nat.card (Sporadic.Schreier.centralizerIn ComponentClassification.J2Cover.P (ι s)) := by
    rw [Nat.card_congr
      (Sporadic.Recognition.McLCentralizer.centralizerEquivOfInjective ι hιinj s).toEquiv, hrange]
    rfl
  have ho : orderOf (ι s) = 2 := by rw [orderOf_injective ι hιinj, hs]
  rw [hCS]
  exact QuasithinUnique.Id2519.Tab.j2_inner_centralizer_card (ι s) (θ s).2 ho

theorem j2_center_eq_bot {S : Type} [Group S] (e : S ≃* NativeSporadic.J2) : center S = ⊥ := by
  set θ : S ≃* ComponentClassification.J2Cover.P :=
    e.trans ComponentClassification.J2Cover.nativeEquivP with hθ
  rw [eq_bot_iff]
  intro z hz
  have hθz : θ z ∈ center ComponentClassification.J2Cover.P := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz x]
  rw [ComponentClassification.J2Cover.center_P, mem_bot] at hθz
  rw [mem_bot]
  exact θ.injective (by rw [hθz, map_one])

theorem j2_card_fixedSubgroup_outer {S : Type} [Group S] (e : S ≃* NativeSporadic.J2)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (fixedSubgroup σ) = 336 := by
  set θ := e.trans ComponentClassification.J2Cover.nativeEquivP
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hc : Nat.card (fixedSubgroup σ) = Nat.card (Sporadic.Schreier.fixSub
      (ComponentClassification.RestrictedStd.Spor.transportAut θ σ)) :=
    Nat.card_congr ((MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub' σ)).trans
      (ComponentClassification.RestrictedStd.Spor.fixSubTransportEquiv θ σ)).toEquiv
  have h := CFSG.QuasithinUnique.Ch1.j2_outer_fixSub_card
    (ComponentClassification.RestrictedStd.Spor.transportAut θ σ)
    (ComponentClassification.RestrictedStd.Spor.transportAut_mul_self θ hσ2)
    (ComponentClassification.RestrictedStd.Spor.transportAut_not_mem_inner θ hout)
  rw [hc]
  simpa using h

end J2

@[expose] def J2OuterFixedClassesInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.J2) →
    ∀ τ : MulAut S, orderOf τ = 2 → τ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ W : Subgroup S, Nat.card W = 16 → (∀ x ∈ W, x * x = 1) → W.map τ.toMonoidHom = W →
      ∃ a ∈ W ⊓ fixedSubgroup τ, ∃ b ∈ W ⊓ fixedSubgroup τ, a ≠ 1 ∧ b ≠ 1 ∧
        ∀ g : S, g * a * g⁻¹ ≠ b

theorem lFiveJTwoInput_of
    (hJ : J2OuterFixedClassesInput) : LinearPilot.LFiveJTwoInput := by
  intro S _ _ hS τ hτ D hD hDm W hW16 hW2 hWτ hWD
  obtain ⟨e⟩ := hS
  have hZS : center S = ⊥ := j2_center_eq_bot e
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center S := by
      rw [mem_center_iff]
      intro y
      have h1 := congrArg (fun β : MulAut S => β y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = g * y * g⁻¹ * g := by rw [h1]
        _ = g * y := by group
    rw [hZS, mem_bot] at hgZ
    exact hgZ
  have hq : Nat.card (D ⧸ center D) = 168 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hDcard : Nat.card D = 168 * Nat.card (center D) := by
    rw [← hq]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  have hDF : Nat.card D ∣ Nat.card (fixedSubgroup τ) := card_subgroup_dvd_card D
  have h7D : 7 ∣ Nat.card D := by
    rw [hDcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hout : τ ∉ (MulAut.conj : S →* MulAut S).range := by
    rintro ⟨s, rfl⟩
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _ hinj s]
      exact hτ
    have h7 : 7 ∣ Nat.card (centralizer ({s} : Set S)) := by
      rw [← fixedSubgroup_conj_eq_centralizerOf s]
      exact h7D.trans hDF
    rcases j2_card_centralizer e hs with h | h <;> rw [h] at h7 <;> norm_num at h7
  have hF : Nat.card (fixedSubgroup τ) = 336 := j2_card_fixedSubgroup_outer e hτ hout
  have hZD : center D = ⊥ := by
    by_contra hne
    have h2 : Nat.card (center D) ∣ 2 := by
      have h1 : 168 * Nat.card (center D) ∣ 168 * 2 := by
        rw [← hDcard, show (168 : ℕ) * 2 = 336 by norm_num, ← hF]
        exact hDF
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    have hZ1 : Nat.card (center D) ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1)
    have hZ2 : Nat.card (center D) = 2 := by
      have hle := Nat.le_of_dvd (by norm_num) h2
      have hpos : 0 < Nat.card (center D) := Nat.card_pos
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center D) 2 (by rw [hZ2])
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := D) 7 h7D
    set z' : S := (((z : D) : fixedSubgroup τ) : S) with hz'
    set y' : S := ((y : fixedSubgroup τ) : S) with hy'
    have hz'o : orderOf z' = 2 := by
      rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hy'o : orderOf y' = 7 := by
      rw [hy', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    have hyz : y' ∈ centralizer ({z'} : Set S) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_center_iff.1 z.2 y
      exact (congrArg (fun x : D => ((x : fixedSubgroup τ) : S)) h1)
    have h7 : 7 ∣ Nat.card (centralizer ({z'} : Set S)) := by
      have h1 := orderOf_dvd_natCard (⟨y', hyz⟩ : centralizer ({z'} : Set S))
      rwa [Subgroup.orderOf_mk, hy'o] at h1
    rcases j2_card_centralizer e hz'o with h | h <;> rw [h] at h7 <;> norm_num at h7
  obtain ⟨φ₀⟩ := nonempty_equiv_SL_three_of_lieModel hDm
  set φ : D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hZD).trans QuotientGroup.quotientBot).symm.trans φ₀
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := hJ S ⟨e⟩ τ hτ hout W hW16 hW2 hWτ
  obtain ⟨a', ha'D, rfl⟩ := hWD ha
  obtain ⟨b', hb'D, rfl⟩ := hWD hb
  have haa : (⟨a', ha'D⟩ : D) * ⟨a', ha'D⟩ = 1 :=
    Subtype.ext (Subtype.ext (hW2 _ (mem_inf.1 ha).1))
  have hbb : (⟨b', hb'D⟩ : D) * ⟨b', hb'D⟩ = 1 :=
    Subtype.ext (Subtype.ext (hW2 _ (mem_inf.1 hb).1))
  have ha1' : (⟨a', ha'D⟩ : D) ≠ 1 := fun h => ha1 (by
    have := congrArg (fun x : D => ((x : fixedSubgroup τ) : S)) h
    simpa using this)
  have hb1' : (⟨b', hb'D⟩ : D) ≠ 1 := fun h => hb1 (by
    have := congrArg (fun x : D => ((x : fixedSubgroup τ) : S)) h
    simpa using this)
  obtain ⟨k, hk⟩ := exists_conj_of_mulEquiv_SL_three_two φ haa ha1' hbb hb1'
  apply hab (((k : D) : fixedSubgroup τ) : S)
  have := congrArg (fun x : D => ((x : fixedSubgroup τ) : S)) hk
  simpa using this

end CFSG.SeitzReduction.SporadicRefine
