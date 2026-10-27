module

public import CFSG.CGT.PushingUpLit.BHS.SLCore
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section SLWrap

variable {V : Type} [CommGroup V] [Finite V]

theorem two_sixteen_sl_gen {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : ∃ s : Finset F, s.card = 4) {A E : Subgroup (MulAut V)} {W : Subgroup V}
    (hWE : commV E = W) (θ : E ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (β : ↥W →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = (W ⊓ fixV E).subgroupOf W)
    (hβe : ∀ (x : E) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ = Multiplicative.ofAdd
        ((θ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β p))))
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) (hAoff : IsOff A)
    (hEA : ⁅E, A⁆ ≠ ⊥) :
    autSub A W ≤ autSub E W ∧ Nat.card (autSub A W) = Nat.card F ∧
      (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W, a' (a w * w⁻¹) = a w * w⁻¹) ∧
      (fixV A).relIndex W = (cenIn A W).relIndex A := by
  classical
  have hEst : E ≤ stabSub W := by
    rw [← hWE]
    exact Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hAst : A ≤ stabSub W := by
    rw [← hWE]
    exact hAN.trans (normalizer_commV_le_stabSub E)
  have hEq : CFSG.Open.IsQuasisimple ↥E :=
    isQuasisimple_of_mulEquiv' θ.symm (isQuasisimple_special_linear_two h4)
  have hperf : ⁅E, E⁆ = E := by
    have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥E)) (H₂ := ⊤) E.subtype
    rw [htop] at h
    rw [← h, ← commutator_def, hEq.1, htop]
  have hcomm : commSub W E = W := by
    have := CFSG.Quasithin.B15P4.commSub_commV_of_perfect hperf
    rwa [hWE] at this
  have hEcen : E ⊓ centSub W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
    obtain ⟨heE, hecen⟩ := he
    have h1 : θ ⟨e, heE⟩ = 1 := by
      apply eq_one_of_forall_smul_vec
      intro v
      obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd v)
      have hpW : (e : MulAut V) p ∈ W := by rw [hecen p p.2]; exact p.2
      have hp' : (⟨e p, hpW⟩ : ↥W) = p := Subtype.ext (hecen p p.2)
      have := hβe ⟨e, heE⟩ p hpW
      rw [hp', hp] at this
      have h2 := congrArg Multiplicative.toAdd this
      have h3 : (θ ⟨e, heE⟩ : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
        simpa only [toAdd_ofAdd] using h2.symm
      exact h3
    have : (⟨e, heE⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  obtain ⟨φE, hφE⟩ := exists_mulEquiv_autSub hEst hEcen
  have htopW : (⊤ : Subgroup ↥W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let D : SLNatData (autSub E W) F :=
    { θ := φE.symm.trans θ
      β := β
      surj := hβs
      ker_fix := fun w hw g hg => by
        obtain ⟨e, he⟩ := φE.surjective ⟨g, hg⟩
        have h1 : (w : V) ∈ W ⊓ fixV E := by
          have : w ∈ β.ker := hw
          rw [hβk, Subgroup.mem_subgroupOf] at this
          exact this
        have h2 : (e : MulAut V) w = w := h1.2 e e.2
        apply Subtype.ext
        have := hφE e w
        rw [he] at this
        rw [this]
        exact h2
      equivar := fun e' w => by
        obtain ⟨e, rfl⟩ := φE.surjective e'
        have hp : (e : MulAut V) w ∈ W := by
          have h2 := (((φE e : ↥(autSub E W)) : MulAut ↥W) w).2
          rw [hφE e w] at h2
          exact h2
        have h3 : (((φE e : ↥(autSub E W)) : MulAut ↥W) w) = ⟨(e : MulAut V) w, hp⟩ :=
          Subtype.ext (hφE e w)
        rw [h3, hβe e w hp]
        simp
      comm_top := by
        refine Subgroup.map_injective W.subtype_injective ?_
        rw [← commSub_eq_map_commV hEst, hcomm, htopW] }
  have hAN' : autSub A W ≤ Subgroup.normalizer ((autSub E W : Subgroup (MulAut ↥W)) :
      Set (MulAut ↥W)) := autSub_le_normalizer hAN
  have hel' : IsElemAbelian2 (autSub A W) := isElemAbelian2_autSub hAoff.2.2.1
  have hcardA : Nat.card (autSub A W) = (cenIn A W).relIndex A := card_autSub_eq_relIndex hAst
  have hcardF : Nat.card (fixV (autSub A W)) = Nat.card ↥(fixV A ⊓ W) := by
    have h1 := map_subtype_fixV_autSub hAst
    have h2 : Nat.card ((fixV (autSub A W)).map W.subtype) = Nat.card (fixV (autSub A W)) :=
      Subgroup.card_map_of_injective W.subtype_injective
    rw [h1, inf_comm] at h2
    exact h2.symm
  have hcardW : (fixV A).relIndex W * Nat.card ↥(fixV A ⊓ W) = Nat.card ↥W :=
    Subgroup.relIndex_mul_card (fixV A) W
  have hoffW : (fixV A).relIndex W ≤ (cenIn A W).relIndex A := offender_card_le hAoff W
  have hAw' : Nat.card ↥W ≤ Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) := by
    rw [hcardA, hcardF, ← hcardW]
    exact Nat.mul_le_mul_right _ hoffW
  have hEA' : ⁅autSub E W, autSub A W⁆ ≠ ⊥ :=
    commutator_autSub_ne_bot hEst hAst hAN hEcen hEA
  obtain ⟨hAE', hAF', hquad, hcard⟩ := sl_core D hAN' hel' hAw' hEA'
  refine ⟨hAE', hAF', ?_, ?_⟩
  · intro a ha a' ha' w hw
    have hgen : (resHom W ⟨a, hAst ha⟩) ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹ ∈ commV (autSub A W) :=
      Subgroup.subset_closure ⟨resHom W ⟨a, hAst ha⟩,
        mem_autSub.mpr ⟨⟨a, hAst ha⟩, ha, rfl⟩, ⟨w, hw⟩, rfl⟩
    have hfx := hquad hgen (resHom W ⟨a', hAst ha'⟩)
      (mem_autSub.mpr ⟨⟨a', hAst ha'⟩, ha', rfl⟩)
    exact congrArg Subtype.val hfx
  · have h := hcard
    rw [hcardA, hcardF, ← hcardW] at h
    have hpos : 0 < Nat.card ↥(fixV A ⊓ W) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h

end SLWrap

theorem two_sixteen_sl {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ}
    (hk : 2 ≤ k) {G A E : Subgroup (MulAut V)} (hA : IsOff A) (hAG : A ≤ G) (hEG : E ≤ G)
    (hsub : CFSG.Open.IsSubnormal E G)
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) k) (hEA : ⁅E, A⁆ ≠ ⊥) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) ∧
      autSub A (commV E) ≤ autSub E (commV E) ∧ Nat.card (autSub A (commV E)) = 2 ^ k ∧
      (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ commV E, a' (a w * w⁻¹) = a w * w⁻¹) ∧
      (fixV A).relIndex (commV E) = (cenIn A (commV E)).relIndex A := by
  have hAN := two_sixteen_a_sl hV hk hA hAG hEG hsub hnat
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨hAE, hcard, hquad, hidx⟩ :=
    two_sixteen_sl_gen (F := GaloisField 2 k) (exists_finset_card_four_galoisField hk) rfl θ β hβs
      hβk hβe hAN hA hEA
  refine ⟨hAN, hAE, ?_, hquad, hidx⟩
  rw [hcard]
  exact GaloisField.card 2 k (by omega)

end CFSG.CGT.PushingUpLit.BHS
