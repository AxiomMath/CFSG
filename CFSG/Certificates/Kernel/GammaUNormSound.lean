
module

public import Certificates.Data.Kernel.GammaUNormK
public import CFSG.Certificates.Kernel.GammaUViolSound
public import CFSG.Certificates.Kernel.GammaUCensusSound
public import CFSG.GF2Type.Smith1979.IdxFourIdentFLCheck
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.IdxFour

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem unitP_spec {TH A : Nat} (hTH : ∀ v, linP TH v = theta0 v) (h : unitP TH A = true) (v : V12) :
    linP A (theta0 v) = theta0 (linP A v) := by
  unfold unitP at h
  rw [Nat.beq_eq] at h
  have := congrArg (fun m => linP m v) h
  simp only [linP_mulP, hTH] at this
  exact this

theorem guOK_spec {TH A : Nat} (hTH : ∀ v, linP TH v = theta0 v) (h : guOK TH A = true) {U : GL}
    (hU : IsP U A) : U ∈ gammaU := by
  unfold guOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, allBelow_iff, beq_iff_eq] at h
  obtain ⟨⟨hq, hf⟩, hθ⟩ := h
  refine ⟨fun x => ?_, ?_⟩
  · rw [hU, linP]
    refine FLCheck.q0_linOfRows (fun j => ?_) (fun j k => ?_) x
    · rw [rowsP_get, q0_vecOf, q0_vecOf, hq j j.2]
    · rw [rowsP_get, rowsP_get, f0_vecOf, f0_vecOf, hf j j.2 k k.2]
  · rcases hθ with hu | ha
    · exact Or.inl fun x => by rw [hU, hU, unitP_spec hTH hu]
    · exact Or.inr fun x => by rw [hU, hU, antiP_spec hTH ha]

theorem span_spec {A : Nat} {D0 : List Nat} (hD : ∀ v ∈ D0, v < 4096)
    (h : D0.all (fun d => memN (ap12 A d) (spanList D0)) = true) :
    ∀ y ∈ spanOf D0, linP A y ∈ spanOf D0 := by
  have hle : spanOf D0 ≤ (spanOf D0).comap (linP A) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    change linP A (vecOf d) ∈ spanOf D0
    rw [← vecOf_ap12]
    exact (mem_spanList_iff hD (ap12_lt A d)).1 ((memN_iff _ _).1 (List.all_eq_true.1 h d hd))
  exact fun y hy => hle hy

@[expose] def FrP (L : List Nat) (l : GL) : Prop := ∃ m < 32, ∀ v, l v = linP (subQ L m) v

@[expose] def NLK (L D0 : List Nat) (U : GL) : Prop :=
  U ∈ gammaU ∧ U (vecOf 3072) = vecOf 3072 ∧ (∀ y, U y ∈ spanOf D0 ↔ y ∈ spanOf D0) ∧
    ∀ l, FrP L (U * l * U⁻¹) ↔ FrP L l

theorem nm_spec {L : List Nat} {A : Nat} {nm : Nat → Nat}
    (h : allBelow 32 (fun m => nmOK L A m (nm m)) = true) {U : GL} (hU : IsP U A) {m : Nat}
    (hm : m < 32) : nm m < 32 ∧ ∀ v, U (linP (subQ L m) (U⁻¹ v)) = linP (subQ L (nm m)) v := by
  have h' := (allBelow_iff _ _).1 h m hm
  unfold nmOK at h'
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
  refine ⟨h'.1, fun v => ?_⟩
  have := congrArg (fun x => linP x (U⁻¹ v)) h'.2
  simp only [linP_mulP] at this
  rw [hU, this, ← hU, apply_inv_apply]

theorem frP_conj {L : List Nat} {A : Nat} {nm : Nat → Nat}
    (h : allBelow 32 (fun m => nmOK L A m (nm m)) = true) {U : GL} (hU : IsP U A) {l : GL}
    (hl : FrP L l) : FrP L (U * l * U⁻¹) := by
  obtain ⟨m, hm, hlm⟩ := hl
  obtain ⟨hnm, hv⟩ := nm_spec h hU hm
  refine ⟨nm m, hnm, fun v => ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlm, hv]

theorem nlP_spec {L : List Nat} {TH : Nat} {D0 : List Nat} {A B : Nat} {nm nm' : Nat → Nat}
    (hTH : ∀ v, linP TH v = theta0 v) (hD : ∀ v ∈ D0, v < 4096)
    (hA : nlP L TH D0 (spanList D0) A nm = true) (hB : nlP L TH D0 (spanList D0) B nm' = true)
    {U : GL} (hU : IsP U A) (hUi : IsP U⁻¹ B) : NLK L D0 U := by
  unfold nlP at hA hB
  simp only [Bool.and_eq_true] at hA hB
  obtain ⟨⟨⟨hgu, hfix⟩, hsp⟩, hnm⟩ := hA
  obtain ⟨⟨⟨-, -⟩, hsp'⟩, hnm'⟩ := hB
  refine ⟨guOK_spec hTH hgu hU, ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun l => ⟨fun hl => ?_,
    frP_conj hnm hU⟩⟩
  · rw [hU.apply_code, Nat.eq_of_beq_eq_true hfix]
  · have := span_spec hD hsp' _ hy
    rwa [← hUi, inv_apply_apply] at this
  · rw [hU]
    exact span_spec hD hsp _ hy
  · have := frP_conj hnm' hUi hl
    rwa [inv_inv, show U⁻¹ * (U * l * U⁻¹) * U = l by group] at this

theorem NLK.one (L D0 : List Nat) : NLK L D0 1 := by
  refine ⟨one_mem _, rfl, fun _ => Iff.rfl, fun l => ?_⟩
  rw [one_mul, inv_one, mul_one]

theorem NLK.mul {L D0 : List Nat} {g h : GL} (hg : NLK L D0 g) (hh : NLK L D0 h) :
    NLK L D0 (g * h) := by
  refine ⟨mul_mem hg.1 hh.1, ?_, fun y => ?_, fun l => ?_⟩
  · rw [LinearEquiv.mul_apply, hh.2.1, hg.2.1]
  · rw [LinearEquiv.mul_apply, hg.2.2.1, hh.2.2.1]
  · rw [show g * h * l * (g * h)⁻¹ = g * (h * l * h⁻¹) * g⁻¹ by group, hg.2.2.2, hh.2.2.2]

theorem lGrp_ind {G n : Nat} (P : GL → Prop) (h1 : P 1) (hmul : ∀ x y, P x → P y → P (x * y))
    (hgen : ∀ g < n, ∀ U, IsP U (look G g) → P U ∧ P U⁻¹) : ∀ U ∈ lGrp G n, P U := by
  intro U hU
  refine Subgroup.closure_induction'' (p := fun x _ => P x) ?_ ?_ h1 (fun x y _ _ => hmul x y) hU
  · rintro x ⟨g, hg, hx⟩
    exact (hgen g hg x hx).1
  · rintro x ⟨g, hg, hx⟩
    exact (hgen g hg x hx).2

theorem cvAt_spec {L : List Nat} {a b p₁ p₂ hh : Nat} (h : cvAt L a b p₁ p₂ hh = true) {U : GL}
    (hU : IsP U hh) :
    (∀ v, linP (subQ L a) (U v) = U (linP (subQ L p₁) v)) ∧
      ∀ v, linP (subQ L b) (U v) = U (linP (subQ L p₂) v) := by
  unfold cvAt at h
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have := congrArg (fun x => linP x v) h.1
    simp only [linP_mulP] at this
    rw [hU, hU, this]
  · have := congrArg (fun x => linP x v) h.2
    simp only [linP_mulP] at this
    rw [hU, hU, this]

theorem rpAt_spec {N2 : List Nat} {NN u : Nat} {rec : List (List Nat)} (h : rpAt N2 NN u rec = true)
    {N : Subgroup GL} (hN : ∀ q < NN, ∃ V ∈ N, IsP V (nthD 0 N2 q))
    (hNle : ∀ M : Subgroup GL, (∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) → N ≤ M) {U : GL}
    (hU : IsP U u) : N.map (MulAut.conj U).toMonoidHom = N := by
  have hle : N.map (MulAut.conj U).toMonoidHom ≤ N := by
    rw [Subgroup.map_le_iff_le_comap]
    refine hNle _ fun q hq V hV => ?_
    unfold rpAt at h
    have hd := (allBelow_iff _ _).1 h q hq
    simp only [Bool.and_eq_true] at hd
    obtain ⟨W, hW, hWP⟩ := isP_wordF hN _ hd.1
    have hUV : U * V = W * U := by
      have h1 := hU.mul hV
      rw [Nat.eq_of_beq_eq_true hd.2] at h1
      exact IsP.inj h1 (hWP.mul hU)
    change U * V * U⁻¹ ∈ N
    rw [hUV, mul_inv_cancel_right]
    exact hW
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj U).injective]

end CFSG.KC.GUV

end
