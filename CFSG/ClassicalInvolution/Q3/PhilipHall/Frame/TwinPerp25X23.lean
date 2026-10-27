module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X22
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X15

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q8P.Asc77.P25T
open CFSG.ClassicalInvolution.Asc77.CX (TwinGroup DiagTriv DiagRel TwinIso centTG fixSubgroup
  centralizer_pair_comm)
open scoped MatrixGroups


section Edge

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem edge_data (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w x y : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') (hLF : LayerFacts hyp hw2) (hxA : x ∈ cA S R R') (hyA : y ∈ cA S R R')
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hyx : y = x * w * z) (hbx : z ∉ zStarOf (Subgroup.centralizer ({w, x} : Set G)))
    (hby : z ∉ zStarOf (Subgroup.centralizer ({w, y} : Set G)))
    (T : TwinLift (eBar hyp hw2 hwA) (eBar' hyp hw2 hwA) (zBar hyp hw2 hwA) (actBar hyp hw2)) :
    ∃ (hA : T.A ≤ subLayer hyp hw2 hx) (hA' : T.A' ≤ subLayer hyp hw2 hx)
      (hB : T.A ≤ subLayer hyp hw2 hy) (hB' : T.A' ≤ subLayer hyp hw2 hy),
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5
          (centTG T.A T.A' (actOf hyp hw2 ⟨x, hx⟩) hA hA') ∧
        CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5
          (centTG T.A T.A' (actOf hyp hw2 ⟨y, hy⟩) hB hB') ∧
          ¬ DiagRel 3 (centTG T.A T.A' (actOf hyp hw2 ⟨x, hx⟩) hA hA')
            (centTG T.A T.A' (actOf hyp hw2 ⟨y, hy⟩) hB hB') := by
  obtain ⟨hyeq, hβ1, hβz⟩ := reflection_of_bad hyp hw2 hwA hLF hxA hyA hx hy hyx hbx hby
  have hmem : actOf hyp hw2 ⟨x, hx⟩ ∈ actBar hyp hw2 :=
    ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxA, rfl⟩
  obtain ⟨hf, hf'⟩ := T.hfix _ hmem
  exact refl_edge_om T (by rw [T.hz]; exact hyeq) hf hf' (hLF.exp2 x hxA hx) hβ1
    (by rw [T.hz]; exact hβz)

end Edge

section Cocycle

variable {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {A₁ A₁' : Subgroup Y}
  {A₂ A₂' : Subgroup Y'} {β : MulAut Y} {β' : MulAut Y'}

theorem restrTo_coe_of_eq (hA : A₁ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : A₁' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : A₂ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : A₂' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hAm : (centTG A₁ A₁' β hA hA').A.map (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β'))) = (centTG A₂ A₂' β' hB hB').A) (k : ↥A₁) {x : Y}
    (hkx : (k : Y) = x) (hx : x ∈ Goldschmidt75.perfRes (fixSubgroup β)) {y : Y'}
    (hψ : ((ψ ⟨x, hx⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') = y) :
    ((restrTo (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k : ↥A₂) : Y') = y := by
  rw [restrTo_coe]
  have : (⟨(k : Y), hA k.2⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β))) = ⟨x, hx⟩ := Subtype.ext hkx
  rw [this]
  exact hψ

theorem restrTo'_coe_of_eq (hA : A₁ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : A₁' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : A₂ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : A₂' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hAm : (centTG A₁ A₁' β hA hA').A'.map (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β'))) = (centTG A₂ A₂' β' hB hB').A') (k : ↥A₁') {x : Y}
    (hkx : (k : Y) = x) (hx : x ∈ Goldschmidt75.perfRes (fixSubgroup β)) {y : Y'}
    (hψ : ((ψ ⟨x, hx⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') = y) :
    ((restrTo' (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k : ↥A₂') : Y') = y := by
  rw [restrTo'_coe]
  have : (⟨(k : Y), hA' k.2⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β))) = ⟨x, hx⟩ := Subtype.ext hkx
  rw [this]
  exact hψ

end Cocycle

section FaceLifts

variable {Y₁ Y₂ Y₃ : Type} [Group Y₁] [Group Y₂] [Group Y₃] [Finite Y₁] [Finite Y₂] [Finite Y₃]
  {E E' : Type} {e₁ : E → Y₁} {e₁' : E' → Y₁} {e₂ : E → Y₂} {e₂' : E' → Y₂} {e₃ : E → Y₃}
  {e₃' : E' → Y₃} {zb₁ : Y₁} {zb₂ : Y₂} {zb₃ : Y₃} {P₁ : Subgroup (MulAut Y₁)}
  {P₂ : Subgroup (MulAut Y₂)} {P₃ : Subgroup (MulAut Y₃)}

theorem false_of_face_lifts (h1 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.DiagThree)
    (T₁ : TwinLift e₁ e₁' zb₁ P₁) (T₂ : TwinLift e₂ e₂' zb₂ P₂) (T₃ : TwinLift e₃ e₃' zb₃ P₃)
    {β₁₂ β₁₃ : MulAut Y₁} {β₂₁ β₂₃ : MulAut Y₂} {β₃₁ β₃₂ : MulAut Y₃}
    (hA₁₂ : T₁.A ≤ Goldschmidt75.perfRes (fixSubgroup β₁₂))
    (hA'₁₂ : T₁.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₁₂))
    (hA₁₃ : T₁.A ≤ Goldschmidt75.perfRes (fixSubgroup β₁₃))
    (hA'₁₃ : T₁.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₁₃))
    (hA₂₁ : T₂.A ≤ Goldschmidt75.perfRes (fixSubgroup β₂₁))
    (hA'₂₁ : T₂.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₂₁))
    (hA₂₃ : T₂.A ≤ Goldschmidt75.perfRes (fixSubgroup β₂₃))
    (hA'₂₃ : T₂.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₂₃))
    (hA₃₁ : T₃.A ≤ Goldschmidt75.perfRes (fixSubgroup β₃₁))
    (hA'₃₁ : T₃.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₃₁))
    (hA₃₂ : T₃.A ≤ Goldschmidt75.perfRes (fixSubgroup β₃₂))
    (hA'₃₂ : T₃.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₃₂))
    (h5₁₂ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂))
    (h5₁₃ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃))
    (h5₂₃ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃))
    (n₁ : ¬ DiagRel 3 (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂) (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃))
    (n₂ : ¬ DiagRel 3 (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁) (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃))
    (n₃ : ¬ DiagRel 3 (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁) (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂))
    (ψ₁₂ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₂)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β₂₁)))
    (m₁₂ : (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂).A.map (ψ₁₂ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₂)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₂₁))) = (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁).A)
    (m'₁₂ : (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂).A'.map (ψ₁₂ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₂)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₂₁))) = (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁).A')
    (ψ₁₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₃)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β₃₁)))
    (m₁₃ : (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃).A.map (ψ₁₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₃)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₃₁))) = (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁).A)
    (m'₁₃ : (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃).A'.map (ψ₁₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₁₃)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₃₁))) = (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁).A')
    (ψ₂₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₂₃)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β₃₂)))
    (m₂₃ : (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃).A.map (ψ₂₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₂₃)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₃₂))) = (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂).A)
    (m'₂₃ : (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃).A'.map (ψ₂₃ : ↥(Goldschmidt75.perfRes (fixSubgroup β₂₃)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β₃₂))) = (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂).A')
    (r₁₂ : ∀ r : E, ((ψ₁₂ ⟨e₁ r, hA₁₂ (T₁.he r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₂₁))) : Y₂) = e₂ r)
    (r'₁₂ : ∀ r : E', ((ψ₁₂ ⟨e₁' r, hA'₁₂ (T₁.he' r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₂₁))) : Y₂) =
      e₂' r)
    (r₁₃ : ∀ r : E, ((ψ₁₃ ⟨e₁ r, hA₁₃ (T₁.he r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₃₁))) : Y₃) = e₃ r)
    (r'₁₃ : ∀ r : E', ((ψ₁₃ ⟨e₁' r, hA'₁₃ (T₁.he' r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₃₁))) : Y₃) =
      e₃' r)
    (r₂₃ : ∀ r : E, ((ψ₂₃ ⟨e₂ r, hA₂₃ (T₂.he r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₃₂))) : Y₃) = e₃ r)
    (r'₂₃ : ∀ r : E', ((ψ₂₃ ⟨e₂' r, hA'₂₃ (T₂.he' r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β₃₂))) : Y₃) =
      e₃' r) : False := by
  classical
  refine false_of_face_abstract h1 (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂) (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃)
    (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁) (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃)
    (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁) (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂) h5₁₂ h5₁₃ h5₂₃ n₁ n₂ n₃
    ψ₁₂ m₁₂ m'₁₂ ψ₁₃ m₁₃ m'₁₃ ψ₂₃ m₂₃ m'₂₃ ?_ ?_
  · intro k
    have key := mulEquiv_eq_of_pow4 T₁.eA
      ((restrTo (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂) (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁) ψ₁₂ m₁₂).trans
        (restrTo (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃) (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂) ψ₂₃ m₂₃))
      (restrTo (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃) (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁) ψ₁₃ m₁₃) ?_
    · exact DFunLike.congr_fun key k
    · intro k hk
      have hk4 : (k : Y₁) ^ 4 = 1 := by
        simpa using congrArg (fun m : ↥T₁.A => (m : Y₁)) hk
      obtain ⟨r, hr⟩ := T₁.hQ _ k.2 hk4
      have h12 := restrTo_coe_of_eq hA₁₂ hA'₁₂ hA₂₁ hA'₂₁ ψ₁₂ m₁₂ k hr (hA₁₂ (T₁.he r)) (r₁₂ r)
      have h23 := restrTo_coe_of_eq hA₂₃ hA'₂₃ hA₃₂ hA'₃₂ ψ₂₃ m₂₃ _ h12 (hA₂₃ (T₂.he r)) (r₂₃ r)
      have h13 := restrTo_coe_of_eq hA₁₃ hA'₁₃ hA₃₁ hA'₃₁ ψ₁₃ m₁₃ k hr (hA₁₃ (T₁.he r)) (r₁₃ r)
      exact Subtype.ext (h23.trans h13.symm)
  · intro k
    have key := mulEquiv_eq_of_pow4 T₁.eA'
      ((restrTo' (centTG T₁.A T₁.A' β₁₂ hA₁₂ hA'₁₂) (centTG T₂.A T₂.A' β₂₁ hA₂₁ hA'₂₁) ψ₁₂ m'₁₂).trans
        (restrTo' (centTG T₂.A T₂.A' β₂₃ hA₂₃ hA'₂₃) (centTG T₃.A T₃.A' β₃₂ hA₃₂ hA'₃₂) ψ₂₃ m'₂₃))
      (restrTo' (centTG T₁.A T₁.A' β₁₃ hA₁₃ hA'₁₃) (centTG T₃.A T₃.A' β₃₁ hA₃₁ hA'₃₁) ψ₁₃ m'₁₃) ?_
    · exact DFunLike.congr_fun key k
    · intro k hk
      have hk4 : (k : Y₁) ^ 4 = 1 := by
        simpa using congrArg (fun m : ↥T₁.A' => (m : Y₁)) hk
      obtain ⟨r, hr⟩ := T₁.hQ' _ k.2 hk4
      have h12 := restrTo'_coe_of_eq hA₁₂ hA'₁₂ hA₂₁ hA'₂₁ ψ₁₂ m'₁₂ k hr (hA'₁₂ (T₁.he' r)) (r'₁₂ r)
      have h23 := restrTo'_coe_of_eq hA₂₃ hA'₂₃ hA₃₂ hA'₃₂ ψ₂₃ m'₂₃ _ h12 (hA'₂₃ (T₂.he' r)) (r'₂₃ r)
      have h13 := restrTo'_coe_of_eq hA₁₃ hA'₁₃ hA₃₁ hA'₃₁ ψ₁₃ m'₁₃ k hr (hA'₁₃ (T₁.he' r)) (r'₁₃ r)
      exact Subtype.ext (h23.trans h13.symm)

end FaceLifts

section Face

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem noFaceAt_proved (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : NoFaceAt hyp := by
  classical
  intro w₁ w₂ w₃ hA₁ hA₂ hA₃ s₁ s₂ s₃ n₁ n₂ n₃ c₁₂ c₁₃ c₂₃ hprod b₁ b₂ b₃ F₁₂ F₁₃ F₂₃
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hC : ∀ {a b : G}, a * b = b * a → b ∈ Subgroup.centralizer ({a} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.symm
  have C₁₂ := hC c₁₂
  have C₂₁ := hC c₁₂.symm
  have C₁₃ := hC c₁₃
  have C₃₁ := hC c₁₃.symm
  have C₂₃ := hC c₂₃
  have C₃₂ := hC c₂₃.symm
  have e₁ : w₃ = w₂ * w₁ * z := by
    calc w₃ = w₂ * (w₁ * w₁) * w₂ * w₃ := by rw [s₁, mul_one, s₂, one_mul]
      _ = w₂ * w₁ * (w₁ * w₂ * w₃) := by group
      _ = w₂ * w₁ * z := by rw [hprod]
  have e₂ : w₃ = w₁ * w₂ * z := by rw [e₁, c₁₂]
  have e₃ : w₂ = w₁ * w₃ * z := by
    calc w₂ = (w₁ * w₁) * w₂ * (w₃ * w₃) := by rw [s₁, s₃, one_mul, mul_one]
      _ = w₁ * (w₁ * w₂ * w₃) * w₃ := by group
      _ = w₁ * w₃ * z := by rw [hprod, mul_assoc, (hzS w₃ hA₃.1).symm, ← mul_assoc]
  have ty₁ := typedL_proved G Ω K K' W S R R' z t u₁ u₂ hyp w₁ hA₁ s₁ n₁ b₁
  have ty₂ := typedL_proved G Ω K K' W S R R' z t u₁ u₂ hyp w₂ hA₂ s₂ n₂ b₂
  have ty₃ := typedL_proved G Ω K K' W S R R' z t u₁ u₂ hyp w₃ hA₃ s₃ n₃ b₃
  have LF₁ := layerFacts_of_typed hyp hA₁ s₁ n₁ ty₁
  have LF₂ := layerFacts_of_typed hyp hA₂ s₂ n₂ ty₂
  have LF₃ := layerFacts_of_typed hyp hA₃ s₃ n₃ ty₃
  have F₂₁ : z ∉ zStarOf (Subgroup.centralizer ({w₂, w₁} : Set G)) := by
    rw [centralizer_pair_comm]
    exact F₁₂
  have F₃₁ : z ∉ zStarOf (Subgroup.centralizer ({w₃, w₁} : Set G)) := by
    rw [centralizer_pair_comm]
    exact F₁₃
  have F₃₂ : z ∉ zStarOf (Subgroup.centralizer ({w₃, w₂} : Set G)) := by
    rw [centralizer_pair_comm]
    exact F₂₃
  have om₁ : SecNoExitAt Ω w₁ ∧ LayerLie Ω w₁ 6 := by
    rcases layer_cases hyp hA₁ s₁ n₁ ty₁ with hfix | h
    · exfalso
      obtain ⟨-, h1, h2⟩ := reflection_of_bad hyp s₁ hA₁ LF₁ hA₂ hA₃ C₁₂ C₁₃ e₁ F₁₂ F₁₃
      rcases hfix w₂ hA₂ C₁₂ with h | h
      · exact h1 h
      · exact h2 h
    · exact h
  have om₂ : SecNoExitAt Ω w₂ ∧ LayerLie Ω w₂ 6 := by
    rcases layer_cases hyp hA₂ s₂ n₂ ty₂ with hfix | h
    · exfalso
      obtain ⟨-, h1, h2⟩ := reflection_of_bad hyp s₂ hA₂ LF₂ hA₁ hA₃ C₂₁ C₂₃ e₂ F₂₁ F₂₃
      rcases hfix w₁ hA₁ C₂₁ with h | h
      · exact h1 h
      · exact h2 h
    · exact h
  have om₃ : SecNoExitAt Ω w₃ ∧ LayerLie Ω w₃ 6 := by
    rcases layer_cases hyp hA₃ s₃ n₃ ty₃ with hfix | h
    · exfalso
      obtain ⟨-, h1, h2⟩ := reflection_of_bad hyp s₃ hA₃ LF₃ hA₁ hA₂ C₃₁ C₃₂ e₃ F₃₁ F₃₂
      rcases hfix w₁ hA₁ C₃₁ with h | h
      · exact h1 h
      · exact h2 h
    · exact h
  obtain ⟨T₁⟩ := twinLiftBar hyp s₁ n₁ hA₁ om₁.1 om₁.2
  obtain ⟨T₂⟩ := twinLiftBar hyp s₂ n₂ hA₂ om₂.1 om₂.2
  obtain ⟨T₃⟩ := twinLiftBar hyp s₃ n₃ hA₃ om₃.1 om₃.2
  obtain ⟨hA₁₂, hA'₁₂, hA₁₃, hA'₁₃, h5₁₂, h5₁₃, nd₁⟩ :=
    edge_data hyp s₁ hA₁ LF₁ hA₂ hA₃ C₁₂ C₁₃ e₁ F₁₂ F₁₃ T₁
  obtain ⟨hA₂₁, hA'₂₁, hA₂₃, hA'₂₃, h5₂₁, h5₂₃, nd₂⟩ :=
    edge_data hyp s₂ hA₂ LF₂ hA₁ hA₃ C₂₁ C₂₃ e₂ F₂₁ F₂₃ T₂
  obtain ⟨hA₃₁, hA'₃₁, hA₃₂, hA'₃₂, h5₃₁, h5₃₂, nd₃⟩ :=
    edge_data hyp s₃ hA₃ LF₃ hA₁ hA₂ C₃₁ C₃₂ e₃ F₃₁ F₃₂ T₃
  have hom5 := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.om5StabDiag_proved
  have hcent5 := CFSG.ClassicalInvolution.Q3.Q3T7P25.cent5Three_proved
  obtain ⟨ψ₁₂, m₁₂, m'₁₂, r₁₂, r'₁₂⟩ := vertexIso hom5 hcent5 hyp s₁ s₂ hA₁ hA₂ C₁₂ C₂₁ T₁ T₂
    hA₁₂ hA'₁₂ hA₂₁ hA'₂₁ h5₁₂ h5₂₁
  obtain ⟨ψ₁₃, m₁₃, m'₁₃, r₁₃, r'₁₃⟩ := vertexIso hom5 hcent5 hyp s₁ s₃ hA₁ hA₃ C₁₃ C₃₁ T₁ T₃
    hA₁₃ hA'₁₃ hA₃₁ hA'₃₁ h5₁₃ h5₃₁
  obtain ⟨ψ₂₃, m₂₃, m'₂₃, r₂₃, r'₂₃⟩ := vertexIso hom5 hcent5 hyp s₂ s₃ hA₂ hA₃ C₂₃ C₃₂ T₂ T₃
    hA₂₃ hA'₂₃ hA₃₂ hA'₃₂ h5₂₃ h5₃₂
  exact false_of_face_lifts CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.diagThree_proved T₁ T₂ T₃
    hA₁₂ hA'₁₂ hA₁₃ hA'₁₃ hA₂₁ hA'₂₁ hA₂₃ hA'₂₃ hA₃₁ hA'₃₁ hA₃₂ hA'₃₂ h5₁₂ h5₁₃ h5₂₃ nd₁ nd₂ nd₃
    ψ₁₂ m₁₂ m'₁₂ ψ₁₃ m₁₃ m'₁₃ ψ₂₃ m₂₃ m'₂₃ r₁₂ r'₁₂ r₁₃ r'₁₃ r₂₃ r'₂₃

end Face

theorem noFace_proved : P25X_NoFace := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact noFaceAt_proved hyp

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
