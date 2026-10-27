module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OutCyc

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S3


theorem marking_transport_central {X : Type} [Group X] (rel : X → X → Prop) {P : LargeEvenMarkProp X}
    (h₁ : CFSG.Assembly.LargeEvenMarking X fun _ R _ I _ θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ rel φ → FP.CentralMod I φ)
    (h₂ : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ =>
      P lab R I F θ ∧ ∀ φ : MulAut R, LargeEvenInduces θ rel φ → FP.CentralMod I φ := by
  obtain ⟨hX, lab₁, hlab₁, hraw₁⟩ := h₁
  obtain ⟨-, lab₂, hlab₂, hraw₂⟩ := h₂
  have hraw₁' := (FP.canonMIiff hlab₁) _ hraw₁
  obtain ⟨R₁, _, I₁, F₁, ⟨hs, hna, θ₁, hcent₁⟩, hMIiff⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₁'
  have hMI := hMIiff hs hna lab₂ hlab₂
  have hraw₂' := hMI _ hraw₂
  refine ⟨hX, lab₂, hlab₂, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw₂'⟩
  rintro R _ I F ⟨⟨hs', hna', θ₂, hP⟩, hG⟩
  refine ⟨hs', hna', θ₂, hP, ?_⟩
  intro φ₂ hind₂
  let σ : R₁ ≃* R := θ₁.symm.trans θ₂
  have hI : ∀ β : MulAut R₁, β ∈ I₁ ↔ MulAut.congr σ β ∈ I := fun β => hG hs' hna' σ β
  have hind₁ : LargeEvenInduces θ₁ rel (MulAut.congr σ.symm φ₂) := by
    intro l l' hll'
    have h1 := hind₂ l l' hll'
    simp only [σ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, h1]
  have hc : MulAut.congr σ (MulAut.congr σ.symm φ₂) = φ₂ := by
    ext x
    simp [MulAut.congr_apply]
  rw [← hc]
  exact centralMod_congr σ hI (hcent₁ _ hind₁)

theorem marking_transport_central_family {X : Type} [Group X] {ι : Type} (rel : ι → X → X → Prop)
    (S : Set ι) (hS : S.Finite) {P : LargeEvenMarkProp X}
    (h₁ : ∀ i ∈ S, CFSG.Assembly.LargeEvenMarking X fun _ R _ I _ θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ (rel i) φ → FP.CentralMod I φ)
    (h₂ : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ =>
      P lab R I F θ ∧ ∀ i ∈ S, ∀ φ : MulAut R, LargeEvenInduces θ (rel i) φ → FP.CentralMod I φ := by
  revert h₁
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _
    exact CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP, by simp⟩) h₂
  | @insert a s has hs ih =>
    intro h₁
    have ih' := ih fun i hi => h₁ i (Set.mem_insert_of_mem a hi)
    have := marking_transport_central (rel a) (h₁ a (Set.mem_insert a s)) ih'
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun lab R _ I F θ ⟨⟨hP, hall⟩, hc⟩ => ?_) this
    refine ⟨hP, ?_⟩
    intro i hi
    rcases Set.mem_insert_iff.1 hi with rfl | hi'
    · exact hc
    · exact hall i hi'


end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
