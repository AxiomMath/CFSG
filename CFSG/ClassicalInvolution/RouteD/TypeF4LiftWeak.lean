module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.WeakCT.DLWeakPair

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock
  shortBlock symplecticBlockPair_le_sup symplecticBlockPair_map)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (lifting_lemma_sp4)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem symplecticBlockPair_lift {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y}
    [O.Normal] (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) {A B : Subgroup Y}
    (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆) {W : Subgroup (Y ⧸ O)}
    (h : SymplecticBlockPair F W (A.map (QuotientGroup.mk' O))
      (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, SymplecticBlockPair F W' A B := by
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  let π := QuotientGroup.mk' O
  let P : Subgroup Y := A ⊔ B
  let π' : ↥P →* Y ⧸ O := π.comp P.subtype
  have hW : W ≤ A.map π ⊔ B.map π := symplecticBlockPair_le_sup h
  obtain ⟨θb, c, hrange, hker, hinjL, hU, hV⟩ := h
  have hrange' : π'.range = A.map π ⊔ B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup]
  have hAle : A.map π ≤ θb.range := hU ▸ Subgroup.map_le_range θb _
  have hBle : B.map π ≤ θb.range := hV ▸ Subgroup.map_le_range θb _
  have hθ : ∀ s, θb s ∈ π'.range := fun s => by
    rw [hrange']
    exact hW (hrange ▸ ⟨s, rfl⟩)
  have hPperf : P ≤ ⁅P, P⁆ :=
    sup_le (hA.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
      (hB.trans (Subgroup.commutator_mono le_sup_right le_sup_right))
  have : Group.IsPerfect ↥P :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)) hPperf)
  have hZc : π'.ker ≤ Subgroup.center ↥P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hZodd : Odd (Nat.card π'.ker) := by
    refine hOodd.of_dvd_nat ?_
    let g : π'.ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  let e : (↥P ⧸ π'.ker) ≃* π'.range := QuotientGroup.quotientKerEquivRange π'
  let θc : StatedSp 2 F →* π'.range := θb.codRestrict π'.range hθ
  let θbar : StatedSp 2 F →* ↥P ⧸ π'.ker := e.symm.toMonoidHom.comp θc
  have hθcsurj : Function.Surjective θc := by
    rintro ⟨w, hw⟩
    rw [hrange'] at hw
    have hw' : w ∈ θb.range := (sup_le hAle hBle) hw
    obtain ⟨x, hx⟩ := hw'
    exact ⟨x, Subtype.ext hx⟩
  have hθbarsurj : Function.Surjective θbar := e.symm.surjective.comp hθcsurj
  have hθbarker : θbar.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro x hx
    apply hker
    have hx' : e.symm (θc x) = 1 := hx
    have : θc x = 1 := (MulEquiv.map_eq_one_iff e.symm).mp hx'
    simpa [θc, Subtype.ext_iff] using this
  obtain ⟨θ, -, hθker, hθeq⟩ := lifting_lemma_sp4 hp2 hF h5 (MulEquiv.refl (StatedSp 2 F)) hZc
    hZodd θbar hθbarsurj hθbarker
  have hπθ : ∀ x, π ((θ x : ↥P) : Y) = θb x := by
    intro x
    have h1 := hθeq x
    have h2 : e ((θ x : ↥P ⧸ π'.ker)) = θc x := by
      rw [h1]
      exact e.apply_symm_apply _
    have h3 : (e ((θ x : ↥P ⧸ π'.ker)) : Y ⧸ O) = π' (θ x) := rfl
    rw [h2] at h3
    exact h3.symm.trans rfl
  let θY : StatedSp 2 F →* Y := P.subtype.comp θ
  have hπθY : π.comp θY = θb := MonoidHom.ext hπθ
  have hperfmap : ∀ X : Subgroup (StatedSp 2 F), X ≤ ⁅X, X⁆ → X.map θY ≤ ⁅X.map θY, X.map θY⁆ := by
    intro X hX
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hX
  have hconjperf : ∀ φ : SL(2, F) →* StatedSp 2 F,
      φ.range.map (MulAut.conj c⁻¹).toMonoidHom ≤
        ⁅φ.range.map (MulAut.conj c⁻¹).toMonoidHom, φ.range.map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    intro φ
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (range_perfect_of_sl2 h4 φ)
  refine ⟨θY.range, θY, c, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hθker
    exact Subtype.ext (MonoidHom.mem_ker.mp hx)
  · intro a b hab
    apply hinjL
    simp only [MonoidHom.comp_apply] at hab ⊢
    rw [← hπθ, ← hπθ]
    exact congrArg π hab
  · refine eq_of_map_mk_eq_of_central hOc (hperfmap _ (hconjperf (longBlock F 2 1))) hA ?_
    rw [Subgroup.map_map, hπθY]
    exact hU
  · refine eq_of_map_mk_eq_of_central hOc (hperfmap _ (hconjperf
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)))) hB ?_
    rw [Subgroup.map_map, hπθY]
    exact hV

theorem symplecticBlockPair_of_locImg_perfect [Finite G] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} {x : G} (hP1 : LocalOddCentral Ω {x}) {A B : Subgroup G}
    (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) (hAp : A ≤ ⁅A, A⁆) (hBp : B ≤ ⁅B, B⁆)
    {W : Subgroup (locQuot Ω x)}
    (h : SymplecticBlockPair (GaloisField p f) W (locImg Ω x A) (locImg Ω x B)) :
    ∃ W' : Subgroup G, SymplecticBlockPair (GaloisField p f) W' A B := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  obtain ⟨W', hW'⟩ := symplecticBlockPair_lift (F := GaloisField p f) hp2
    (GaloisField.card p f hf) h5 (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) (perfect_subgroupOf hA hAp)
    (perfect_subgroupOf hB hBp) h
  have := symplecticBlockPair_map hW' (locLayer Ω x).subtype
    (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA,
    inf_eq_left.mpr hB] at this
  exact ⟨_, this⟩

end Lift

end CFSG.ClassicalInvolution.RouteD
