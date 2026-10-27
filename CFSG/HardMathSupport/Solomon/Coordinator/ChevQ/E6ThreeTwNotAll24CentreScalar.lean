module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompKac
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

set_option maxRecDepth 100000

section Scalar


variable {L : Type} [Field L]

theorem conjDiagn_center {ν : ℕ} (d : Fin ν → Lˣ) {A : SL(ν, L)}
    (hA : A ∈ Subgroup.center SL(ν, L)) : conjDiagn d A = A := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  apply Subtype.ext
  rw [coe_conjDiagn, ← hr]
  have hc : Commute (Matrix.scalar (Fin ν) r) (diagGLn d : Matrix (Fin ν) (Fin ν) L) :=
    Matrix.scalar_commute r (fun r' => Commute.all r r') _
  rw [← hc.eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem frame_center_cube_eq_one [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {ψ : SL(6, L) →* ModGL Tag.E6 L}
    {σ : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (B : List (Fin Tag.E6.rank → ℤ))
    (hlat : ∀ y : Fin Tag.E6.rank → ZMod 3,
      (∀ β ∈ B, ∑ i, y i * ((β i : ℤ) : ZMod 3) = 0) → y = 0)
    {A : SL(6, L)} (hA : A ∈ Subgroup.center SL(6, L)) (hA3 : A ^ 3 = 1)
    (hB : ∀ β ∈ B, IsRoot Tag.E6 β ∧ Commute (pinnedX Tag.E6 L β 1) (ψ A)) : ψ A = 1 := by
  classical
  by_contra hne
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ω₀, hω₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ω₀ := hω₀.isUnit (by norm_num)
  set ω : Lˣ := hu.unit with hωdef
  have hωprim : IsPrimitiveRoot ω 3 :=
    IsPrimitiveRoot.coe_units_iff.1 (by rw [hωdef, IsUnit.unit_spec]; exact hω₀)
  have hω : orderOf ω = 3 := hωprim.eq_orderOf.symm
  have hω3 : ω ^ 3 = 1 := hωprim.pow_eq_one
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  have hcomm : ∀ x : Fin Tag.E6.rank → ZMod 3, Commute (dV ω x) (ψ A) := fun x => by
    have h := hψ.torus ⟨0, by norm_num⟩ (torV ω x) A
    rw [conjDiagn_center _ hA] at h
    change rootDiagUnit Tag.E6 (torV ω x) * ψ A = ψ A * rootDiagUnit Tag.E6 (torV ω x)
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hψA : ψ A ∈ adjointGroup Tag.E6 L := hψ.range_le_adjointGroup ⟨A, rfl⟩
  have hT := mem_torusGroup_of_commute_dV hω hψA hcomm
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hψ3 : (ψ A) ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have ha3 : a ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← rootDiagUnit_pow, rootDiagUnit_one, ← ha]
    exact hψ3
  have hai : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun ha3 i
  choose y hy using fun i => CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hω (hai i)
  have hay : a = torV ω y := funext fun i => (hy i).symm
  have hy0 : y = 0 := by
    refine hlat y fun β hβ => ?_
    obtain ⟨hβr, hβc⟩ := hB β hβ
    have h1 : rootChar a β = 1 := by
      have h2 := hβc.eq
      have h4 := rootDiagUnit_conj_pinnedX a hβr (1 : L)
      rw [← ha, ← h2, mul_inv_cancel_right] at h4
      have h5 := pinnedX_injective Tag.E6 L β h4
      exact Units.ext (by simpa using h5.symm)
    rw [hay] at h1
    exact (rootChar_torV_eq_one_iff hω3 hω1 y β).1 h1
  apply hne
  rw [ha, hay, hy0]
  have : torV ω (0 : Fin Tag.E6.rank → ZMod 3) = 1 := torV_zero ω
  rw [this, rootDiagUnit_one]

theorem commute_pinnedX_of_mem_rootSpan {Ψ : Set (Fin Tag.E6.rank → ℤ)} {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsRoot Tag.E6 θ) (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ ∧ iform γ θ = 0) {g : ModGL Tag.E6 L}
    (hg : g ∈ rootSpan Tag.E6 L Ψ) (c : L) : Commute (pinnedX Tag.E6 L θ c) g := by
  have hle : rootSpan Tag.E6 L Ψ ≤ Subgroup.centralizer {pinnedX Tag.E6 L θ c} := by
    refine iSup₂_le fun γ hγ x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ((simply_laced_orthogonal_root_commutation Tag.E6 (Or.inr (Or.inl rfl))).2 L γ θ
      (hΨ γ hγ).1 hθ (by rw [dotProduct_mulVec_eq_iform]; exact (hΨ γ hγ).2) x hx _
      (Subgroup.subset_closure ⟨c, rfl⟩)).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hg)) _ rfl

theorem commute_pinnedX_frame_center {ν : ℕ} {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ frameRoots σ) {A : SL(ν, L)} (hA : A ∈ Subgroup.center SL(ν, L)) (c : L) :
    Commute (pinnedX Tag.E6 L γ c) (ψ A) := by
  have hmem : pinnedX Tag.E6 L γ c ∈ ψ.range := by
    rw [hψ.range]
    exact pinnedX_mem_rootSpan hγ c
  obtain ⟨B, hB⟩ := hmem
  rw [← hB]
  change ψ B * ψ A = ψ A * ψ B
  rw [← map_mul, ← map_mul]
  congr 1
  exact (Subgroup.mem_center_iff.1 hA B)

theorem frame_center_cube_eq_one_of_rootsOf [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {S : Finset (Option (Fin Tag.E6.rank))} (hS : ∃ x, x ∉ S)
    {θ : Fin Tag.E6.rank → ℤ} (hθ : IsRoot Tag.E6 θ)
    (horth : ∀ γ ∈ R6, kacTest θ6 S γ → iform γ θ = 0)
    (hlat : ∀ y : Fin Tag.E6.rank → ZMod 3,
      (∀ β ∈ R6.filter (fun γ => decide (kacTest θ6 S γ)) ++ [θ],
        ∑ i, y i * ((β i : ℤ) : ZMod 3) = 0) → y = 0)
    {ψ : SL(6, L) →* ModGL Tag.E6 L} {σ : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hr : frameRoots σ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank))))
    {A : SL(6, L)} (hA : A ∈ Subgroup.center SL(6, L)) (hA3 : A ^ 3 = 1) : ψ A = 1 := by
  refine frame_center_cube_eq_one h3 hψ _ hlat hA hA3 fun β hβ => ?_
  rw [List.mem_append, List.mem_filter, List.mem_singleton] at hβ
  rcases hβ with ⟨hβR, hβk⟩ | rfl
  · have hβS : β ∈ frameRoots σ := by
      rw [hr]
      exact (mem_rootsOf_iff kacE6 facts_E6 hS).2 ⟨isRoot_of_mem_R6 hβR, of_decide_eq_true hβk⟩
    exact ⟨isRoot_of_mem_R6 hβR, commute_pinnedX_frame_center hψ hβS hA 1⟩
  · refine ⟨hθ, commute_pinnedX_of_mem_rootSpan hθ (Ψ := frameRoots σ) (fun γ hγ => ?_)
      (by rw [← hψ.range]; exact ⟨A, rfl⟩) 1⟩
    rw [hr] at hγ
    obtain ⟨hγr, hγk⟩ := (mem_rootsOf_iff kacE6 facts_E6 hS).1 hγ
    exact ⟨hγr, horth γ (mem_R6_of_isRoot hγr) hγk⟩

theorem exists_notMem_sA5 : (∃ x, x ∉ sA5a) ∧ (∃ x, x ∉ sA5b) ∧ (∃ x, x ∉ sA5c) := by
  refine ⟨⟨none, ?_⟩, ⟨some 0, ?_⟩, ⟨some 4, ?_⟩⟩ <;> decide

theorem sA5a_lat : ∀ y : Fin Tag.E6.rank → ZMod 3,
    (∀ β ∈ R6.filter (fun γ => decide (kacTest θ6 sA5a γ)) ++ [θ6],
      ∑ i, y i * ((β i : ℤ) : ZMod 3) = 0) → y = 0 := by
  decide +kernel

theorem sA5b_lat : ∀ y : Fin Tag.E6.rank → ZMod 3,
    (∀ β ∈ R6.filter (fun γ => decide (kacTest θ6 sA5b γ)) ++ [Pi.single 0 1],
      ∑ i, y i * ((β i : ℤ) : ZMod 3) = 0) → y = 0 := by
  decide +kernel

theorem sA5c_lat : ∀ y : Fin Tag.E6.rank → ZMod 3,
    (∀ β ∈ R6.filter (fun γ => decide (kacTest θ6 sA5c γ)) ++ [Pi.single 5 1],
      ∑ i, y i * ((β i : ℤ) : ZMod 3) = 0) → y = 0 := by
  decide +kernel

theorem sA5a_orth : ∀ γ ∈ R6, kacTest θ6 sA5a γ → iform γ θ6 = 0 := by decide +kernel

theorem sA5b_orth : ∀ γ ∈ R6, kacTest θ6 sA5b γ → iform γ (Pi.single 0 1) = 0 := by
  decide +kernel

theorem sA5c_orth : ∀ γ ∈ R6, kacTest θ6 sA5c γ → iform γ (Pi.single 5 1) = 0 := by
  decide +kernel

theorem frame_A5_center_cube_eq_one [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {S : Finset (Option (Fin Tag.E6.rank))}
    (hS : S = sA5a ∨ S = sA5b ∨ S = sA5c)
    {ψ : SL(6, L) →* ModGL Tag.E6 L} {σ : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hr : frameRoots σ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank))))
    {A : SL(6, L)} (hA : A ∈ Subgroup.center SL(6, L)) (hA3 : A ^ 3 = 1) : ψ A = 1 := by
  obtain ⟨ha, hb, hc⟩ := exists_notMem_sA5
  rcases hS with rfl | rfl | rfl
  · exact frame_center_cube_eq_one_of_rootsOf h3 ha (isRoot_of_mem_R6 (by decide)) sA5a_orth
      sA5a_lat hψ hr hA hA3
  · exact frame_center_cube_eq_one_of_rootsOf h3 hb (isRoot_of_mem_R6 (by decide)) sA5b_orth
      sA5b_lat hψ hr hA hA3
  · exact frame_center_cube_eq_one_of_rootsOf h3 hc (isRoot_of_mem_R6 (by decide)) sA5c_orth
      sA5c_lat hψ hr hA hA3

end Scalar

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
