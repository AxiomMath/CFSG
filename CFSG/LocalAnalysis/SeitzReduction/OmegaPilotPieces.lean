module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL leviEmbedSL_injective)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear consecutiveBlock)
open CFSG.SeitzReduction.SymplecticPilot (siegelBlock)
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] {m : ℕ}

variable (F) in
@[expose] noncomputable def modelTheta (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) :
    SL(3, F) →* GL (Fin m ⊕ Fin m) F :=
  (MulAut.conj (flipGL F P)).toMonoidHom.comp ((StatedSp m F).subtype.comp
    ((leviEmbedSL F m).comp (CFSG.ClassicalInvolution.WeakCT.blockSL F m 3 a ha)))

theorem modelTheta_injective (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) :
    Function.Injective (modelTheta F a ha P) :=
  (MulAut.conj (flipGL F P)).injective.comp (Subtype.val_injective.comp
    (leviEmbedSL_injective.comp (CFSG.ClassicalInvolution.WeakCT.blockSL_injective ha)))

theorem map_modelTheta (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) (H : Subgroup SL(3, F)) :
    H.map (modelTheta F a ha P) =
      (((H.map (CFSG.ClassicalInvolution.WeakCT.blockSL F m 3 a ha)).map (leviEmbedSL F m)).map
        (StatedSp m F).subtype).map (MulAut.conj (flipGL F P)).toMonoidHom := by
  simp only [modelTheta, Subgroup.map_map]

theorem map_blockSL_siegel {k i : ℕ} (h : i + k ≤ m) :
    (((⊤ : Subgroup SL(k, F)).map (CFSG.ClassicalInvolution.WeakCT.blockSL F m k i h)).map
        (leviEmbedSL F m)).map (StatedSp m F).subtype =
      siegelBlockGL F (consecutiveBlock m i k) := by
  rw [← MonoidHom.range_eq_map, LinearPilot.range_blockSL_eq h]
  rfl

theorem range_modelTheta (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) :
    (modelTheta F a ha P).range =
      (siegelBlockGL F (consecutiveBlock m a 3)).map (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [MonoidHom.range_eq_map, map_modelTheta, map_blockSL_siegel]

theorem map_B12_modelTheta (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) :
    (B12 F).map (modelTheta F a ha P) =
      (siegelBlockGL F (consecutiveBlock m a 2)).map (MulAut.conj (flipGL F P)).toMonoidHom := by
  have h : (B12 F).map (CFSG.ClassicalInvolution.WeakCT.blockSL F m 3 a ha) =
      (⊤ : Subgroup SL(2, F)).map (CFSG.ClassicalInvolution.WeakCT.blockSL F m 2 a (by omega)) := by
    rw [B12, MonoidHom.range_eq_map, Subgroup.map_map,
      CFSG.ClassicalInvolution.WeakCT.blockSL_comp]
    rfl
  rw [map_modelTheta, h, map_blockSL_siegel]

theorem map_B23_modelTheta (a : ℕ) (ha : a + 3 ≤ m) (P : Finset (Fin m)) :
    (B23 F).map (modelTheta F a ha P) =
      (siegelBlockGL F (consecutiveBlock m (a + 1) 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom := by
  have h : (B23 F).map (CFSG.ClassicalInvolution.WeakCT.blockSL F m 3 a ha) =
      (⊤ : Subgroup SL(2, F)).map
        (CFSG.ClassicalInvolution.WeakCT.blockSL F m 2 (a + 1) (by omega)) := by
    rw [B23, MonoidHom.range_eq_map, Subgroup.map_map,
      CFSG.ClassicalInvolution.WeakCT.blockSL_comp]
  rw [map_modelTheta, h, map_blockSL_siegel]

theorem commutator_B12 [Finite F] (hF : 4 ≤ Nat.card F) : ⁅B12 F, B12 F⁆ = B12 F := by
  have h : B12 F = blockSpecialLinear (K := F) (consecutiveBlock 3 0 2) :=
    LinearPilot.range_blockSL_eq (by omega)
  rw [h]
  exact LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF

theorem commutator_B23 [Finite F] (hF : 4 ≤ Nat.card F) : ⁅B23 F, B23 F⁆ = B23 F := by
  have h : B23 F = blockSpecialLinear (K := F) (consecutiveBlock 3 1 2) :=
    LinearPilot.range_blockSL_eq (by omega)
  rw [h]
  exact LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF

end Model

section Pair

variable {G : Type*} [Group G] {F : Type} [Field F] [Finite F]

theorem commutator_subgroupOf_eq_of_le_perfect {M H : Subgroup G} (hHM : H ≤ M)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf M, H.subgroupOf M⁆ = H.subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHM, hH]

theorem exists_theta_of_central (hF : 5 ≤ Nat.card F) {M U V : Subgroup G} (hUM : U ≤ M)
    (hVM : V ≤ M) (hUp : ⁅U, U⁆ = U) (hVp : ⁅V, V⁆ = V) {Q : Type*} [Group Q]
    {θ₀ : SL(3, F) →* Q} (hθ₀ : Function.Injective θ₀) (ρ : M →* Q) (hρ : ρ.range = θ₀.range)
    (hker : ρ.ker ≤ center M) (hU : (U.subgroupOf M).map ρ = (B12 F).map θ₀)
    (hV : (V.subgroupOf M).map ρ = (B23 F).map θ₀) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have hmem : ∀ x : M, ρ x ∈ θ₀.range := fun x => by
    rw [← hρ]
    exact ⟨x, rfl⟩
  let ρ' : M →* SL(3, F) :=
    (MonoidHom.ofInjective hθ₀).symm.toMonoidHom.comp (ρ.codRestrict θ₀.range hmem)
  have hρ' : ∀ x, θ₀ (ρ' x) = ρ x := fun x => by
    rw [← MonoidHom.ofInjective_apply hθ₀]
    change ((MonoidHom.ofInjective hθ₀ ((MonoidHom.ofInjective hθ₀).symm
      (ρ.codRestrict θ₀.range hmem x)) : θ₀.range) : Q) = ρ x
    rw [MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply]
  have hsurj : Function.Surjective ρ' := fun A => by
    obtain ⟨x, hx⟩ : θ₀ A ∈ ρ.range := by
      rw [hρ]
      exact ⟨A, rfl⟩
    exact ⟨x, hθ₀ (by rw [hρ', hx])⟩
  have hkerc : ρ'.ker ≤ center M := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hρ', hx, map_one])
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (m := 2) le_rfl hF hsurj hkerc
  have hs' : ρ'.comp s = MonoidHom.id _ := MonoidHom.ext hs
  have key : ∀ (H : Subgroup G) (B : Subgroup SL(3, F)), H ≤ M → ⁅H, H⁆ = H → ⁅B, B⁆ = B →
      (H.subgroupOf M).map ρ = B.map θ₀ → B.map (M.subtype.comp s) = H := by
    intro H B hHM hHp hBp hHB
    have h1 : (H.subgroupOf M).map ρ' = B := by
      ext A
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨A', hA', h'⟩ : θ₀ (ρ' x) ∈ B.map θ₀ := by
          rw [← hHB, hρ']
          exact ⟨x, hx, rfl⟩
        rwa [← hθ₀ h']
      · intro hA
        obtain ⟨x, hx, h'⟩ : θ₀ A ∈ (H.subgroupOf M).map ρ := by
          rw [hHB]
          exact ⟨A, hA, rfl⟩
        exact ⟨x, hx, hθ₀ (by rw [hρ', h'])⟩
    have h2 : (B.map s).map ρ' = B := by
      rw [Subgroup.map_map, hs', Subgroup.map_id]
    have hBs : ⁅B.map s, B.map s⁆ = B.map s := by
      rw [← Subgroup.map_commutator, hBp]
    have h3 : H.subgroupOf M = B.map s :=
      eq_of_map_eq_of_perfect hkerc (commutator_subgroupOf_eq_of_le_perfect hHM hHp) hBs
        (h1.trans h2.symm)
    rw [← Subgroup.map_map, ← h3, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHM]
  refine ⟨M.subtype.comp s, ?_, key U (B12 F) hUM hUp (commutator_B12 hF4) hU,
    key V (B23 F) hVM hVp (commutator_B23 hF4) hV⟩
  intro A hA
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hA
  have h1 : s A = 1 := Subtype.ext hA
  have : A = 1 := by rw [← hs A, h1, map_one]
  rw [this]
  exact one_mem _

theorem map_inclusion_subgroupOf {A M E : Subgroup G} (hAM : A ≤ M) (hME : M ≤ E) :
    (A.subgroupOf M).map (Subgroup.inclusion hME) = A.subgroupOf E := by
  ext x
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hAM hx⟩, hx, rfl⟩

end Pair

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {m : ℕ}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}
  {k : Fin (m + 1)}

omit [Finite F] in
theorem PlusFieldCover.ker_comp_subtype_le (C : PlusFieldCover e ι k) :
    ((StatedOmega (StatedQuadPlus m F)).subtype.comp C.π).ker ≤
      center (plusNeighbourCore e k) := by
  intro x hx
  apply C.ker_le
  rw [MonoidHom.mem_ker] at hx ⊢
  exact Subtype.val_injective hx

theorem PlusFieldCover.exists_theta (C : PlusFieldCover e ι k) (hF : 5 ≤ Nat.card F)
    {M U V : Subgroup G} (hME : M ≤ plusNeighbourCore e k) (hUM : U ≤ M) (hVM : V ≤ M)
    (hUp : ⁅U, U⁆ = U) (hVp : ⁅V, V⁆ = V) {a : ℕ} (ha : a + 3 ≤ m) (P : Finset (Fin m))
    (hM : ((M.subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype =
      (siegelBlockGL F (consecutiveBlock m a 3)).map (MulAut.conj (flipGL F P)).toMonoidHom)
    (hU : ((U.subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype =
      (siegelBlockGL F (consecutiveBlock m a 2)).map (MulAut.conj (flipGL F P)).toMonoidHom)
    (hV : ((V.subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype =
      (siegelBlockGL F (consecutiveBlock m (a + 1) 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  set E := plusNeighbourCore e k
  set π' : E →* GL (Fin m ⊕ Fin m) F := (StatedOmega (StatedQuadPlus m F)).subtype.comp C.π
  set ρ : M →* GL (Fin m ⊕ Fin m) F := π'.comp (Subgroup.inclusion hME)
  have hmap : ∀ A : Subgroup G, A ≤ M →
      (A.subgroupOf M).map ρ =
        ((A.subgroupOf E).map C.π).map (StatedOmega (StatedQuadPlus m F)).subtype := by
    intro A hAM
    rw [← map_inclusion_subgroupOf hAM hME, Subgroup.map_map, Subgroup.map_map]
  refine exists_theta_of_central hF hUM hVM hUp hVp (modelTheta_injective a ha P) ρ ?_ ?_ ?_ ?_
  · rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self, hmap M le_rfl, hM,
      range_modelTheta]
  · intro x hx
    have hx' : Subgroup.inclusion hME x ∈ center E := C.ker_comp_subtype_le hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    have h2 := congrArg Subtype.val (hx' (Subgroup.inclusion hME y))
    exact Subtype.ext h2
  · rw [hmap U hUM, hU, map_B12_modelTheta]
  · rw [hmap V hVM, hV, map_B23_modelTheta]

omit [Finite F] in
theorem PlusFieldCover.le_centralizer (C : PlusFieldCover e ι k) {A B : Subgroup G}
    (hA : A ≤ plusNeighbourCore e k) (hB : B ≤ plusNeighbourCore e k) (hBp : ⁅B, B⁆ = B)
    (h : ∀ x ∈ ((A.subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype,
      ∀ y ∈ ((B.subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype, Commute x y) :
    A ≤ centralizer (B : Set G) := by
  set E := plusNeighbourCore e k
  have hc := le_centralizer_of_map_commute C.ker_comp_subtype_le (A := A.subgroupOf E)
    (B := B.subgroupOf E) (commutator_subgroupOf_eq_of_le_perfect hB hBp)
    (fun a ha b hb => (h _ ⟨C.π a, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨C.π b, ⟨b, hb, rfl⟩, rfl⟩).eq)
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have h1 := mem_centralizer_iff.1 (hc (show (⟨a, hA ha⟩ : E) ∈ A.subgroupOf E from ha))
    ⟨b, hB hb⟩ hb
  exact congrArg Subtype.val h1

end Cover


end CFSG.SeitzReduction.OmegaPilot
