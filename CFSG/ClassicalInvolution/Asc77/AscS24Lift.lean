module

public import CFSG.ClassicalInvolution.RouteD.TypeULift
public import CFSG.ClassicalInvolution.Asc77.AscIH8Red
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {c : G} {K J : Subgroup G}

@[expose] noncomputable def supQuot (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G)) :
    ↥(K ⊔ J) →* OddQuot c :=
  (oddQuotMk c).comp (Subgroup.inclusion hXc)

omit [Finite G] in
theorem supQuot_ker_le_center (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G))
    (hcent : K ⊔ J ≤ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({c} : Set G)) : Subgroup G) : Set G)) :
    (supQuot hXc).ker ≤ Subgroup.center ↥(K ⊔ J) := by
  intro x hx
  have h1 : oddQuotMk c (Subgroup.inclusion hXc x) = 1 := hx
  have h3 : (x : G) ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
    ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hcent y.2) _ h3).symm

theorem odd_card_supQuot_ker (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G)) :
    Odd (Nat.card (supQuot hXc).ker) := by
  refine (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn
    (Subgroup.centralizer ({c} : Set G))).of_dvd_nat ?_
  have hmem : ∀ x : (supQuot hXc).ker,
      ((x : ↥(K ⊔ J)) : G) ∈ oddCoreIn (Subgroup.centralizer ({c} : Set G)) := fun x =>
    ⟨_, oddQuotMk_eq_one_iff.mp (MonoidHom.mem_ker.mp x.2), rfl⟩
  let g : (supQuot hXc).ker →* oddCoreIn (Subgroup.centralizer ({c} : Set G)) :=
    { toFun := fun x => ⟨((x : ↥(K ⊔ J)) : G), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Subgroup.card_dvd_of_injective g fun x₁ x₂ h =>
    Subtype.ext (Subtype.ext (congrArg (fun y : oddCoreIn _ => (y : G)) h))

omit [Finite G] in
theorem map_supQuot (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G)) {M : Subgroup G}
    (hM : M ≤ K ⊔ J) : (M.subgroupOf (K ⊔ J)).map (supQuot hXc) = modOdd c M := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Subgroup.inclusion hXc x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx),
      rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨x, hM hxM⟩, Subgroup.mem_subgroupOf.mpr hxM, ?_⟩
    rfl

theorem linear_lift_of_centralizes {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (hF : RouteD.OddCoverSL3 F) (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G))
    (hKp : K ≤ ⁅K, K⁆) (hJp : J ≤ ⁅J, J⁆)
    (hcent : K ⊔ J ≤ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({c} : Set G)) : Subgroup G) : Set G))
    {W : Subgroup (OddQuot c)} (h : LinearBlockStandardPair F W (modOdd c K) (modOdd c J)) :
    LinearBlockStandardPair F (K ⊔ J) K J := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  set φ := supQuot hXc with hφ
  have hker := supQuot_ker_le_center hXc hcent
  have hodd := odd_card_supQuot_ker hXc
  have hmapK := map_supQuot hXc (M := K) le_sup_left
  have hmapJ := map_supQuot hXc (M := J) le_sup_right
  have hW : W ≤ modOdd c K ⊔ modOdd c J := RouteD.linearBlockStandardPair_le_sup' h
  obtain ⟨θb, c', hrange, hkerb, hcases⟩ := h
  have hθ : θb.range ≤ φ.range := by
    rw [hrange]
    refine hW.trans (sup_le ?_ ?_)
    · rw [← hmapK]; exact Subgroup.map_le_range _ _
    · rw [← hmapJ]; exact Subgroup.map_le_range _ _
  obtain ⟨θ', hθ'⟩ := RouteD.exists_lift_of_oddCoverSL3 hF φ hker hodd θb hθ
  let θ : SL(3, F) →* G := (K ⊔ J).subtype.comp θ'
  have hperfθ : ∀ Y : Subgroup SL(3, F), Y ≤ ⁅Y, Y⁆ → Y.map θ' ≤ ⁅Y.map θ', Y.map θ'⁆ := by
    intro Y hY
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hY
  have hB12 : ((WeakCT.B12 F).map (MulAut.conj c'⁻¹).toMonoidHom) ≤
      ⁅(WeakCT.B12 F).map (MulAut.conj c'⁻¹).toMonoidHom,
        (WeakCT.B12 F).map (MulAut.conj c'⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator, RouteD.commutator_B12_eq h4]
  have hB23 : ((WeakCT.B23 F).map (MulAut.conj c'⁻¹).toMonoidHom) ≤
      ⁅(WeakCT.B23 F).map (MulAut.conj c'⁻¹).toMonoidHom,
        (WeakCT.B23 F).map (MulAut.conj c'⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator, RouteD.commutator_B23_eq h4]
  have key : ∀ (Y : Subgroup SL(3, F)) (M : Subgroup G), M ≤ K ⊔ J → M ≤ ⁅M, M⁆ →
      Y ≤ ⁅Y, Y⁆ → Y.map θb = modOdd c M → Y.map θ = M := by
    intro Y M hMX hMp hYp hY
    have hMX' := map_supQuot hXc hMX
    have h1 : (Y.map θ').map φ = (M.subgroupOf (K ⊔ J)).map φ := by
      rw [Subgroup.map_map, hθ', hY, hMX']
    have h2 : Y.map θ' = M.subgroupOf (K ⊔ J) :=
      ih8_eq_of_map_eq φ hker (hperfθ Y hYp) (RouteD.typeU_perfect_subgroupOf hMX hMp) h1
    show Y.map ((K ⊔ J).subtype.comp θ') = M
    rw [← Subgroup.map_map, h2, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMX]
  have hKθ : K ≤ θ.range ∧ J ≤ θ.range := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← key _ K le_sup_left hKp hB12 h1, ← key _ J le_sup_right hJp hB23 h2]
      exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩
    · rw [← key _ K le_sup_left hKp hB23 h2, ← key _ J le_sup_right hJp hB12 h1]
      exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩
  have hrangeθ : θ.range = K ⊔ J := by
    refine le_antisymm ?_ (sup_le hKθ.1 hKθ.2)
    rintro _ ⟨x, rfl⟩
    exact (θ' x).2
  refine ⟨θ, c', hrangeθ, ?_, ?_⟩
  · intro x hx
    apply hkerb
    have h1 : θ' x = 1 := Subtype.ext hx
    rw [MonoidHom.mem_ker, ← hθ', MonoidHom.comp_apply, h1, map_one]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨key _ K le_sup_left hKp hB12 h1, key _ J le_sup_right hJp hB23 h2⟩
    · exact Or.inr ⟨key _ J le_sup_right hJp hB12 h1, key _ K le_sup_left hKp hB23 h2⟩

theorem unitary_lift_of_centralizes {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ} [Fact p.Prime]
    [CharP K₀ p] (hK₀ : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hF : RouteD.OddCoverSU3 K₀ p f) (hXc : K ⊔ J ≤ Subgroup.centralizer ({c} : Set G))
    (hKp : K ≤ ⁅K, K⁆) (hJp : J ≤ ⁅J, J⁆)
    (hcent : K ⊔ J ≤ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({c} : Set G)) : Subgroup G) : Set G))
    {W : Subgroup (OddQuot c)} (h : UnitaryBlockStandardPair K₀ p f W (modOdd c K) (modOdd c J)) :
    UnitaryBlockStandardPair K₀ p f (K ⊔ J) K J := by
  have : Group.IsPerfect (Su K₀ p f 3) := RouteD.isPerfect_su_gen hK₀ hq (by omega)
  have hq2 : p ^ f ≠ 2 := by omega
  set φ := supQuot hXc with hφ
  have hker := supQuot_ker_le_center hXc hcent
  have hodd := odd_card_supQuot_ker hXc
  have hmapK := map_supQuot hXc (M := K) le_sup_left
  have hmapJ := map_supQuot hXc (M := J) le_sup_right
  have hW : W ≤ modOdd c K ⊔ modOdd c J := (RouteD.typeU_standardPair_eq_sup hK₀ hq2 h).le
  obtain ⟨θb, c', hrange, hkerb, hcases⟩ := h
  have hθ : θb.range ≤ φ.range := by
    rw [hrange]
    refine hW.trans (sup_le ?_ ?_)
    · rw [← hmapK]; exact Subgroup.map_le_range _ _
    · rw [← hmapJ]; exact Subgroup.map_le_range _ _
  obtain ⟨θ', hθ'⟩ := RouteD.exists_lift_of_oddCoverSU3 hF φ hker hodd θb hθ
  let θ : Su K₀ p f 3 →* G := (K ⊔ J).subtype.comp θ'
  have hperfθ : ∀ Y : Subgroup (Su K₀ p f 3), Y ≤ ⁅Y, Y⁆ → Y.map θ' ≤ ⁅Y.map θ', Y.map θ'⁆ := by
    intro Y hY
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hY
  have hB12 : ((Phan.B12 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom) ≤
      ⁅(Phan.B12 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom,
        (Phan.B12 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (RouteD.B12_perfect_su hK₀ hq)
  have hB23 : ((Phan.B23 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom) ≤
      ⁅(Phan.B23 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom,
        (Phan.B23 K₀ p f).map (MulAut.conj c'⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (RouteD.B23_perfect_su hK₀ hq)
  have key : ∀ (Y : Subgroup (Su K₀ p f 3)) (M : Subgroup G), M ≤ K ⊔ J → M ≤ ⁅M, M⁆ →
      Y ≤ ⁅Y, Y⁆ → Y.map θb = modOdd c M → Y.map θ = M := by
    intro Y M hMX hMp hYp hY
    have hMX' := map_supQuot hXc hMX
    have h1 : (Y.map θ').map φ = (M.subgroupOf (K ⊔ J)).map φ := by
      rw [Subgroup.map_map, hθ', hY, hMX']
    have h2 : Y.map θ' = M.subgroupOf (K ⊔ J) :=
      ih8_eq_of_map_eq φ hker (hperfθ Y hYp) (RouteD.typeU_perfect_subgroupOf hMX hMp) h1
    show Y.map ((K ⊔ J).subtype.comp θ') = M
    rw [← Subgroup.map_map, h2, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMX]
  have hKθ : K ≤ θ.range ∧ J ≤ θ.range := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← key _ K le_sup_left hKp hB12 h1, ← key _ J le_sup_right hJp hB23 h2]
      exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩
    · rw [← key _ K le_sup_left hKp hB23 h2, ← key _ J le_sup_right hJp hB12 h1]
      exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩
  have hrangeθ : θ.range = K ⊔ J := by
    refine le_antisymm ?_ (sup_le hKθ.1 hKθ.2)
    rintro _ ⟨x, rfl⟩
    exact (θ' x).2
  refine ⟨θ, c', hrangeθ, ?_, ?_⟩
  · intro x hx
    apply hkerb
    have h1 : θ' x = 1 := Subtype.ext hx
    rw [MonoidHom.mem_ker, ← hθ', MonoidHom.comp_apply, h1, map_one]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨key _ K le_sup_left hKp hB12 h1, key _ J le_sup_right hJp hB23 h2⟩
    · exact Or.inr ⟨key _ J le_sup_right hJp hB12 h1, key _ K le_sup_left hKp hB23 h2⟩

end Lift

end CFSG.ClassicalInvolution.Asc77.S24
