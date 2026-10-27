module

public import CFSG.ClassicalInvolution.Balance.QNineLift
public import CFSG.ClassicalInvolution.RouteD.TypeULift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

section Block

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]

theorem nonempty_equiv_of_block {S X₀ : Type} [Group S] [Group.IsPerfect S] [Group X₀] [Finite X₀]
    [Group.IsPerfect X₀] (hX₀ : NoCover.{0} Odd X₀) (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) (β : S →* X₀) (θbar : X₀ →* Y ⧸ O)
    (hker : θbar.ker ≤ Subgroup.center X₀) (hinj : Function.Injective (θbar.comp β))
    {K : Subgroup Y} (hK : K ≤ ⁅K, K⁆)
    (hKP : K.map (QuotientGroup.mk' O) = β.range.map θbar) : Nonempty (K ≃* S) := by
  obtain ⟨θ, hθ, -, hKθ⟩ := exists_lift_map_eq hX₀ hOc hOodd θbar hker
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range β)).ge hK hKP
  refine nonempty_equiv_of_map_eq β θ ?_ hKθ
  intro a b hab
  apply hinj
  have h1 : (θbar.comp β) a = (QuotientGroup.mk' O) ((θ.comp β) a) := by
    rw [← hθ]
    rfl
  have h2 : (θbar.comp β) b = (QuotientGroup.mk' O) ((θ.comp β) b) := by
    rw [← hθ]
    rfl
  rw [h1, h2, hab]

end Block

section Linear

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]

theorem nonempty_equiv_sl2_of_linearBlockStandardPair {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) {K : Subgroup Y} (hK : K ≤ ⁅K, K⁆) {W V : Subgroup (Y ⧸ O)}
    (h : LinearBlockStandardPair F W (K.map (QuotientGroup.mk' O)) V) :
    Nonempty (K ≃* SL(2, F)) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have : Group.IsPerfect SL(2, F) := sl2_isPerfect h4
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hX₀ : NoCover.{0} Odd SL(3, F) := noCover_odd_sl3 hF h5
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  have hker' := WeakCT.ker_comp_mulEquiv_le_center hker (MulAut.conj c⁻¹)
  rcases hcases with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine nonempty_equiv_of_block hX₀ hOc hOodd (blockSL F 3 2 0 (by omega))
      (θ.comp (MulAut.conj c⁻¹).toMonoidHom) hker'
      (comp_blockSL_injective hker' (by omega) (by omega)) hK ?_
    show K.map _ = (B12 F).map _
    rw [map_comp_mulEquiv, h1]
  · refine nonempty_equiv_of_block hX₀ hOc hOodd (blockSL F 3 2 1 (by omega))
      (θ.comp (MulAut.conj c⁻¹).toMonoidHom) hker'
      (comp_blockSL_injective hker' (by omega) (by omega)) hK ?_
    show K.map _ = (B23 F).map _
    rw [map_comp_mulEquiv, h2]

end Linear

section Unitary

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
open CFSG.LieType.Steinberg (embSUid)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] {K₀ : Type} [Field K₀]
  [Finite K₀] {p f : ℕ} [Fact p.Prime] [CharP K₀ p]

theorem nonempty_su_two_equiv_sl2 (hK : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Nonempty (Su K₀ p f 2 ≃* SL(2, GaloisField p f)) := by
  have hf := ne_zero_of_five_le_pow hq
  obtain ⟨e₃⟩ := nonempty_sl2_mulEquiv_su_two (K := K₀) (p := p) (f := f) hK
  have hcard : Nat.card (GaloisField p f) =
      Nat.card (CFSG.LieType.Steinberg.fixedSubfield K₀ p f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK, GaloisField.card p f hf]
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  let _ : Fintype (CFSG.LieType.Steinberg.fixedSubfield K₀ p f) := Fintype.ofFinite _
  have hcard' : Fintype.card (GaloisField p f) =
      Fintype.card (CFSG.LieType.Steinberg.fixedSubfield K₀ p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let r := FiniteField.ringEquivOfCardEq hcard'
  let e : SL(2, GaloisField p f) ≃* SL(2, CFSG.LieType.Steinberg.fixedSubfield K₀ p f) :=
    { toFun := Matrix.SpecialLinearGroup.map (r : GaloisField p f →+* _)
      invFun := Matrix.SpecialLinearGroup.map (r.symm : _ →+* GaloisField p f)
      left_inv A := by ext i j; simp
      right_inv A := by ext i j; simp
      map_mul' := map_mul _ }
  exact ⟨e₃.symm.trans e.symm⟩

theorem nonempty_equiv_sl2_of_unitaryBlockStandardPair (hp2 : p ≠ 2)
    (hK₀ : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) {K : Subgroup Y} (hK : K ≤ ⁅K, K⁆) {W V : Subgroup (Y ⧸ O)}
    (h : UnitaryBlockStandardPair K₀ p f W (K.map (QuotientGroup.mk' O)) V) :
    Nonempty (K ≃* SL(2, GaloisField p f)) := by
  have : Group.IsPerfect (Su K₀ p f 2) := isPerfect_su_two hK₀ hq
  have : Group.IsPerfect (Su K₀ p f 3) := isPerfect_su_gen hK₀ hq (by norm_num)
  have hX₀ : NoCover.{0} Odd (Su K₀ p f 3) := oddCoverSU3 hp2 hK₀ hq
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  have hker' := WeakCT.ker_comp_mulEquiv_le_center hker (MulAut.conj c⁻¹)
  obtain ⟨e⟩ := nonempty_su_two_equiv_sl2 hK₀ hq
  suffices Nonempty (K ≃* Su K₀ p f 2) from this.map fun e' => e'.trans e
  rcases hcases with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine nonempty_equiv_of_block hX₀ hOc hOodd (embSUid (unitaryInvolution K₀ p f) 2)
      (θ.comp (MulAut.conj c⁻¹).toMonoidHom) hker'
      (comp_embSUid_injective hK₀ hker' 2) hK ?_
    show K.map _ = (B12 K₀ p f).map _
    rw [WeakCT.map_comp_mulEquiv, h1]
  · refine nonempty_equiv_of_block hX₀ hOc hOodd (embSUid (unitaryInvolution K₀ p f) 0)
      (θ.comp (MulAut.conj c⁻¹).toMonoidHom) hker'
      (comp_embSUid_injective hK₀ hker' 0) hK ?_
    show K.map _ = (B23 K₀ p f).map _
    rw [WeakCT.map_comp_mulEquiv, h2]

end Unitary

section Symplectic

open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]

@[expose] def SymplecticLongBlockImage (F : Type) [Field F] {X : Type} [Group X]
    (U : Subgroup X) : Prop :=
  ∃ θ : CFSG.Assembly.LowTwoRank.StatedSp 2 F →* X,
    θ.ker ≤ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp 2 F) ∧
      (longBlock F 2 1).range.map θ = U

theorem symplecticLongBlockImage_of_standardPair {F : Type} [Field F] {X : Type} [Group X]
    {W U V : Subgroup X} (h : SymplecticBlockStandardPair F W U V) :
    SymplecticLongBlockImage F U := by
  obtain ⟨θ, c, -, hker, -, -, hU, -⟩ := h
  refine ⟨θ.comp (MulAut.conj c⁻¹).toMonoidHom, WeakCT.ker_comp_mulEquiv_le_center hker _, ?_⟩
  rw [WeakCT.map_comp_mulEquiv]
  exact hU

theorem comp_longBlock_injective {F : Type} [Field F] {X : Type} [Group X]
    {θ : CFSG.Assembly.LowTwoRank.StatedSp 2 F →* X}
    (hθ : θ.ker ≤ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :
    Function.Injective (θ.comp (longBlock F 2 1)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 := eq_one_of_mem_center_of_mem_suppGroup (hθ (MonoidHom.mem_ker.mpr hA))
    (isSupp_longBlock 1 A) (t := Sum.inl (0 : Fin 2)) (by
      rintro (h | h)
      · have := Sum.inl_injective h
        simp at this
      · exact Sum.inl_ne_inr h)
  exact longBlock_injective 1 (by rw [h1, map_one])

theorem nonempty_equiv_sl2_of_symplecticLongBlockImage {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f)
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) {K : Subgroup Y}
    (hK : K ≤ ⁅K, K⁆) (h : SymplecticLongBlockImage F (K.map (QuotientGroup.mk' O))) :
    Nonempty (K ≃* SL(2, F)) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have : Group.IsPerfect SL(2, F) := sl2_isPerfect h4
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := isPerfect_sp4 (by omega)
  have hX₀ : NoCover.{0} Odd (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := noCover_odd_sp4 hp2 hF h5
  obtain ⟨θ, hker, hU⟩ := h
  exact nonempty_equiv_of_block hX₀ hOc hOodd (longBlock F 2 1) θ hker
    (comp_longBlock_injective hker) hK hU.symm

theorem nonempty_equiv_sl2_of_symplecticBlockStandardPair {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f)
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) {K : Subgroup Y}
    (hK : K ≤ ⁅K, K⁆) {W V : Subgroup (Y ⧸ O)}
    (h : SymplecticBlockStandardPair F W (K.map (QuotientGroup.mk' O)) V) :
    Nonempty (K ≃* SL(2, F)) :=
  nonempty_equiv_sl2_of_symplecticLongBlockImage hp2 hF h5 hOc hOodd hK
    (symplecticLongBlockImage_of_standardPair h)

end Symplectic

section Transport

variable {K X : Type} [Group K] [Group X]

theorem ker_comp_le_center_of_perfect {S : Type} [Group S] [Group.IsPerfect S] (θ : S →* K)
    (ψ : K →* X) (hθ : θ.ker ≤ Subgroup.center S) (hψ : ψ.ker ≤ Subgroup.center K) :
    (ψ.comp θ).ker ≤ Subgroup.center S := by
  intro x hx
  have hx' : θ x ∈ Subgroup.center K := hψ hx
  refine mem_center_of_comm_mem_center fun s => hθ ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hx' (θ s)).symm

theorem linearBlockStandardPair_map_of_ker_le_center {F : Type} [Field F] {W U V : Subgroup K}
    (h : LinearBlockStandardPair F W U V) (ψ : K →* X) (hψ : ψ.ker ≤ Subgroup.center K) :
    LinearBlockStandardPair F (W.map ψ) (U.map ψ) (V.map ψ) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  refine ⟨ψ.comp θ, c, ?_, ker_comp_le_center_of_perfect θ ψ hker hψ, ?_⟩
  · rw [MonoidHom.range_comp, hW]
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem unitaryBlockStandardPair_map_of_ker_le_center {K₀ : Type} [Field K₀] [Finite K₀]
    {p f : ℕ} [Fact p.Prime] [CharP K₀ p] (hK₀ : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {W U V : Subgroup K} (h : Phan.UnitaryBlockStandardPair K₀ p f W U V) (ψ : K →* X)
    (hψ : ψ.ker ≤ Subgroup.center K) :
    Phan.UnitaryBlockStandardPair K₀ p f (W.map ψ) (U.map ψ) (V.map ψ) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  have : Group.IsPerfect (Phan.Su K₀ p f 3) := isPerfect_su_gen hK₀ hq (by norm_num)
  refine ⟨ψ.comp θ, c, ?_, ker_comp_le_center_of_perfect θ ψ hker hψ, ?_⟩
  · rw [MonoidHom.range_comp, hW]
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem symplecticLongBlockImage_map {F : Type} [Field F] (h5 : 5 ≤ Nat.card F) {U : Subgroup K}
    (h : SymplecticLongBlockImage F U) (ψ : K →* X) (hψ : ψ.ker ≤ Subgroup.center K) :
    SymplecticLongBlockImage F (U.map ψ) := by
  obtain ⟨θ, hker, hU⟩ := h
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := isPerfect_sp4 h5
  exact ⟨ψ.comp θ, ker_comp_le_center_of_perfect θ ψ hker hψ, by rw [← Subgroup.map_map, hU]⟩

end Transport

end CFSG.ClassicalInvolution.Balance
