module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodClass

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

set_option linter.unusedSectionVars false

theorem toMat_e8Eight_eq_tab (j i : Fin 8) :
    ((toMat Tag.E8.rank e8EightMat : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) j i) =
      e8MTab17 j i := by
  fin_cases j <;> fin_cases i <;> rfl

theorem mulVec_single_apply (i k : Fin Tag.E8.rank) :
    ((toMat Tag.E8.rank e8EightMat : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) *ᵥ
      (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) k =
      (toMat Tag.E8.rank e8EightMat : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) k i := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem pairZ17_mulVec_single (y : Fin 8 → ZMod 17) (i : Fin Tag.E8.rank) :
    pairZ17 y ((toMat Tag.E8.rank e8EightMat : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) *ᵥ
      (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = ∑ k, y k * ((e8MTab17 k i : ℤ) : ZMod 17) := by
  unfold pairZ17
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun t : ℤ => y k * ((t : ℤ) : ZMod 17))
    ((mulVec_single_apply i k).trans (toMat_e8Eight_eq_tab k i))

theorem exists_zeta17 {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ζ : Lˣ, orderOf ζ = 17 := by
  have : NeZero ((17 : ℕ) : L) := NeZero.of_not_dvd L (p := 2) (by norm_num)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 17
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hζu : IsPrimitiveRoot hu.unit 17 := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact ⟨hu.unit, hζu.eq_orderOf.symm⟩

section Setup


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem exists_param_of_mem_E (S : LangSetup .E8 L p) (hρ : RhoIs S e8EightMat)
    (hq : S.D.q = 2) (hp : p = 17) {ζ : Lˣ} (hζ : orderOf ζ = 17) {x : ModGL .E8 L}
    (hx : x ∈ S.E) : ∃ c : Fin 2 → ZMod 17, x = rootDiagUnit Tag.E8 (famPar17 ζ c) := by
  have h17 : ζ ^ 17 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hxT : x ∈ S.D.torus := (S.E_le hx).1
  have hxTor : x ∈ torusGroup Tag.E8 L := (mem_twistedTorusOf.1 hxT).1
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom hxTor
  have hxa : x = rootDiagUnit Tag.E8 a := ha.symm
  have hapow : ∀ i, a i ^ 17 = 1 := by
    have hx17 : x ^ 17 = 1 := by
      have := S.E_exp x hx
      rwa [hp] at this
    have h1 : rootDiagUnit Tag.E8 (a ^ 17) = rootDiagUnit Tag.E8 a ^ 17 :=
      map_pow (rootDiagUnitHom Tag.E8 L) a 17
    have h2 : rootDiagUnit Tag.E8 (a ^ 17) = rootDiagUnit Tag.E8 1 := by
      rw [h1, ← hxa, hx17, rootDiagUnit_one]
    have h3 : a ^ 17 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h2
    intro i
    exact congrFun h3 i
  obtain ⟨y, hy⟩ := exists_eq_torV17 hζ a hapow
  have hxd : rootDiagUnit Tag.E8 a ∈ S.D.torus := by rw [← hxa]; exact hxT
  have heig : ∀ j : Fin Tag.E8.rank, ∑ k, y k * ((e8MTab17 k j : ℤ) : ZMod 17) = 2 * y j := by
    intro j
    have hroot := S.frob.rootChar_eq a hxd (Pi.single j 1) (isRoot_single Tag.E8 j)
    rw [hρ _ (isRoot_single Tag.E8 j), hq, hy, rootChar_torV17 h17, rootChar_torV17 h17,
      pow_two, ← chi17_add h17] at hroot
    have h1 := chi17_injective hζ hroot
    have h3 : pairZ17 y (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = y j := pairZ17_single y j
    have h2 : pairZ17 y ((toMat Tag.E8.rank e8EightMat :
        Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) *ᵥ (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) =
        ∑ k, y k * ((e8MTab17 k j : ℤ) : ZMod 17) := pairZ17_mulVec_single y j
    calc ∑ k, y k * ((e8MTab17 k j : ℤ) : ZMod 17)
        = pairZ17 y (Pi.single j 1 : Fin Tag.E8.rank → ℤ) +
          pairZ17 y (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := h2.symm.trans h1
      _ = 2 * y j := by rw [h3]; exact (two_mul (y j)).symm
  refine ⟨![y 6, y 7], ?_⟩
  rw [hxa, hy]
  have hyx : y = xc17 ![y 6, y 7] := eig_eq_xc17_aux heig
  rw [famPar17, ← hyx]

theorem famPar17_add {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (c d : Fin 2 → ZMod 17) :
    famPar17 ζ (c + d) = famPar17 ζ c * famPar17 ζ d := by
  rw [famPar17, famPar17, famPar17, xc17_add]
  exact torV17_add h17 _ _

theorem famPar17_zero (ζ : Lˣ) : famPar17 ζ (0 : Fin 2 → ZMod 17) = 1 := by
  rw [famPar17, xc17_zero]
  exact torV17_zero ζ

theorem famPar17_injective {ζ : Lˣ} (hζ : orderOf ζ = 17) : Function.Injective (famPar17 ζ) := by
  intro c d h
  apply xc17_injective
  funext i
  exact chi17_injective hζ (congrFun h i)

@[expose] noncomputable def phi17 (ζ : Lˣ) (h17 : ζ ^ 17 = 1) :
    Multiplicative (Fin 2 → ZMod 17) →* ModGL .E8 L where
  toFun c := rootDiagUnit Tag.E8 (famPar17 ζ (Multiplicative.toAdd c))
  map_one' := by
    show rootDiagUnit Tag.E8 (famPar17 ζ 0) = 1
    rw [famPar17_zero]
    exact rootDiagUnit_one
  map_mul' a b := by
    show rootDiagUnit Tag.E8 (famPar17 ζ (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [famPar17_add h17]
    exact rootDiagUnit_mul _ _

theorem phi17_injective {ζ : Lˣ} (hζ : orderOf ζ = 17) (h17 : ζ ^ 17 = 1) :
    Function.Injective (phi17 (L := L) ζ h17) := by
  intro a b h
  have h1 : rootDiagUnit Tag.E8 (famPar17 ζ (Multiplicative.toAdd a)) =
      rootDiagUnit Tag.E8 (famPar17 ζ (Multiplicative.toAdd b)) := h
  exact Multiplicative.toAdd.injective (famPar17_injective hζ (CFSG.LieType.Chevalley.rootDiagUnit_injective h1))

theorem card_range_phi17 {ζ : Lˣ} (hζ : orderOf ζ = 17) (h17 : ζ ^ 17 = 1) :
    Nat.card (phi17 (L := L) ζ h17).range = 17 ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (phi17_injective hζ h17)).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  simp

theorem mem_plane_of_card (S : LangSetup .E8 L p) (hρ : RhoIs S e8EightMat)
    (hq : S.D.q = 2) (hp : p = 17) {ζ : Lˣ} (hζ : orderOf ζ = 17)
    {D₁ : Subgroup (ModGL .E8 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2)
    (c : Fin 2 → ZMod 17) : rootDiagUnit Tag.E8 (famPar17 ζ c) ∈ D₁ := by
  have h17 : ζ ^ 17 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hle : D₁ ≤ (phi17 (L := L) ζ h17).range := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_param_of_mem_E S hρ hq hp hζ (hD₁E hx)
    exact ⟨Multiplicative.ofAdd c, by rw [hc]; rfl⟩
  have : Finite (phi17 (L := L) ζ h17).range :=
    Finite.of_surjective (phi17 (L := L) ζ h17).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hcard : Nat.card (phi17 (L := L) ζ h17).range ≤ Nat.card D₁ := by
    rw [card_range_phi17 hζ h17, hD₁c, hp]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem mem_torusGroup_of_commute_plane (S : LangSetup .E8 L p) (hρ : RhoIs S e8EightMat)
    (hq : S.D.q = 2) (hp : p = 17) {ζ : Lˣ} (hζ : orderOf ζ = 17)
    {D₁ : Subgroup (ModGL .E8 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2)
    {z : ModGL .E8 L} (hz : z ∈ adjointGroup Tag.E8 L) (hcomm : ∀ x ∈ D₁, Commute z x) :
    z ∈ torusGroup Tag.E8 L := by
  obtain ⟨hK, hS⟩ := fam17_data fam17_ok
  exact mem_torusGroup_of_commute17 hζ hK hS hz fun c =>
    hcomm _ (mem_plane_of_card S hρ hq hp hζ hD₁E hD₁c c)

end Setup

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
