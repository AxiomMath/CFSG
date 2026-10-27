module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open scoped Matrix

@[expose] def e6Pair (w : Fin Tag.E6.rank → ZMod 5) (γ : Fin Tag.E6.rank → ℤ) : ZMod 5 :=
  ∑ i, w i * (γ i : ZMod 5)

@[expose] def E6FourIsSol (v : Fin Tag.E6.rank → ZMod 5) : Prop :=
  ∀ j, ∑ i, (((wordMat Tag.E6 e6TwoWord) i j : ℤ) : ZMod 5) * v i = - v j

private lemma prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type*}
    (s : Finset ι) (y : G) (e : ι → ℤ) :
    (∏ i ∈ s, y ^ e i) = y ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

private lemma rootChar_zeta {L : Type} [Field L] (ζ : Lˣ) (n : Fin Tag.E6.rank → ℕ)
    (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (fun j => ζ ^ (n j)) γ = ζ ^ (∑ i, (n i : ℤ) * γ i) := by
  change (∏ i, (ζ ^ n i) ^ γ i) = ζ ^ (∑ i, (n i : ℤ) * γ i)
  calc (∏ i, (ζ ^ n i) ^ γ i)
      = ∏ i, ζ ^ ((n i : ℤ) * γ i) :=
        Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ← zpow_mul]
    _ = ζ ^ (∑ i, (n i : ℤ) * γ i) :=
        prod_zpow_eq_zpow_sum Finset.univ ζ (fun i => (n i : ℤ) * γ i)

private lemma zeta_zpow_eq_iff {L : Type} [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    (m m' : ℤ) : ζ ^ m = ζ ^ m' ↔ m ≡ m' [ZMOD 5] := by
  have hζ' : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.coe_units_iff.mp hζ
  rw [zpow_eq_zpow_iff_modEq, hζ'.eq_orderOf.symm]
  rfl

private lemma zeta_zpow_eq_iff_zmod {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (m m' : ℤ) :
    ζ ^ m = ζ ^ m' ↔ (m : ZMod 5) = (m' : ZMod 5) := by
  rw [zeta_zpow_eq_iff ζ hζ]
  exact (ZMod.intCast_eq_intCast_iff m m' 5).symm

private lemma cast_e6Pair (v : Fin Tag.E6.rank → ZMod 5) (γ : Fin Tag.E6.rank → ℤ) :
    (((∑ i, ((v i).val : ℤ) * γ i) : ℤ) : ZMod 5) = e6Pair v γ := by
  rw [e6Pair]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

private lemma mulVec_single_apply (k j : Fin Tag.E6.rank) :
    ((wordMat Tag.E6 e6TwoWord) *ᵥ Pi.single j (1 : ℤ)) k =
      (wordMat Tag.E6 e6TwoWord) k j := by
  simp [Matrix.mulVec]

theorem e6Four_rootChar_eq_one_iff {L : Type} [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    (v : Fin Tag.E6.rank → ZMod 5) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (fun j => ζ ^ (v j).val) γ = 1 ↔ e6Pair v γ = 0 := by
  have h1 : rootChar (fun j => ζ ^ (v j).val) γ
      = ζ ^ (∑ i, ((v i).val : ℤ) * γ i) :=
    rootChar_zeta ζ (fun j => (v j).val) γ
  rw [h1, ← zpow_zero ζ, zeta_zpow_eq_iff_zmod ζ hζ, cast_e6Pair, Int.cast_zero]


theorem e6Four_torus_mem {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    {x : ModGL Tag.E6 L} (hx : x ∈ S.D.torus) :
    ∃ a : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit Tag.E6 a := by
  rw [LangDatum.torus, mem_twistedTorusOf] at hx
  exact exists_rootDiagUnit_eq_of_mem_torusGroup hx.1

theorem e6Four_torus_exp {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) :
    ∀ j, a j ^ 15 = 1 := by
  intro j
  set γ : Fin Tag.E6.rank → ℤ := Pi.single j 1 with hγdef
  have hγ : IsRoot Tag.E6 γ := by rw [hγdef]; exact IsRoot.basis j
  have hγ' : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hρfix : S.ρ (S.ρ γ) = γ := by
    rw [hρ (S.ρ γ) hγ', hρ γ hγ, Matrix.mulVec_mulVec, ← pow_two, e6Two_pow,
      Matrix.one_mulVec]
  have h2 : rootChar a (S.ρ (S.ρ γ)) = rootChar a (S.ρ γ) ^ S.D.q :=
    S.frob.rootChar_eq a hT (S.ρ γ) hγ'
  have h1 : rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q :=
    S.frob.rootChar_eq a hT γ hγ
  have hchain : rootChar a γ = rootChar a γ ^ 16 := by
    calc rootChar a γ = rootChar a (S.ρ (S.ρ γ)) := by rw [hρfix]
      _ = rootChar a (S.ρ γ) ^ S.D.q := h2
      _ = (rootChar a γ ^ S.D.q) ^ S.D.q := by rw [h1]
      _ = rootChar a γ ^ (S.D.q * S.D.q) := by rw [← pow_mul]
      _ = rootChar a γ ^ 16 := by rw [hq]
  have hx : a j = a j ^ 16 := by
    rw [hγdef] at hchain
    have hγchar : rootChar a (Pi.single j (1 : ℤ)) = a j := by
      simpa using rootChar_nsmul_single a j 1
    rwa [hγchar] at hchain
  apply mul_right_cancel (b := a j)
  rw [← pow_succ, one_mul, ← hx]

theorem e6Four_torsion_sol {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (h5 : ∀ j, a j ^ 5 = 1) :
    ∃ v : Fin Tag.E6.rank → ZMod 5, E6FourIsSol v ∧ ∀ j, a j = ζ ^ (v j).val := by
  classical
  have hex : ∀ j, ∃ i : ℕ, i < 5 ∧ a j = ζ ^ i := by
    intro j
    have hLj : (a j : L) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h5 j, Units.val_one]
    obtain ⟨i, hi, hzi⟩ := hζ.eq_pow_of_pow_eq_one hLj
    exact ⟨i, hi, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hzi.symm)⟩
  let i : Fin Tag.E6.rank → ℕ := fun j => Classical.choose (hex j)
  have hi : ∀ j, i j < 5 := fun j => (Classical.choose_spec (hex j)).1
  have hzi : ∀ j, a j = ζ ^ (i j) := fun j => (Classical.choose_spec (hex j)).2
  have ha : a = fun j => ζ ^ (i j) := funext hzi
  refine ⟨fun j => (i j : ZMod 5), ?_, ?_⟩
  · intro j
    have hroot := S.frob.rootChar_eq a hT (Pi.single j (1 : ℤ)) (IsRoot.basis j)
    rw [hρ (Pi.single j (1 : ℤ)) (IsRoot.basis j), hq] at hroot
    have hL : rootChar a ((wordMat Tag.E6 e6TwoWord) *ᵥ Pi.single j (1 : ℤ))
        = ζ ^ (∑ k, (i k : ℤ) * (wordMat Tag.E6 e6TwoWord) k j) := by
      rw [ha, rootChar_zeta]
      exact congrArg (fun e : ℤ => ζ ^ e)
        (Finset.sum_congr rfl fun k _ => by rw [mulVec_single_apply])
    have hR : rootChar a (Pi.single j (1 : ℤ)) ^ 4
        = ζ ^ ((i j : ℤ) * 4) := by
      have h1 : rootChar a (Pi.single j (1 : ℤ)) = a j := by
        simpa using rootChar_nsmul_single a j 1
      rw [h1, hzi j, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
      rfl
    have hzeq : ζ ^ (∑ k, (i k : ℤ) * (wordMat Tag.E6 e6TwoWord) k j)
        = ζ ^ ((i j : ℤ) * 4) := by
      rw [← hL, ← hR]
      exact hroot
    have hcast : (((∑ k, (i k : ℤ) * (wordMat Tag.E6 e6TwoWord) k j) : ℤ) : ZMod 5)
        = ((((i j : ℤ) * 4) : ℤ) : ZMod 5) :=
      (zeta_zpow_eq_iff_zmod ζ hζ _ _).mp hzeq
    have hsum : (((∑ k, (i k : ℤ) * (wordMat Tag.E6 e6TwoWord) k j) : ℤ) : ZMod 5)
        = ∑ k, (i k : ZMod 5) * ((wordMat Tag.E6 e6TwoWord) k j : ZMod 5) := by
      push_cast
      rfl
    have hrhs : ((((i j : ℤ) * 4) : ℤ) : ZMod 5) = (i j : ZMod 5) * 4 := by
      push_cast
      rfl
    calc ∑ k, ((wordMat Tag.E6 e6TwoWord) k j : ZMod 5) * (i k : ZMod 5)
        = ∑ k, (i k : ZMod 5) * ((wordMat Tag.E6 e6TwoWord) k j : ZMod 5) :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = (i j : ZMod 5) * 4 := by rw [← hsum, ← hrhs]; exact hcast
      _ = (i j : ZMod 5) * (-1) := by rw [show (4 : ZMod 5) = -1 by decide]
      _ = - (i j : ZMod 5) := by rw [mul_neg, mul_one]
  · intro j
    rw [hzi j, ZMod.val_natCast_of_lt (hi j)]

end CFSG.Assembly

end
