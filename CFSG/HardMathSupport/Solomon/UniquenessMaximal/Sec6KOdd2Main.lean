module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Abs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Borel
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2

open Matrix

theorem index_borel_mod_four {L : Type} [Field L] [Finite L] (h : Nat.card L % 4 = 1) :
    (borel L).index % 4 = 2 := by
  rw [index_borel]
  generalize Nat.card L = q at *
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  ring_nf
  omega

theorem exists_index_two_injective_diag {L : Type} [Field L] [Finite L]
    (hL : Nat.card L % 4 = 1) {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (τ : T →* Matrix.GeneralLinearGroup (Fin 3) L) (hτ : Function.Injective τ)
    (hdet : ∀ t, ((τ t : Matrix.GeneralLinearGroup (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L).det = 1) :
    ∃ (A : Subgroup T) (δ : A →* L × L), A.index ≤ 2 ∧ Function.Injective δ := by
  classical
  let _ : MulAction T (Matrix.GeneralLinearGroup (Fin 3) L ⧸ borel L) := MulAction.compHom _ τ
  have hX : Nat.card (Matrix.GeneralLinearGroup (Fin 3) L ⧸ borel L) % 4 = 2 :=
    index_borel_mod_four hL
  obtain ⟨x, hx⟩ := exists_index_stabilizer_le_two hT hX
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hmem : ∀ a : T, a ∈ MulAction.stabilizer T (y : Matrix.GeneralLinearGroup (Fin 3) L ⧸
      borel L) ↔ y⁻¹ * τ a * y ∈ borel L := by
    intro a
    rw [MulAction.mem_stabilizer_iff]
    show ((τ a * y : Matrix.GeneralLinearGroup (Fin 3) L) :
      Matrix.GeneralLinearGroup (Fin 3) L ⧸ borel L) = _ ↔ _
    rw [QuotientGroup.eq, ← inv_mem_iff (x := y⁻¹ * τ a * y)]
    have : (τ a * y)⁻¹ * y = (y⁻¹ * τ a * y)⁻¹ := by group
    rw [this]
  let A := MulAction.stabilizer T (y : Matrix.GeneralLinearGroup (Fin 3) L ⧸ borel L)
  let φ : A →* borel L :=
    { toFun := fun a => ⟨y⁻¹ * τ a * y, (hmem a).1 a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show y⁻¹ * τ (a * b : T) * y = (y⁻¹ * τ a * y) * (y⁻¹ * τ b * y)
        simp only [map_mul]
        group }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : y⁻¹ * τ a * y = y⁻¹ * τ b * y := congrArg Subtype.val hab
    have h2 : τ (a : T) = τ (b : T) := by simpa using h1
    exact Subtype.ext (hτ h2)
  let δ : A →* L × L :=
    ((MonoidHom.fst L (L × L)).prod ((MonoidHom.fst L L).comp (MonoidHom.snd L (L × L)))).comp
      (diagB.comp φ)
  refine ⟨A, δ, hx, ?_⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have hg : IsUT ((φ a : Matrix.GeneralLinearGroup (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) := (φ a).2
  have h00 : ((φ a : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0 = 1 :=
    congrArg Prod.fst ha
  have h11 : ((φ a : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 1 = 1 :=
    congrArg Prod.snd ha
  have hdet' : ((φ a : Matrix.GeneralLinearGroup (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L).det = 1 := by
    show (((y⁻¹ * τ a * y : Matrix.GeneralLinearGroup (Fin 3) L)) :
      Matrix (Fin 3) (Fin 3) L).det = 1
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [Matrix.det_units_conj']
    exact hdet a
  have h22 : ((φ a : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 2 = 1 := by
    rw [IsUT.det_eq hg, h00, h11] at hdet'
    simpa using hdet'
  have hker : φ a ∈ (diagB (L := L)).ker := by
    rw [MonoidHom.mem_ker]
    exact Prod.ext h00 (Prod.ext h11 h22)
  have hdvd : orderOf (φ a) ∣ Nat.card L ^ 3 := by
    rw [← card_ker_diagB (L := L)]
    have := orderOf_dvd_natCard (⟨φ a, hker⟩ : (diagB (L := L)).ker)
    rwa [← Subgroup.orderOf_coe] at this
  rw [orderOf_injective φ hφ a, ← Subgroup.orderOf_coe] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT (a : T)
  rw [hk] at hdvd
  have hodd : ¬ 2 ∣ Nat.card L ^ 3 := by
    intro h
    have := Nat.prime_two.dvd_of_dvd_pow h
    omega
  have hk0 : k = 0 := by
    by_contra hne
    exact hodd (dvd_trans (dvd_pow_self 2 hne) hdvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact Subtype.ext hk

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
