module

public import CFSG.RankThree.PartOne.KE.CTTorus

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

variable {L : Type} [Field L]

@[expose] def tupE (ζ : Lˣ) (e : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → Lˣ := fun i => ζ ^ e i

@[expose] def dotE (e v : Fin Tag.E8.rank → ℤ) : ℤ := ∑ i, e i * v i

theorem prod_zpow_sum_E {G : Type*} [CommGroup G] (ξ : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_tupE (ζ : Lˣ) (e v : Fin Tag.E8.rank → ℤ) :
    rootChar (τ := Tag.E8) (tupE ζ e) v = ζ ^ dotE e v := by
  simp only [rootChar, tupE, dotE, ← zpow_mul]
  exact prod_zpow_sum_E ζ _ _

theorem rootChar_tupE_eq_one_iff {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) (e v : Fin Tag.E8.rank → ℤ) :
    rootChar (τ := Tag.E8) (tupE ζ e) v = 1 ↔ (5 : ℤ) ∣ dotE e v := by
  rw [rootChar_tupE, hζ.zpow_eq_one_iff_dvd]
  rfl

theorem tupE_pow_five {ζ : Lˣ} (hζ : ζ ^ 5 = 1) (e : Fin Tag.E8.rank → ℤ) (i : Fin Tag.E8.rank) :
    tupE ζ e i ^ 5 = 1 := by
  simp only [tupE]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hζ]

theorem exists_tupE {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Lˣ)
    (ha : ∀ i, a i ^ 5 = 1) : ∃ e : Fin Tag.E8.rank → ℤ, a = tupE ζ e := by
  have hζ' : IsPrimitiveRoot (ζ : L) 5 := IsPrimitiveRoot.coe_units_iff.2 hζ
  have ha' : ∀ i, ((a i : Lˣ) : L) ^ 5 = 1 := fun i => by
    have := congrArg (fun x : Lˣ => (x : L)) (ha i)
    simpa using this
  choose k hk using fun i => hζ'.eq_pow_of_pow_eq_one (ha' i)
  refine ⟨fun i => (k i : ℤ), funext fun i => ?_⟩
  simp only [tupE, zpow_natCast]
  exact Units.ext (by simpa using (hk i).2.symm)

theorem dotE_mulVec (e : Fin Tag.E8.rank → ℤ) (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) (v : Fin Tag.E8.rank → ℤ) :
    dotE e (M *ᵥ v) = ∑ j, (∑ i, e i * M i j) * v j := by
  simp only [dotE, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem dvd_forall_iff {c : Fin Tag.E8.rank → ℤ} :
    (∀ v : Fin Tag.E8.rank → ℤ, (5 : ℤ) ∣ ∑ j, c j * v j) ↔ ∀ j, (5 : ℤ) ∣ c j := by
  constructor
  · intro h j
    simpa [Pi.single_apply] using h (Pi.single j 1)
  · intro h v
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (h j) _

theorem mem_twistedFixedTuples_tupE {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) (e : Fin Tag.E8.rank → ℤ)
    {w : WeylGroup Tag.E8} {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hw : ∀ u, w • u = M *ᵥ u) {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) :
    tupE ζ e ∈ twistedFixedTuples w Fr ↔
      ∀ j, (5 : ℤ) ∣ (∑ i, e i * M i j) - q * e j := by
  rw [twistedFixedTuples_eq_fixedCharTuples hw, mem_fixedCharTuples_iff]
  have key : ∀ u : Fin Tag.E8.rank → ℤ, rootChar (τ := Tag.E8) (tupE ζ e) (M *ᵥ u) =
      Units.map Fr.toMonoidHom (rootChar (tupE ζ e) u) ↔
      (5 : ℤ) ∣ ∑ j, ((∑ i, e i * M i j) - q * e j) * u j := by
    intro u
    rw [rootChar_tupE, rootChar_tupE, CTTorus.map_units_eq_pow hFr, ← zpow_natCast,
      ← zpow_mul, ← mul_inv_eq_one, ← zpow_sub, hζ.zpow_eq_one_iff_dvd, dotE_mulVec]
    have : (∑ j, (∑ i, e i * M i j) * u j) - dotE e u * (q : ℤ) =
        ∑ j, ((∑ i, e i * M i j) - q * e j) * u j := by
      rw [dotE, Finset.sum_mul (s := Finset.univ) (f := fun j => e j * u j), 
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    rfl
  simp only [key]
  exact dvd_forall_iff

theorem mem_rootCharStabilizer_tupE {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) (e : Fin Tag.E8.rank → ℤ)
    {z : WeylGroup Tag.E8} {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hz : ∀ u, z • u = M *ᵥ u) :
    z ∈ rootCharStabilizer (tupE ζ e) ↔ ∀ j, (5 : ℤ) ∣ (∑ i, e i * M i j) - e j := by
  have key : ∀ u : Fin Tag.E8.rank → ℤ, rootChar (τ := Tag.E8) (tupE ζ e) (z • u) =
      rootChar (tupE ζ e) u ↔ (5 : ℤ) ∣ ∑ j, ((∑ i, e i * M i j) - e j) * u j := by
    intro u
    rw [hz, rootChar_tupE, rootChar_tupE, ← mul_inv_eq_one, ← zpow_sub,
      hζ.zpow_eq_one_iff_dvd, dotE_mulVec]
    have : (∑ j, (∑ i, e i * M i j) * u j) - dotE e u =
        ∑ j, ((∑ i, e i * M i j) - e j) * u j := by
      rw [dotE, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    rfl
  show (∀ u, rootChar (τ := Tag.E8) (tupE ζ e) (z • u) = rootChar (tupE ζ e) u) ↔ _
  simp only [key]
  exact dvd_forall_iff

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
