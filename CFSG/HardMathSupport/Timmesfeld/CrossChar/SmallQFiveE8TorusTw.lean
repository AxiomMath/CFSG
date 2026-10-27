module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Torus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

set_option linter.unusedSectionVars false

section Twisted

variable {L : Type} [Field L]

theorem smul_e8PhiFourWeyl (v : Fin Tag.E8.rank → ℤ) : e8PhiFourWeyl • v = e8M *ᵥ v := by
  rw [e8PhiFourWeyl, wordProd_smul_eq_wordMat_mulVec, e8Four_wordMat]
  rfl

theorem pairZ_mulVec (x : Fin 8 → ZMod 5) (v : Fin Tag.E8.rank → ℤ) :
    pairZ x (e8M *ᵥ v) = ∑ j, (∑ k, x k * ((e8M k j : ℤ) : ZMod 5)) * ((v j : ℤ) : ZMod 5) := by
  simp only [pairZ, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pairZ_smul_of_isEig {x : Fin 8 → ZMod 5} (hx : IsEig x) (v : Fin Tag.E8.rank → ℤ) :
    pairZ x (e8PhiFourWeyl • v) = 2 * pairZ x v := by
  have h1 := (congrArg (pairZ x) (smul_e8PhiFourWeyl v)).trans (pairZ_mulVec x v)
  refine h1.trans ?_
  simp only [pairZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hx j]
  ring

theorem isEig_of_pairZ_smul {x : Fin 8 → ZMod 5}
    (h : ∀ v : Fin Tag.E8.rank → ℤ, pairZ x (e8PhiFourWeyl • v) = 2 * pairZ x v) : IsEig x := by
  intro j
  have h1 := h (Pi.single j 1)
  have h2 := ((congrArg (pairZ x) (smul_e8PhiFourWeyl (Pi.single j 1))).symm.trans h1)
  have h3 := (pairZ_mulVec x (Pi.single j 1)).symm.trans h2
  have h4 : ∑ j', (∑ k, x k * ((e8M k j' : ℤ) : ZMod 5)) *
      (((Pi.single j 1 : Fin Tag.E8.rank → ℤ) j' : ℤ) : ZMod 5) = 2 * x j :=
    h3.trans (congrArg (fun t => 2 * t) (pairZ_single x j))
  exact (sum_mul_single (fun j' => ∑ k, x k * ((e8M k j' : ℤ) : ZMod 5)) j).symm.trans h4

theorem torV5_mem_twistedFixedTuples {ζ : Lˣ} (hζ : orderOf ζ = 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ 2) (x : Fin 8 → ZMod 5) :
    torV5 ζ x ∈ twistedFixedTuples e8PhiFourWeyl Fr ↔ IsEig x := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hmap : ∀ z : Lˣ, Units.map Fr.toMonoidHom z = z ^ 2 := fun z =>
    Units.ext (by simp [hFr])
  rw [mem_twistedFixedTuples_iff]
  constructor
  · intro h
    apply isEig_of_pairZ_smul
    intro v
    have := h v
    rw [rootChar_torV5 h5, hmap, rootChar_torV5 h5, sq, ← chiZ_add h5, ← two_mul] at this
    exact chiZ_injective hζ this
  · intro hx v
    rw [rootChar_torV5 h5, hmap, rootChar_torV5 h5, sq, ← chiZ_add h5, ← two_mul,
      pairZ_smul_of_isEig hx]

theorem pow_five_of_mem_twistedFixedTuples {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2)
    {a : Fin Tag.E8.rank → Lˣ} (ha : a ∈ twistedFixedTuples e8PhiFourWeyl Fr)
    (i : Fin Tag.E8.rank) : a i ^ 5 = 1 := by
  have hmap : ∀ z : Lˣ, Units.map Fr.toMonoidHom z = z ^ 2 := fun z =>
    Units.ext (by simp [hFr])
  rw [mem_twistedFixedTuples_iff] at ha
  have h1 := ha (Pi.single i 1)
  rw [CTTorus.rootChar_single, hmap] at h1
  have h2 := ha (e8PhiFourWeyl • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))
  rw [h1, hmap, e8PhiFourWeyl_sq_smul5] at h2
  have h3 : rootChar a (-(Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = (a i)⁻¹ := by
    rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul, CTTorus.rootChar_single]
  rw [h3] at h2
  have h4 : a i * (a i)⁻¹ = 1 := mul_inv_cancel _
  rw [h2] at h4
  calc a i ^ 5 = a i * ((a i ^ 2) ^ 2) := by rw [← pow_mul, ← pow_succ']
    _ = 1 := h4

@[expose] noncomputable def d5 (ζ : Lˣ) (x : Fin 8 → ZMod 5) : ModGL Tag.E8 L :=
  rootDiagUnit Tag.E8 (torV5 ζ x)

theorem d5_add {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (x y : Fin 8 → ZMod 5) :
    d5 ζ (x + y) = d5 ζ x * d5 ζ y := by
  rw [d5, d5, d5, torV5_add h5]
  exact rootDiagUnit_mul _ _

theorem d5_zero (ζ : Lˣ) : d5 (L := L) ζ 0 = 1 := by
  rw [d5, torV5_zero]
  exact rootDiagUnit_one

theorem d5_injective {ζ : Lˣ} (hζ : orderOf ζ = 5) : Function.Injective (d5 (L := L) ζ) := by
  intro x y h
  have h1 := rootDiagUnit_injective h
  funext i
  exact chiZ_injective hζ (congrFun h1 i)

@[expose] noncomputable def phi5 (ζ : Lˣ) (h5 : ζ ^ 5 = 1) :
    Multiplicative (Fin 4 → ZMod 5) →* ModGL Tag.E8 L where
  toFun c := d5 ζ (xc (Multiplicative.toAdd c))
  map_one' := by simp [xc_zero, d5_zero]
  map_mul' a b := by simp only [toAdd_mul, xc_add, d5_add h5]

theorem phi5_injective {ζ : Lˣ} (hζ : orderOf ζ = 5) (h5 : ζ ^ 5 = 1) :
    Function.Injective (phi5 (L := L) ζ h5) := by
  intro a b h
  have h1 : d5 ζ (xc (Multiplicative.toAdd a)) = d5 ζ (xc (Multiplicative.toAdd b)) := h
  exact Multiplicative.toAdd.injective (xc_injective (d5_injective hζ h1))

theorem phi5_mem_twModel {ζ : Lˣ} (hζ : orderOf ζ = 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ 2) (c : Fin 4 → ZMod 5) :
    d5 ζ (xc c) ∈ twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) Fr := by
  refine twistedTorus_le_twModel _ _ (mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup_E8 _, ?_⟩)
  exact mem_twistedFixedTuples_iff_conj.1
    ((torV5_mem_twistedFixedTuples hζ hFr (xc c)).2 (isEig_xc c))

theorem exists_phi5_of_mem_twModel {ζ : Lˣ} (hζ : orderOf ζ = 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ 2) {d : ModGL Tag.E8 L}
    (hd : d ∈ twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) Fr)
    (hdT : d ∈ torusGroup Tag.E8 L) : ∃ c : Fin 4 → ZMod 5, d = d5 ζ (xc c) := by
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom hdT
  have hda : d = rootDiagUnit Tag.E8 a := ha.symm
  have hfix : a ∈ twistedFixedTuples e8PhiFourWeyl Fr := by
    rw [mem_twistedFixedTuples_iff_conj, ← hda]
    exact hd.2
  obtain ⟨x, hx⟩ := exists_eq_torV5 hζ a (pow_five_of_mem_twistedFixedTuples hFr hfix)
  subst hx
  have hxe := (torV5_mem_twistedFixedTuples hζ hFr x).1 hfix
  exact ⟨![x 4, x 2, x 1, x 0], by rw [hda, d5, ← eig_eq_xc hxe]⟩

theorem five_nsmul_eq_zero (c : Fin 4 → ZMod 5) : (5 • c : Fin 4 → ZMod 5) = 0 := by
  funext j
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  have : (5 : ZMod 5) = 0 := rfl
  rw [Nat.cast_ofNat, this, zero_mul]

theorem pow_five_of_mem_twModel_torus {ζ : Lˣ} (hζ : orderOf ζ = 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ 2) {d : ModGL Tag.E8 L}
    (hd : d ∈ twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) Fr)
    (hdT : d ∈ torusGroup Tag.E8 L) : d ^ 5 = 1 := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨c, rfl⟩ := exists_phi5_of_mem_twModel hζ hFr hd hdT
  have h1 : d5 (L := L) ζ (xc c) = phi5 ζ h5 (Multiplicative.ofAdd c) := rfl
  rw [h1, ← map_pow, ← ofAdd_nsmul, five_nsmul_eq_zero, ofAdd_zero, map_one]

end Twisted

section Zeta

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem exists_zeta5 : ∃ ζ : Lˣ, orderOf ζ = 5 := by
  have : NeZero ((5 : ℕ) : L) := NeZero.of_not_dvd L (p := 2) (by norm_num)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hζu : IsPrimitiveRoot hu.unit 5 := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact ⟨hu.unit, hζu.eq_orderOf.symm⟩

end Zeta

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
