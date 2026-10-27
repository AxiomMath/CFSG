module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightSound
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

set_option linter.unusedSectionVars false

section Chi

variable {L : Type} [Field L]

@[expose] def torV17 (ζ : Lˣ) (x : Fin 8 → ZMod 17) : Fin Tag.E8.rank → Lˣ :=
  fun i => ζ ^ (x i).val

@[expose] def chi17 (ζ : Lˣ) (a : ZMod 17) : Lˣ := ζ ^ a.val

theorem pow_val_add17 {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (a b : ZMod 17) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have key : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 17) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 17]
    rw [pow_add, pow_mul, h17, one_pow, mul_one]
  rw [← pow_add, ZMod.val_add, ← key]

theorem chi17_add {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (a b : ZMod 17) :
    chi17 ζ (a + b) = chi17 ζ a * chi17 ζ b :=
  pow_val_add17 h17 a b

theorem chi17_zero (ζ : Lˣ) : chi17 ζ 0 = 1 := by
  simp [chi17]

theorem chi17_injective {ζ : Lˣ} (hζ : orderOf ζ = 17) : Function.Injective (chi17 ζ) := by
  intro a b h
  have h2 : ζ ^ a.val = ζ ^ b.val := h
  rw [pow_eq_pow_iff_modEq, hζ] at h2
  have hx := ZMod.val_lt a
  have hy := ZMod.val_lt b
  have : a.val = b.val := by
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact ZMod.val_injective _ this

theorem zpow_eq_chi17 {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (z : ℤ) : ζ ^ z = chi17 ζ (z : ZMod 17) := by
  have h1 : (((z : ZMod 17).val : ℕ) : ℤ) = z % 17 := ZMod.val_intCast z
  have h17z : ζ ^ (17 : ℤ) = 1 := by
    rw [show (17 : ℤ) = ((17 : ℕ) : ℤ) from rfl, zpow_natCast, h17]
  rw [chi17, ← zpow_natCast, h1]
  conv_lhs => rw [← Int.emod_add_mul_ediv z 17]
  rw [zpow_add, zpow_mul, h17z, one_zpow, mul_one]

theorem rootChar_torV17 {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (x : Fin 8 → ZMod 17)
    (v : Fin Tag.E8.rank → ℤ) : rootChar (torV17 ζ x) v = chi17 ζ (pairZ17 x v) := by
  have h1 : rootChar (torV17 ζ x) v = ζ ^ (∑ i, (((x i).val : ℕ) : ℤ) * v i) := by
    rw [rootChar, ← SmallQ3.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [torV17, ← zpow_natCast, ← zpow_mul]
  rw [h1, zpow_eq_chi17 h17]
  congr 1
  simp [pairZ17]

theorem torV17_add {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (x y : Fin 8 → ZMod 17) :
    torV17 ζ (x + y) = torV17 ζ x * torV17 ζ y :=
  funext fun i => pow_val_add17 h17 _ _

theorem torV17_zero (ζ : Lˣ) : torV17 ζ (0 : Fin 8 → ZMod 17) = 1 := by
  funext i
  show ζ ^ ((0 : ZMod 17)).val = 1
  simp

theorem exists_eq_torV17 {ζ : Lˣ} (hζ : orderOf ζ = 17) (a : Fin Tag.E8.rank → Lˣ)
    (ha : ∀ i, a i ^ 17 = 1) : ∃ x : Fin 8 → ZMod 17, a = torV17 ζ x := by
  have hprim : IsPrimitiveRoot ζ 17 := IsPrimitiveRoot.iff_orderOf.2 hζ
  have hprimL : IsPrimitiveRoot (ζ : L) 17 := IsPrimitiveRoot.coe_units_iff.2 hprim
  have : ∀ i, ∃ k : ℕ, k < 17 ∧ ζ ^ k = a i := fun i => by
    have h1 : ((a i : Lˣ) : L) ^ 17 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
    obtain ⟨k, hk, hk'⟩ := hprimL.eq_pow_of_pow_eq_one h1
    exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk')⟩
  choose k hk hka using this
  refine ⟨fun i => (k i : ZMod 17), funext fun i => ?_⟩
  rw [torV17, ZMod.val_natCast_of_lt (hk i), hka i]

end Chi

@[expose] def flOf17 (c : Fin 2 → ZMod 17) : List ℤ := List.ofFn fun i => ((c i).val : ℤ)

theorem length_flOf17 (c : Fin 2 → ZMod 17) : (flOf17 c).length = 2 := by
  simp [flOf17]

theorem getElem_flOf17 (g : Fin 2 → ZMod 17) {k : ℕ} (hk : k < (flOf17 g).length) :
    (flOf17 g)[k] = ((g ⟨k, by simpa [length_flOf17] using hk⟩).val : ℤ) := by
  simp only [flOf17, List.getElem_ofFn]

theorem flOf17_zero : flOf17 (0 : Fin 2 → ZMod 17) = List.replicate 2 0 := by
  simp [flOf17, List.ofFn_const]

theorem ofFn_getD_eq17 {n : ℕ} {b : List ℤ} (hb : b.length = n) :
    List.ofFn (fun i : Fin n => b.getD i 0) = b := by
  refine List.ext_getElem (by simp [hb]) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

theorem rr17_ofFn8 (v : Fin 8 → ℤ) : rr17 (List.ofFn v) = flOf17 (rrv17 v) := by
  have hlen : ∀ k, k < 2 → (e17Rows.getD k []).length = 8 := by decide
  refine List.ext_getElem (by simp [rr17, e17Rows, length_flOf17]) fun k h1 h2 => ?_
  have hk : k < 2 := by simpa [length_flOf17] using h2
  have hk' : k < e17Rows.length := by simpa [e17Rows] using hk
  have hdot : dotZ (e17Rows.getD k []) (List.ofFn v) =
      ∑ j : Fin 8, (e17Rows.getD k []).getD j 0 * v j := by
    have h := dotZ_ofFn (fun j : Fin 8 => (e17Rows.getD k []).getD j 0) v
    rwa [ofFn_getD_eq17 (hlen k hk)] at h
  have hrrv : rrv17 v ⟨k, hk⟩ =
      ((∑ j : Fin 8, (e17Rows.getD k []).getD j 0 * v j : ℤ) : ZMod 17) := by
    simp [rrv17, pairZ17, E17]
  have hL : (rr17 (List.ofFn v))[k] =
      (∑ j : Fin 8, (e17Rows.getD k []).getD j 0 * v j) % 17 := by
    simp only [rr17, List.getElem_map]
    rw [← hdot, List.getD_eq_getElem _ _ hk']
  refine hL.trans ?_
  rw [getElem_flOf17]
  show _ = ((rrv17 v ⟨k, hk⟩).val : ℤ)
  rw [hrrv, ZMod.val_intCast] <;> rfl

theorem rr17_ofFn (v : Fin Tag.E8.rank → ℤ) : rr17 (List.ofFn v) = flOf17 (rrv17 v) :=
  rr17_ofFn8 v

section Family

variable {L : Type} [Field L]

@[expose] def famPar17 (ζ : Lˣ) : (Fin 2 → ZMod 17) → Fin Tag.E8.rank → Lˣ :=
  fun c => torV17 ζ (xc17 c)

theorem rootChar_famPar17 {ζ : Lˣ} (h17 : ζ ^ 17 = 1) (c : Fin 2 → ZMod 17)
    (v : Fin Tag.E8.rank → ℤ) : rootChar (famPar17 ζ c) v = chi17 ζ (c ⬝ᵥ rrv17 v) := by
  rw [famPar17, rootChar_torV17 h17]
  exact congrArg (chi17 ζ) (pairZ17_xc c v)

theorem familyKernel_famPar17_eq_empty {ζ : Lˣ} (hζ : orderOf ζ = 17) (hK : fK17 = ∅) :
    familyKernel (famPar17 ζ) = (∅ : Set (Fin Tag.E8.rank → ℤ)) := by
  have h17 : ζ ^ 17 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
  obtain ⟨hγr, hall⟩ := hγ
  have hz : rrv17 γ = 0 := by
    apply eq_zero_of_dotProduct17
    intro c
    have h1 := hall c
    rw [rootChar_famPar17 h17] at h1
    exact chi17_injective hζ (h1.trans (chi17_zero ζ).symm)
  have : γ ∈ fK17 := ⟨hγr, by rw [rr17_ofFn, hz, flOf17_zero]⟩
  rw [hK] at this
  exact this

theorem familyStabilizer_famPar17_subset {ζ : Lˣ} (hζ : orderOf ζ = 17) :
    familyStabilizer (famPar17 ζ) ⊆ fS17 := by
  have h17 : ζ ^ 17 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  intro u hu i
  rw [rr17_ofFn, rr17_ofFn]
  congr 1
  apply eq_of_dotProduct17
  intro c
  have h1 := hu c (Pi.single i 1)
  rw [rootChar_famPar17 h17, rootChar_famPar17 h17] at h1
  exact chi17_injective hζ h1

end Family

section Centralizer

variable {L : Type} [Field L]

theorem mem_torusGroup_of_commute17 {ζ : Lˣ} (hζ : orderOf ζ = 17) (hK : fK17 = ∅)
    (hS : ∀ u ∈ fS17, u = 1) {z : ModGL Tag.E8 L} (hz : z ∈ adjointGroup Tag.E8 L)
    (hcomm : ∀ c : Fin 2 → ZMod 17,
      Commute z (rootDiagUnit Tag.E8 (famPar17 ζ c))) : z ∈ torusGroup Tag.E8 L := by
  have hfam : z ∈ familyCentralizer Tag.E8 L (famPar17 ζ) := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun c => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm c).eq.symm
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul Tag.E8 L (famPar17 ζ) hfam
  have hw1 : w = 1 := hS w (familyStabilizer_famPar17_subset hζ hw)
  have hker := familyKernel_famPar17_eq_empty (L := L) hζ hK
  have hmT : m ∈ torusGroup Tag.E8 L := by
    have hm' : m ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (familyKernel (famPar17 ζ)) := hm
    rw [hker] at hm'
    have hbot : rootSpan Tag.E8 L (∅ : Set (Fin Tag.E8.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hw1, canonicalRep_one, mul_one]
  exact hmT

end Centralizer

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
