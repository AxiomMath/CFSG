module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Pieces
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev E6Idx : Type := Fin Tag.E6.rank

theorem cartan_eq_cartanE6 : ∀ k i : E6Idx, Tag.E6.cartan k i = cartanE6 i k := by
  intro k i
  fin_cases k <;> fin_cases i <;> rfl

section W


@[expose] noncomputable def weylActI (w : WeylGroup Tag.E6) : Matrix E6Idx E6Idx (ZMod 3) :=
  dualMatrix (ZMod 3) w⁻¹

theorem weylActI_mul (w w' : WeylGroup Tag.E6) :
    weylActI (w * w') = weylActI w * weylActI w' := by
  unfold weylActI
  rw [mul_inv_rev, dualMatrix_mul]

theorem weylActI_one : weylActI (1 : WeylGroup Tag.E6) = 1 := by
  unfold weylActI
  rw [inv_one, dualMatrix_one]

@[expose] noncomputable def weylActHom : WeylGroup Tag.E6 →* Matrix E6Idx E6Idx (ZMod 3) where
  toFun := weylActI
  map_one' := weylActI_one
  map_mul' := weylActI_mul

@[expose] noncomputable def weylActGL :
    WeylGroup Tag.E6 →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) :=
  weylActHom.toHomUnits

@[expose] noncomputable def weylAct (w : WeylGroup Tag.E6) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  weylActI w

theorem coe_weylActGL (w : WeylGroup Tag.E6) :
    ((weylActGL w : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      weylAct w := rfl

theorem reflect_single_apply (k i j : E6Idx) :
    reflect Tag.E6 k (Pi.single i 1) j =
      (if j = i then 1 else 0) - Tag.E6.cartan k i * (if j = k then 1 else 0) := by
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have : ∑ l, Tag.E6.cartan k l * (if l = i then (1 : ℤ) else 0) = Tag.E6.cartan k i := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [this]

theorem weylActI_simple (k : E6Idx) : weylActI (simple Tag.E6 k) = reflMat k := by
  ext i j
  have h := reflect_single_apply k i j
  have hc := cartan_eq_cartanE6 k i
  have hinv : (simple Tag.E6 k)⁻¹ = simple Tag.E6 k := (coxeterSystem Tag.E6).inv_simple k
  unfold weylActI
  rw [hinv]
  simp only [dualMatrix, Matrix.transpose_apply, Matrix.map_apply, weylMatrix_apply, simple_smul]
  rw [h, hc]
  clear h hc hinv
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide

theorem weylAct_simple (k : Fin 6) : weylAct (simple Tag.E6 k) = reflMat k :=
  weylActI_simple k

theorem range_weylActGL : (weylActGL).range = W3 := by
  have h1 : (⊤ : Subgroup (WeylGroup Tag.E6)).map weylActGL = W3 := by
    rw [← (coxeterSystem Tag.E6).subgroup_closure_range_simple, MonoidHom.map_closure]
    unfold W3
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, Units.ext (weylAct_simple k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, Units.ext (weylAct_simple k)⟩
  rw [MonoidHom.range_eq_map, h1]

theorem weylActGL_mem_W3 (w : WeylGroup Tag.E6) : weylActGL w ∈ W3 := by
  rw [← range_weylActGL]
  exact ⟨w, rfl⟩

theorem iform_self_nonneg (x : E6Idx → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem iform_self_isRoot_E6 {γ : E6Idx → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]
  have : Tag.E6.symmetrizer j j = 1 := by
    show (1 : Matrix E6Idx E6Idx ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [this]
  norm_num

theorem eq_of_root_sub_mem_three {β : E6Idx → ℤ} (hβ : IsRoot Tag.E6 β) (j : E6Idx)
    (h : ∀ i, (3 : ℤ) ∣ β i - (Pi.single j (1 : ℤ) : E6Idx → ℤ) i) :
    β = Pi.single j 1 := by
  choose y hy using h
  have hd : β - (Pi.single j (1 : ℤ) : E6Idx → ℤ) = (3 : ℤ) • y := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hy i
  have hej : IsRoot Tag.E6 (Pi.single j (1 : ℤ) : E6Idx → ℤ) := IsRoot.basis j
  have h1 : iform β β = 2 := iform_self_isRoot_E6 hβ
  have h2 : iform (Pi.single j (1 : ℤ) : E6Idx → ℤ) (Pi.single j 1) = 2 :=
    iform_self_isRoot_E6 hej
  have h3 : 0 ≤ iform (β + Pi.single j 1) (β + Pi.single j 1) := iform_self_nonneg _
  rw [iform_add_left, iform_add_right, iform_add_right, h1, h2,
    iform_comm (Pi.single j 1) β] at h3
  have h4 : iform ((3 : ℤ) • y) ((3 : ℤ) • y) = 9 * iform y y := by
    rw [iform_smul_left, iform_smul_right]
    ring
  have h5 : iform (β - Pi.single j 1) (β - Pi.single j 1) ≤ 8 := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, h1, h2,
      iform_comm (Pi.single j 1) β]
    linarith
  rw [hd, h4] at h5
  have hy0 : y = 0 := by
    by_contra hne
    have := iform_self_pos hne
    omega
  rw [hy0, smul_zero] at hd
  exact sub_eq_zero.mp hd

theorem weylAct_eq_one {w : WeylGroup Tag.E6} (h : weylActI w = 1) : w = 1 := by
  have hv : ∀ j : E6Idx, w⁻¹ • (Pi.single j (1 : ℤ) : E6Idx → ℤ) = Pi.single j 1 := by
    intro j
    refine eq_of_root_sub_mem_three (IsRoot.smul (IsRoot.basis j) w⁻¹) j fun i => ?_
    have h1 := congrFun (congrFun h j) i
    simp only [weylActI, dualMatrix, Matrix.transpose_apply, Matrix.map_apply,
      weylMatrix_apply] at h1
    have key : (((w⁻¹ • (Pi.single j (1 : ℤ) : E6Idx → ℤ)) i -
        (Pi.single j (1 : ℤ) : E6Idx → ℤ) i : ℤ) : ZMod 3) = 0 := by
      rw [Int.cast_sub]
      rw [Matrix.one_apply] at h1
      by_cases hji : j = i
      · subst hji
        simp only [if_true] at h1
        simp [h1]
      · have : ¬ i = j := fun h => hji h.symm
        simp only [hji, if_false] at h1
        simp [h1, Pi.single_apply, this]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 key
  have : w⁻¹ = 1 := ext_single fun j => by rw [hv j, one_smul]
  exact inv_eq_one.mp this

end W

section Tor


variable {K : Type} [Field K]

@[expose] noncomputable def Psi6 {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 K :=
  DiagTorus.Psi hζ

theorem Psi6_apply {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin 6 → ZMod 3)) :
    Psi6 (K := K) hζ u = rootDiagUnit Tag.E6 (fun i => DiagTorus.theta ζ (Multiplicative.toAdd u i)) :=
  rfl

theorem Psi6_injective {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Function.Injective (Psi6 (K := K) hζ) :=
  DiagTorus.Psi_injective hζ hζ'

theorem Psi6_pow_three {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin 6 → ZMod 3)) :
    Psi6 (K := K) hζ u ^ 3 = 1 :=
  DiagTorus.Psi_pow_three hζ u

theorem weylTuple_theta {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (w : WeylGroup Tag.E6) (u : E6Idx → ZMod 3) :
    weylTuple w (fun i => DiagTorus.theta ζ (u i)) =
      fun i => DiagTorus.theta ζ ((weylActI w).mulVec u i) := by
  funext i
  unfold weylTuple
  rw [DiagTorus.rootChar_theta hζ u]
  congr 1

theorem conj_Psi6_of_mem_monoHat {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (x : monoHat Tag.E6 K)
    (u : Fin 6 → ZMod 3) :
    (x : ModGL Tag.E6 K) * Psi6 hζ (Multiplicative.ofAdd u) * (x : ModGL Tag.E6 K)⁻¹ =
      Psi6 hζ (Multiplicative.ofAdd
        ((weylAct (psiHat Tag.E6 K x)).mulVec u)) := by
  show (x : ModGL Tag.E6 K) * DiagTorus.Psi hζ (Multiplicative.ofAdd u) * (x : ModGL Tag.E6 K)⁻¹ =
    DiagTorus.Psi hζ (Multiplicative.ofAdd ((weylActI (psiHat Tag.E6 K x)).mulVec u))
  rw [DiagTorus.Psi_apply, DiagTorus.Psi_apply, conj_rootDiagUnit_of_mem_monoHat]
  simp only [toAdd_ofAdd]
  rw [weylTuple_theta hζ]
  rfl

end Tor

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
