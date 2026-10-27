module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatAct
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Census

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open CFSG.Fischer
open Sec3Theta Census
open scoped Pointwise

namespace Sec3Lift

@[expose] def epsInv (v : V₀) : Fin 6 → ZMod 2 := fun i => ((v i).code.val : ZMod 2)

theorem epsF_epsInv {v : V₀} (hv : v ∈ N0) : epsF (epsInv v) = v := by
  funext i
  apply F4_eq_of_val
  rcases (show (v i).code.val = 0 ∨ (v i).code.val = 1 by have := hv i; omega) with h | h
  · simp only [epsF, epsInv, h, Nat.cast_zero, map_zero]
    rfl
  · simp only [epsF, epsInv, h, Nat.cast_one, map_one]
    rfl

theorem epsF_smul (c : ZMod 2) (y : Fin 6 → ZMod 2) : epsF (c • y) = toF4 c • epsF y := by
  funext i
  simp [epsF]

theorem epsF_single (k : Fin 6) : epsF (Pi.single k 1) = Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · subst h
    simp [epsF]
  · simp [epsF, h]

@[expose] noncomputable def f2Map (M : Array ℕ) (hM : f2Mat M = true) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun y := epsInv (toLin M (epsF y))
  map_add' y y' := by
    apply epsF_injective
    rw [epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 _)), epsF_add, epsF_add,
      epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 _)),
      epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 _)), map_add]
  map_smul' c y := by
    apply epsF_injective
    rw [RingHom.id_apply, epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 _)), epsF_smul, epsF_smul,
      epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 _)), map_smul]

theorem epsF_f2Map {M : Array ℕ} (hM : f2Mat M = true) (y : Fin 6 → ZMod 2) :
    epsF (f2Map M hM y) = toLin M (epsF y) :=
  epsF_epsInv (toLin_mem_N0 hM (epsF_mem_N0 y))

theorem f2Map_single {M : Array ℕ} (hM : f2Mat M = true) (k : Fin 6) :
    f2Map M hM (Pi.single k 1) = epsInv (decodeV M[k.val]!) := by
  change epsInv (toLin M (epsF (Pi.single k 1))) = _
  rw [epsF_single, toLin_single]

theorem f2Map_apply {M : Array ℕ} (hM : f2Mat M = true) (y : Fin 6 → ZMod 2) :
    f2Map M hM y = ∑ k, y k • epsInv (decodeV M[k.val]!) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : Pi.single k (y k) = y k • (Pi.single k 1 : Fin 6 → ZMod 2) := by
    funext j
    by_cases h : j = k
    · subst h
      simp
    · simp [h]
  rw [e1, map_smul, f2Map_single]

theorem qplus_f2Map {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true)
    (y : Fin 6 → ZMod 2) : Sec3Coord.qplus (f2Map M hM y) = Sec3Coord.qplus y := by
  apply toF4_injective
  rw [← Q₀_epsF, ← Q₀_epsF, epsF_f2Map hM, toLin_isometry hI]

theorem f2Map_injective {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true) :
    Function.Injective (f2Map M hM) := by
  intro y y' h
  apply epsF_injective
  apply toLin_injective hI
  rw [← epsF_f2Map hM, ← epsF_f2Map hM, h]

@[expose] noncomputable def f2Equiv (M : Array ℕ) (hM : f2Mat M = true) (hI : isomOK M = true) :
    (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearEquiv.ofInjectiveEndo (f2Map M hM) (f2Map_injective hM hI)

theorem f2Equiv_apply {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true)
    (y : Fin 6 → ZMod 2) : f2Equiv M hM hI y = f2Map M hM y := rfl

theorem epsF_pow {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true) (k : ℕ)
    (y : Fin 6 → ZMod 2) : epsF ((f2Equiv M hM hI ^ k) y) = (toLin M ^ k) (epsF y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, LinearEquiv.mul_apply, ih, Module.End.mul_apply, f2Equiv_apply,
      epsF_f2Map hM]

theorem f2Equiv_pow_eq_one {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true) {k : ℕ}
    (h : toLin M ^ k = 1) : f2Equiv M hM hI ^ k = 1 :=
  LinearEquiv.ext fun y => epsF_injective (by rw [epsF_pow, h]; rfl)

theorem toLin_mul (A B : Array ℕ) : toLin A * toLin B = toLin (matMul A B) := by
  rw [toLin_matMul]
  rfl

theorem toLin_idMat_eq_one : toLin idMat = 1 := toLin_idMat

theorem toLin_g1_pow : toLin g1M ^ 7 = 1 := by
  have h2 : matMul g1M g1M = #[1024, 1361, 1028, 1029, 1040, 1088] := by decide
  have h3 : matMul #[1024, 1361, 1028, 1029, 1040, 1088] g1M =
      #[1280, 337, 1285, 81, 21, 80] := by decide
  have h4 : matMul #[1024, 1361, 1028, 1029, 1040, 1088] #[1024, 1361, 1028, 1029, 1040, 1088] =
      #[1088, 1105, 273, 1297, 68, 69] := by decide
  have h7 : matMul #[1088, 1105, 273, 1297, 68, 69] #[1280, 337, 1285, 81, 21, 80] = idMat := by
    decide
  have e2 : toLin g1M ^ 2 = toLin #[1024, 1361, 1028, 1029, 1040, 1088] := by
    rw [pow_two, toLin_mul, h2]
  have e3 : toLin g1M ^ 3 = toLin #[1280, 337, 1285, 81, 21, 80] := by
    rw [pow_succ, e2, toLin_mul, h3]
  have e4 : toLin g1M ^ 4 = toLin #[1088, 1105, 273, 1297, 68, 69] := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, e2, pow_two, toLin_mul, h4]
  rw [show 7 = 4 + 3 from rfl, pow_add, e4, e3, toLin_mul, h7, toLin_idMat_eq_one]

theorem toLin_g2_pow : toLin g2M ^ 15 = 1 := by
  have h2 : matMul g2M g2M = #[1105, 1040, 321, 1045, 320, 341] := by decide
  have h3 : matMul #[1105, 1040, 321, 1045, 320, 341] g2M =
      #[340, 337, 1285, 277, 21, 1344] := by decide
  have h4 : matMul #[1105, 1040, 321, 1045, 320, 341] #[1105, 1040, 321, 1045, 320, 341] =
      #[80, 20, 260, 85, 1365, 1109] := by decide
  have h8 : matMul #[80, 20, 260, 85, 1365, 1109] #[80, 20, 260, 85, 1365, 1109] =
      #[337, 272, 1345, 277, 21, 1344] := by decide
  have h12 : matMul #[337, 272, 1345, 277, 21, 1344] #[80, 20, 260, 85, 1365, 1109] =
      #[1108, 1105, 261, 1045, 320, 341] := by decide
  have h15 : matMul #[1108, 1105, 261, 1045, 320, 341] #[340, 337, 1285, 277, 21, 1344] =
      idMat := by decide
  have e2 : toLin g2M ^ 2 = toLin #[1105, 1040, 321, 1045, 320, 341] := by
    rw [pow_two, toLin_mul, h2]
  have e3 : toLin g2M ^ 3 = toLin #[340, 337, 1285, 277, 21, 1344] := by
    rw [pow_succ, e2, toLin_mul, h3]
  have e4 : toLin g2M ^ 4 = toLin #[80, 20, 260, 85, 1365, 1109] := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, e2, pow_two, toLin_mul, h4]
  have e8 : toLin g2M ^ 8 = toLin #[337, 272, 1345, 277, 21, 1344] := by
    rw [show 8 = 4 * 2 from rfl, pow_mul, e4, pow_two, toLin_mul, h8]
  have e12 : toLin g2M ^ 12 = toLin #[1108, 1105, 261, 1045, 320, 341] := by
    rw [show 12 = 8 + 4 from rfl, pow_add, e8, e4, toLin_mul, h12]
  rw [show 15 = 12 + 3 from rfl, pow_add, e12, e3, toLin_mul, h15, toLin_idMat_eq_one]

theorem toLin_b3_pow : toLin b3M ^ 3 = 1 := by
  have h2 : matMul b3M b3M = #[1, 4, 1104, 16, 1296, 1024] := by decide
  have h3 : matMul #[1, 4, 1104, 16, 1296, 1024] b3M = idMat := by decide
  rw [pow_succ, pow_two, toLin_mul, h2, toLin_mul, h3, toLin_idMat_eq_one]

theorem toLin_b5_pow : toLin b5M ^ 5 = 1 := by
  have h2 : matMul b5M b5M = #[1, 4, 1360, 336, 80, 1040] := by decide
  have h4 : matMul #[1, 4, 1360, 336, 80, 1040] #[1, 4, 1360, 336, 80, 1040] =
      #[1, 4, 64, 1104, 1024, 320] := by decide
  have h5 : matMul #[1, 4, 64, 1104, 1024, 320] b5M = idMat := by decide
  have e2 : toLin b5M ^ 2 = toLin #[1, 4, 1360, 336, 80, 1040] := by
    rw [pow_two, toLin_mul, h2]
  have e4 : toLin b5M ^ 4 = toLin #[1, 4, 64, 1104, 1024, 320] := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, e2, pow_two, toLin_mul, h4]
  rw [pow_succ, e4, toLin_mul, h5, toLin_idMat_eq_one]

section Omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem mem_omegaGroup_of_pow_eq_one (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) {k : ℕ} (hk : Odd k) (h : g ^ k = 1) :
    g ∈ omegaGroup q hq := by
  have hk1 : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup q) ^ k = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
  have hd : dicksonHom q hq ⟨g, hg⟩ ^ k = 1 := by rw [← map_pow, hk1, map_one]
  have hy2 : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := fun y => by
    induction y using Multiplicative.rec with
    | ofAdd a => rw [← ofAdd_nsmul, two_nsmul, ZModModule.add_self, ofAdd_zero]
  obtain ⟨m, rfl⟩ := hk
  have h1 : dicksonHom q hq ⟨g, hg⟩ = 1 := by
    rw [pow_succ, pow_mul, hy2, one_pow, one_mul] at hd
    exact hd
  have hker : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup q) ∈ (dicksonHom q hq).ker := h1
  rw [dicksonHom_ker, mem_subgroupOf] at hker
  exact hker

end Omega

theorem f2Map_eq_of_cols {M : Array ℕ} (hM : f2Mat M = true) {col : Fin 6 → Fin 6 → ZMod 2}
    (h : ∀ k : Fin 6, epsInv (decodeV M[k.val]!) = col k) (y : Fin 6 → ZMod 2) :
    f2Map M hM y = ∑ k, y k • col k := by
  rw [f2Map_apply]
  simp_rw [h]

@[expose] def x0Col : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def b3Col : Fin 6 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1]]

@[expose] def b5Col : Fin 6 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]

theorem x0_cols (k : Fin 6) : epsInv (decodeV x0M[k.val]!) = x0Col k := by
  fin_cases k <;> decide

theorem b3_cols (k : Fin 6) : epsInv (decodeV b3M[k.val]!) = b3Col k := by
  fin_cases k <;> decide

theorem b5_cols (k : Fin 6) : epsInv (decodeV b5M[k.val]!) = b5Col k := by
  fin_cases k <;> decide

theorem f2Map_x0 (hM : f2Mat x0M = true) (y : Fin 6 → ZMod 2) :
    f2Map x0M hM y = ![y 1, y 0 + y 1, y 2, y 3, y 4, y 5] := by
  rw [f2Map_eq_of_cols hM x0_cols]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_six, x0Col]

theorem block_of_cols {M : Array ℕ} (hM : f2Mat M = true) {col : Fin 6 → Fin 6 → ZMod 2}
    (h : ∀ k : Fin 6, epsInv (decodeV M[k.val]!) = col k)
    (h0 : ∀ i, col 0 i = ![1, 0, 0, 0, 0, 0] i) (h1 : ∀ i, col 1 i = ![0, 1, 0, 0, 0, 0] i)
    (h2 : ∀ k : Fin 6, 2 ≤ k.val → col k 0 = 0 ∧ col k 1 = 0) :
    (∀ y, f2Map M hM y 0 = y 0 ∧ f2Map M hM y 1 = y 1) ∧
      ∀ y : Fin 6 → ZMod 2, (∀ k : Fin 6, 2 ≤ k.val → y k = 0) → f2Map M hM y = y := by
  obtain ⟨c20, c21⟩ := h2 2 (by decide)
  obtain ⟨c30, c31⟩ := h2 3 (by decide)
  obtain ⟨c40, c41⟩ := h2 4 (by decide)
  obtain ⟨c50, c51⟩ := h2 5 (by decide)
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · rw [f2Map_eq_of_cols hM h]
    simp [Fin.sum_univ_six, h0, h1, c20, c21, c30, c31, c40, c41, c50, c51]
  · rw [f2Map_eq_of_cols hM h]
    have y2 := hy 2 (by decide)
    have y3 := hy 3 (by decide)
    have y4 := hy 4 (by decide)
    have y5 := hy 5 (by decide)
    funext i
    fin_cases i <;> simp [Fin.sum_univ_six, h0, h1, y2, y3, y4, y5]

theorem block_b3 (hM : f2Mat b3M = true) :
    (∀ y, f2Map b3M hM y 0 = y 0 ∧ f2Map b3M hM y 1 = y 1) ∧
      ∀ y : Fin 6 → ZMod 2, (∀ k : Fin 6, 2 ≤ k.val → y k = 0) → f2Map b3M hM y = y :=
  block_of_cols hM b3_cols (fun i => rfl) (fun i => rfl) (by decide)

theorem block_b5 (hM : f2Mat b5M = true) :
    (∀ y, f2Map b5M hM y 0 = y 0 ∧ f2Map b5M hM y 1 = y 1) ∧
      ∀ y : Fin 6 → ZMod 2, (∀ k : Fin 6, 2 ≤ k.val → y k = 0) → f2Map b5M hM y = y :=
  block_of_cols hM b5_cols (fun i => rfl) (fun i => rfl) (by decide)

end Sec3Lift

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem x_mem_nSHat : x ∈ nSHat Q₀ Q Zs := by
  have hxC : x ∈ centralizer (Zs : Set G) :=
    mem_centralizer_iff.mpr fun s hs => (H.x_comm_Zs hs).symm
  exact ⟨hxC, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (Sec2.mem_normalizer_inf (H.N_le_normalizer_F H.x_mem_N) (le_normalizer hxC))⟩

theorem exists_B₀ {γ : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt}
    (hγO : γ ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q) {k : ℕ} (hk : Odd k)
    (hγk : γ ^ k = 1) (hW₀ : ∀ v ∈ H.xsub.clSub Q₀, γ v = v)
    (hW' : ∀ v ∈ H.xsub.clSub Q, γ v ∈ H.xsub.clSub Q) :
    ∃ c ∈ B₀, ∃ hcN : c ∈ H.xsub.N, H.ρG ⟨c, hcN⟩ = γ := by
  have hmap : (H.xsub.clSub Q).map (γ : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq γ _)
    rintro _ ⟨v, hv, rfl⟩
    exact hW' v hv
  have hrO := resLE_mem_orthogonalGroup hγO hmap
  have hpow : ∀ j (w : ↥(H.xsub.clSub Q)),
      (((resLE (H.xsub.clSub Q) hmap ^ j) w : ↥(H.xsub.clSub Q)) : H.xsub.Qt) = (γ ^ j) w := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [pow_succ, LinearEquiv.mul_apply, ih, coe_resLE, pow_succ, LinearEquiv.mul_apply]
  have hrk : resLE (H.xsub.clSub Q) hmap ^ k = 1 :=
    LinearEquiv.ext fun w => Subtype.ext (by rw [hpow, hγk]; rfl)
  have hrΩ := Sec3Lift.mem_omegaGroup_of_pow_eq_one H.W'_nondegenerate hrO hk hrk
  rw [← H.range_resB₀] at hrΩ
  obtain ⟨c, hc⟩ := hrΩ
  refine ⟨c, c.2, H.B₀_le_N c.2, LinearEquiv.ext fun v => ?_⟩
  have hv : v ∈ H.xsub.clSub Q₀ ⊔ H.xsub.clSub Q := H.W₀_sup_W' ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, H.ρB₀_W₀ c.2 hu, hW₀ u hu]
  congr 1
  have h1 := H.coe_resB₀_apply c ⟨w, hw⟩
  rw [hc, coe_resLE] at h1
  exact h1.symm

end Sec38Hyp

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem coord_cl_e : Sec3Coord.coord H.xsub.q b (H.xsub.cl e) = 0 := by
  funext i
  rw [Sec3Coord.coord_apply, hT.frame_perp]
  rfl

omit hT in
theorem single_mem_N0 (i : Fin 6) : (Pi.single i 1 : Census.V₀) ∈ N0 := by
  rw [← Sec3Lift.epsF_single]
  exact epsF_mem_N0 _

theorem hN_eq_ofArr (n : ↥(nSHat Q₀ Q Zs)) (hnN : (n : G) ∈ H.xsub.N) {M : Array ℕ}
    (hM : f2Mat M = true) (hI : isomOK M = true)
    (hc : ∀ v, Sec3Coord.coord H.xsub.q b (H.ρG ⟨n, hnN⟩ v) =
      Sec3Lift.f2Map M hM (Sec3Coord.coord H.xsub.q b v)) :
    hT.hN n = ofArr M hI := by
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (linMap_ext fun i => ?_))
  have hmem := single_mem_N0 i
  rw [← hT.theta_image_U] at hmem
  obtain ⟨u, hu, hθ⟩ := hmem
  have hnU : (n : G) * u * (n : G)⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    (mem_normalizer_iff.mp (H.mem_normalizer_U hnN n.2.1) u).mp hu
  have hcl : H.xsub.cl ((n : G) * u * (n : G)⁻¹) = H.ρG ⟨n, hnN⟩ (H.xsub.cl u) :=
    (H.ρG_cl ⟨n, hnN⟩ hu.1).symm
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← hθ, hT.hN_theta n (H.U_le_SHat hT.hQF hu),
    ofArr_apply, hT.theta_U hnU, hT.theta_U hu, hcl, hc, Sec3Lift.epsF_f2Map hM]

theorem exists_lift_omega {γ : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt}
    (hγ : γ ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate) (hγa : γ (H.xsub.cl e) = H.xsub.cl e) :
    ∃ f ∈ nSHat Q₀ Q Zs, ∃ hfN : f ∈ H.xsub.N, H.ρG ⟨f, hfN⟩ = γ := by
  obtain ⟨f₀, hf₀⟩ := H.exists_F_of_omega hT.hΩ hγ
  obtain ⟨f', hf'C, hf'⟩ := H.exists_mem_centralizer_of_apply hT.hQF hT.hZQ hT.he hT.hez f₀
    (by rw [hf₀]; exact hγa)
  refine ⟨f', ⟨hf'C, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    (mem_inf.mpr ⟨f'.2, hf'C⟩)⟩, H.F_le_N f'.2, ?_⟩
  rw [← hf₀, ← hf']
  rfl

theorem ofArr_mem_range {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true) {k : ℕ}
    (hk : Odd k) (hpow : toLin M ^ k = 1) : ofArr M hI ∈ hT.hN.range := by
  set g := Sec3Lift.f2Equiv M hM hI with hg
  have hγO : Sec3Coord.gam hT.frame g ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q :=
    Sec3Coord.gam_mem_orthogonalGroup hT.frame fun y => Sec3Lift.qplus_f2Map hM hI y
  have hγk : Sec3Coord.gam hT.frame g ^ k = 1 := by
    rw [← map_pow, Sec3Lift.f2Equiv_pow_eq_one hM hI hpow, map_one]
  have hγΩ := Sec3Lift.mem_omegaGroup_of_pow_eq_one H.xsub.q_nondegenerate hγO hk hγk
  have hγa : Sec3Coord.gam hT.frame g (H.xsub.cl e) = H.xsub.cl e :=
    Sec3Coord.gam_apply_of_eq hT.frame (by rw [hT.coord_cl_e, map_zero])
  obtain ⟨f, hf, hfN, hρ⟩ := hT.exists_lift_omega hγΩ hγa
  refine ⟨⟨f, hf⟩, hT.hN_eq_ofArr ⟨f, hf⟩ hfN hM hI fun v => ?_⟩
  rw [hρ, Sec3Coord.coord_gam]
  rfl

theorem coord_ρx (hM : f2Mat x0M = true) (v : H.xsub.Qt) :
    Sec3Coord.coord H.xsub.q b (H.ρG ⟨x, H.x_mem_N⟩ v) =
      Sec3Lift.f2Map x0M hM (Sec3Coord.coord H.xsub.q b v) := by
  have hO : H.ρG ⟨x, H.x_mem_N⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q :=
    (H.xsub.ρ _).2
  have hpol : ∀ w, polar H.xsub.q (H.ρG ⟨x, H.x_mem_N⟩ v) (H.ρG ⟨x, H.x_mem_N⟩ w) =
      polar H.xsub.q v w :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO v
  obtain ⟨hx0, hx1⟩ := hT.frame_x
  have hb0 : H.ρG ⟨x, H.x_mem_N⟩ (b 0 + b 1) = b 0 := by
    rw [map_add, hx0, hx1, add_comm (b 0) (b 1), ← add_assoc, ZModModule.add_self, zero_add]
  have hk : ∀ k : Fin 6, 2 ≤ k.val → H.ρG ⟨x, H.x_mem_N⟩ (b k) = b k := fun k hk =>
    H.ρx_W' (hT.frame_W' k hk)
  rw [Sec3Lift.f2Map_x0]
  funext i
  fin_cases i
  · change polar H.xsub.q _ (b 1) = polar H.xsub.q v (b 0)
    rw [← hx0, hpol]
  · change polar H.xsub.q _ (b 0) = polar H.xsub.q v (b 1) + polar H.xsub.q v (b 0)
    conv_lhs => rw [← hb0]
    rw [hpol, polar_add_right, add_comm]
  · change polar H.xsub.q _ (b 3) = polar H.xsub.q v (b 3)
    conv_lhs => rw [← hk 3 (by decide)]
    rw [hpol]
  · change polar H.xsub.q _ (b 2) = polar H.xsub.q v (b 2)
    conv_lhs => rw [← hk 2 (by decide)]
    rw [hpol]
  · change polar H.xsub.q _ (b 5) = polar H.xsub.q v (b 5)
    conv_lhs => rw [← hk 5 (by decide)]
    rw [hpol]
  · change polar H.xsub.q _ (b 4) = polar H.xsub.q v (b 4)
    conv_lhs => rw [← hk 4 (by decide)]
    rw [hpol]

theorem exists_mul_mem_centralizer {c : G} (hcB : c ∈ B₀) (hcN : c ∈ H.xsub.N)
    (hca : H.ρG ⟨c, hcN⟩ (H.xsub.cl e) = H.xsub.cl e) :
    ∃ j ∈ Q, j * c ∈ centralizer (Zs : Set G) := by
  have heQ : e ∈ Q := hT.hZQ hT.he
  have heQ₁ : e ∈ H.xsub.Q₁ := H.Q_le heQ
  have hcl : H.xsub.cl (c * e * c⁻¹) = H.xsub.cl e := by
    rw [← H.ρG_cl ⟨c, hcN⟩ heQ₁]
    exact hca
  have h := (H.xsub.cl_eq_cl_iff heQ₁ (H.xsub.conj_mem hcN heQ₁)).mp hcl.symm
  have hzC : ∀ d ∈ B₀, d * z = z * d := fun d hd =>
    (mem_centralizer_iff.mp (H.B₀_le hd) z H.z_mem_Q₀).symm
  have hcen : ∀ d ∈ B₀, d * e = e * d → d ∈ centralizer (Zs : Set G) := by
    intro d hd hde
    refine mem_centralizer_iff.mpr fun s hs => ?_
    rcases hT.mem_cases hs with rfl | rfl | rfl | rfl
    · group
    · exact (hzC d hd).symm
    · exact hde.symm
    · rw [mul_assoc, ← hzC d hd, ← mul_assoc, ← hde, mul_assoc]
  rcases H.xsub.mem_zpowers_z_iff.mp h with h1 | h1
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    refine hcen c hcB ?_
    have h2 : c * e * c⁻¹ = e := by
      calc c * e * c⁻¹ = e * (e⁻¹ * (c * e * c⁻¹)) := by group
        _ = e := by rw [h1, mul_one]
    calc c * e = c * e * c⁻¹ * c := by group
      _ = e * c := by rw [h2]
  · have h2 : c * e * c⁻¹ = e * z := by
      calc c * e * c⁻¹ = e * (e⁻¹ * (c * e * c⁻¹)) := by group
        _ = e * z := by rw [show e⁻¹ * (c * e * c⁻¹) = z from h1]
    have heZ : e ∉ centerIn Q := by
      rw [H.q0.dData.suz.Q_center]
      exact hT.hez
    obtain ⟨j, hjQ, hj⟩ : ∃ j ∈ Q, j * e * j⁻¹ * e⁻¹ = z := by
      by_contra hcon
      push Not at hcon
      apply heZ
      refine ⟨heQ, mem_centralizer_iff.mpr fun j hjQ => ?_⟩
      have hm := H.commutator_mem_zpowers (H.Q_le hjQ) heQ₁
      rcases H.xsub.mem_zpowers_z_iff.mp hm with h3 | h3
      · rw [comm_eq_one_iff] at h3
        exact h3
      · exact absurd h3 (hcon j hjQ)
    refine ⟨j, hjQ, hcen (j * c) (mul_mem (H.B₀_quot.1 hjQ) hcB) ?_⟩
    have hje : j * e * j⁻¹ = z * e := by rw [← hj]; group
    have hzj : j * z = z * j := H.xsub.z_comm (H.Q_le hjQ)
    have hzz : z * z = 1 := H.xsub.z_mul_z
    calc j * c * e = j * (c * e * c⁻¹) * c := by group
      _ = j * e * j⁻¹ * (j * z) * c := by rw [h2]; group
      _ = z * e * (z * j) * c := by rw [hje, hzj]
      _ = e * (z * z) * j * c := by
        rw [show z * e = e * z from H.comm_of_mem_Zs H.z_mem_Zs hT.he]; group
      _ = e * (j * c) := by rw [hzz]; group

theorem vec_mem_W' {y : Fin 6 → ZMod 2} (h0 : y 0 = 0) (h1 : y 1 = 0) :
    Sec3Coord.vec b y ∈ H.xsub.clSub Q := by
  rw [Sec3Coord.vec_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  fin_cases i
  · change y 0 • b 0 ∈ _
    rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · change y 1 • b 1 ∈ _
    rw [h1, zero_smul]
    exact Submodule.zero_mem _
  all_goals exact Submodule.smul_mem _ _ (hT.frame_W' _ (by decide))

theorem exists_B₁ {M : Array ℕ} (hM : f2Mat M = true) (hI : isomOK M = true) {k : ℕ}
    (hk : Odd k) (hpow : toLin M ^ k = 1)
    (hblock : (∀ y, Sec3Lift.f2Map M hM y 0 = y 0 ∧ Sec3Lift.f2Map M hM y 1 = y 1) ∧
      ∀ y : Fin 6 → ZMod 2, (∀ k : Fin 6, 2 ≤ k.val → y k = 0) → Sec3Lift.f2Map M hM y = y) :
    ∃ c ∈ B₀ ⊓ centralizer (Zs : Set G), ∃ hc : c ∈ nSHat Q₀ Q Zs,
      hT.hN ⟨c, hc⟩ = ofArr M hI := by
  set g := Sec3Lift.f2Equiv M hM hI with hg
  set γ := Sec3Coord.gam hT.frame g with hγ
  have hγO : γ ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q :=
    Sec3Coord.gam_mem_orthogonalGroup hT.frame fun y => Sec3Lift.qplus_f2Map hM hI y
  have hγk : γ ^ k = 1 := by rw [hγ, ← map_pow, Sec3Lift.f2Equiv_pow_eq_one hM hI hpow, map_one]
  have hπ : ∀ i : Fin 6, 2 ≤ i.val → 2 ≤ (Sec3Coord.piF i).val := by decide
  have hW₀ : ∀ v ∈ H.xsub.clSub Q₀, γ v = v := by
    intro v hv
    refine Sec3Coord.gam_apply_of_eq hT.frame (hblock.2 _ fun i hi => ?_)
    rw [Sec3Coord.coord_apply]
    exact H.polar_W₀_W' hv (hT.frame_W' _ (hπ i hi))
  have hW' : ∀ v ∈ H.xsub.clSub Q, γ v ∈ H.xsub.clSub Q := by
    intro v hv
    have h0 : Sec3Coord.coord H.xsub.q b v 0 = 0 := by
      rw [Sec3Coord.coord_apply, polar_comm]
      exact H.polar_W₀_W' hT.frame_W₀.2 hv
    have h1 : Sec3Coord.coord H.xsub.q b v 1 = 0 := by
      rw [Sec3Coord.coord_apply, polar_comm]
      exact H.polar_W₀_W' hT.frame_W₀.1 hv
    rw [hγ, Sec3Coord.gam_apply]
    refine Submodule.sub_mem _ (Submodule.add_mem _ hv (hT.vec_mem_W' ?_ ?_))
      (hT.vec_mem_W' h0 h1)
    · rw [Sec3Lift.f2Equiv_apply, (hblock.1 _).1, h0]
    · rw [Sec3Lift.f2Equiv_apply, (hblock.1 _).2, h1]
  obtain ⟨c, hcB, hcN, hρc⟩ := H.exists_B₀ hγO hk hγk hW₀ hW'
  have hca : H.ρG ⟨c, hcN⟩ (H.xsub.cl e) = H.xsub.cl e := by
    rw [hρc, hγ]
    exact Sec3Coord.gam_apply_of_eq hT.frame (by rw [hT.coord_cl_e, map_zero])
  obtain ⟨j, hjQ, hjc⟩ := hT.exists_mul_mem_centralizer hcB hcN hca
  have hjcB : j * c ∈ B₀ := mul_mem (H.B₀_quot.1 hjQ) hcB
  have hjcN : j * c ∈ H.xsub.N := H.B₀_le_N hjcB
  have hjcS : j * c ∈ nSHat Q₀ Q Zs := ⟨hjc, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    (mem_inf.mpr ⟨H.B₀_le_F hjcB, hjc⟩)⟩
  have hρ : H.ρG ⟨j * c, hjcN⟩ = γ := by
    have hj1 : H.ρG ⟨j, H.xsub.le_N (H.Q_le hjQ)⟩ = 1 :=
      (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (g := ⟨j, _⟩) (H.Q_le hjQ))
    have e1 : (⟨j * c, hjcN⟩ : H.xsub.N) = ⟨j, H.xsub.le_N (H.Q_le hjQ)⟩ * ⟨c, hcN⟩ := rfl
    rw [e1, map_mul, hj1, one_mul, hρc]
  refine ⟨j * c, ⟨hjcB, hjc⟩, hjcS, hT.hN_eq_ofArr ⟨j * c, hjcS⟩ hjcN hM hI fun v => ?_⟩
  change Sec3Coord.coord H.xsub.q b (H.ρG ⟨j * c, hjcN⟩ v) = _
  rw [hρ, hγ, Sec3Coord.coord_gam]
  rfl

section Census

theorem G1_mem_range : G1 ∈ hT.hN.range :=
  hT.ofArr_mem_range f2_g1 isom_g1 (by decide) Sec3Lift.toLin_g1_pow

theorem G2_mem_range : G2 ∈ hT.hN.range :=
  hT.ofArr_mem_range f2_g2 isom_g2 (by decide) Sec3Lift.toLin_g2_pow

theorem hN_x : hT.hN ⟨x, H.x_mem_nSHat⟩ = X0 :=
  hT.hN_eq_ofArr ⟨x, H.x_mem_nSHat⟩ H.x_mem_N f2_x0 isom_x0 (hT.coord_ρx f2_x0)

theorem exists_B3 : ∃ c ∈ B₀ ⊓ centralizer (Zs : Set G), ∃ hc : c ∈ nSHat Q₀ Q Zs,
    hT.hN ⟨c, hc⟩ = B3 :=
  hT.exists_B₁ f2_b3 isom_b3 (by decide) Sec3Lift.toLin_b3_pow (Sec3Lift.block_b3 f2_b3)

theorem exists_B5 : ∃ c ∈ B₀ ⊓ centralizer (Zs : Set G), ∃ hc : c ∈ nSHat Q₀ Q Zs,
    hT.hN ⟨c, hc⟩ = B5 :=
  hT.exists_B₁ f2_b5 isom_b5 (by decide) Sec3Lift.toLin_b5_pow (Sec3Lift.block_b5 f2_b5)

end Census

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81
