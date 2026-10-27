module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourNonInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFusion
public import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

section Coords

@[expose] def e6InnerCoords (x : Fin Tag.E6.rank → ZMod 3) : Fin 5 → ZMod 3 :=
  ![2 * x 0 - (2 * x 3 - (2 * x 1 - (2 * x 4 - 2 * x 5)) - (2 * x 4 - 2 * x 5) - 2 * x 5),
    2 * x 1 - (2 * x 4 - 2 * x 5),
    2 * x 3 - (2 * x 1 - (2 * x 4 - 2 * x 5)) - (2 * x 4 - 2 * x 5) - 2 * x 5,
    2 * x 4 - 2 * x 5,
    2 * x 5]

theorem e6InnerCoords_key : ∀ a b c d e f : ZMod 3, a + 2 * c + e + 2 * f = 0 →
    let y0 := 2 * a - (2 * d - (2 * b - (2 * e - 2 * f)) - (2 * e - 2 * f) - 2 * f)
    let y1 := 2 * b - (2 * e - 2 * f)
    let y2 := 2 * d - (2 * b - (2 * e - 2 * f)) - (2 * e - 2 * f) - 2 * f
    let y3 := 2 * e - 2 * f
    let y4 := 2 * f
    y0 * 2 + y1 * 0 + y2 * 2 + y3 * 0 + y4 * 0 = a ∧
      y0 * 0 + y1 * 2 + y2 * 0 + y3 * 2 + y4 * 0 = b ∧
      y0 * 2 + y1 * 0 + y2 * 2 + y3 * 2 + y4 * 0 = c ∧
      y0 * 0 + y1 * 2 + y2 * 2 + y3 * 2 + y4 * 2 = d ∧
      y0 * 0 + y1 * 0 + y2 * 0 + y3 * 2 + y4 * 2 = e ∧
      y0 * 0 + y1 * 0 + y2 * 0 + y3 * 0 + y4 * 2 = f := by
  decide


theorem subLin_e6InnerCoords {x : Fin Tag.E6.rank → ZMod 3}
    (hx : x 0 + 2 * x 2 + x 4 + 2 * x 5 = 0) :
    subLin (τ := .E6) e6InnerVec (e6InnerCoords x) = x := by
  obtain ⟨a0, a1, a2, a3, a4⟩ : e6InnerVec 0 0 = 2 ∧ e6InnerVec 1 0 = 0 ∧
      e6InnerVec 2 0 = 2 ∧ e6InnerVec 3 0 = 0 ∧ e6InnerVec 4 0 = 0 := by decide
  obtain ⟨b0, b1, b2, b3, b4⟩ : e6InnerVec 0 1 = 0 ∧ e6InnerVec 1 1 = 2 ∧
      e6InnerVec 2 1 = 0 ∧ e6InnerVec 3 1 = 2 ∧ e6InnerVec 4 1 = 0 := by decide
  obtain ⟨c0, c1, c2, c3, c4⟩ : e6InnerVec 0 2 = 2 ∧ e6InnerVec 1 2 = 0 ∧
      e6InnerVec 2 2 = 2 ∧ e6InnerVec 3 2 = 2 ∧ e6InnerVec 4 2 = 0 := by decide
  obtain ⟨d0, d1, d2, d3, d4⟩ : e6InnerVec 0 3 = 0 ∧ e6InnerVec 1 3 = 2 ∧
      e6InnerVec 2 3 = 2 ∧ e6InnerVec 3 3 = 2 ∧ e6InnerVec 4 3 = 2 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ : e6InnerVec 0 4 = 0 ∧ e6InnerVec 1 4 = 0 ∧
      e6InnerVec 2 4 = 0 ∧ e6InnerVec 3 4 = 2 ∧ e6InnerVec 4 4 = 2 := by decide
  obtain ⟨g0, g1, g2, g3, g4⟩ : e6InnerVec 0 5 = 0 ∧ e6InnerVec 1 5 = 0 ∧
      e6InnerVec 2 5 = 0 ∧ e6InnerVec 3 5 = 0 ∧ e6InnerVec 4 5 = 2 := by decide
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ :=
    e6InnerCoords_key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) hx
  have v0 : e6InnerCoords x 0 = 2 * x 0 - (2 * x 3 - (2 * x 1 - (2 * x 4 - 2 * x 5)) -
      (2 * x 4 - 2 * x 5) - 2 * x 5) := rfl
  have v1 : e6InnerCoords x 1 = 2 * x 1 - (2 * x 4 - 2 * x 5) := rfl
  have v2 : e6InnerCoords x 2 = 2 * x 3 - (2 * x 1 - (2 * x 4 - 2 * x 5)) -
      (2 * x 4 - 2 * x 5) - 2 * x 5 := rfl
  have v3 : e6InnerCoords x 3 = 2 * x 4 - 2 * x 5 := rfl
  have v4 : e6InnerCoords x 4 = 2 * x 5 := rfl
  funext j
  rw [subLin_e6InnerVec_apply, v0, v1, v2, v3, v4]
  fin_cases j
  · rw [show ((⟨0, by decide⟩ : Fin Tag.E6.rank)) = 0 from rfl, a0, a1, a2, a3, a4]
    exact k0
  · rw [show ((⟨1, by decide⟩ : Fin Tag.E6.rank)) = 1 from rfl, b0, b1, b2, b3, b4]
    exact k1
  · rw [show ((⟨2, by decide⟩ : Fin Tag.E6.rank)) = 2 from rfl, c0, c1, c2, c3, c4]
    exact k2
  · rw [show ((⟨3, by decide⟩ : Fin Tag.E6.rank)) = 3 from rfl, d0, d1, d2, d3, d4]
    exact k3
  · rw [show ((⟨4, by decide⟩ : Fin Tag.E6.rank)) = 4 from rfl, f0, f1, f2, f3, f4]
    exact k4
  · rw [show ((⟨5, by decide⟩ : Fin Tag.E6.rank)) = 5 from rfl, g0, g1, g2, g3, g4]
    exact k5

theorem exists_subLin_eq_of_rootChar {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : rootChar (torV ω x) e6Omega3 = 1) :
    ∃ y : Fin 5 → ZMod 3, subLin (τ := .E6) e6InnerVec y = x := by
  refine ⟨e6InnerCoords x, subLin_e6InnerCoords ?_⟩
  rw [rootChar_torV, ← orderOf_dvd_iff_zpow_eq_one, hω] at hx
  have h3 : ((∑ i, ((x i).val : ℤ) * e6Omega3 i : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hx)
  rw [Int.cast_sum] at h3
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  have h3' : ∑ i : Fin 6, x i * ((e6Omega3 i : ℤ) : ZMod 3) = 0 := h3
  rw [Fin.sum_univ_six] at h3'
  have e0 : ((e6Omega3 (0 : Fin 6) : ℤ) : ZMod 3) = 1 := by decide
  have e1 : ((e6Omega3 (1 : Fin 6) : ℤ) : ZMod 3) = 0 := by decide
  have e2 : ((e6Omega3 (2 : Fin 6) : ℤ) : ZMod 3) = 2 := by decide
  have e3 : ((e6Omega3 (3 : Fin 6) : ℤ) : ZMod 3) = 0 := by decide
  have e4 : ((e6Omega3 (4 : Fin 6) : ℤ) : ZMod 3) = 1 := by decide
  have e5 : ((e6Omega3 (5 : Fin 6) : ℤ) : ZMod 3) = 2 := by decide
  rw [e0, e1, e2, e3, e4, e5] at h3'
  have key : ∀ a b c d e f : ZMod 3, a * 1 + b * 0 + c * 2 + d * 0 + e * 1 + f * 2 = 0 →
      a + 2 * c + e + 2 * f = 0 := by
    decide
  exact key _ _ _ _ _ _ h3'

end Coords

section TorusK


variable {K : Type} [Field K]

theorem subLin_smul_E6 (n : ℕ) (y : Fin 5 → ZMod 3) :
    subLin (τ := .E6) e6InnerVec (n • y) = n • subLin (τ := .E6) e6InnerVec y := by
  simp only [subLin, Pi.smul_apply, Finset.smul_sum, smul_assoc]

theorem subLin_e6InnerVec_col5 :
    subLin (τ := .E6) e6InnerVec ![1, 0, 2, 0, 1] =
      fun j => ((Tag.E6.cartan ⟨5, by decide⟩ j : ℤ) : ZMod 3) := by
  funext j
  rw [subLin_e6InnerVec_apply]
  fin_cases j <;> decide

theorem exists_subLin_torusElt {ω : Kˣ} (hω : ω ^ 3 = 1) (i : Fin Tag.E6.rank) :
    ∃ y : Fin 5 → ZMod 3, torusElt Tag.E6 K i ω = dV ω (subLin (τ := .E6) e6InnerVec y) := by
  by_cases hi : i.val < 5
  · refine ⟨Pi.single ⟨i.val, hi⟩ 1, ?_⟩
    rw [subLin_single, dV_e6InnerVec hω]
  · have hi5 : i = ⟨5, by decide⟩ := by
      have := i.2
      ext
      change i.val = 5
      have : i.val < 6 := this
      omega
    subst hi5
    refine ⟨![1, 0, 2, 0, 1], ?_⟩
    rw [subLin_e6InnerVec_col5, torusElt_eq_rootDiagUnit, dV]
    congr 1
    funext j
    rw [torV, zpow_val_intCast hω]

theorem exists_subLin_of_mem_torusGroup [Finite K] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {g : ModGL Tag.E6 K} (hg : g ∈ torusGroup Tag.E6 K) :
    ∃ y : Fin 5 → ZMod 3, g = dV ω (subLin (τ := .E6) e6InnerVec y) := by
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, μ⟩, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := exists_eq_pow hK hω μ
    obtain ⟨y, hy⟩ := exists_subLin_torusElt hω3 i
    refine ⟨m • y, ?_⟩
    change torusElt Tag.E6 K i (ω ^ m) = _
    rw [← torusElt_pow', hy, subLin_smul_E6, dV_nsmul hω3]
  | one => exact ⟨0, by rw [subLin_zero, dV_zero]⟩
  | mul x x' _ _ ihx ihx' =>
    obtain ⟨y, rfl⟩ := ihx
    obtain ⟨y', rfl⟩ := ihx'
    exact ⟨y + y', by rw [subLin_add, dV_add hω3]⟩
  | inv x _ ihx =>
    obtain ⟨y, rfl⟩ := ihx
    refine ⟨2 • y, ?_⟩
    rw [subLin_smul_E6, dV_nsmul hω3]
    have h3 : dV ω (subLin (τ := .E6) e6InnerVec y) ^ 3 = 1 := by
      rw [← dV_nsmul hω3]
      have h : (3 • subLin (τ := .E6) e6InnerVec y) = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have : (3 : ZMod 3) = 0 := rfl
        rw [Nat.cast_ofNat, this, zero_mul]
      rw [h, dV_zero]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)).symm

end TorusK

section BaseChange


theorem baseChangeGL_mem_toralRootGroup {τ : Tag} {k k' : Type} [Field k] [Field k']
    (ι : k →+* k') {a : Fin τ.rank → kˣ} {g : ModGL τ k} (hg : g ∈ toralRootGroup τ k a) :
    baseChangeGL ι g ∈ toralRootGroup τ k' (fun i => Units.map ι.toMonoidHom (a i)) := by
  have hle : toralRootGroup τ k a ≤ (toralRootGroup τ k'
      (fun i => Units.map ι.toMonoidHom (a i))).comap (baseChangeGL ι) := by
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact Subgroup.mem_sup_left (torusElt_mem_torusGroup _ _)
    · refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_pinnedX]
      refine Subgroup.mem_sup_right ?_
      refine le_iSup₂_of_le (f := fun β (_ : β ∈ rootCharKernel
        (fun i => Units.map ι.toMonoidHom (a i))) => rootSubgroup τ k' β) γ ⟨hγ.1, ?_⟩ le_rfl
        (Subgroup.subset_closure ⟨ι c, rfl⟩)
      rw [rootChar_map_tuple, hγ.2, map_one]
  exact hle hg

end BaseChange

section Descent


theorem exists_rootDiagUnit_mul_of_frobenius_fixed {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hbij : Function.Bijective Fr) {g : ModGL Tag.E6 L} (hg : g ∈ adjointGroup Tag.E6 L)
    (hfix : Units.map (entrywiseHom Fr) g = g) :
    ∃ b : Fin Tag.E6.rank → Kˣ, ∃ j ∈ adjointGroup Tag.E6 K,
      g = baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E6 b * j) := by
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap K L) := fun c hc =>
    CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hg' : g ∈ entrywiseFixedGroup Tag.E6 σ := ⟨hg, by
    change Units.map (entrywiseHom σ.toRingHom) g = g
    rw [hσ]
    exact hfix⟩
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
  obtain ⟨hhT, -, hhF⟩ := hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hbσ : (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) = b := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← baseChangeGL_rootDiagUnit, ← units_map_entrywiseHom_eq_baseChangeGL]
    exact hhF
  have hbK : ∀ i, ∃ c : Kˣ, Units.map (algebraMap K L).toMonoidHom c = b i := by
    intro i
    obtain ⟨c, hc⟩ := hσfix (b i : L) (by
      have := congrArg Units.val (congrFun hbσ i)
      simpa using this)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (b i).ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩
  choose bK hbK using hbK
  have hjK : j ∈ (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) := by
    rw [fixedFieldImage_eq_closure] at hj
    refine (Subgroup.closure_le _).2 ?_ hj
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨xUnit Tag.E6 K i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨yUnit Tag.E6 K i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩
  obtain ⟨jK, hjKC, rfl⟩ := hjK
  refine ⟨bK, jK, hjKC, ?_⟩
  rw [map_mul, baseChangeGL_rootDiagUnit]
  congr 2
  funext i
  exact (hbK i).symm

end Descent

section InnerLift


variable {K : Type} [Field K]

@[expose] noncomputable def e6InnerParam (ω : Kˣ) (y : Fin 5 → ZMod 3) :
    Fin Tag.E6.rank → Kˣ :=
  ((List.finRange 5).map fun i =>
    (Pi.mulSingle (⟨i.val, by have := i.2; decide +revert⟩ : Fin Tag.E6.rank) ω) ^
      (y i).val).prod

theorem e6RootParams_e6InnerParam [Finite K] {ω : Kˣ} (hω : ω ^ 3 = 1) (y : Fin 5 → ZMod 3) :
    e6RootParams (e6InnerParam ω y) = torV ω (subLin (τ := .E6) e6InnerVec y) := by
  apply rootDiagUnit_injective (τ := .E6) (K := K)
  obtain ⟨π', hπ'⟩ : ∃ π' : (Fin Tag.E6.rank → Kˣ) →* ModGL Tag.E6 K,
      π' = (adjointGroup Tag.E6 K).subtype.comp ((e6Isogeny K).comp
        (minTorus e6Data_valid K)) := ⟨_, rfl⟩
  have hπu : ∀ u, π' u = rootDiagUnit Tag.E6 (e6RootParams u) := fun u => by
    rw [hπ']
    exact e6Isogeny_minTorus u
  have hπs : ∀ i : Fin 5, π' (Pi.mulSingle (⟨i.val, by have := i.2; decide +revert⟩ :
      Fin Tag.E6.rank) ω) = dV ω (e6InnerVec i) := fun i => by
    rw [hπ', dV_e6InnerVec hω]
    change ((e6Isogeny K (minTorus e6Data_valid K (Pi.mulSingle _ ω)) :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = _
    rw [minTorus_mulSingle, e6Isogeny_hm_eq, ← torusElt_eq_rootDiagUnit]
  have h2 : π' (e6InnerParam ω y) = dV ω (subLin (τ := .E6) e6InnerVec y) := by
    rw [e6InnerParam, map_list_prod, List.map_map, dV_subLin hω]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [Function.comp_apply, map_pow, hπs]
  rw [← hπu, h2]
  rfl

theorem e6RootParams_map {k k' : Type} [Field k] [Field k'] (ι : k →+* k')
    (u : Fin Tag.E6.rank → kˣ) :
    e6RootParams (fun l => Units.map ι.toMonoidHom (u l)) =
      fun j => Units.map ι.toMonoidHom (e6RootParams u j) := by
  funext j
  simp only [e6RootParams, map_prod, map_zpow]

end InnerLift

section Frob

theorem conj_comm_of_frobenius {G : Type*} [Group G] (F : G →* G) {y T z s : G}
    (hs : s = y * T * y⁻¹ * z) (hFs : F s = s) (hFT : F T = T) (hFz : F z = z) :
    (y⁻¹ * F y) * T = T * (y⁻¹ * F y) := by
  have e2 : F s = F y * T * (F y)⁻¹ * z := by
    rw [hs, map_mul, map_mul, map_mul, map_inv, hFT, hFz]
  rw [hFs, hs] at e2
  have e3 : y * T * y⁻¹ = F y * T * (F y)⁻¹ := mul_right_cancel e2
  calc (y⁻¹ * F y) * T = y⁻¹ * (F y * T * (F y)⁻¹) * F y := by group
    _ = y⁻¹ * (y * T * y⁻¹) * F y := by rw [e3]
    _ = T * (y⁻¹ * F y) := by group

end Frob

section InnerLang


variable {K : Type} [Field K] [Finite K]

theorem lang_cocycle_mem_toralRootGroup_inner [CharP K 2] [CharP (AlgebraicClosure K) 2]
    [Fact (Nat.Prime 2)] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {s : ModGL Tag.E6 K} (hs : s ∈ adjointGroup Tag.E6 K)
    (y₀ : Fin 5 → ZMod 3) {y : ModGL Tag.E6 (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hsy : baseChangeGL (algebraMap K (AlgebraicClosure K)) s =
      y * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (dV ω (subLin (τ := .E6) e6InnerVec y₀)) * y⁻¹) :
    y⁻¹ * entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 2 y ∈
      toralRootGroup Tag.E6 (AlgebraicClosure K) (fun i =>
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
          (torV ω (subLin (τ := .E6) e6InnerVec y₀) i)) := by
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  obtain ⟨Ey, hEy⟩ := exists_finset_descent hy
  obtain ⟨K₃, hK₃, hEK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K) Ey
  have : Finite K₃ := hK₃
  have : CharP K₃ 2 := Subfield.charP K₃ 2
  obtain ⟨y₃, hy₃C, hy₃⟩ := hEy K₃ hEK₃
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃,
      K₃.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) :=
    ⟨(algebraMap K (AlgebraicClosure K)).codRestrict K₃ fun c => hιK₃ ⟨c, rfl⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨Fr₃, hFr₃def⟩ : ∃ Fr₃ : K₃ →+* K₃, Fr₃ = iterateFrobenius K₃ 2 2 := ⟨_, rfl⟩
  have hFr₃ : ∀ c, Fr₃ c = c ^ 4 := fun c => by
    rw [hFr₃def, iterateFrobenius_def]
    norm_num
  have hFrι : Fr₃.comp ι₃ = ι₃ := by
    have : Fintype K := Fintype.ofFinite K
    ext c
    rw [RingHom.comp_apply, hFr₃, ← map_pow]
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    rw [h]
  have hFrL : K₃.subtype.comp Fr₃ = (iterateFrobenius (AlgebraicClosure K) 2 2).comp
      K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hFr₃, iterateFrobenius_def]
    norm_num
  have hbcinj : Function.Injective (baseChangeGL (τ := Tag.E6) K₃.subtype) :=
    baseChangeGL_injective K₃.subtype
  have hbcι : ∀ g : ModGL Tag.E6 K, baseChangeGL K₃.subtype (baseChangeGL ι₃ g) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) g := fun g => by
    rw [baseChangeGL_baseChangeGL, hιι]
  obtain ⟨d₃, hd₃⟩ : ∃ d, d = baseChangeGL ι₃ (dV ω (subLin (τ := .E6) e6InnerVec y₀)) :=
    ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s', s' = baseChangeGL ι₃ s := ⟨_, rfl⟩
  have hs₃y : s₃ = y₃ * d₃ * y₃⁻¹ := by
    apply hbcinj
    rw [map_mul, map_mul, map_inv, hy₃, hd₃, hs₃, hbcι, hbcι]
    exact hsy
  have hF₃bc : ∀ g : ModGL Tag.E6 K₃, Units.map (entrywiseHom Fr₃) g = baseChangeGL Fr₃ g :=
    fun g => units_map_entrywiseHom_eq_baseChangeGL Fr₃ g
  obtain ⟨c₃, hc₃⟩ : ∃ c, c = y₃⁻¹ * Units.map (entrywiseHom Fr₃) y₃ := ⟨_, rfl⟩
  have hc₃L : baseChangeGL K₃.subtype c₃ =
      y⁻¹ * entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 2 y := by
    rw [hc₃, map_mul, map_inv, hy₃]
    congr 1
    rw [← hy₃]
    exact (units_map_entrywiseHom_baseChangeGL K₃.subtype
      (iterateFrobenius (AlgebraicClosure K) 2 2) Fr₃ hFrL.symm y₃).symm
  have hF₃d : Units.map (entrywiseHom Fr₃) d₃ = d₃ := by
    rw [hF₃bc, hd₃, baseChangeGL_baseChangeGL, hFrι]
  have hF₃s : Units.map (entrywiseHom Fr₃) s₃ = s₃ := by
    rw [hF₃bc, hs₃, baseChangeGL_baseChangeGL, hFrι]
  have hF₃y₃ : Units.map (entrywiseHom Fr₃) y₃ ∈ adjointGroup Tag.E6 K₃ := by
    rw [hF₃bc]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup Fr₃ hy₃C
  obtain ⟨a₃, ha₃⟩ : ∃ a : Fin Tag.E6.rank → K₃ˣ,
      a = fun i => Units.map ι₃.toMonoidHom (torV ω (subLin (τ := .E6) e6InnerVec y₀) i) :=
    ⟨_, rfl⟩
  have hd₃a : d₃ = rootDiagUnit Tag.E6 a₃ := by
    rw [hd₃, dV, baseChangeGL_rootDiagUnit, ha₃]
  have hc₃d : c₃ * d₃ = d₃ * c₃ := by
    have h1 : Units.map (entrywiseHom Fr₃) y₃ * d₃ * (Units.map (entrywiseHom Fr₃) y₃)⁻¹ =
        y₃ * d₃ * y₃⁻¹ := by
      rw [← hs₃y, ← hF₃s, hs₃y, map_mul, map_mul, map_inv, hF₃d]
    have h2 : c₃ * d₃ * c₃⁻¹ = d₃ := by
      calc c₃ * d₃ * c₃⁻¹ = y₃⁻¹ * (Units.map (entrywiseHom Fr₃) y₃ * d₃ *
            (Units.map (entrywiseHom Fr₃) y₃)⁻¹) * y₃ := by rw [hc₃]; group
        _ = y₃⁻¹ * (y₃ * d₃ * y₃⁻¹) * y₃ := by rw [h1]
        _ = d₃ := by group
    rw [← mul_inv_eq_iff_eq_mul.1 h2]
  have hc₃C : c₃ ∈ toralCentralizer Tag.E6 K₃ a₃ := by
    refine mem_toralCentralizer.2 ⟨by rw [hc₃]; exact mul_mem (inv_mem hy₃C) hF₃y₃, ?_⟩
    rw [← hd₃a]
    calc d₃ * c₃ * d₃⁻¹ = c₃ * d₃ * d₃⁻¹ := by rw [hc₃d]
      _ = c₃ := by group
  obtain ⟨w, hw, h₃, hh₃, u₃, hu₃, v₃, hv₃, hdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 K₃ a₃).1 c₃ hc₃C
  obtain ⟨u₀₃, hu₀₃⟩ : ∃ u : Fin Tag.E6.rank → K₃ˣ,
      u = fun l => Units.map ι₃.toMonoidHom (e6InnerParam ω y₀ l) := ⟨_, rfl⟩
  have hu₀₃a : e6RootParams u₀₃ = a₃ := by
    rw [hu₀₃, e6RootParams_map, e6RootParams_e6InnerParam hω3, ha₃]
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid K₃ u₀₃ := ⟨_, rfl⟩
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup K₃ →* ModGL Tag.E6 K₃,
      π = (adjointGroup Tag.E6 K₃).subtype.comp (e6Isogeny K₃) := ⟨_, rfl⟩
  have hπ₃a : ∀ g, π₃ g = ((e6Isogeny K₃ g : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) :=
    fun g => by rw [hπ₃]; rfl
  have hπT : π₃ T = d₃ := by
    rw [hπ₃a, hT, hd₃a, ← hu₀₃a]
    exact e6Isogeny_minTorus u₀₃
  obtain ⟨yl, hyl⟩ := e6Isogeny_surjective K₃ ⟨y₃, hy₃C⟩
  have hπy : π₃ yl = y₃ := by
    rw [hπ₃a, hyl]
  obtain ⟨sl, hsl⟩ := e6Isogeny_surjective K ⟨s, hs⟩
  obtain ⟨sl₃, hsl₃⟩ : ∃ g, g = minBC e6Data_valid ι₃ sl := ⟨_, rfl⟩
  have hπs : π₃ sl₃ = s₃ := by
    rw [hπ₃a, hsl₃, e6Isogeny_minBC, hsl, hs₃]
  obtain ⟨z₀, hz₀⟩ : ∃ z, z = (yl * T * yl⁻¹)⁻¹ * sl₃ := ⟨_, rfl⟩
  have hz₀c : z₀ ∈ Subgroup.center (e6Data_valid.minGroup K₃) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [← hπ₃a, hz₀, map_mul, map_inv, map_mul, map_mul, map_inv, hπy, hπT, hπs, hs₃y]
    group
  have hsT : sl₃ = yl * T * yl⁻¹ * z₀ := by
    rw [hz₀]
    group
  obtain ⟨Fl, hFl⟩ : ∃ F : e6Data_valid.minGroup K₃ →* e6Data_valid.minGroup K₃,
      F = minBC e6Data_valid Fr₃ := ⟨_, rfl⟩
  have hFls : Fl sl₃ = sl₃ := by
    rw [hFl, hsl₃, minBC_minBC_E6, hFrι]
  have hFlT : Fl T = T := by
    rw [hFl, hT, minBC_minTorus_E6]
    congr 1
    funext l
    rw [hu₀₃]
    apply Units.ext
    change Fr₃ (ι₃ ((e6InnerParam ω y₀ l : Kˣ) : K)) = ι₃ ((e6InnerParam ω y₀ l : Kˣ) : K)
    exact RingHom.congr_fun hFrι _
  have hFlz : Fl z₀ = z₀ := by
    obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hz₀c
    rw [hv, hFl, minBC_minTorus_E6]
    congr 1
    funext l
    apply Units.ext
    change Fr₃ ((v l : K₃ˣ) : K₃) = ((v l : K₃ˣ) : K₃)
    rw [hFr₃]
    have h := congrArg Units.val (hv3 l)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [pow_succ, h, one_mul]
  have hπFy : π₃ (Fl yl) = Units.map (entrywiseHom Fr₃) y₃ := by
    rw [hπ₃a, hFl, e6Isogeny_minBC, hF₃bc, hyl]
  have hcomm := conj_comm_of_frobenius Fl hsT hFls hFlT hFlz
  have hπc : π₃ (yl⁻¹ * Fl yl) = c₃ := by
    rw [map_mul, map_inv, hπy, hπFy, hc₃]
  have hdec' : ((e6Isogeny K₃ (yl⁻¹ * Fl yl) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      h₃ * u₃ * canonicalRep (coxeterSystem Tag.E6) K₃ w * v₃ := by
    rw [← hπ₃a, hπc, hdec]
  have hw' : w ∈ rootCharStabilizer (e6RootParams u₀₃) := by rw [hu₀₃a]; exact hw
  have hcomm' : (yl⁻¹ * Fl yl) * minTorus e6Data_valid K₃ u₀₃ =
      minTorus e6Data_valid K₃ u₀₃ * (yl⁻¹ * Fl yl) := by
    rw [← hT]
    exact hcomm
  have hshift := rootChar_e6Shift_of_commute_lift u₀₃ hcomm' hh₃
    (by rw [hu₀₃a]; exact rootSpan_mono Set.inter_subset_left hu₃)
    (by rw [hu₀₃a]; exact rootSpan_mono Set.inter_subset_left hv₃) hdec' hw'
  rw [hu₀₃a] at hshift
  have ha₃3 : ∀ i, a₃ i ^ 3 = 1 := fun i => by
    rw [ha₃, ← map_pow, torV, ← pow_mul, mul_comm, pow_mul, hω3, one_pow, map_one]
  have hwS : w ∈ kernelReflectionGroup a₃ :=
    mem_kernelReflectionGroup_of_e6Shift a₃ ha₃3 hw hshift
  have hnM : canonicalRep (coxeterSystem Tag.E6) K₃ w ∈ toralRootGroup Tag.E6 K₃ a₃ := by
    have hk := kernelReflectionGroup_le_ker (K := K₃) a₃
      (show (⟨w, hw⟩ : rootCharStabilizerSubgroup a₃) ∈
        (kernelReflectionGroup a₃).subgroupOf (rootCharStabilizerSubgroup a₃) from hwS)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hk
    exact hk
  have hc₃M : c₃ ∈ toralRootGroup Tag.E6 K₃ a₃ := by
    rw [hdec]
    exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh₃)
      (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu₃))) hnM)
      (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv₃))
  have hM := baseChangeGL_mem_toralRootGroup K₃.subtype hc₃M
  rw [hc₃L] at hM
  convert hM using 2
  funext i
  rw [ha₃]
  apply Units.ext
  change (algebraMap K (AlgebraicClosure K)) ((torV ω (subLin (τ := .E6) e6InnerVec y₀) i :
    Kˣ) : K) = K₃.subtype (ι₃ ((torV ω (subLin (τ := .E6) e6InnerVec y₀) i : Kˣ) : K))
  rw [← RingHom.comp_apply, hιι]

end InnerLang

section Fusion


variable {K : Type} [Field K] [Finite K]

theorem exists_conj_dE6_four (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    {s : ModGL Tag.E6 K} (hs : s ∈ adjointGroup Tag.E6 K) (hs3 : s ^ 3 = 1) :
    ∃ c ∈ adjointGroup Tag.E6 K, ∃ y : Fin 5 → ZMod 3,
      c * s * c⁻¹ = dV ω (subLin (τ := .E6) e6InnerVec y) := by
  have : CharP K 2 := charP_two_of_card_four hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  obtain ⟨sL, hsL⟩ : ∃ g, g = baseChangeGL (algebraMap K (AlgebraicClosure K)) s := ⟨_, rfl⟩
  have hsLG : sL ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hsL]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hs
  have hsL3 : sL ^ 3 = 1 := by rw [hsL, ← map_pow, hs3, map_one]
  have hfin : ((Subgroup.zpowers sL : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
      Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hsL3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers sL, x ^ 3 = 1 := by
    rintro _ ⟨n, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsL3, one_zpow]
  have hzle : Subgroup.zpowers sL ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [Subgroup.zpowers_le]
    exact hsLG
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := 2) (p := 3)
    (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hzle hfin hexp
  have hn := hc₁m sL (Subgroup.mem_zpowers sL)
  have hn3 : (c₁ * sL * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hsL3, mul_one, mul_inv_cancel]
  have hL3 : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) 2]
    norm_num
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial
    monomialToralAt_E6_three hL3 hn hn3
  obtain ⟨t, ht⟩ : ∃ t, t = (c₂ * c₁) * sL * (c₂ * c₁)⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * sL * c₁⁻¹) * c₂⁻¹ := by rw [ht]; group
  have htT : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit Tag.E6 a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hsL3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom Tag.E6 (AlgebraicClosure K) (a ^ 3) =
        rootDiagUnitHom Tag.E6 (AlgebraicClosure K) 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit Tag.E6 a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := rootDiagUnit_injective (τ := Tag.E6) (K := AlgebraicClosure K) h1
    intro i
    have := congrFun h2 i
    simpa using this
  choose m hm using fun i => exists_eq_map_pow_of_pow_three
    (algebraMap K (AlgebraicClosure K)) hω (ha3 i)
  obtain ⟨x, hx⟩ : ∃ x : Fin Tag.E6.rank → ZMod 3, x = fun i => (m i : ZMod 3) := ⟨_, rfl⟩
  have hax : (fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
      (torV ω x i)) = a := by
    funext i
    rw [hm i, torV, hx, ZMod.val_natCast]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (m i) 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  have htx : t = baseChangeGL (algebraMap K (AlgebraicClosure K)) (dV ω x) := by
    rw [dV, baseChangeGL_rootDiagUnit, hax, hta]
  obtain ⟨y, hy⟩ : ∃ y, y = (c₂ * c₁)⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := hy ▸ inv_mem (mul_mem hc₂ hc₁)
  have hsy : sL = y * t * y⁻¹ := by rw [ht, hy]; group
  obtain ⟨F, hF⟩ : ∃ F : ModGL Tag.E6 (AlgebraicClosure K) →* ModGL Tag.E6 (AlgebraicClosure K),
      F = entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 2 := ⟨_, rfl⟩
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 2 c =
      c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
    norm_num
  have hFs : F sL = sL := by
    rw [hF, hsL]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap _ hFr s
  have hFt : F t = t := by
    rw [hta, hF, entrywiseFrobGL_rootDiagUnit_pow 2 2 a, ← hta]
    have : t ^ 2 ^ 2 = t ^ 3 * t := by rw [← pow_succ]; norm_num
    rw [this, ht3, one_mul]
  have hcc : y⁻¹ * F y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a := by
    have hFsy : F y * t * (F y)⁻¹ = sL := by
      have := congrArg F hsy
      rw [map_mul, map_mul, map_inv, hFt, hFs] at this
      exact this.symm
    have h1 : F y * t * (F y)⁻¹ = y * t * y⁻¹ := hFsy.trans hsy
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem hyG) (by rw [hF]; exact entrywiseFrobGL_mem 2 2 hyG), ?_⟩
    have h2 : (y⁻¹ * F y) * t = t * (y⁻¹ * F y) := by
      calc (y⁻¹ * F y) * t = y⁻¹ * (F y * t * (F y)⁻¹) * y * (y⁻¹ * F y) := by group
        _ = y⁻¹ * (y * t * y⁻¹) * y * (y⁻¹ * F y) := by rw [h1]
        _ = t * (y⁻¹ * F y) := by group
    rw [← hta]
    calc t * (y⁻¹ * F y) * t⁻¹ = (y⁻¹ * F y) * t * t⁻¹ := by rw [h2]
      _ = y⁻¹ * F y := by group
  have hcM : y⁻¹ * F y ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a := by
    by_cases hinner : rootChar (torV ω x) e6Omega3 = 1
    · obtain ⟨y₀, hy₀⟩ := exists_subLin_eq_of_rootChar hω hinner
      have hsy' : baseChangeGL (algebraMap K (AlgebraicClosure K)) s =
          y * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (dV ω (subLin (τ := .E6) e6InnerVec y₀)) * y⁻¹ := by
        rw [hy₀, ← htx, ← hsy, hsL]
      have h := lang_cocycle_mem_toralRootGroup_inner hK hω hs y₀ hyG hsy'
      rw [hy₀, hax] at h
      rw [hF]
      exact h
    · have hnon : rootChar a e6Omega3 ≠ 1 := by
        intro h1
        apply hinner
        rw [← hax, rootChar_map_tuple] at h1
        exact Units.map_injective (f := (algebraMap K (AlgebraicClosure K)).toMonoidHom)
          (algebraMap K (AlgebraicClosure K)).injective (h1.trans (map_one _).symm)
      have hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := fun w hw =>
        mem_kernelReflectionGroup_of_nonInner a ha3 hnon hw
      rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 _ a hW]
      exact hcc
  have hstab : ∀ g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a,
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 2 g ∈
        toralRootGroup Tag.E6 (AlgebraicClosure K) a := by
    intro g hg
    have h1 := baseChangeGL_mem_toralRootGroup (iterateFrobenius (AlgebraicClosure K) 2 2) hg
    have h2 : (fun i => Units.map (iterateFrobenius (AlgebraicClosure K) 2 2).toMonoidHom
        (a i)) = a := by
      funext i
      apply Units.ext
      change iterateFrobenius (AlgebraicClosure K) 2 2 ((a i : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K) = _
      rw [hFr, hK]
      have h := congrArg Units.val (ha3 i)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h
      rw [pow_succ, h, one_mul]
    rw [h2] at h1
    rw [show entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 2 g =
      baseChangeGL (iterateFrobenius (AlgebraicClosure K) 2 2) g from
        units_map_entrywiseHom_eq_baseChangeGL _ g]
    exact h1
  obtain ⟨z, hz, hzc⟩ := toralRootGroup_lang 2 a 2 (by norm_num) hstab _ (hF ▸ hcM)
  rw [← hF] at hzc
  obtain ⟨u, hu⟩ : ∃ u, u = y * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (y⁻¹ * F y) := by rw [← hzc]; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have hzt : z * t = t * z := by
    have h3 := (mem_toralCentralizer.1 (toralRootGroup_le a hz)).2
    rw [← hta] at h3
    calc z * t = (t * z * t⁻¹) * t := by rw [h3]
      _ = t * z := by group
  have hut : u * t * u⁻¹ = sL := by
    rw [hsy, hu]
    calc y * z⁻¹ * t * (y * z⁻¹)⁻¹ = y * (z⁻¹ * (t * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * t)) * y⁻¹ := by rw [hzt]
      _ = y * t * y⁻¹ := by group
  have huG : u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hu]
    exact mul_mem hyG (inv_mem ((toralRootGroup_le a hz).1))
  have hFu' : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 2)) u = u := by
    have h := hFu
    rw [hF] at h
    exact h
  obtain ⟨b, j, hjC, hbj⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed
    (iterateFrobenius (AlgebraicClosure K) 2 2) hFr
    (bijective_iterateFrobenius (AlgebraicClosure K) 2 2) huG hFu'
  have hs' : s = (rootDiagUnit Tag.E6 b * j) * dV ω x * (rootDiagUnit Tag.E6 b * j)⁻¹ := by
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
    rw [← hsL, map_mul, map_mul, map_inv, ← hbj, ← htx, hut]
  have hdx : rootDiagUnit Tag.E6 b * dV ω x = dV ω x * rootDiagUnit Tag.E6 b := by
    rw [dV, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hc0 : (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ ∈
      adjointGroup Tag.E6 K := inv_mem (conj_rootDiagUnit_mem_adjointGroup b hjC)
  have hconj : (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ * s *
      (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹⁻¹ = dV ω x := by
    rw [hs']
    calc (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ *
          (rootDiagUnit Tag.E6 b * j * dV ω x * (rootDiagUnit Tag.E6 b * j)⁻¹) *
          (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹⁻¹ =
        rootDiagUnit Tag.E6 b * dV ω x * (rootDiagUnit Tag.E6 b)⁻¹ := by group
      _ = dV ω x := by rw [hdx]; group
  have hxC : dV ω x ∈ adjointGroup Tag.E6 K := by
    rw [← hconj]
    exact mul_mem (mul_mem hc0 hs) (inv_mem hc0)
  obtain ⟨y', hy'⟩ := exists_subLin_of_mem_torusGroup hK hω
    (CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup (torV ω x) hxC)
  exact ⟨_, hc0, y', hconj.trans hy'⟩

end Fusion

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
