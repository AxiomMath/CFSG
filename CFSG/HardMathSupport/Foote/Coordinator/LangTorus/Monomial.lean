module

public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorus

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator

open Matrix CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Lang.TwE6Step3 (rectMono rectMono_apply rectMono_mul monoHom monoHom_apply
  monoHom_surjective_of_det_ne_zero exists_unit_zpow_eq)

set_option linter.unusedSectionVars false

variable {τ : Tag}

section Form


theorem iform_eq_sum_single' (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ i, x i * iform (Pi.single i 1 : Fin τ.rank → ℤ) y := by
  unfold iform
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (∑ i', ∑ j, (Pi.single i (1 : ℤ) : Fin τ.rank → ℤ) i' * τ.symmetrizedCartan i' j * y j) =
      ∑ j, τ.symmetrizedCartan i j * y j := by
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Form

section Torus

variable {Ω : Type} [Field Ω]

@[expose] def cartanTJ (τ : Tag) (J : Set (Fin τ.rank)) : Matrix (Fin τ.rank) J ℤ :=
  Matrix.of fun l j => τ.cartan j l

theorem rootChar_single' (b : Fin τ.rank → Ωˣ) (i : Fin τ.rank) :
    rootChar b (Pi.single i 1) = b i := by
  simp [rootChar, Pi.single_apply]

theorem rootChar_rectMono' (J : Set (Fin τ.rank)) [Fintype J] (a : J → Ωˣ)
    (w : Fin τ.rank → ℤ) :
    rootChar (rectMono (cartanTJ τ J) a) w = ∏ j, a j ^ ∑ l, w l * cartanTJ τ J l j := by
  simp only [rootChar, rectMono]
  have h1 : ∀ l, (∏ j, a j ^ cartanTJ τ J l j) ^ w l = ∏ j, a j ^ (cartanTJ τ J l j * w l) :=
    fun l => by
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun j _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem supportedTorusHom_eq' (J : Set (Fin τ.rank)) [Fintype J] (a : J → Ωˣ) :
    supportedTorusHom τ Ω J a = rootDiagUnit τ (rectMono (cartanTJ τ J) a) := by
  classical
  let φ : (J → Ωˣ) →* ModGL τ Ω :=
    { toFun := fun a => rootDiagUnit τ (rectMono (cartanTJ τ J) a)
      map_one' := by
        have : rectMono (cartanTJ τ J) (1 : J → Ωˣ) = 1 := by
          ext l
          simp [rectMono]
        rw [this]
        exact CFSG.LieType.Chevalley.rootDiagUnit_one
      map_mul' := fun s t => by
        rw [rectMono_mul]
        exact CFSG.LieType.Chevalley.rootDiagUnit_mul _ _ }
  have : supportedTorusHom τ Ω J = φ := by
    refine MonoidHom.pi_ext fun j t => ?_
    rw [supportedTorusHom_mulSingle, torusElt_eq_rootDiagUnit]
    change _ = rootDiagUnit τ (rectMono (cartanTJ τ J) (Pi.mulSingle j t))
    congr 1
    ext l
    simp only [rectMono, cartanTJ, Matrix.of_apply]
    rw [Finset.prod_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.mulSingle_eq_of_ne hj']
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [this]
  rfl

theorem rootChar_tupd (J : Set (Fin τ.rank)) [Fintype J] (c : J → Ωˣ) (v : Fin τ.rank → ℤ) :
    rootChar (rectMono (cartanTJ τ J) (fun j => c j ^ τ.symmetrizer j j)) v =
      ∏ j : J, c j ^ (τ.symmetrizer j j * ∑ l, τ.cartan j l * v l) := by
  rw [rootChar_rectMono']
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← _root_.zpow_mul]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun l _ => by simp [cartanTJ, mul_comm]

theorem rootChar_pow_tuple' (c : Fin τ.rank → Ωˣ) (m : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (c ^ m) v = rootChar c v ^ m := by
  rw [rootChar, rootChar, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]

theorem entrywise_frob_rootDiagUnit' {Fr : Ω →+* Ω} {q : ℕ} (hF : ∀ c, Fr c = c ^ q)
    (c : Fin τ.rank → Ωˣ) :
    Units.map (entrywiseHom Fr) (rootDiagUnit τ c) = rootDiagUnit τ (c ^ q) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  change entrywise Fr (rootDiag c) = rootDiag (c ^ q)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  refine Units.ext ?_
  simp [hF]

end Torus

section Weyl


open Classical in
@[expose] def extJ' (J : Set (Fin τ.rank)) (u : J → ℤ) : Fin τ.rank → ℤ :=
  fun a => if h : a ∈ J then u ⟨a, h⟩ else 0

theorem extJ'_apply_mem {J : Set (Fin τ.rank)} (u : J → ℤ) {a : Fin τ.rank} (ha : a ∈ J) :
    extJ' J u a = u ⟨a, ha⟩ := by
  simp [extJ', ha]

theorem extJ'_apply_notMem {J : Set (Fin τ.rank)} (u : J → ℤ) {a : Fin τ.rank} (ha : a ∉ J) :
    extJ' J u a = 0 := by
  simp [extJ', ha]

theorem sum_fin_eq_sum_J' (J : Set (Fin τ.rank)) [Fintype J] (f : Fin τ.rank → ℤ)
    (hf : ∀ a, a ∉ J → f a = 0) : ∑ a, f a = ∑ j : J, f j := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ J)) (fun a => by simp) f]
  exact (Finset.sum_subset (Finset.filter_subset _ _) fun a _ ha => hf a (by simpa using ha)).symm

@[expose] def blockP (w : WeylGroup τ) (J : Set (Fin τ.rank)) : Matrix J J ℤ :=
  Matrix.of fun m j => (w • (Pi.single (j : Fin τ.rank) 1 : Fin τ.rank → ℤ)) m

variable {w : WeylGroup τ} {J : Set (Fin τ.rank)}
  (hJ : ∀ β ∈ parabolicRoots τ J, w • β ∈ parabolicRoots τ J)

include hJ in
theorem smul_single_apply_eq_zero {j k : Fin τ.rank} (hj : j ∈ J) (hk : k ∉ J) :
    (w • (Pi.single j 1 : Fin τ.rank → ℤ)) k = 0 := by
  have hroot : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J := by
    refine ⟨IsRoot.basis j, fun i hi => ?_⟩
    have : i ≠ j := fun h => hi (h ▸ hj)
    simp [this]
  exact (hJ _ hroot).2 k hk

include hJ in
theorem cartan_inv_smul [Fintype J] (j : J) (v : Fin τ.rank → ℤ) :
    τ.symmetrizer j j * ∑ l, τ.cartan j l * (w⁻¹ • v) l =
      ∑ m : J, blockP w J m j * (τ.symmetrizer m m * ∑ l, τ.cartan m l * v l) := by
  rw [← iform_single_left, ← iform_smul w, smul_inv_smul, iform_eq_sum_single']
  rw [sum_fin_eq_sum_J' J]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [iform_single_left]
    rfl
  · intro a ha
    rw [smul_single_apply_eq_zero hJ j.2 ha, zero_mul]

include hJ in
theorem weylMatrix_mulVec_extJ' [Fintype J] (u : J → ℤ) :
    weylMatrix w *ᵥ extJ' J u = extJ' J (blockP w J *ᵥ u) := by
  funext a
  have h1 : (weylMatrix w *ᵥ extJ' J u) a =
      ∑ j : J, (w • (Pi.single (j : Fin τ.rank) 1 : Fin τ.rank → ℤ)) a * u j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_fin_eq_sum_J' J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [extJ'_apply_mem u j.2]
      rfl
    · intro b hb
      rw [extJ'_apply_notMem u hb, mul_zero]
  rw [h1]
  by_cases ha : a ∈ J
  · rw [extJ'_apply_mem _ ha]
    simp [Matrix.mulVec, dotProduct, blockP]
  · rw [extJ'_apply_notMem _ ha]
    exact Finset.sum_eq_zero fun j _ => by rw [smul_single_apply_eq_zero hJ j.2 ha, zero_mul]

include hJ in
theorem weylMatrix_pow_mulVec_extJ' [Fintype J] [DecidableEq J] (m : ℕ) (u : J → ℤ) :
    weylMatrix w ^ m *ᵥ extJ' J u = extJ' J (blockP w J ^ m *ᵥ u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      weylMatrix_mulVec_extJ' hJ]

include hJ in
theorem blockP_pow_orderOf_mulVec [Fintype J] [DecidableEq J] (u : J → ℤ) :
    blockP w J ^ orderOf w *ᵥ u = u := by
  have h := weylMatrix_pow_mulVec_extJ' hJ (orderOf w) u
  rw [← weylMatrix_pow, pow_orderOf_eq_one, weylMatrix_one, Matrix.one_mulVec] at h
  funext j
  have := congrFun h j
  rwa [extJ'_apply_mem _ j.2, extJ'_apply_mem _ j.2, eq_comm] at this

end Weyl

theorem det_ne_zero_of_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℤ) {m : ℕ}
    (hm : 0 < m) (hN : ∀ u, N ^ m *ᵥ u = u) {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℤ) • N - 1).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hq1 : (q : ℤ) • (N *ᵥ v) = v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hpow : ∀ k : ℕ, (q : ℤ) ^ k • (N ^ k *ᵥ v) = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (q : ℤ) ^ (k + 1) • (N ^ (k + 1) *ᵥ v)
          = (q : ℤ) ^ k • (N ^ k *ᵥ ((q : ℤ) • (N *ᵥ v))) := by
            rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, mul_smul]
        _ = v := by rw [hq1, ih]
  have h6 := hpow m
  rw [hN v] at h6
  apply hv0
  funext j
  have h := congrFun h6 j
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hq6 : ((q : ℤ) ^ m - 1) * v j = 0 := by linarith
  have hne : ((q : ℤ) ^ m - 1) ≠ 0 := by
    have := one_lt_pow₀ (show (1 : ℤ) < q by omega) hm.ne'
    omega
  exact (mul_eq_zero.mp hq6).resolve_left hne

theorem monoHom_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [CommGroup G]
    (A : Matrix ι ι ℤ) (c : ι → G) : monoHom (A - 1) c = monoHom A c * c⁻¹ := by
  ext i
  simp only [monoHom_apply, Matrix.sub_apply, Matrix.one_apply, Pi.mul_apply, Pi.inv_apply,
    _root_.zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem prod_zpow_sum_pow {ι : Type*} [Fintype ι] {G : Type*} [CommGroup G] (P : Matrix ι ι ℤ)
    (c : ι → G) (X : ι → ℤ) (q : ℕ) :
    (∏ j, c j ^ ∑ m, P m j * X m) ^ q = ∏ m, (monoHom ((q : ℤ) • P) c m) ^ X m := by
  simp only [monoHom_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← zpow_natCast, ← Finset.prod_zpow]
  have h1 : ∀ m, (∏ j, c j ^ ((q : ℤ) * P m j)) ^ X m = ∏ j, c j ^ ((q : ℤ) * P m j * X m) :=
    fun m => by
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun j _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← _root_.zpow_mul, ← zpow_finsetSum]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

section Main

variable {Ω : Type} [Field Ω]

theorem conj_frob_rootDiagUnit {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (n : ModGL τ Ω) (hnm : n ∈ monomialSubgroup τ Ω) (b : Fin τ.rank → Ωˣ) :
    n * Units.map (entrywiseHom Fr) (rootDiagUnit τ b) * n⁻¹ =
      rootDiagUnit τ (weylTuple (weylQuotientHom τ Ω ⟨n, hnm⟩) (b ^ q)) := by
  obtain ⟨w', k, hk, hnk⟩ := monomialSubgroup_le_torusWeylCosets hnm
  have hmaps : MapsRootLines n w' := by
    rw [hnk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  have hw : weylQuotientHom τ Ω ⟨n, hnm⟩ = w' := weylQuotientHom_eq hmaps
  rw [hw, entrywise_frob_rootDiagUnit' hFr, hnk]
  have hc := rootDiagUnit_mul_comm_of_mem_torusGroup (K := Ω) (weylTuple w' (b ^ q)) hk
  calc k * canonicalRep (coxeterSystem τ) Ω w' * rootDiagUnit τ (b ^ q) *
        (k * canonicalRep (coxeterSystem τ) Ω w')⁻¹
      = k * (canonicalRep (coxeterSystem τ) Ω w' * rootDiagUnit τ (b ^ q) *
          (canonicalRep (coxeterSystem τ) Ω w')⁻¹) * k⁻¹ := by group
    _ = _ := by rw [canonicalRep_conj_rootDiagUnit, ← hc, mul_inv_cancel_right]

theorem weylTuple_pow_tupd {w : WeylGroup τ} {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]
    (hJ : ∀ β ∈ parabolicRoots τ J, w • β ∈ parabolicRoots τ J) {q : ℕ} (c : J → Ωˣ) :
    weylTuple w ((rectMono (cartanTJ τ J) (fun j => c j ^ τ.symmetrizer j j)) ^ q) =
      rectMono (cartanTJ τ J)
        (fun m => (monoHom ((q : ℤ) • blockP w J) c m) ^ τ.symmetrizer m m) := by
  funext i
  have hR := rootChar_single'
    (rectMono (cartanTJ τ J)
      (fun m => (monoHom ((q : ℤ) • blockP w J) c m) ^ τ.symmetrizer m m)) i
  rw [← hR, rootChar_tupd]
  simp only [weylTuple]
  rw [rootChar_pow_tuple', rootChar_tupd]
  simp only [cartan_inv_smul hJ]
  exact prod_zpow_sum_pow (blockP w J) c _ q

theorem exists_lang_supportedTorus_of_monomial [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (n : ModGL τ Ω) (hnm : n ∈ monomialSubgroup τ Ω) {J : Set (Fin τ.rank)}
    (hJ : ∀ β ∈ parabolicRoots τ J, weylQuotientHom τ Ω ⟨n, hnm⟩ • β ∈ parabolicRoots τ J) :
    ∀ s ∈ supportedTorus τ Ω J, ∃ t ∈ supportedTorus τ Ω J,
      t⁻¹ * (n * Units.map (entrywiseHom Fr) t * n⁻¹) = s := by
  classical
  have : Fintype J := Fintype.ofFinite J
  rintro s ⟨a₀, rfl⟩
  set w := weylQuotientHom τ Ω ⟨n, hnm⟩ with hw
  choose c₀ hc₀ using fun j : J => exists_unit_zpow_eq (a₀ j) (symmetrizer_pos τ j).ne'
  obtain ⟨c, hc⟩ := monoHom_surjective_of_det_ne_zero (L := Ω) ((q : ℤ) • blockP w J - 1)
    (det_ne_zero_of_pow _ (orderOf_pos w) (blockP_pow_orderOf_mulVec hJ) hq) c₀
  refine ⟨supportedTorusHom τ Ω J (fun j => c j ^ τ.symmetrizer j j),
    supportedTorusHom_mem _ _, ?_⟩
  have key : n * Units.map (entrywiseHom Fr)
      (supportedTorusHom τ Ω J (fun j => c j ^ τ.symmetrizer j j)) * n⁻¹ =
      supportedTorusHom τ Ω J
        (fun m => (monoHom ((q : ℤ) • blockP w J) c m) ^ τ.symmetrizer m m) := by
    rw [supportedTorusHom_eq' J (fun j => c j ^ τ.symmetrizer j j),
      conj_frob_rootDiagUnit hFr n hnm, weylTuple_pow_tupd hJ,
      ← supportedTorusHom_eq' J]
  rw [key, ← map_inv, ← map_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply]
  have h := congrFun hc j
  rw [monoHom_sub_one] at h
  rw [← hc₀ j, ← h]
  simp [mul_zpow, mul_comm]

end Main

end CFSG.HardMathSupport.Foote.Coordinator
