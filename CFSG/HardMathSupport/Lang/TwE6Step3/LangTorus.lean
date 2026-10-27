module

public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial
public import CFSG.RankThree.PartOne.KE6.Tw6Transport
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open Matrix CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2

set_option linter.unusedSectionVars false

section Form

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_mulVec_reflect {C : Matrix ι ι ℤ} (hC : Cᵀ = C) (h2 : ∀ i, C i i = 2) (i : ι)
    (u v : ι → ℤ) :
    (u - (C *ᵥ u) i • Pi.single i 1) ⬝ᵥ C *ᵥ (v - (C *ᵥ v) i • Pi.single i 1) = u ⬝ᵥ C *ᵥ v := by
  have e1 : (Pi.single i (1 : ℤ)) ⬝ᵥ (C *ᵥ v) = (C *ᵥ v) i := by simp
  have e2 : u ⬝ᵥ (C *ᵥ Pi.single i (1 : ℤ)) = (C *ᵥ u) i := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hC]
    simp
  have e3 : (Pi.single i (1 : ℤ)) ⬝ᵥ (C *ᵥ Pi.single i (1 : ℤ)) = 2 := by
    simp [h2]
  generalize hm : (C *ᵥ u) i = m at *
  generalize hn : (C *ᵥ v) i = n at *
  have : ∀ (a b : ι → ℤ) (m n : ℤ), (a - m • Pi.single i 1) ⬝ᵥ C *ᵥ (b - n • Pi.single i 1) =
      a ⬝ᵥ C *ᵥ b - n * (a ⬝ᵥ C *ᵥ Pi.single i 1) - m * ((Pi.single i 1) ⬝ᵥ C *ᵥ b) +
        m * n * ((Pi.single i 1) ⬝ᵥ C *ᵥ Pi.single i 1) := by
    intro a b m n
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [this, e1, e2, e3]
  ring

end Form

section Weyl

theorem E6_cartan_transpose : Tag.E6.cartanᵀ = Tag.E6.cartan := by
  ext i j
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem weyl_dotProduct_mulVec (w : WeylGroup Tag.E6) (u v : Fin Tag.E6.rank → ℤ) :
    (w • u) ⬝ᵥ Tag.E6.cartan *ᵥ (w • v) = u ⬝ᵥ Tag.E6.cartan *ᵥ v := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul, simple_smul, simple_smul]
    exact (dotProduct_mulVec_reflect E6_cartan_transpose (Tag.cartan_self Tag.E6) i _ _).trans ih

end Weyl

section Theta

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {q : ℕ}

theorem tw6ThetaConj_rootDiagUnit (hFr : ∀ c, Fr c = c ^ q) (x : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Ωˣ) :
    ∃ b' : Fin Tag.E6.rank → Ωˣ,
      tw6ThetaConj Ω Fr x (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b' ∧
      ∀ v, rootChar b' v = rootChar b (-((x * e6T3W * x⁻¹)⁻¹ • v)) ^ q := by
  have h1 : (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ * rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) Ω x = rootDiagUnit Tag.E6 (weylTuple x⁻¹ b) := by
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := Ω) b (weylTuple x⁻¹ b) x).2
      (fun v => by rw [rootChar_weylTuple, inv_inv])
    rw [this]
    group
  rw [tw6ThetaConj_apply, h1, tw6Theta_apply, twistE6_rootDiagUnit]
  rw [show tw6N Ω = canonicalRep (coxeterSystem Tag.E6) Ω tw6W from rfl,
    canonicalRep_conj_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  refine ⟨_, rfl, fun v => ?_⟩
  have hb' : (fun i => Units.map Fr.toMonoidHom (weylTuple x⁻¹ b (e6Rho.symm i))) =
      (fun i => weylTuple x⁻¹ b (e6Rho.symm i)) ^ q := by
    funext i
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hFr]
    rfl
  have key : x • permLattice e6Rho (tw6W⁻¹ • x⁻¹ • v) = -((x * e6T3W * x⁻¹)⁻¹ • v) := by
    set z := tw6W⁻¹ • x⁻¹ • v with hz
    have h2 : tw6W • z = x⁻¹ • v := by rw [hz, smul_inv_smul]
    rw [tw6W_smul, neg_eq_iff_eq_neg] at h2
    have h3 : permLattice e6Rho z = e6T3W⁻¹ • -(x⁻¹ • v) := by
      rw [eq_inv_smul_iff]
      exact h2
    rw [h3, smul_neg, ← mul_smul, smul_neg, ← mul_smul, _root_.mul_inv_rev, _root_.mul_inv_rev,
      inv_inv]
  rw [rootChar_weylTuple, rootChar_weylTuple]
  rw [hb', CFSG.RankThree.Chevalley.rootChar_pow_tuple, ← rootChar_permLattice,
    CFSG.RankThree.Classical2.e6Rho_symm, rootChar_weylTuple, inv_inv, key]

end Theta

section Rect

variable {κ ι : Type*} [Fintype ι] {G : Type*} [CommGroup G]

@[expose] def rectMono (A : Matrix κ ι ℤ) (t : ι → G) : κ → G := fun k => ∏ i, t i ^ A k i

theorem rectMono_apply (A : Matrix κ ι ℤ) (t : ι → G) (k : κ) :
    rectMono A t k = ∏ i, t i ^ A k i := rfl

theorem rectMono_mul (A : Matrix κ ι ℤ) (s t : ι → G) :
    rectMono A (s * t) = rectMono A s * rectMono A t := by
  ext k
  simp [rectMono, mul_zpow, Finset.prod_mul_distrib]

theorem rectMono_add (A B : Matrix κ ι ℤ) (t : ι → G) :
    rectMono (A + B) t = rectMono A t * rectMono B t := by
  ext k
  simp [rectMono, _root_.zpow_add, Finset.prod_mul_distrib]

theorem rectMono_rectMono {ι' : Type*} [Fintype ι'] (A : Matrix κ ι' ℤ) (B : Matrix ι' ι ℤ)
    (t : ι → G) : rectMono A (rectMono B t) = rectMono (A * B) t := by
  ext k
  simp only [rectMono_apply, Matrix.mul_apply]
  have h1 : ∀ j, (∏ l, t l ^ B j l) ^ A k j = ∏ l, t l ^ (B j l * A k j) := fun j => by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun l _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Rect

section Torus

variable {Ω : Type} [Field Ω]
variable (J : Set (Fin Tag.E6.rank)) [Fintype J]

@[expose] def cartanJ : Matrix (Fin Tag.E6.rank) J ℤ := Matrix.of fun l j => Tag.E6.cartan j l

theorem rootChar_rectMono (A : Matrix (Fin Tag.E6.rank) J ℤ) (a : J → Ωˣ)
    (w : Fin Tag.E6.rank → ℤ) :
    rootChar (rectMono A a) w = ∏ j, a j ^ ∑ l, w l * A l j := by
  simp only [rootChar, rectMono]
  have h1 : ∀ l, (∏ j, a j ^ A l j) ^ w l = ∏ j, a j ^ (A l j * w l) := fun l => by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun j _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem rootChar_single (b : Fin Tag.E6.rank → Ωˣ) (i : Fin Tag.E6.rank) :
    rootChar b (Pi.single i 1) = b i := by
  simp [rootChar, Pi.single_apply]

theorem supportedTorusHom_eq (a : J → Ωˣ) :
    supportedTorusHom Tag.E6 Ω J a = rootDiagUnit Tag.E6 (rectMono (cartanJ J) a) := by
  classical
  let φ : (J → Ωˣ) →* ModGL Tag.E6 Ω :=
    { toFun := fun a => rootDiagUnit Tag.E6 (rectMono (cartanJ J) a)
      map_one' := by
        have : rectMono (cartanJ J) (1 : J → Ωˣ) = 1 := by
          ext l
          simp [rectMono]
        rw [this]
        exact CFSG.LieType.Chevalley.rootDiagUnit_one
      map_mul' := fun s t => by
        rw [rectMono_mul]
        exact CFSG.LieType.Chevalley.rootDiagUnit_mul _ _ }
  have : supportedTorusHom Tag.E6 Ω J = φ := by
    refine MonoidHom.pi_ext fun j t => ?_
    rw [supportedTorusHom_mulSingle, torusElt_eq_rootDiagUnit]
    change _ = rootDiagUnit Tag.E6 (rectMono (cartanJ J) (Pi.mulSingle j t))
    congr 1
    ext l
    simp only [rectMono, cartanJ, Matrix.of_apply]
    rw [Finset.prod_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.mulSingle_eq_of_ne hj']
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [this]
  rfl

end Torus

section Lattice

@[expose] def phiMat (x : WeylGroup Tag.E6) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  -weylMatrix (x * e6T3W * x⁻¹)

@[expose] def psiMat (x : WeylGroup Tag.E6) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  -weylMatrix (x * e6T3W * x⁻¹)⁻¹

theorem phiMat_mulVec (x : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    phiMat x *ᵥ v = -((x * e6T3W * x⁻¹) • v) := by
  rw [phiMat, Matrix.neg_mulVec, weylMatrix_mulVec]

theorem psiMat_mulVec (x : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    psiMat x *ᵥ v = -((x * e6T3W * x⁻¹)⁻¹ • v) := by
  rw [psiMat, Matrix.neg_mulVec, weylMatrix_mulVec]

theorem phiMat_psiMat (x : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    phiMat x *ᵥ (psiMat x *ᵥ v) = v := by
  rw [psiMat_mulVec, phiMat_mulVec, smul_neg, neg_neg, smul_inv_smul]

theorem phiMat_form (x : WeylGroup Tag.E6) (u v : Fin Tag.E6.rank → ℤ) :
    (phiMat x *ᵥ u) ⬝ᵥ Tag.E6.cartan *ᵥ (phiMat x *ᵥ v) = u ⬝ᵥ Tag.E6.cartan *ᵥ v := by
  rw [phiMat_mulVec, phiMat_mulVec, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  exact weyl_dotProduct_mulVec _ _ _

theorem phiMat_pow_six (x : WeylGroup Tag.E6) :
    phiMat x ^ 6 = 1 := by
  have h3 : (x * e6T3W * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, e6T3_cube]
    group
  rw [phiMat, neg_pow, show (-1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) ^ 6 = 1 by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul]; simp, one_mul, ← weylMatrix_pow,
    show (6 : ℕ) = 3 * 2 by rfl, pow_mul, h3, one_pow, weylMatrix_one]

variable {x : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
  (hJ : ∀ β ∈ parabolicRoots Tag.E6 J, -((x * e6T3W * x⁻¹) • β) ∈ parabolicRoots Tag.E6 J)

include hJ in
theorem phiMat_apply_eq_zero {j k : Fin Tag.E6.rank} (hj : j ∈ J) (hk : k ∉ J) :
    phiMat x k j = 0 := by
  have hroot : Pi.single j (1 : ℤ) ∈ parabolicRoots Tag.E6 J := by
    refine ⟨IsRoot.basis j, fun i hi => ?_⟩
    have : i ≠ j := fun h => hi (h ▸ hj)
    simp [this]
  have h := (hJ _ hroot).2 k hk
  have h2 : (phiMat x *ᵥ (Pi.single j (1 : ℤ))) k = phiMat x k j := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← h2, phiMat_mulVec]
  exact h

variable [Fintype J]

@[expose] def extJ (J : Set (Fin Tag.E6.rank)) (u : J → ℤ) : Fin Tag.E6.rank → ℤ :=
  open Classical in fun a => if h : a ∈ J then u ⟨a, h⟩ else 0

theorem extJ_apply_mem (u : J → ℤ) {a : Fin Tag.E6.rank} (ha : a ∈ J) :
    extJ J u a = u ⟨a, ha⟩ := by
  simp [extJ, ha]

theorem extJ_apply_notMem (u : J → ℤ) {a : Fin Tag.E6.rank} (ha : a ∉ J) :
    extJ J u a = 0 := by
  simp [extJ, ha]

theorem sum_fin_eq_sum_J (f : Fin Tag.E6.rank → ℤ) (hf : ∀ a, a ∉ J → f a = 0) :
    ∑ a, f a = ∑ j : J, f j := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ J)) (fun a => by simp) f]
  exact (Finset.sum_subset (Finset.filter_subset _ _) fun a _ ha => hf a (by simpa using ha)).symm

@[expose] def latN (x : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank)) : Matrix J J ℤ :=
  Matrix.of fun k j => phiMat x k j

include hJ in
theorem phiMat_mulVec_extJ (u : J → ℤ) :
    phiMat x *ᵥ extJ J u = extJ J (latN x J *ᵥ u) := by
  funext a
  have h1 : (phiMat x *ᵥ extJ J u) a = ∑ j : J, phiMat x a j * u j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_fin_eq_sum_J (J := J)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [extJ_apply_mem u j.2]
    · intro b hb
      rw [extJ_apply_notMem u hb, mul_zero]
  rw [h1]
  by_cases ha : a ∈ J
  · rw [extJ_apply_mem _ ha]
    simp [Matrix.mulVec, dotProduct, latN]
  · rw [extJ_apply_notMem _ ha]
    exact Finset.sum_eq_zero fun j _ => by rw [phiMat_apply_eq_zero hJ j.2 ha, zero_mul]

include hJ in
theorem phiMat_pow_mulVec_extJ (m : ℕ) (u : J → ℤ) :
    phiMat x ^ m *ᵥ extJ J u = extJ J (latN x J ^ m *ᵥ u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      phiMat_mulVec_extJ hJ]

include hJ in
theorem latN_pow_six_mulVec (u : J → ℤ) : latN x J ^ 6 *ᵥ u = u := by
  have h := phiMat_pow_mulVec_extJ hJ 6 u
  rw [phiMat_pow_six, Matrix.one_mulVec] at h
  funext j
  have := congrFun h j
  rwa [extJ_apply_mem _ j.2, extJ_apply_mem _ j.2, eq_comm] at this

include hJ in
theorem det_latN_ne_zero {q : ℕ} (hq : 2 ≤ q) : ((q : ℤ) • latN x J - 1).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hq1 : (q : ℤ) • (latN x J *ᵥ v) = v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hpow : ∀ m : ℕ, (q : ℤ) ^ m • (latN x J ^ m *ᵥ v) = v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (q : ℤ) ^ (m + 1) • (latN x J ^ (m + 1) *ᵥ v)
          = (q : ℤ) ^ m • (latN x J ^ m *ᵥ ((q : ℤ) • (latN x J *ᵥ v))) := by
            rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, mul_smul]
        _ = v := by rw [hq1, ih]
  have h6 := hpow 6
  rw [latN_pow_six_mulVec hJ] at h6
  apply hv0
  funext j
  have h := congrFun h6 j
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hq6 : ((q : ℤ) ^ 6 - 1) * v j = 0 := by linarith
  have hne : ((q : ℤ) ^ 6 - 1) ≠ 0 := by
    have : (2 : ℤ) ^ 6 ≤ (q : ℤ) ^ 6 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) 6
    omega
  exact (mul_eq_zero.mp hq6).resolve_left hne

include hJ in
theorem cartan_psiMat_mulVec (j : J) (v : Fin Tag.E6.rank → ℤ) :
    (Tag.E6.cartan *ᵥ (psiMat x *ᵥ v)) j = ∑ k : J, latN x J k j * (Tag.E6.cartan *ᵥ v) k := by
  have e1 : ∀ w : Fin Tag.E6.rank → ℤ, (Tag.E6.cartan *ᵥ w) j = Pi.single (j : Fin Tag.E6.rank) (1 : ℤ) ⬝ᵥ (Tag.E6.cartan *ᵥ w) := fun w => by simp
  rw [e1, ← phiMat_form x, phiMat_psiMat]
  have h2 : (phiMat x *ᵥ Pi.single (j : Fin Tag.E6.rank) (1 : ℤ)) = fun a => phiMat x a j := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [h2]
  simp only [dotProduct]
  rw [sum_fin_eq_sum_J (J := J)]
  · rfl
  · intro a ha
    rw [phiMat_apply_eq_zero hJ j.2 ha, zero_mul]

end Lattice

section Main

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {q : ℕ}

theorem tw6ThetaConj_supportedTorusHom (hFr : ∀ c, Fr c = c ^ q) (x : WeylGroup Tag.E6)
    {J : Set (Fin Tag.E6.rank)} [Fintype J]
    (hJ : ∀ β ∈ parabolicRoots Tag.E6 J, -((x * e6T3W * x⁻¹) • β) ∈ parabolicRoots Tag.E6 J)
    (a : J → Ωˣ) [DecidableEq J] :
    tw6ThetaConj Ω Fr x (supportedTorusHom Tag.E6 Ω J a) =
      supportedTorusHom Tag.E6 Ω J a *
        supportedTorusHom Tag.E6 Ω J (monoHom (G := Ωˣ) ((q : ℤ) • latN x J - 1) a) := by
  rw [supportedTorusHom_eq J a, supportedTorusHom_eq J]
  obtain ⟨b', hb', hchar⟩ := tw6ThetaConj_rootDiagUnit hFr x (rectMono (cartanJ J) a)
  rw [hb', ← CFSG.LieType.Chevalley.rootDiagUnit_mul]
  congr 1
  have hsum : ∀ (w : Fin Tag.E6.rank → ℤ) (j : J),
      ∑ l, w l * cartanJ J l j = (Tag.E6.cartan *ᵥ w) j := by
    intro w j
    simp [Matrix.mulVec, dotProduct, cartanJ, mul_comm]
  have hb'eq : b' = rectMono (cartanJ J * ((q : ℤ) • latN x J)) a := by
    funext i
    have h1 := hchar (Pi.single i 1)
    rw [rootChar_single, ← psiMat_mulVec, rootChar_rectMono] at h1
    rw [h1, rectMono_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, hsum, cartan_psiMat_mulVec hJ]
    congr 1
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, cartanJ, Matrix.of_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrhs : rectMono (cartanJ J) a * rectMono (cartanJ J) (monoHom (G := Ωˣ) ((q : ℤ) • latN x J - 1) a) =
      rectMono (cartanJ J * ((q : ℤ) • latN x J)) a := by
    have e : monoHom (G := Ωˣ) ((q : ℤ) • latN x J - 1) a = rectMono ((q : ℤ) • latN x J - 1) a := rfl
    have hm : cartanJ J * ((q : ℤ) • latN x J) =
        cartanJ J + cartanJ J * ((q : ℤ) • latN x J - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    rw [e, rectMono_rectMono, hm, rectMono_add]
  rw [hb'eq, hrhs]

theorem exists_lang_supportedTorus [IsAlgClosed Ω] (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (x : WeylGroup Tag.E6) {J : Set (Fin Tag.E6.rank)}
    (hJ : ∀ β ∈ parabolicRoots Tag.E6 J, -((x * e6T3W * x⁻¹) • β) ∈ parabolicRoots Tag.E6 J) :
    ∀ s ∈ supportedTorus Tag.E6 Ω J, ∃ t ∈ supportedTorus Tag.E6 Ω J,
      t⁻¹ * tw6ThetaConj Ω Fr x t = s := by
  classical
  have : Fintype J := Fintype.ofFinite J
  rintro s ⟨a₀, rfl⟩
  obtain ⟨a, ha⟩ := monoHom_surjective_of_det_ne_zero (L := Ω)
    ((q : ℤ) • latN x J - 1) (det_latN_ne_zero hJ hq) a₀
  refine ⟨supportedTorusHom Tag.E6 Ω J a, supportedTorusHom_mem _ _, ?_⟩
  rw [tw6ThetaConj_supportedTorusHom hFr x hJ a, ha, inv_mul_cancel_left]

end Main

end CFSG.HardMathSupport.Lang.TwE6Step3
