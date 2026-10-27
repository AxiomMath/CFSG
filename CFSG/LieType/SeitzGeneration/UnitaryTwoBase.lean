module

public import CFSG.LieType.SeitzGeneration.UnitaryONExt
public import CFSG.LieType.SeitzGeneration.UnitaryTwoPlane

public section

namespace CFSG.LieType.SeitzGeneration.UnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

structure EigenFrame (σ : K ≃+* K) (n : ℕ) (𝔈 : Set (SUid σ n)) where
  u : Fin n → Fin n → K
  isON : IsON σ u
  spans : ∀ v, ∃ c, orthoEmb u c = v
  eig : ∀ e ∈ 𝔈, ∃ lam : Fin n → K, ∀ i, e • u i = lam i • u i

@[expose] def centSub (𝔈 : Set (SUid σ n)) : Subgroup (SUid σ n) :=
  Subgroup.closure {g | ∃ e ∈ 𝔈, g * e = e * g}

theorem mem_centSub {𝔈 : Set (SUid σ n)} {e g : SUid σ n} (he : e ∈ 𝔈) (hg : g * e = e * g) :
    g ∈ centSub 𝔈 :=
  Subgroup.subset_closure ⟨e, he, hg⟩

theorem isCenter_of_eigenvector (hσ : IsUnitaryInvolution σ) (hq : ∀ c : K, c ≠ 0 → σ c * c = 1)
    {𝔈 : Set (SUid σ n)} {e : SUid σ n} (he : e ∈ 𝔈) {v : Fin n → K} {t : K}
    (hv : herm σ v v = 0) (hev : e • v = t • v) : IsCenter (centSub 𝔈) v := by
  by_cases hv0 : v = 0
  · subst hv0
    exact isCenter_zero
  · have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hev
      apply hv0
      have := congrArg (fun w => e⁻¹ • w) hev
      simpa using this
    exact isCenter_of_eigen hσ.invol (fun g hg => mem_centSub he hg) hv (hq t ht) hev

theorem isON_comp {m k : ℕ} {x : Fin m → Fin n → K} (hx : IsON σ x) {τ : Fin k → Fin m}
    (hτ : Function.Injective τ) : IsON σ (fun i => x (τ i)) := by
  intro i j
  rw [hx (τ i) (τ j)]
  simp [hτ.eq_iff]

theorem smul_orthoEmb_of_eig {m : ℕ} {x : Fin m → Fin n → K} (e : SUid σ n) {D : Fin m → K}
    (hD : ∀ i, e • x i = D i • x i) (c : Fin m → K) :
    e • orthoEmb x c = orthoEmb x (fun i => D i * c i) := by
  simp only [orthoEmb_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm e (c i) (x i), hD i, smul_smul, mul_comm]

theorem commute_ext_gen (hσ : ∀ c, σ (σ c) = c) {m : ℕ} {x : Fin m → Fin n → K}
    (hx : IsON σ x) (G : SUid σ m) (e : SUid σ n) (D : Fin m → K)
    (hD : ∀ i, e • x i = D i • x i)
    (hG : ∀ c : Fin m → K, G • (fun i => D i * c i) = fun i => D i * (G • c) i) :
    e * ext hσ hx G = ext hσ hx G * e := by
  refine ext_smul σ fun v => ?_
  obtain ⟨c, w, hw, rfl⟩ := exists_decomp hx v
  have hD0 : ∀ i, D i ≠ 0 := by
    intro i h0
    have h1 : herm σ (x i) (x i) = 1 := by simpa using hx i i
    have h2 : e • x i = 0 := by rw [hD i, h0, zero_smul]
    have h3 : x i = 0 := by
      have := congrArg (fun w => e⁻¹ • w) h2
      simpa using this
    rw [h3, herm_zero_left] at h1
    exact zero_ne_one h1
  have hew : ∀ i, herm σ (x i) (e • w) = 0 := by
    intro i
    have h1 := herm_smul_smul σ e⁻¹ (x i) (e • w)
    have h2 : e⁻¹ • x i = (D i)⁻¹ • x i := by
      rw [inv_smul_eq_iff, smul_comm e, hD, smul_smul, inv_mul_cancel₀ (hD0 i), one_smul]
    rw [inv_smul_smul, h2, herm_smul_left, hw i, mul_zero] at h1
    exact h1.symm
  have e1 : ext hσ hx G • (orthoEmb x c + w) = orthoEmb x (G • c) + w := by
    rw [smul_add, ext_smul_orthoEmb hσ hx, ext_smul_of_orth hσ hx _ hw]
  have e2 : e • (orthoEmb x (G • c) + w) = orthoEmb x (fun i => D i * (G • c) i) + e • w := by
    rw [smul_add, smul_orthoEmb_of_eig e hD]
  have e3 : e • (orthoEmb x c + w) = orthoEmb x (fun i => D i * c i) + e • w := by
    rw [smul_add, smul_orthoEmb_of_eig e hD]
  have e4 : ext hσ hx G • (orthoEmb x (fun i => D i * c i) + e • w) =
      orthoEmb x (G • fun i => D i * c i) + e • w := by
    rw [smul_add, ext_smul_orthoEmb hσ hx, ext_smul_of_orth hσ hx _ hew]
  rw [mul_smul, mul_smul, e1, e2, e3, e4, hG]

section DFT

variable {ω : K}

@[expose] def dftMat (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

theorem one_add_add_sq_eq_zero (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)

theorem ne_zero_of_cube (hω3 : ω ^ 3 = 1) : ω ≠ 0 := by
  rintro rfl
  norm_num at hω3

theorem sigma_cube_root (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) (hω3 : ω ^ 3 = 1) :
    σ ω = ω ^ 2 := by
  have h := hq ω (ne_zero_of_cube hω3)
  linear_combination ω ^ 2 * h - σ ω * hω3

theorem sigma_cube_root_sq (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) (hω3 : ω ^ 3 = 1) :
    σ (ω ^ 2) = ω := by
  rw [map_pow, sigma_cube_root hq hω3]
  linear_combination ω * hω3

theorem conjTr_dftMat (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (h2 : (1 : K) + 1 = 0) : conjTr σ (dftMat ω) * dftMat ω = 1 := by
  have hω2 := one_add_add_sq_eq_zero hω3 hω1
  have hσω := sigma_cube_root hq hω3
  have hσω2 := sigma_cube_root_sq hq hω3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, dftMat, Matrix.mul_apply, Fin.sum_univ_three, hσω, hσω2, Matrix.one_apply] <;>
    first
    | exact h2
    | linear_combination hω2
    | linear_combination (2 : K) * hω3 + h2
    | linear_combination ω * hω3 + hω2

theorem det_dftMat (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (h2 : (1 : K) + 1 = 0) :
    (dftMat ω).det = 1 := by
  have hω2 := one_add_add_sq_eq_zero hω3 hω1
  rw [dftMat, Matrix.det_fin_three]
  simp
  linear_combination (3 : K) * hω2 - (3 * ω + 2) * h2 - ω * hω3

@[expose] noncomputable def dftSU (σ : K ≃+* K) (hq : ∀ c : K, c ≠ 0 → σ c * c = 1)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (h2 : (1 : K) + 1 = 0) : SUid σ 3 :=
  mkSU σ (dftMat ω) (det_dftMat hω3 hω1 h2) (fun x y => by
    rw [herm_mulVec, conjTr_dftMat hq hω3 hω1 h2, one_mulVec])

theorem dftSU_smul_single_zero (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (h2 : (1 : K) + 1 = 0) :
    dftSU σ hq hω3 hω1 h2 • (Pi.single 0 1 : Fin 3 → K) = fun _ => 1 := by
  funext i
  simp only [dftSU, mkSU_smul]
  fin_cases i <;> simp [dftMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end DFT

structure Field4 (σ : K ≃+* K) (ω : K) : Prop where
  invol : IsUnitaryInvolution σ
  norm_one : ∀ c : K, c ≠ 0 → σ c * c = 1
  two : (1 : K) + 1 = 0
  cube : ω ^ 3 = 1
  ne_one : ω ≠ 1

section Frame

variable {ω : K} {𝔈 : Set (SUid σ n)} (F : EigenFrame σ n 𝔈)

theorem EigenFrame.herm_u (i j : Fin n) :
    herm σ (F.u i) (F.u j) = if i = j then 1 else 0 := F.isON i j

theorem EigenFrame.herm_u_self (i : Fin n) : herm σ (F.u i) (F.u i) = 1 := by
  simp [F.herm_u]

theorem EigenFrame.herm_u_of_ne {i j : Fin n} (h : i ≠ j) : herm σ (F.u i) (F.u j) = 0 := by
  simp [F.herm_u, h]

theorem EigenFrame.herm_pair {a b : Fin n} (hab : a ≠ b) (α β : K) :
    herm σ (α • F.u a + β • F.u b) (α • F.u a + β • F.u b) = σ α * α + σ β * β := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, F.herm_u_self,
    F.herm_u_of_ne hab, F.herm_u_of_ne hab.symm]
  ring

theorem EigenFrame.isCenter_pair (hK : Field4 σ ω)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {a b : Fin n} (hab : a ≠ b) {α β : K} (hiso : σ α * α + σ β * β = 0) :
    IsCenter (centSub 𝔈) (α • F.u a + β • F.u b) := by
  obtain ⟨e, he, t, ha, hb⟩ := hpair a b hab
  refine isCenter_of_eigenvector hK.invol hK.norm_one he (t := t)
    (by rw [F.herm_pair hab]; exact hiso) ?_
  rw [smul_add, smul_add, smul_comm e α, smul_comm e β, ha, hb, smul_comm α t, smul_comm β t]

theorem EigenFrame.isCenter_pair_one (hK : Field4 σ ω)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {a b : Fin n} (hab : a ≠ b) : IsCenter (centSub 𝔈) (F.u a + F.u b) := by
  have := F.isCenter_pair hK hpair hab (α := 1) (β := 1) (by simpa using hK.two)
  simpa using this

end Frame

section Triple

variable {ω : K} {𝔈 : Set (SUid σ n)} (F : EigenFrame σ n 𝔈)

theorem tri_injective {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Fin n) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

@[expose] noncomputable def EigenFrame.dftExt (hK : Field4 σ ω) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : SUid σ n :=
  ext hK.invol.invol (isON_comp F.isON (tri_injective hab hac hbc))
    (dftSU σ hK.norm_one hK.cube hK.ne_one hK.two)

theorem EigenFrame.dftExt_smul_a (hK : Field4 σ ω) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : F.dftExt hK hab hac hbc • F.u a = F.u a + F.u b + F.u c := by
  set x : Fin 3 → Fin n → K := fun i => F.u (![a, b, c] i) with hx
  have h0 : F.u a = orthoEmb x (Pi.single 0 1) := by
    rw [orthoEmb_single]
    rfl
  have h1 : F.dftExt hK hab hac hbc • orthoEmb x (Pi.single 0 1) = orthoEmb x (fun _ => 1) := by
    rw [EigenFrame.dftExt, ext_smul_orthoEmb, dftSU_smul_single_zero]
  have h2 : orthoEmb x (fun _ => 1) = F.u a + F.u b + F.u c := by
    rw [orthoEmb_apply, Fin.sum_univ_three]
    simp [hx]
  calc F.dftExt hK hab hac hbc • F.u a = F.dftExt hK hab hac hbc • orthoEmb x (Pi.single 0 1) :=
        congrArg _ h0
    _ = orthoEmb x (fun _ => 1) := h1
    _ = F.u a + F.u b + F.u c := h2

theorem EigenFrame.dftExt_smul_of_ne (hK : Field4 σ ω) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {l : Fin n} (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c) :
    F.dftExt hK hab hac hbc • F.u l = F.u l := by
  rw [EigenFrame.dftExt]
  refine ext_smul_of_orth _ _ _ fun i => ?_
  fin_cases i
  · exact F.herm_u_of_ne hla.symm
  · exact F.herm_u_of_ne hlb.symm
  · exact F.herm_u_of_ne hlc.symm

theorem EigenFrame.dftExt_mem (hK : Field4 σ ω) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {e : SUid σ n} (he : e ∈ 𝔈) {t : K} (ha : e • F.u a = t • F.u a)
    (hb : e • F.u b = t • F.u b) (hc : e • F.u c = t • F.u c) :
    F.dftExt hK hab hac hbc ∈ centSub 𝔈 := by
  refine mem_centSub he ?_
  symm
  refine commute_ext_gen hK.invol.invol _ _ e (fun _ => t) ?_ ?_
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · intro v
    show dftSU σ hK.norm_one hK.cube hK.ne_one hK.two • (t • v) =
      t • (dftSU σ hK.norm_one hK.cube hK.ne_one hK.two • v)
    exact smul_comm _ _ _

end Triple

section Scale

variable {ω : K} {𝔈 : Set (SUid σ n)} (F : EigenFrame σ n 𝔈)

theorem pair_injective {i m : Fin n} (him : i ≠ m) :
    Function.Injective (![i, m] : Fin 2 → Fin n) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

@[expose] noncomputable def diagPair (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) {t : K} (ht : t ≠ 0) :
    SUid σ 2 :=
  diagSU σ ![t, t⁻¹]
    (fun i => by
      fin_cases i
      · simpa using hq t ht
      · simp [map_inv₀, ← mul_inv, hq t ht])
    (by simp [Fin.prod_univ_two, ht])

theorem diagPair_smul (hq : ∀ c : K, c ≠ 0 → σ c * c = 1) {t : K} (ht : t ≠ 0)
    (v : Fin 2 → K) (i : Fin 2) :
    (diagPair (σ := σ) hq ht • v) i = ![t, t⁻¹] i * v i := diagSU_smul _ _ _ _ _

@[expose] noncomputable def EigenFrame.scaleExt (hK : Field4 σ ω) {i m : Fin n} (him : i ≠ m)
    {t : K} (ht : t ≠ 0) : SUid σ n :=
  ext hK.invol.invol (isON_comp F.isON (pair_injective him)) (diagPair hK.norm_one ht)

theorem EigenFrame.scaleExt_smul_self (hK : Field4 σ ω) {i m : Fin n} (him : i ≠ m) {t : K}
    (ht : t ≠ 0) : F.scaleExt hK him ht • F.u i = t • F.u i := by
  set x : Fin 2 → Fin n → K := fun s => F.u (![i, m] s) with hx
  have h0 : F.u i = orthoEmb x (Pi.single 0 1) := by
    rw [orthoEmb_single]
    rfl
  have h1 : (diagPair (σ := σ) hK.norm_one ht • (Pi.single 0 1 : Fin 2 → K)) =
      t • Pi.single 0 1 := by
    funext s
    rw [diagPair_smul]
    fin_cases s <;> simp
  calc F.scaleExt hK him ht • F.u i = F.scaleExt hK him ht • orthoEmb x (Pi.single 0 1) :=
        congrArg _ h0
    _ = orthoEmb x (diagPair (σ := σ) hK.norm_one ht • Pi.single 0 1) := by
        rw [EigenFrame.scaleExt, ext_smul_orthoEmb]
    _ = t • F.u i := by rw [h1, map_smul, ← h0]

theorem EigenFrame.scaleExt_smul_of_ne (hK : Field4 σ ω) {i m : Fin n} (him : i ≠ m) {t : K}
    (ht : t ≠ 0) {j : Fin n} (hji : j ≠ i) (hjm : j ≠ m) :
    F.scaleExt hK him ht • F.u j = F.u j := by
  rw [EigenFrame.scaleExt]
  refine ext_smul_of_orth _ _ _ fun s => ?_
  fin_cases s
  · exact F.herm_u_of_ne hji.symm
  · exact F.herm_u_of_ne hjm.symm

theorem EigenFrame.scaleExt_mem (hK : Field4 σ ω) (hne : 𝔈.Nonempty) {i m : Fin n}
    (him : i ≠ m) {t : K} (ht : t ≠ 0) : F.scaleExt hK him ht ∈ centSub 𝔈 := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨lam, hlam⟩ := F.eig e he
  refine mem_centSub he ?_
  symm
  refine commute_ext_gen hK.invol.invol _ _ e ![lam i, lam m] ?_ ?_
  · intro s
    fin_cases s
    · exact hlam i
    · exact hlam m
  · intro v
    funext s
    simp only [diagPair_smul]
    ring

end Scale

section Block

variable {ω : K} {𝔈 : Set (SUid σ n)} (F : EigenFrame σ n 𝔈)

theorem EigenFrame.isCenter_sum_four (hK : Field4 σ ω)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {τ : Fin 5 → Fin n} (hτ : Function.Injective τ)
    (htri : ∃ e ∈ 𝔈, ∃ t : K, e • F.u (τ 0) = t • F.u (τ 0) ∧ e • F.u (τ 1) = t • F.u (τ 1) ∧
      e • F.u (τ 2) = t • F.u (τ 2)) :
    IsCenter (centSub 𝔈) (F.u (τ 0) + F.u (τ 1) + F.u (τ 2) + F.u (τ 3)) := by
  obtain ⟨e, he, t, ha, hb, hc⟩ := htri
  have h01 : τ 0 ≠ τ 1 := hτ.ne (by decide)
  have h02 : τ 0 ≠ τ 2 := hτ.ne (by decide)
  have h12 : τ 1 ≠ τ 2 := hτ.ne (by decide)
  have h03 : τ 0 ≠ τ 3 := hτ.ne (by decide)
  have h30 : τ 3 ≠ τ 0 := hτ.ne (by decide)
  have h31 : τ 3 ≠ τ 1 := hτ.ne (by decide)
  have h32 : τ 3 ≠ τ 2 := hτ.ne (by decide)
  have hD := F.dftExt_mem hK h01 h02 h12 he ha hb hc
  have hp : IsCenter (centSub 𝔈) (F.u (τ 0) + F.u (τ 3)) := F.isCenter_pair_one hK hpair h03
  have := hp.map hD
  rwa [smul_add, F.dftExt_smul_a hK h01 h02 h12, F.dftExt_smul_of_ne hK h01 h02 h12 h30 h31 h32]
    at this

@[expose] def EigenFrame.blk (τ : Fin 5 → Fin n) : Fin 4 → Fin n → K :=
  fun s => F.u (τ s.castSucc)

theorem EigenFrame.blk_isON {τ : Fin 5 → Fin n} (hτ : Function.Injective τ) :
    IsON σ (F.blk τ) :=
  isON_comp F.isON (τ := fun s : Fin 4 => τ s.castSucc) (hτ.comp (Fin.castSucc_injective 4))

theorem EigenFrame.scaleExt_smul_blk (hK : Field4 σ ω) {τ : Fin 5 → Fin n}
    (hτ : Function.Injective τ) (i : Fin 4) {t : K} (ht : t ≠ 0) (c c' : Fin 4 → K)
    (hc' : ∀ s, c' s = if s = i then t * c s else c s) :
    F.scaleExt hK (hτ.ne (Fin.castSucc_lt_last i).ne : τ i.castSucc ≠ τ 4) ht •
      orthoEmb (F.blk τ) c = orthoEmb (F.blk τ) c' := by
  simp only [orthoEmb_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_comm _ (c s), hc' s]
  by_cases hs : s = i
  · subst hs
    rw [if_pos rfl, EigenFrame.blk, F.scaleExt_smul_self, smul_smul, mul_comm]
  · rw [if_neg hs, EigenFrame.blk, F.scaleExt_smul_of_ne]
    · exact hτ.ne (fun h => hs (Fin.castSucc_injective 4 h))
    · exact hτ.ne (Fin.castSucc_lt_last s).ne

theorem EigenFrame.isCenter_full (hK : Field4 σ ω) (hne : 𝔈.Nonempty)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {τ : Fin 5 → Fin n} (hτ : Function.Injective τ)
    (htri : ∃ e ∈ 𝔈, ∃ t : K, e • F.u (τ 0) = t • F.u (τ 0) ∧ e • F.u (τ 1) = t • F.u (τ 1) ∧
      e • F.u (τ 2) = t • F.u (τ 2)) (c : Fin 4 → K) (hc : ∀ s, c s ≠ 0) :
    IsCenter (centSub 𝔈) (orthoEmb (F.blk τ) c) := by
  have hc₀ := F.isCenter_sum_four hK hpair hτ htri
  have step : ∀ (i : Fin 4) (t : K) (ht : t ≠ 0) (c c' : Fin 4 → K),
      (∀ s, c' s = if s = i then t * c s else c s) → IsCenter (centSub 𝔈) (orthoEmb (F.blk τ) c) →
      IsCenter (centSub 𝔈) (orthoEmb (F.blk τ) c') := fun i t ht c c' hc' hw => by
    rw [← F.scaleExt_smul_blk hK hτ i ht c c' hc']
    exact hw.map (F.scaleExt_mem hK hne _ ht)
  have e0 : IsCenter (centSub 𝔈) (orthoEmb (F.blk τ) ![1, 1, 1, 1]) := by
    convert hc₀ using 1
    simp [orthoEmb_apply, Fin.sum_univ_four, EigenFrame.blk]
  have e1 := step 0 (c 0) (hc 0) _ ![c 0, 1, 1, 1] (fun s => by fin_cases s <;> simp) e0
  have e2 := step 1 (c 1) (hc 1) _ ![c 0, c 1, 1, 1] (fun s => by fin_cases s <;> simp) e1
  have e3 := step 2 (c 2) (hc 2) _ ![c 0, c 1, c 2, 1] (fun s => by fin_cases s <;> simp) e2
  have e4 := step 3 (c 3) (hc 3) _ ![c 0, c 1, c 2, c 3] (fun s => by fin_cases s <;> simp) e3
  convert e4 using 2
  funext s
  fin_cases s <;> simp

theorem EigenFrame.allCenters_blk (hK : Field4 σ ω) (hne : 𝔈.Nonempty)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {τ : Fin 5 → Fin n} (hτ : Function.Injective τ)
    (htri : ∃ e ∈ 𝔈, ∃ t : K, e • F.u (τ 0) = t • F.u (τ 0) ∧ e • F.u (τ 1) = t • F.u (τ 1) ∧
      e • F.u (τ 2) = t • F.u (τ 2)) :
    AllCenters (centSub 𝔈) (Submodule.span K (Set.range (F.blk τ))) := by
  classical
  intro v hv hiso
  obtain ⟨c, rfl⟩ := (mem_span_range_iff _ v).1 hv
  have hiso' : herm σ c c = 0 := by rwa [herm_orthoEmb (F.blk_isON hτ)] at hiso
  have hn : ∀ t : K, σ t * t = if t = 0 then 0 else 1 := fun t => by
    by_cases ht : t = 0 <;> simp [ht, hK.norm_one]
  have hpr : ∀ (a b : Fin n), a ≠ b → ∀ (α β : K), α ≠ 0 → β ≠ 0 →
      IsCenter (centSub 𝔈) (α • F.u a + β • F.u b) := fun a b hab α β hα hβ =>
    F.isCenter_pair hK hpair hab (by rw [hK.norm_one α hα, hK.norm_one β hβ]; exact hK.two)
  have hvec : orthoEmb (F.blk τ) c = c 0 • F.u (τ 0) + c 1 • F.u (τ 1) + c 2 • F.u (τ 2) +
      c 3 • F.u (τ 3) := by
    simp [orthoEmb_apply, Fin.sum_univ_four, EigenFrame.blk]
  have n01 : τ 0 ≠ τ 1 := hτ.ne (by decide)
  have n02 : τ 0 ≠ τ 2 := hτ.ne (by decide)
  have n03 : τ 0 ≠ τ 3 := hτ.ne (by decide)
  have n12 : τ 1 ≠ τ 2 := hτ.ne (by decide)
  have n13 : τ 1 ≠ τ 3 := hτ.ne (by decide)
  have n23 : τ 2 ≠ τ 3 := hτ.ne (by decide)
  rw [herm_def, Fin.sum_univ_four] at hiso'
  simp only [hn] at hiso'
  by_cases h0 : c 0 = 0 <;> by_cases h1 : c 1 = 0 <;> by_cases h2 : c 2 = 0 <;>
    by_cases h3 : c 3 = 0 <;>
    first
    | (exfalso; simp [h0, h1, h2, h3, hK.two] at hiso'; done)
    | skip
  · rw [hvec]
    simp only [h0, h1, h2, h3, zero_smul, add_zero]
    exact isCenter_zero
  · rw [hvec]
    simp only [h0, h1, zero_smul, zero_add]
    exact hpr _ _ n23 _ _ h2 h3
  · rw [hvec]
    simp only [h0, h2, zero_smul, zero_add, add_zero]
    exact hpr _ _ n13 _ _ h1 h3
  · rw [hvec]
    simp only [h0, h3, zero_smul, zero_add, add_zero]
    exact hpr _ _ n12 _ _ h1 h2
  · rw [hvec]
    simp only [h1, h2, zero_smul, zero_add, add_zero]
    exact hpr _ _ n03 _ _ h0 h3
  · rw [hvec]
    simp only [h1, h3, zero_smul, zero_add, add_zero]
    exact hpr _ _ n02 _ _ h0 h2
  · rw [hvec]
    simp only [h2, h3, zero_smul, add_zero]
    exact hpr _ _ n01 _ _ h0 h1
  · exact F.isCenter_full hK hne hpair hτ htri c (fun s => by fin_cases s <;> assumption)

end Block

end CFSG.LieType.SeitzGeneration.UnitaryTwo
