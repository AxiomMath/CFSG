module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Reduce
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019PSL
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalOdd Matrix

section SU

variable {K : Type} [Field K]

theorem signVec_mul_self' {n : ℕ} (k : Fin n) :
    signVec (n := n) (F := K) k * signVec (n := n) (F := K) k = 1 := by
  unfold signVec
  split_ifs <;> norm_num

@[expose] noncomputable def tGLU (n : ℕ) : GL (Fin n) K :=
  ⟨Matrix.diagonal signVec, Matrix.diagonal signVec,
    by
      rw [Matrix.diagonal_mul_diagonal]
      simp only [signVec_mul_self']
      exact Matrix.diagonal_one,
    by
      rw [Matrix.diagonal_mul_diagonal]
      simp only [signVec_mul_self']
      exact Matrix.diagonal_one⟩

theorem tGLU_mul_self (n : ℕ) : tGLU (K := K) n * tGLU n = 1 := by
  apply Units.ext
  change Matrix.diagonal (signVec (n := n) (F := K)) * Matrix.diagonal signVec = 1
  rw [Matrix.diagonal_mul_diagonal]
  simp only [signVec_mul_self']
  exact Matrix.diagonal_one

theorem tGLU_mem {n p f : ℕ} (hn : 4 ≤ n) (hodd : Odd (p ^ f)) :
    tGLU (K := K) n ∈ StatedSU n (p ^ f) K := by
  refine Subgroup.subset_closure ⟨det_diagonal_signVec hn, ?_⟩
  change ((Matrix.diagonal (signVec (n := n) (F := K))).map (· ^ (p ^ f)))ᵀ *
    Matrix.diagonal (signVec (n := n) (F := K)) = 1
  rw [Matrix.diagonal_map (f := fun x : K => x ^ (p ^ f)) (zero_pow hodd.pos.ne'),
    Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have : ∀ k : Fin n, signVec (n := n) (F := K) k ^ (p ^ f) * signVec (n := n) (F := K) k = 1 := by
    intro k
    unfold signVec
    split_ifs
    · rw [hodd.neg_one_pow]; norm_num
    · simp
  simp only [this]
  exact Matrix.diagonal_one

section Comm

variable {σ : K →+* K} {u : K} {n : ℕ} (hn : 4 ≤ n)

theorem uε_support (j : Fin 2) (i : Fin n) (h : uε u hn j i ≠ 0) : i.val < 4 := by
  by_contra hlt
  apply h
  have hj := j.isLt
  have h1 : i ≠ ⟨2 * j, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have h2 : i ≠ ⟨2 * j + 1, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  simp [uε, Pi.single_apply, h1, h2]

theorem uεbar_support (j : Fin 2) (i : Fin n) (h : uεbar σ u hn j i ≠ 0) : i.val < 4 := by
  by_contra hlt
  apply h
  have hj := j.isLt
  have h1 : i ≠ ⟨2 * j, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have h2 : i ≠ ⟨2 * j + 1, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  simp [uεbar, Pi.single_apply, h1, h2]

theorem diag_mul_uP (j k : Fin 2) :
    Matrix.diagonal (signVec (n := n) (F := K)) * uP σ u hn j k =
      uP σ u hn j k * Matrix.diagonal (signVec (n := n) (F := K)) := by
  ext i i'
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [uP, vecMulVec_apply]
  by_cases ha : uε u hn j i = 0
  · simp [ha]
  by_cases hb : uεbar σ u hn k i' = 0
  · simp [hb]
  have hi := uε_support hn j i ha
  have hi' := uεbar_support hn k i' hb
  simp only [signVec, hi, hi', if_true]
  ring

theorem diag_mul_uN (η : K) (v : K × K) :
    Matrix.diagonal (signVec (n := n) (F := K)) * uN hn σ u η v =
      uN hn σ u η v * Matrix.diagonal (signVec (n := n) (F := K)) := by
  simp only [uN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    diag_mul_uP hn]

theorem tGLU_comm_uHom₄ (hu : σ u * u = -1) {η : K} (x : Multiplicative (K × K)) :
    tGLU n * uHom₄ hn (η := η) hu x = uHom₄ hn (η := η) hu x * tGLU n := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change Matrix.diagonal (signVec (n := n) (F := K)) * (uHom₄ hn (η := η) hu x : Matrix _ _ K) =
    (uHom₄ hn (η := η) hu x : Matrix _ _ K) * Matrix.diagonal (signVec (n := n) (F := K))
  rw [uHom₄, coe_glOfAdd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    diag_mul_uN hn]

end Comm

theorem injective_statedProj_of_fix {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}
    {A : Type*} [Group A] (φ : A →* GL ι K) (hφ : Function.Injective φ) (hH : ∀ a, φ a ∈ H)
    {v : ι → K} (hv : v ≠ 0) (hfix : ∀ a, (φ a : Matrix ι ι K) *ᵥ v = v) :
    Function.Injective
      ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp (φ.codRestrict H hH)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at ha
  obtain ⟨c, hc⟩ := ha
  have hc' : (φ a : Matrix ι ι K) = scalar ι (c : K) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  have h1 : (c : K) • v = v := by
    have h := hfix a
    rw [hc'] at h
    calc (c : K) • v = scalar ι (c : K) *ᵥ v := by
          ext i
          simp [scalar_apply, mulVec_diagonal]
      _ = v := h
  have hc1 : (c : K) = 1 := by
    by_contra hne
    apply hv
    have h2 : ((c : K) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have h3 : φ a = 1 := by
    apply Units.ext
    rw [hc', hc1, map_one, Units.val_one]
  exact hφ (h3.trans (map_one φ).symm)

end SU

theorem exists_involution_statedSU {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ t : StatedProj (StatedSU n (p ^ f) K), orderOf t = 2 ∧
      ∃ E : Subgroup (StatedProj (StatedSU n (p ^ f) K)),
        E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hn4 : 4 ≤ n := by omega
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := charP_of_card hK'
  obtain ⟨u, η, hu, hη0, hη⟩ := exists_unitary_elems hp2 hK
  set σ := iterateFrobenius K p f with hσdef
  have hσ := frob_frob hK
  have hu' : σ u * u = -1 := by rw [frob_apply]; exact hu
  have hη' : σ η = -η := by rw [frob_apply]; exact hη
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hodd : Odd (p ^ f) := (((Fact.out : p.Prime).eq_two_or_odd').resolve_left hp2).pow
  let cc : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hcc : Function.Injective cc := (ZMod.castHom (dvd_refl p) K).injective
  have hσcc : ∀ x, σ (cc x) = cc x := fun x =>
    RingHom.congr_fun (RingHom.ext_zmod (σ.comp cc) cc) x
  have hind : ∀ a b : ZMod p, cc a + cc b * η = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg σ hab
    rw [map_add, map_mul, hσcc, hσcc, hη', map_zero] at h1
    have h3 : cc a = 0 := by
      have : (2 : K) * cc a = 0 := by linear_combination hab + h1
      exact (mul_eq_zero.1 this).resolve_left h2
    have h4 : cc b = 0 := by
      rw [h3, zero_add] at hab
      exact (mul_eq_zero.1 hab).resolve_right hη0
    exact ⟨(map_eq_zero_iff cc hcc).1 h3, (map_eq_zero_iff cc hcc).1 h4⟩
  let ψ : (Fin 4 → ZMod p) →+ K × K :=
    { toFun := fun c => (cc (c 0) + cc (c 1) * η, cc (c 2) + cc (c 3) * η)
      map_zero' := by simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h01 := hind _ _ (congrArg Prod.fst hc)
    have h23 := hind _ _ (congrArg Prod.snd hc)
    funext i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h23.1
    · exact h23.2
  let φ : Multiplicative (Fin 4 → ZMod p) →* GL (Fin n) K :=
    (uHom₄ hn4 (η := η) hu').comp (AddMonoidHom.toMultiplicative ψ)
  have hinj₄ : Function.Injective (uHom₄ hn4 (η := η) hu') :=
    glOfAdd_injective fun v w h => uN_injective hn4 h2 hη0 (add_left_cancel h)
  have hφinj : Function.Injective φ := fun a b h =>
    Multiplicative.toAdd.injective (hψ (Multiplicative.ofAdd.injective (hinj₄ h)))
  have hmem₄ : ∀ x : Multiplicative (K × K),
      uHom₄ hn4 (η := η) hu' x ∈ StatedSU n (p ^ f) K := by
    intro x
    refine Subgroup.subset_closure ⟨det_eq_one_of_hom (p := p) _ x, ?_⟩
    have hmap : ((uHom₄ hn4 (η := η) hu' x : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f))) =
        (uHom₄ hn4 (η := η) hu' x : Matrix (Fin n) (Fin n) K).map σ := by
      congr 1
    rw [hmap]
    exact hstar_uHom₄ hn4 hu' hσ hη' x
  have hmem : ∀ a, φ a ∈ StatedSU n (p ^ f) K := fun a => hmem₄ _
  have hfix : ∀ a, (φ a : Matrix (Fin n) (Fin n) K) *ᵥ uε u hn4 0 = uε u hn4 0 := fun a => by
    change (uHom₄ hn4 (η := η) hu' _ : Matrix (Fin n) (Fin n) K) *ᵥ uε u hn4 0 = uε u hn4 0
    rw [uHom₄, coe_glOfAdd, add_mulVec, one_mulVec, uN_mulVec hn4 hu', add_zero]
  have hv : uε u hn4 0 ≠ 0 := fun h => by
    simpa [uε, Pi.single_apply, Fin.ext_iff] using congrFun h ⟨0, by omega⟩
  let π := QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))
  have hinj : Function.Injective (π.comp (φ.codRestrict (StatedSU n (p ^ f) K) hmem)) :=
    injective_statedProj_of_fix φ hφinj hmem hv hfix
  let xt : StatedSU n (p ^ f) K := ⟨tGLU n, tGLU_mem hn4 hodd⟩
  have ht_sq : π xt ^ 2 = 1 := by
    rw [← map_pow]
    have : xt ^ 2 = 1 := Subtype.ext (by
      change tGLU (K := K) n ^ 2 = 1
      rw [pow_two, tGLU_mul_self])
    rw [this, map_one]
  have ht_ne : π xt ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    have hc' : (Matrix.scalar (Fin n) (c : K)) = Matrix.diagonal (signVec (n := n) (F := K)) := by
      rw [← GeneralLinearGroup.coe_scalar, hc]
      rfl
    have e0 : (c : K) = -1 := by
      have := congrArg (fun B : Matrix (Fin n) (Fin n) K => B ⟨0, by omega⟩ ⟨0, by omega⟩) hc'
      simpa [signVec, scalar_apply] using this
    have e4 : (c : K) = 1 := by
      have := congrArg (fun B : Matrix (Fin n) (Fin n) K => B ⟨4, by omega⟩ ⟨4, by omega⟩) hc'
      simpa [signVec, scalar_apply] using this
    apply h2
    linear_combination e0 - e4
  have hcomm : ∀ a, π xt * (π.comp (φ.codRestrict (StatedSU n (p ^ f) K) hmem)) a =
      (π.comp (φ.codRestrict (StatedSU n (p ^ f) K) hmem)) a * π xt := by
    intro a
    show π xt * π (φ.codRestrict _ hmem a) = π (φ.codRestrict _ hmem a) * π xt
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (tGLU_comm_uHom₄ hn4 hu' _)
  obtain ⟨E, hEc, hEab, hEcard⟩ := exists_subgroup_of_hom _ hinj (π xt) hcomm
  exact ⟨π xt, orderOf_eq_prime ht_sq ht_ne, E, hEc, hEab, hEcard⟩

theorem involution_typeTwistedA4 : InvolutionAt FamTwistedA4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.twistedA r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  obtain ⟨t, ht, E, hEc, hE, hcard'⟩ := exists_involution_statedSU (n := r + 1) (p := q.p)
    (f := q.exponent) hp2 (by omega) hcard
  obtain ⟨t', ht', E', hEc', hE', hcard''⟩ := exists_involution_transport e' hEc hE hcard'
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard''⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
