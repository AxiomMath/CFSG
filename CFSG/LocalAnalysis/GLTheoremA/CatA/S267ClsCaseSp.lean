module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCases
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutB2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamLayer
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LieType.Steinberg.CentralExt.SpThree
import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped IsMulCommutative

section Alt

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {p : ℕ}
variable {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]

theorem glRep_mem_weightFamily [Finite ↥Aε] (a : ↥Aε) (i : Option (Hyperplane ↥Aε p))
    {v : ι → K} (hv : v ∈ weightFamily (p := p) (glRep Aε) i) :
    glRep Aε a v ∈ weightFamily (p := p) (glRep Aε) i := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨glRep Aε a w, (apply_asAlgebraHom_comm (glRep Aε) _ a w).symm⟩

theorem projI_glRep [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (I : Finset (Hyperplane ↥Aε p)) (a : ↥Aε) (v : ι → K) :
    projI (glRep Aε) I (glRep Aε a v) = glRep Aε a (projI (glRep Aε) I v) :=
  projI_comm_of_preserves (glRep Aε) hp hA hpK I (glRep Aε a).toAddMonoidHom
    (fun i _ hv => glRep_mem_weightFamily a i hv) v

theorem wtU_wtW_orth [Finite ↥Aε] {σ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K}
    (hAεβ : Aε ≤ isomGL β) (I : Finset (Hyperplane ↥Aε p)) {u w : ι → K}
    (hu : u ∈ wtU Aε I) (hw : w ∈ wtW Aε I) : β u w = 0 ∧ β w u = 0 := by
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have hu0 : projI (glRep Aε) I u = 0 := hu
  obtain ⟨v, rfl⟩ := hw
  refine ⟨?_, ?_⟩
  · rw [← projI_left (glRep Aε) β hρ I u v, hu0, map_zero, LinearMap.zero_apply]
  · rw [projI_left (glRep Aε) β hρ I v u, hu0, map_zero]

theorem wtU_nondeg [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    {σ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} (hβ : β.SeparatingLeft)
    (hAεβ : Aε ≤ isomGL β) (I : Finset (Hyperplane ↥Aε p)) {u : ι → K} (hu : u ∈ wtU Aε I)
    (h : ∀ u' ∈ wtU Aε I, β u u' = 0) : u = 0 := by
  refine hβ u fun v => ?_
  have hv : v - projI (glRep Aε) I v ∈ wtU Aε I := by
    show projI (glRep Aε) I (v - projI (glRep Aε) I v) = 0
    rw [map_sub, projI_projI (glRep Aε) hp hA hpK, sub_self]
  rw [← sub_add_cancel v (projI (glRep Aε) I v), map_add, h _ hv,
    (wtU_wtW_orth hAεβ I hu ⟨v, rfl⟩).1, add_zero]

theorem weightSpace_le_wtU [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) {I : Finset (Hyperplane ↥Aε p)} {H₀ : Hyperplane ↥Aε p} (hH₀ : H₀ ∉ I) :
    weightSpace (glRep Aε) H₀.1 ≤ wtU Aε I := fun v hv =>
  projI_apply_of_not_mem (glRep Aε) hp hA hpK
    (fun H hH h => hH₀ (by rw [Option.some_injective _ h]; exact hH))
    (show v ∈ weightFamily (p := p) (glRep Aε) (some H₀) from hv)

theorem wtW_mono [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    {I I' : Finset (Hyperplane ↥Aε p)} (hII' : I ⊆ I') : wtW Aε I ≤ wtW Aε I' := by
  show LinearMap.range (projI (glRep Aε) I) ≤ LinearMap.range (projI (glRep Aε) I')
  rw [range_projI (glRep Aε) hp hA hpK, range_projI (glRep Aε) hp hA hpK]
  exact iSup₂_le fun H hH => le_iSup₂_of_le (f := fun H (_ : H ∈ I') =>
    weightSpace (glRep Aε) H.1) H (hII' hH) le_rfl

theorem wtU_anti [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    {I I' : Finset (Hyperplane ↥Aε p)} (hII' : I ⊆ I') : wtU Aε I' ≤ wtU Aε I := fun v hv =>
  (projI_eq_zero_iff (glRep Aε) hp hA hpK I v).2 fun H hH =>
    (projI_eq_zero_iff (glRep Aε) hp hA hpK I' v).1 hv H (hII' hH)

theorem mem_blkSub_wt [Finite ↥Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) {σ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K}
    (hAεβ : Aε ≤ isomGL β) (I : Finset (Hyperplane ↥Aε p)) {x : ↥Aε} (hx : ∀ H ∈ I, x ∈ H.1) :
    (x : GL ι K) ∈ blkSub β (wtU Aε I) (wtW Aε I) := by
  refine ⟨hAεβ x.2, fun u hu => ?_, fun w hw => ?_⟩
  · show projI (glRep Aε) I (glEquiv (x : GL ι K) u) = 0
    rw [← glRep_apply_eq_glEquiv, projI_glRep hp hA hpK I x u,
      (hu : projI (glRep Aε) I u = 0), map_zero]
  · obtain ⟨v, rfl⟩ := hw
    rw [← glRep_apply_eq_glEquiv, projI_apply, map_sum]
    exact Finset.sum_congr rfl fun H hH =>
      apply_eq_of_mem_weightSpace (glRep Aε) (hx H hH) ⟨v, rfl⟩

theorem scalar_eq_one_of_isom [Finite ↥Aε] (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : ∀ a : ↥Aε, a ^ p = 1) {J : Matrix ι ι K} (hAεβ : Aε ≤ isomGL (Matrix.toBilin' J))
    {U : Submodule K (ι → K)} (hU : U ≠ ⊥)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0) {y : GL ι K}
    (hy : y ∈ Aε) {c : K} (hc : ∀ u ∈ U, glEquiv y u = c • u) : c = 1 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨u', hu', huu'⟩ : ∃ u' ∈ U, Matrix.toBilin' J u u' ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd u hu h)
  have hiso := mem_isomGL.1 (hAεβ hy) u u'
  rw [← glEquiv_apply, ← glEquiv_apply, hc u hu, hc u' hu'] at hiso
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hiso
  have hc2 : c ^ 2 = 1 := by
    have h0 : (c * c - 1) * Matrix.toBilin' J u u' = 0 := by linear_combination hiso
    rcases mul_eq_zero.1 h0 with h | h
    · linear_combination h
    · exact absurd h huu'
  have hyp : y ^ p = 1 := by simpa using congrArg Subtype.val (hA ⟨y, hy⟩)
  have hpow : ∀ n : ℕ, glEquiv (y ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hc u hu, map_smul, ih, smul_smul,
        ← pow_succ']
  have hcp : c ^ p = 1 := by
    have h := hpow p
    rw [hyp, map_one] at h
    have h' : (c ^ p - 1) • u = 0 := by
      rw [sub_smul, ← h, one_smul]
      simp
    rcases smul_eq_zero.1 h' with h'' | h''
    · exact sub_eq_zero.1 h''
    · exact absurd h'' hu0
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at hcp
  exact hcp

theorem false_of_finrank_two_of_card_mod [Finite K] (hp : p.Prime)
    (hK3 : ((Nat.card K : ℕ) : ZMod p) = 3)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {σ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K}
    {M N : Submodule K (ι → K)} (hM : Module.finrank K M = 2) {x : GL ι K}
    (hx : x ∈ blkSub β M N) (hxp : x ^ p = 1) (hx1 : ∃ m ∈ M, glEquiv x m ≠ m) : False := by
  classical
  set g := resU β M N ⟨x, hx⟩ with hg
  have hgp : g ^ p = 1 := by
    have h1 : (⟨x, hx⟩ : blkSub β M N) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hg, ← map_pow, h1, map_one]
  have hg1 : g ≠ 1 := by
    obtain ⟨m, hm, hxm⟩ := hx1
    intro h
    apply hxm
    have h1 := congrArg (fun e : M ≃ₗ[K] M => ((e ⟨m, hm⟩ : M) : ι → K)) h
    simpa [hg, coe_resU_apply] using h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  haveI : Fintype K := Fintype.ofFinite K
  let b := Module.finBasisOfFinrankEq K M hM
  let c : (M ≃ₗ[K] M) ≃ ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    { toFun := fun e => (b.equivFun.symm.trans e).trans b.equivFun
      invFun := fun e => (b.equivFun.trans e).trans b.equivFun.symm
      left_inv := fun e => LinearEquiv.ext fun m => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      right_inv := fun e => LinearEquiv.ext fun v => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] }
  have hcard : Nat.card (M ≃ₗ[K] M) =
      (Nat.card K ^ 2 - Nat.card K ^ 0) * (Nat.card K ^ 2 - Nat.card K ^ 1) := by
    rw [Nat.card_congr c, ← Nat.card_congr
      (glEquiv : GL (Fin 2) K ≃* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K))).toEquiv,
      Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
    rfl
  have h1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have h2 : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : 1 ≤ Nat.card K ^ 2 := h1.trans h2
  have hdvd : p ∣ 2 ^ 4 * 3 := by
    have h := orderOf_dvd_natCard g
    rw [hord, hcard, pow_zero, pow_one] at h
    have h' := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h2, Nat.cast_pow, Nat.cast_one, hK3] at h'
    rw [← ZMod.natCast_eq_zero_iff]
    rw [show ((2 ^ 4 * 3 : ℕ) : ZMod p) = (3 ^ 2 - 1) * (3 ^ 2 - 3) by push_cast; ring]
    exact h'
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem finrank_ne_two_of_card_mod [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK3 : ((Nat.card K : ℕ) : ZMod p) = 3) (hpK : (p : K) ≠ 0) [Finite ↥Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) {J : Matrix ι ι K}
    (hJ : ∀ x, Matrix.toBilin' J x x = 0) (hJnd : (Matrix.toBilin' J).SeparatingLeft)
    (hAεβ : Aε ≤ isomGL (Matrix.toBilin' J)) (H : Hyperplane ↥Aε p)
    (hH : weightSpace (glRep Aε) H.1 ≠ ⊥) {x : ↥Aε} (hxH : x ∉ H.1)
    (hx' : ∀ H' : Hyperplane ↥Aε p, H' ≠ H → weightSpace (glRep Aε) H'.1 ≠ ⊥ → x ∈ H'.1)
    {M : Submodule K (ι → K)} (hWM : weightSpace (glRep Aε) H.1 ≤ M) :
    Module.finrank K M ≠ 2 := by
  classical
  have hρ : IsIsomRep (Matrix.toBilin' J) (glRep Aε) := isIsomRep_glRep hAεβ
  have hnd : ∀ u ∈ weightSpace (glRep Aε) H.1,
      (∀ u' ∈ weightSpace (glRep Aε) H.1, Matrix.toBilin' J u u' = 0) → u = 0 :=
    fun u hu h => weightFamily_nondeg (Matrix.toBilin' J) (glRep Aε) hρ hp hA hpK hJnd
      (some H) hu h
  have h2 := CFSG.ComponentClassification.CatalogueBSymplecticB.two_le_finrank_of_ne_bot hH
    (resBilin J _) (resBilin_isAlt hJ _) (resBilin_nondegenerate hJ hnd)
  have hne : Module.finrank K (weightSpace (glRep Aε) H.1) ≠ 2 := by
    intro h2'
    refine false_of_finrank_two_of_card_mod hp hK3 hp2 hp3 h2' (N := wtU Aε {H})
      (x := (x : GL ι K)) ⟨hAεβ x.2, fun u hu => ?_, fun w hw => ?_⟩
      (by simpa using congrArg Subtype.val (hA x)) ?_
    · rw [← glRep_apply_eq_glEquiv]
      exact apply_mem_weightSpace (glRep Aε) H.1 x hu
    · rw [← glRep_apply_eq_glEquiv]
      exact (apply_eq_self_iff_projI (glRep Aε) hp hA hpK (I := {H})
        (fun H'' hH'' => by rw [Finset.mem_singleton.1 hH'']; exact hxH)
        (fun H' hH' hne => hx' H' (fun h => hH' (Finset.mem_singleton.2 h)) hne) w).2 hw
    · obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
      refine ⟨m, hm, fun hfix => hm0 ?_⟩
      rw [← glRep_apply_eq_glEquiv] at hfix
      exact eq_zero_of_mem_weightSpace_of_fixed (glRep Aε) hp hA hpK hxH hm hfix
  have := Submodule.finrank_mono hWM
  omega

theorem finrank_ne_two_or [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    [Finite ↥Aε] (hA : ∀ a : ↥Aε, a ^ p = 1) {J : Matrix ι ι K}
    (hJ : ∀ x, Matrix.toBilin' J x x = 0) (hJnd : (Matrix.toBilin' J).SeparatingLeft)
    (hAεβ : Aε ≤ isomGL (Matrix.toBilin' J)) (H : Hyperplane ↥Aε p)
    (hH : weightSpace (glRep Aε) H.1 ≠ ⊥) {x : ↥Aε} (hxH : x ∉ H.1)
    (hx' : ∀ H' : Hyperplane ↥Aε p, H' ≠ H → weightSpace (glRep Aε) H'.1 ≠ ⊥ → x ∈ H'.1)
    {M : Submodule K (ι → K)} (hWM : weightSpace (glRep Aε) H.1 ≤ M) :
    Module.finrank K M ≠ 2 ∨ Nat.card K ≠ 3 := by
  by_cases hK3 : Nat.card K = 3
  swap
  · exact Or.inr hK3
  left
  have hp3 : p ≠ 3 := by
    rintro rfl
    haveI : CharP K 3 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three le_rfl (by rw [hK3, pow_one])
    exact hpK (by exact_mod_cast CharP.cast_eq_zero K 3)
  exact finrank_ne_two_of_card_mod hp hp2 hp3 (by rw [hK3]; push_cast; rfl) hpK hA hJ hJnd hAεβ
    H hH hxH hx' hWM

theorem glaPLayer_blkI_inf_centralizer_ne_bot [Finite K] (hodd : Odd (Nat.card K))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) [Finite ↥Aε] (hA : ∀ a : ↥Aε, a ^ p = 1)
    {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0)
    (hJnd : (Matrix.toBilin' J).SeparatingLeft) (hAεβ : Aε ≤ isomGL (Matrix.toBilin' J))
    [DecidableEq (Hyperplane ↥Aε p)] {I : Finset (Hyperplane ↥Aε p)}
    {H₂ H₀ : Hyperplane ↥Aε p} (hH₂ : H₂ ∉ I) (hH₀ : H₀ ∉ insert H₂ I)
    (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥) (hI : ∀ H ∈ I, weightSpace (glRep Aε) H.1 ≠ ⊥)
    (hW₂ : weightSpace (glRep Aε) H₂.1 ≠ ⊥) {a : ↥Aε} (ha : a ∉ H₂.1)
    (ha' : ∀ H' : Hyperplane ↥Aε p, H' ≠ H₂ → weightSpace (glRep Aε) H'.1 ≠ ⊥ → a ∈ H'.1)
    {x : ↥Aε} (hx : x ∉ H₀.1)
    (hx' : ∀ H' : Hyperplane ↥Aε p, H' ≠ H₀ → weightSpace (glRep Aε) H'.1 ≠ ⊥ → x ∈ H'.1) :
    GLAPLayer p (blkI (Matrix.toBilin' J) (wtU Aε I) (wtW Aε I) ⊓
      Subgroup.centralizer {(a : GL ι K)}) ≠ ⊥ := by
  classical
  set β := Matrix.toBilin' J with hβdef
  set ρ := glRep Aε with hρdef
  set I' := insert H₂ I with hI'def
  have hII' : I ⊆ I' := Finset.subset_insert _ _
  have hH₂I' : H₂ ∈ I' := Finset.mem_insert_self _ _
  have hUW' : IsCompl (wtU Aε I') (wtW Aε I') := isCompl_ker_range_projI ρ hp hA hpK I'
  have horth' : ∀ u ∈ wtU Aε I', ∀ w ∈ wtW Aε I', β u w = 0 ∧ β w u = 0 :=
    fun u hu w hw => wtU_wtW_orth hAεβ I' hu hw
  have hnd' : ∀ u ∈ wtU Aε I', (∀ u' ∈ wtU Aε I', β u u' = 0) → u = 0 :=
    fun u hu h => wtU_nondeg hp hA hpK hJnd hAεβ I' hu h
  have hW₀U' : weightSpace ρ H₀.1 ≤ wtU Aε I' := weightSpace_le_wtU hp hA hpK hH₀
  have hU'ne : wtU Aε I' ≠ ⊥ := fun h => hW₀ (eq_bot_iff.2 (hW₀U'.trans h.le))
  have hdim' := CFSG.ComponentClassification.CatalogueBSymplecticB.two_le_finrank_of_ne_bot hU'ne
    (resBilin J _) (resBilin_isAlt hJ _) (resBilin_nondegenerate hJ hnd')
  have hexc' := finrank_ne_two_or hp hp2 hpK hA hJ hJnd hAεβ H₀ hW₀ hx hx' hW₀U'
  have hxI' : ∀ H ∈ I', x ∈ H.1 := fun H hH => hx' H (fun h => hH₀ (h ▸ hH)) (by
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact hW₂
    · exact hI H hH)
  have hxB := mem_blkSub_wt hp hA hpK hAεβ I' hxI'
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf (x : GL ι K) = p := orderOf_eq_prime
    (by simpa using congrArg Subtype.val (hA x))
    (fun h => hx (by rw [show x = 1 from Subtype.ext h]; exact H₀.1.one_mem))
  have hq := isQuasisimple_blkI_toBilin' hodd hJ hUW' horth' hnd' hdim' hexc'
  have hpJ := dvd_card_blkI_toBilin' hodd hJ hUW' horth' hnd' hdim' hexc' hxB hxo
  have hafix : ∀ v, glEquiv (a : GL ι K) v = v ↔ projI ρ {H₂} v = 0 := fun v => by
    rw [← glRep_apply_eq_glEquiv]
    exact apply_eq_self_iff_projI ρ hp hA hpK
      (fun H hH => by rw [Finset.mem_singleton.1 hH]; exact ha)
      (fun H' hH' hne => ha' H' (fun h => hH' (Finset.mem_singleton.2 h)) hne) v
  have haU' : ∀ u ∈ wtU Aε I', glEquiv (a : GL ι K) u = u := fun u hu =>
    (hafix u).2 ((projI_eq_zero_iff ρ hp hA hpK {H₂} u).2 fun H hH => by
      rw [Finset.mem_singleton.1 hH]
      exact (projI_eq_zero_iff ρ hp hA hpK I' u).1 hu H₂ hH₂I')
  have haW' : ∀ w ∈ wtW Aε I', glEquiv (a : GL ι K) w ∈ wtW Aε I' := by
    rintro _ ⟨v, rfl⟩
    rw [← glRep_apply_eq_glEquiv, ← projI_glRep hp hA hpK I' a v]
    exact ⟨_, rfl⟩
  have hU'iff : ∀ v ∈ wtU Aε I, glEquiv (a : GL ι K) v = v → v ∈ wtU Aε I' := fun v hv hav => by
    have h1 := (hafix v).1 hav
    show projI ρ I' v = 0
    refine (projI_eq_zero_iff ρ hp hA hpK I' v).2 fun H hH => ?_
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact (projI_eq_zero_iff ρ hp hA hpK {H} v).1 h1 H (Finset.mem_singleton_self _)
    · exact (projI_eq_zero_iff ρ hp hA hpK I v).1 hv H hH
  have hsub : blkSub β (wtU Aε I') (wtW Aε I') ≤ blkSub β (wtU Aε I) (wtW Aε I) := by
    intro g hg
    refine ⟨hg.1, fun u hu => ?_, fun w hw => hg.2.2 w (wtW_mono hp hA hpK hII' hw)⟩
    set e := ρ.asAlgebraHom (eps K ↥Aε p (some H₂)) u with he
    have heW : e ∈ weightSpace ρ H₂.1 := ⟨u, rfl⟩
    have heU : e ∈ wtU Aε I := weightSpace_le_wtU hp hA hpK hH₂ heW
    have heW' : e ∈ wtW Aε I' := ⟨e, projI_apply_of_mem ρ hp hA hpK hH₂I' heW⟩
    have hu' : u - e ∈ wtU Aε I' := by
      show projI ρ I' (u - e) = 0
      refine (projI_eq_zero_iff ρ hp hA hpK I' _).2 fun H hH => ?_
      rcases Finset.mem_insert.1 hH with rfl | hH
      · rw [map_sub, eps_apply_of_mem ρ hp hA hpK (some H) heW, sub_self]
      · have hne : some H ≠ some H₂ := fun h => hH₂ (Option.some_injective _ h ▸ hH)
        rw [map_sub, (projI_eq_zero_iff ρ hp hA hpK I u).1 hu H hH,
          eps_apply_of_mem_ne ρ hp hA hpK hne heW, sub_self]
    have hsplit : u = (u - e) + e := by abel
    rw [hsplit, map_add, hg.2.2 e heW']
    exact (wtU Aε I).add_mem (wtU_anti hp hA hpK hII' (hg.2.1 _ hu')) heU
  have hJle : blkI β (wtU Aε I') (wtW Aε I') ≤ blkI β (wtU Aε I) (wtW Aε I) :=
    Subgroup.commutator_mono hsub hsub
  have hcent : blkSub β (wtU Aε I') (wtW Aε I') ≤ Subgroup.centralizer {(a : GL ι K)} := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply glEquiv.injective
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    set w := projI ρ I' v with hw
    have hwW' : w ∈ wtW Aε I' := ⟨v, rfl⟩
    have hu' : v - w ∈ wtU Aε I' := by
      show projI ρ I' (v - w) = 0
      rw [map_sub, hw, projI_projI ρ hp hA hpK, sub_self]
    have hv : v = (v - w) + w := by abel
    have h1 : glEquiv g (glEquiv (a : GL ι K) v) =
        glEquiv g (v - w) + glEquiv (a : GL ι K) w := by
      conv_lhs => rw [hv]
      rw [map_add, haU' _ hu', map_add, hg.2.2 _ (haW' w hwW')]
    have h2 : glEquiv (a : GL ι K) (glEquiv g v) =
        glEquiv g (v - w) + glEquiv (a : GL ι K) w := by
      conv_lhs => rw [hv]
      rw [map_add, map_add, hg.2.2 w hwW', haU' _ (hg.2.1 _ hu')]
    rw [h1, h2]
  have hJcent : blkI β (wtU Aε I') (wtW Aε I') ≤ Subgroup.centralizer {(a : GL ι K)} :=
    (blkI_le_blkSub β _ _).trans hcent
  set M := blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {(a : GL ι K)} with hM
  have hpres : ∀ m ∈ M, (∀ u ∈ wtU Aε I', glEquiv m u ∈ wtU Aε I') ∧
      ∀ w ∈ wtW Aε I', glEquiv m w ∈ wtW Aε I' := by
    intro m hm
    have hmB : m ∈ blkSub β (wtU Aε I) (wtW Aε I) := blkI_le_blkSub β _ _ hm.1
    have hma : m * (a : GL ι K) = (a : GL ι K) * m :=
      Subgroup.mem_centralizer_singleton_iff.1 hm.2
    have hcomm : ∀ v, glEquiv m (glEquiv (a : GL ι K) v) =
        glEquiv (a : GL ι K) (glEquiv m v) := fun v => by
      rw [← LinearEquiv.mul_apply, ← map_mul, hma, map_mul, LinearEquiv.mul_apply]
    refine ⟨fun u hu => ?_, fun w hw => ?_⟩
    · refine hU'iff _ (hmB.2.1 u (wtU_anti hp hA hpK hII' hu)) ?_
      rw [← hcomm, haU' u hu]
    · obtain ⟨v, rfl⟩ := hw
      have hsplit : projI ρ I' v = projI ρ {H₂} v + projI ρ I v := by
        rw [projI_apply, projI_apply, projI_apply, hI'def, Finset.sum_insert hH₂,
          Finset.sum_singleton]
      have hm2 := (preserves_of_comm_supported ρ hp hA hpK (I := {H₂}) (x := a)
        (fun H hH => by rw [Finset.mem_singleton.1 hH]; exact ha)
        (fun H' hH' hne => ha' H' (fun h => hH' (Finset.mem_singleton.2 h)) hne)
        (glEquiv m).toLinearMap (fun v => by
          rw [glRep_apply_eq_glEquiv]
          exact hcomm v)).2 _ ⟨v, rfl⟩
      rw [hsplit, map_add, hmB.2.2 _ ⟨v, rfl⟩]
      exact (wtW Aε I').add_mem
        (wtW_mono hp hA hpK (Finset.singleton_subset_iff.2 hH₂I') hm2)
        (wtW_mono hp hA hpK hII' ⟨v, rfl⟩)
  have hconj : ∀ m ∈ M, (blkSub β (wtU Aε I') (wtW Aε I')).map (MulAut.conj m).toMonoidHom ≤
      blkSub β (wtU Aε I') (wtW Aε I') := by
    rintro m hm _ ⟨g, hg, rfl⟩
    have hmi : m⁻¹ ∈ M := M.inv_mem hm
    have hmβ : m ∈ isomGL β := blkSub_le_isomGL β _ _ (blkI_le_blkSub β _ _ hm.1)
    obtain ⟨hU1, hW1⟩ := hpres m hm
    obtain ⟨hU2, hW2⟩ := hpres m⁻¹ hmi
    refine ⟨?_, fun u hu => ?_, fun w hw => ?_⟩
    · exact (isomGL β).mul_mem ((isomGL β).mul_mem hmβ hg.1) ((isomGL β).inv_mem hmβ)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, LinearEquiv.mul_apply]
      exact hU1 _ (hg.2.1 _ (by simpa using hU2 u hu))
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, LinearEquiv.mul_apply]
      have h1 : glEquiv m⁻¹ w ∈ wtW Aε I' := hW2 w hw
      rw [map_inv] at h1 ⊢
      rw [hg.2.2 _ h1, ← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
  have hnormal : ((blkI β (wtU Aε I') (wtW Aε I')).subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : GL ι K) * n * (g : GL ι K)⁻¹ ∈
        (blkI β (wtU Aε I') (wtW Aε I')).map (MulAut.conj (g : GL ι K)).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rw [blkI, Subgroup.map_commutator] at h1
    have h2 := Subgroup.commutator_mono (hconj g g.2) (hconj g g.2) h1
    unfold blkI
    simpa using h2
  have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hq hpJ
    (le_inf hJle hJcent) hnormal
  intro hbot
  have hle : blkI β (wtU Aε I') (wtW Aε I') ≤ GLAPLayer p M := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.not_dvd_one hpJ

end Alt

section Sp

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem invol_mem_statedSp {Aε : Subgroup (GL (Fin r ⊕ Fin r) K)} [IsMulCommutative Aε]
    (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    (hAεβ : Aε ≤ isomGL (Matrix.toBilin' (formJ r K))) (I : Finset (Hyperplane ↥Aε p)) :
    glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ StatedSp r K := by
  apply ModelGen.mem_statedSp_of_mem_isomGL
  rw [mem_isomGL]
  intro x y
  rw [← glEquiv_apply, ← glEquiv_apply, MulEquiv.apply_symm_apply]
  exact invol_isometry (glRep Aε) hp hA hpK _ (isIsomRep_glRep hAεβ) I x y

theorem concA_sp_of_weights (hp : p.Prime) (hp2 : p ≠ 2) [hSn : S.Normal]
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hodd : Odd (Nat.card K)) (h2 : (2 : K) ≠ 0)
    (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B (StatedSp r K) (Matrix.toBilin' (formJ r K)))
    {Aε : Subgroup (GL (Fin r ⊕ Fin r) K)} [IsMulCommutative Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) (hAεL : Aε = liftGroup Dat)
    (hAεβ : Aε ≤ isomGL (Matrix.toBilin' (formJ r K))) (hAε𝒮 : Aε ≤ centGL (fieldSet Dat))
    (hmaxE : IsMaxElem (Matrix.toBilin' (formJ r K)) (glRep Aε) p (fieldSet Dat))
    [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p))
    (hI : ∀ H' ∈ I, weightSpace (glRep Aε) H'.1 ≠ ⊥) (hI1 : 1 ≤ I.card)
    {H₀ : Hyperplane ↥Aε p} (hH₀ : H₀ ∉ I) (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (hrank : p ^ (3 + I.card) ≤ Nat.card B) {x : ↥Aε} (hx : x ∉ H₀.1)
    (hx' : ∀ H' : Hyperplane ↥Aε p, H' ≠ H₀ → weightSpace (glRep Aε) H'.1 ≠ ⊥ → x ∈ H'.1)
    (hE : I.card = 1 →
      (∃ a ∈ Aε, (∃ u ∈ wtU Aε I, glEquiv a u ≠ u) ∧
        GLAPLayer p (blkI (Matrix.toBilin' (formJ r K)) (wtU Aε I) (wtW Aε I) ⊓
          Subgroup.centralizer {a}) ≠ ⊥) ∨
      FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A Dat.σ) :
    S267ConcA p S B := by
  classical
  have hJ : ∀ v, Matrix.toBilin' (formJ r K) v v = 0 := toBilin'_formJ_self
  have hJnd : (Matrix.toBilin' (formJ r K)).SeparatingLeft :=
    (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
      CFSG.RankThree.Classical.SteinbergBY.det_formJ_ne_zero).1
  have hUW := isCompl_ker_range_projI (glRep Aε) hp hA hpK I
  have horth : ∀ u ∈ wtU Aε I, ∀ w ∈ wtW Aε I,
      Matrix.toBilin' (formJ r K) u w = 0 ∧ Matrix.toBilin' (formJ r K) w u = 0 :=
    fun u hu w hw => wtU_wtW_orth hAεβ I hu hw
  have hnd : ∀ u ∈ wtU Aε I, (∀ u' ∈ wtU Aε I, Matrix.toBilin' (formJ r K) u u' = 0) →
      u = 0 :=
    fun u hu h => wtU_nondeg hp hA hpK hJnd hAεβ I hu h
  have hW₀U := weightSpace_le_wtU hp hA hpK hH₀
  have hUne : wtU Aε I ≠ ⊥ := fun h => hW₀ (eq_bot_iff.2 (hW₀U.trans h.le))
  have hdim := CFSG.ComponentClassification.CatalogueBSymplecticB.two_le_finrank_of_ne_bot hUne
    (resBilin _ _) (resBilin_isAlt hJ _) (resBilin_nondegenerate hJ hnd)
  have hexc := finrank_ne_two_or hp hp2 hpK hA hJ hJnd hAεβ H₀ hW₀ hx hx' hW₀U
  have hxI : ∀ H ∈ I, x ∈ H.1 := fun H hH => hx' H (fun h => hH₀ (h ▸ hH)) (hI H hH)
  have hxB := mem_blkSub_wt hp hA hpK hAεβ I hxI
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf (x : GL (Fin r ⊕ Fin r) K) = p := orderOf_eq_prime
    (by simpa using congrArg Subtype.val (hA x))
    (fun h => hx (by rw [show x = 1 from Subtype.ext h]; exact H₀.1.one_mem))
  have hsemi : FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A
      Dat.σ → ∀ i, ∀ v ∈ weightFamily (p := p)
      (glRep Aε) i, ModelGen.semiMap Dat.A Dat.σ v ∈ weightFamily (p := p) (glRep Aε) i := by
    intro hF i v hv
    refine preserves_weightFamily_of_semilinear (glRep Aε) (Dat.σ : K →+* K)
      (ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (fun a v => ?_) i hv
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) _ ⟨hF, rfl⟩ v).symm
  have hsemiU : FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A
      Dat.σ →
      ∀ u ∈ wtU Aε I, ModelGen.semiMap Dat.A Dat.σ u ∈ wtU Aε I := fun hF u hu => by
    show projI (glRep Aε) I (ModelGen.semiMap Dat.A Dat.σ u) = 0
    have h1 := projI_comm_of_preserves (glRep Aε) hp hA hpK I
      (ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom (hsemi hF) u
    exact h1.trans (by rw [(hu : projI (glRep Aε) I u = 0)]; exact map_zero _)
  have hsemiW : FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A
      Dat.σ →
      ∀ w ∈ wtW Aε I, ModelGen.semiMap Dat.A Dat.σ w ∈ wtW Aε I := by
    rintro hF _ ⟨v, rfl⟩
    exact ⟨ModelGen.semiMap Dat.A Dat.σ v, projI_comm_of_preserves (glRep Aε) hp hA hpK I
      (ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom (hsemi hF) v⟩
  refine concA_of_weights hp hB hBC hcore h2 hpK Dat ModelGen.statedSp_le_isomGL hA hAεL hAεβ
    hAε𝒮 hmaxE I hI hI1 hH₀ hW₀ hrank (invol_mem_statedSp hp hA hpK hAεβ I)
    (blkI_le_statedSp _ _) (isQuasisimple_blkI_toBilin' hodd hJ hUW horth hnd hdim hexc)
    (dvd_card_blkI_toBilin' hodd hJ hUW horth hnd hdim hexc hxB hxo)
    (fun y hyU hy => exists_smul_of_commute_blkI_toBilin' hodd hJ hUW horth hnd hdim hexc hyU hy)
    (fun hF y hyU _ k hk0 hkp => not_forall_semiConj_pow_toBilin' hodd hJ hUW horth hnd hdim
      hexc hF.2.2.2.2.1.1 (hsemiU hF) hyU hk0 hkp)
    (fun y hy c hc => scalar_eq_one_of_isom hp hp2 hA hAεβ hUne hnd hy hc) fun h1 => ?_
  rcases hE h1 with h | hF
  · exact Or.inl h
  · refine Or.inr ⟨hF, ?_⟩
    have hxcent : (x : GL (Fin r ⊕ Fin r) K) ∈
        centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom} := by
      rw [mem_centGL]
      intro s hs v
      rw [Set.mem_singleton_iff.1 hs]
      exact (mem_centGL.1 (hAε𝒮 x.2)) _ ⟨hF, rfl⟩ v
    have hexcσ : Module.finrank K (wtU Aε I) ≠ 2 ∨
        Nat.card (semilinearFixedSubfield Dat.σ) ≠ 3 := by
      by_cases h3 : Nat.card (semilinearFixedSubfield Dat.σ) = 3
      · left
        have hp3 : p ≠ 3 := by
          rintro rfl
          haveI : CharP (semilinearFixedSubfield Dat.σ) 3 :=
            CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
              Nat.prime_three le_rfl (by rw [h3, pow_one])
          apply hpK
          have h0 : ((3 : ℕ) : semilinearFixedSubfield Dat.σ) = 0 := CharP.cast_eq_zero _ 3
          have h' := congrArg (semilinearFixedSubfield Dat.σ).subtype h0
          rwa [map_natCast, map_zero] at h'
        refine finrank_ne_two_of_card_mod hp hp2 hp3 ?_ hpK hA hJ hJnd hAεβ H₀ hW₀ hx hx' hW₀U
        rw [hF.2.2.2.2.1.2.1, h3, Nat.cast_pow]
        exact ZMod.pow_card _
      · exact Or.inr h3
    exact glaPLayer_inf_centGL_ne_bot_toBilin' hodd hJ hUW horth hnd hp hF.2.2.2.2.1.1
      (hsemiU hF) (hsemiW hF) hF.2.2.2.2.2.1 hdim hexcσ ⟨hxB, hxcent⟩ hxo

theorem concA_sp (hp : p.Prime) (hp2 : p ≠ 2) [hSn : S.Normal]
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hr : 2 ≤ r) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p)
    (e : PSimple p S ≃* StatedProj (StatedSp r K)) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) :
    S267ConcA p S B := by
  classical
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h1 := (CharP.cast_eq_zero_iff K ℓ p).1 h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1)
  have hodd : Odd (Nat.card K) := hK ▸ (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_sp hp hp2 hcore hZ hr hℓ hf hK hℓ2 e hB
  obtain ⟨b, A, σ, hsplit'⟩ : ∃ (b : Ω) (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K),
      innerPart S B = B ∨ FieldElt p S B φ (Matrix.toBilin' (formJ r K)) θ b A σ := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, -, hact, hform, hfix⟩
    · exact ⟨1, 1, RingEquiv.refl K, Or.inl hBB⟩
    · exact ⟨b, A, σ, Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩
  let Dat : ClsInner p S B (StatedSp r K) (Matrix.toBilin' (formJ r K)) :=
    ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ, hsplit'⟩
  have hHβ : StatedSp r K ≤ isomGL (Matrix.toBilin' (formJ r K)) := ModelGen.statedSp_le_isomGL
  obtain ⟨Aε, hle, hAε, hAεβ, hAε𝒮, hmax⟩ := exists_maximal_engine Dat hHβ
  haveI : IsMulCommutative Aε := hAε.1
  have hA : ∀ a : ↥Aε, a ^ p = 1 := fun a => Subtype.ext (hAε.2 a a.2)
  haveI : DecidableEq (Hyperplane ↥Aε p) := Classical.decEq _
  have hAεH : Aε ≤ StatedSp r K := fun g hg => ModelGen.mem_statedSp_of_mem_isomGL (hAεβ hg)
  have heq := inf_eq_liftGroup hp hB hrank hBC hcore hZ hB4 h2 hpK Dat hHβ hle hAε hAεβ hAε𝒮
    hmax hA (fun _ _ _ _ _ _ _ _ _ => Or.inl (invol_mem_statedSp hp hA hpK hAεβ _))
  have hAεL : Aε = liftGroup Dat := by rw [← heq, inf_eq_left.2 hAεH]
  have hmaxE := isMaxElem_of_maximal _ (fieldSet Dat) Aε hAε hAεβ hAε𝒮 hmax
  have hρ : IsIsomRep (Matrix.toBilin' (formJ r K)) (glRep Aε) := isIsomRep_glRep hAεβ
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear (glRep Aε) (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  set T : Finset (Hyperplane ↥Aε p) :=
    Finset.univ.filter fun H' => weightSpace (glRep Aε) H'.1 ≠ ⊥ with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hcardA : Nat.card ↥Aε = p ^ T.card :=
    card_eq_pow_support _ (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT
  have hθT : Nat.card Dat.θ.range = p ^ T.card := by
    rw [← hcardA, hAεL]
    exact (Subgroup.card_map_of_injective (StatedSp r K).subtype_injective).symm
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
    exact hBC
  have hθcard := ModelGen.card_range_mul_card_inf Dat.θ Dat.θ_eq_one
  have hBsplit : (innerPart S B = B ∧ Nat.card B = p * p ^ T.card) ∨
      (FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A Dat.σ ∧
        Nat.card B = p * p ^ T.card * Nat.card (Subgroup.zpowers Dat.b)) := by
    rcases Dat.split with hBB | hF
    · left
      refine ⟨hBB, ?_⟩
      have h1 : innerPart S B ⊓ Subgroup.centralizer (S : Set Ω) =
          B ⊓ Subgroup.centralizer (S : Set Ω) := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
          S ⊔ Subgroup.centralizer (S : Set Ω))]
      rw [h1, hBC', hθT] at hθcard
      have hB1 : Nat.card ↥(innerPart S B) = Nat.card B := by rw [hBB]
      rw [← hB1, ← hθcard, mul_comm]
    · right
      obtain ⟨hbB, -, hBb, hbout, -⟩ := id hF
      exact ⟨hF, by rw [card_eq_of_inner_split hB hBC' hbB hBb hbout hθcard, hθT]⟩
  have hlow : p * p ^ T.card ≤ Nat.card B := by
    rcases hBsplit with ⟨-, h⟩ | ⟨-, h⟩
    · exact h.ge
    · rw [h]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hup : Nat.card B ≤ p ^ (T.card + 2) := by
    rcases hBsplit with ⟨-, h⟩ | ⟨hF, h⟩
    · rw [h, pow_add]
      nlinarith [pow_pos hp.pos T.card, hp.two_le]
    · have hbp : Nat.card (Subgroup.zpowers Dat.b) ≤ p := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 _ hF.1))
      rw [h, pow_add, pow_two]
      calc p * p ^ T.card * Nat.card (Subgroup.zpowers Dat.b) ≤ p * p ^ T.card * p :=
            Nat.mul_le_mul_left _ hbp
        _ = p ^ T.card * (p * p) := by ring
  have ht2 : 2 ≤ T.card := by
    have h := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hB4.trans hup)
    omega
  have hsupp : ∀ H ∈ T, ∃ x : ↥Aε, x ∉ H.1 ∧ ∀ H' : Hyperplane ↥Aε p, H' ≠ H →
      weightSpace (glRep Aε) H'.1 ≠ ⊥ → x ∈ H'.1 := by
    intro H hH
    obtain ⟨x, hx, hx'⟩ := exists_supported_element _ (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W
      {H} (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact (hT H).1 hH)
    exact ⟨x, hx H (Finset.mem_singleton_self _),
      fun H' hne hW => hx' H' (fun h => hne (Finset.mem_singleton.1 h)) hW⟩
  rcases (show 4 ≤ T.card ∨ T.card = 3 ∨ T.card = 2 by omega) with h4 | h3 | h2'
  ·
    obtain ⟨H₁, hH₁, H₂, hH₂, H₀, hH₀, h12, h10, h20⟩ :=
      Finset.two_lt_card.1 (by omega : 2 < T.card)
    obtain ⟨x, hx, hx'⟩ := hsupp H₀ hH₀
    have hcard2 : ({H₁, H₂} : Finset (Hyperplane ↥Aε p)).card = 2 := Finset.card_pair h12
    refine concA_sp_of_weights hp hp2 hB hBC hcore hodd h2 hpK Dat hA hAεL hAεβ hAε𝒮 hmaxE
      {H₁, H₂} ?_ (by rw [hcard2]; norm_num) (H₀ := H₀) ?_ ((hT H₀).1 hH₀) ?_ hx hx' ?_
    · intro H' hH'
      rcases Finset.mem_insert.1 hH' with rfl | hH'
      · exact (hT _).1 hH₁
      · rw [Finset.mem_singleton.1 hH']
        exact (hT _).1 hH₂
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h10, Ne.symm h20⟩
    · rw [hcard2]
      calc p ^ (3 + 2) = p * p ^ 4 := by ring
        _ ≤ p * p ^ T.card := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos h4)
        _ ≤ Nat.card B := hlow
    · intro h
      rw [hcard2] at h
      norm_num at h
  ·
    obtain ⟨H₁, H₂, H₀, h12, h10, h20, hTeq⟩ := Finset.card_eq_three.1 h3
    have hH₀ : H₀ ∈ T := by rw [hTeq]; simp
    have hH₁ : H₁ ∈ T := by rw [hTeq]; simp
    have hH₂ : H₂ ∈ T := by rw [hTeq]; simp
    obtain ⟨x, hx, hx'⟩ := hsupp H₀ hH₀
    obtain ⟨a, ha, ha'⟩ := hsupp H₂ hH₂
    have hH₂I : H₂ ∉ ({H₁} : Finset (Hyperplane ↥Aε p)) := by
      simpa using Ne.symm h12
    refine concA_sp_of_weights hp hp2 hB hBC hcore hodd h2 hpK Dat hA hAεL hAεβ hAε𝒮 hmaxE
      {H₁} (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact (hT _).1 hH₁)
      (by simp) (H₀ := H₀) (by simpa using Ne.symm h10) ((hT H₀).1 hH₀)
      (by simpa using hB4) hx hx' (fun _ => Or.inl ⟨(a : GL (Fin r ⊕ Fin r) K), a.2, ?_, ?_⟩)
    ·
      obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hT H₂).1 hH₂)
      refine ⟨m, weightSpace_le_wtU hp hA hpK hH₂I hm, fun hfix => hm0 ?_⟩
      rw [← glRep_apply_eq_glEquiv] at hfix
      exact eq_zero_of_mem_weightSpace_of_fixed (glRep Aε) hp hA hpK ha hm hfix
    · have hJ : ∀ v, Matrix.toBilin' (formJ r K) v v = 0 := toBilin'_formJ_self
      have hJnd : (Matrix.toBilin' (formJ r K)).SeparatingLeft :=
        (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
          CFSG.RankThree.Classical.SteinbergBY.det_formJ_ne_zero).1
      refine glaPLayer_blkI_inf_centralizer_ne_bot hodd hp hp2 hpK hA hJ hJnd hAεβ hH₂I ?_
        ((hT H₀).1 hH₀) (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact (hT _).1 hH₁)
        ((hT H₂).1 hH₂) ha ha' hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h20, Ne.symm h10⟩
  ·
    obtain ⟨H₁, H₀, h10, hTeq⟩ := Finset.card_eq_two.1 h2'
    have hH₀ : H₀ ∈ T := by rw [hTeq]; simp
    have hH₁ : H₁ ∈ T := by rw [hTeq]; simp
    obtain ⟨x, hx, hx'⟩ := hsupp H₀ hH₀
    have hF : FieldElt p S B Dat.φ (Matrix.toBilin' (formJ r K)) Dat.θ Dat.b Dat.A Dat.σ := by
      rcases hBsplit with ⟨-, hBcard⟩ | ⟨hF, -⟩
      · exfalso
        rw [h2'] at hBcard
        have h1 : p ^ 4 ≤ p ^ 3 := by
          calc p ^ 4 ≤ Nat.card B := hB4
            _ = p ^ 3 := by rw [hBcard]; ring
        exact absurd h1 (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
      · exact hF
    exact concA_sp_of_weights hp hp2 hB hBC hcore hodd h2 hpK Dat hA hAεL hAεβ hAε𝒮 hmaxE
      {H₁} (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact (hT _).1 hH₁)
      (by simp) (H₀ := H₀) (by simpa using Ne.symm h10) ((hT H₀).1 hH₀)
      (by simpa using hB4) hx hx' (fun _ => Or.inr hF)

theorem not_dvd_card_hopfMultiplier_psp (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hK : 5 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 3 ≤ r)) :
    ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp r K))) := by
  obtain ⟨-, ⟨eM⟩⟩ : commutator (StatedProj (StatedSp r K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp r K)) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
    rcases hK with h5 | ⟨h3, hr3⟩
    · exact CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier hr h5
    · exact CFSG.LieType.Steinberg.CentralExt.SpThree.psp_three_hopfMultiplier hr3 h3
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h.trans (Nat.gcd_dvd_left 2 _)))

end Sp

section Cat

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem five_le_or_eq_three {K : Type} [Field K] [Finite K] (Q : TauCeti.PrimePower)
    (hQ2 : Q.p ≠ 2) (hK : Nat.card K = Q.p ^ Q.exponent) : 5 ≤ Nat.card K ∨ Nat.card K = 3 := by
  have hodd : Odd (Nat.card K) := hK ▸ (Q.prime_p.odd_of_ne_two hQ2).pow
  have h3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ Q.p := by have := Q.prime_p.two_le; omega
      _ ≤ Q.p ^ Q.exponent := Nat.le_self_pow Q.exponent_pos.ne' _
  obtain ⟨k, hk⟩ := hodd
  omega

theorem badClsAt_C (n : ℕ) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C n Q).Valid) (hn : 3 ≤ n) :
    BadClsAt ⟨.C n Q, hv⟩ := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar ⟨e⟩ hB _ hrank hB4 hBC _ _
  rw [TauCeti.LieTypeIndex.characteristic_C] at hchar
  subst hchar
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C n Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hKc : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C n Q, hv⟩) =
      Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_C n Q) (TauCeti.LieTypeIndex.fieldExponent_C n Q)
  let e' := e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n Q hv)
  have hK5 := five_le_or_eq_three Q hq2 hKc
  have hZ := BadExc.center_eq_bot_of_multiplier hp hperf hcore e'
    (not_dvd_card_hopfMultiplier_psp hp hp2 (by omega) (hK5.imp_right fun h => ⟨h, hn⟩))
  exact Or.inl (concA_sp hp hp2 hcore hZ (by omega) Q.prime_p Q.exponent_pos hKc hq2 hqp e' hB
    hrank hB4 hBC)

theorem badClsAt_B_two (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) :
    BadClsAt ⟨.B 2 Q, hv⟩ := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar ⟨e⟩ hB _ hrank hB4 hBC hp3B _
  rw [TauCeti.LieTypeIndex.characteristic_B] at hchar
  subst hchar
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hKc : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) =
      Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_B 2 Q) (TauCeti.LieTypeIndex.fieldExponent_B 2 Q)
  let e' := e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj Q hv)
  have hdup := (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).not.mp
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  have hQ3 : Q.p ^ Q.exponent ≠ 3 := by
    intro h
    apply hdup
    simp [h]
  have hK5 : 5 ≤ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) :=
    (five_le_or_eq_three Q hq2 hKc).resolve_right (by rw [hKc]; exact hQ3)
  have hZ := BadExc.center_eq_bot_of_multiplier hp hperf hcore e'
    (not_dvd_card_hopfMultiplier_psp hp hp2 le_rfl (Or.inl hK5))
  rcases eq_or_ne p 3 with rfl | hp3
  · have hℓ3 : Q.p ≠ 3 := hqp
    exact (ModelGen.false_of_sp_two_three hcore hZ Q.prime_p Q.exponent_pos hKc hq2 hℓ3 e' hB
      hBC hB4 (fun h => hp3B ⟨rfl, h⟩)).elim
  · exact Or.inl (concA_sp hp hp2 hcore hZ le_rfl Q.prime_p Q.exponent_pos hKc hq2 hqp e' hB
      hrank hB4 hBC)

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
