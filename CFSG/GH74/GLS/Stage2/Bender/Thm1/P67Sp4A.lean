module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Act
public import CFSG.GH74.GLS.Stage2.OddAut.CoprimeCrit
public import CFSG.GH74.GLS.Stage2.OddAut.FixStep
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

@[expose] def InQ (E : Submodule K (Fin 2 ⊕ Fin 2 → K)) (x : StatedSp 2 K) : Prop :=
  (∀ v, act x v - v ∈ E) ∧ ∀ v ∈ E, act x v - v ∈ orth E

theorem fix_orth {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {x : StatedSp 2 K}
    (hx : ∀ v, act x v - v ∈ E) {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ orth E) : act x w = w := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_spForm
  intro v
  have h1 : spForm 2 K v (act x w) = spForm 2 K (act x⁻¹ v) w := by
    conv_lhs => rw [← act_act_inv x v]
    rw [spForm_act]
  have h2 : act x⁻¹ v - v ∈ E := by
    have := E.neg_mem (hx (act x⁻¹ v))
    rwa [act_act_inv, neg_sub] at this
  have h3 : spForm 2 K (act x⁻¹ v - v) w = 0 := (mem_orth.mp hw) _ h2
  rw [map_sub, h1]
  simpa [map_sub] using h3

theorem InQ.one (E : Submodule K (Fin 2 ⊕ Fin 2 → K)) : InQ E (1 : StatedSp 2 K) :=
  ⟨fun v => by simp [act_one], fun v _ => by simp [act_one]⟩

theorem InQ.mul {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {x y : StatedSp 2 K} (hx : InQ E x)
    (hy : InQ E y) : InQ E (x * y) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have : act (x * y) v - v = (act x (act y v) - act y v) + (act y v - v) := by
      rw [act_mul]; abel
    rw [this]
    exact E.add_mem (hx.1 _) (hy.1 v)
  · have hyv : act y v = v + (act y v - v) := by abel
    have h1 : act x (act y v - v) = act y v - v := fix_orth hx.1 (hy.2 v hv)
    have : act (x * y) v - v = (act x v - v) + (act y v - v) := by
      rw [act_mul]
      conv_lhs => rw [hyv]
      rw [act_add, h1]; abel
    rw [this]
    exact (orth E).add_mem (hx.2 v hv) (hy.2 v hv)

theorem InQ.inv {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {x : StatedSp 2 K} (hx : InQ E x) :
    InQ E x⁻¹ := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have := E.neg_mem (hx.1 (act x⁻¹ v))
    rwa [act_act_inv, neg_sub] at this
  · have hd : act x (act x v - v) = act x v - v := fix_orth hx.1 (hx.2 v hv)
    have h1 : act x (v - (act x v - v)) = v := by
      rw [act_sub, hd]; abel
    have h2 : act x⁻¹ v = v - (act x v - v) := by
      conv_lhs => rw [← h1]
      rw [act_inv_act]
    rw [h2]
    have := (orth E).neg_mem (hx.2 v hv)
    convert this using 1
    abel

@[expose] def QE (E : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Subgroup (StatedSp 2 K) where
  carrier := {x | InQ E x}
  mul_mem' := InQ.mul
  one_mem' := InQ.one E
  inv_mem' := InQ.inv

theorem pow_succ_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι K) (k : ℕ)
    (v : ι → K) : N ^ (k + 1) *ᵥ v = N *ᵥ (N ^ k *ᵥ v) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]

theorem InQ.pow_eq_one {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {x : StatedSp 2 K} (hx : InQ E x)
    {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2) : x ^ p = 1 := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := mx (x : GL _ K) with hM
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := M - 1 with hN
  have hNv : ∀ v, N *ᵥ v = act x v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have h3 : N ^ 3 = 0 := by
    by_contra hne
    obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hne
    apply hv
    have hv1 : N *ᵥ v ∈ E := by rw [hNv]; exact hx.1 v
    have hv2 : N *ᵥ (N *ᵥ v) ∈ orth E := by rw [hNv]; exact hx.2 _ hv1
    have e1 : N ^ 3 *ᵥ v = N *ᵥ (N *ᵥ (N *ᵥ v)) := by
      rw [pow_succ_mulVec, pow_succ_mulVec, pow_succ_mulVec, pow_zero, Matrix.one_mulVec]
    rw [e1, hNv (N *ᵥ (N *ᵥ v)), fix_orth hx.1 hv2, sub_self]
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hNp : N ^ p = 0 := by
    rw [show p = 3 + (p - 3) by omega, pow_add, h3, zero_mul]
  have hMp : M ^ p = 1 := by
    have h1 : M = N + 1 := by rw [hN]; abel
    rw [h1, add_pow_char_of_commute p (Commute.one_right N), hNp, one_pow, zero_add]
  apply Subtype.ext
  apply Units.ext
  simpa [hM, mx] using hMp

@[expose] def fixSp (u : StatedSp 2 K) : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.ker (Matrix.mulVecLin (mx (u : GL _ K) - 1))

theorem mem_fixSp {u : StatedSp 2 K} {w : Fin 2 ⊕ Fin 2 → K} : w ∈ fixSp u ↔ act u w = w := by
  rw [fixSp, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]
  rfl

theorem act_sub_mem_orth_fixSp (u : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    act u v - v ∈ orth (fixSp u) := by
  rw [mem_orth]
  intro e he
  rw [mem_fixSp] at he
  have h1 : spForm 2 K e (act u v) = spForm 2 K (act u⁻¹ e) v := by
    conv_lhs => rw [← act_act_inv u e]
    rw [spForm_act]
  have h2 : act u⁻¹ e = e := by
    calc act u⁻¹ e = act u⁻¹ (act u e) := by rw [he]
      _ = e := act_inv_act u e
  rw [map_sub, h1, h2, sub_self]

theorem commute_of_inQ {u x : StatedSp 2 K} (hx : InQ (fixSp u) x) : x * u = u * x := by
  apply act_ext
  intro v
  rw [act_mul, act_mul]
  have hn : act u v - v ∈ orth (fixSp u) := act_sub_mem_orth_fixSp u v
  have hd : act x v - v ∈ fixSp u := hx.1 v
  have h1 : act x (act u v) = act x v + (act u v - v) := by
    have : act u v = v + (act u v - v) := by abel
    conv_lhs => rw [this]
    rw [act_add, fix_orth hx.1 hn]
  have h2 : act u (act x v) = act x v + (act u v - v) := by
    have hx' : act x v = v + (act x v - v) := by abel
    conv_lhs => rw [hx']
    rw [act_add, mem_fixSp.mp hd]
    abel
  rw [h1, h2]

section Invariance

variable [Finite K]

theorem exists_semi_mem {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} (A : gsp 2 K) (σ : K ≃+* K)
    (h : ∀ v ∈ E, semi A σ v ∈ E) : ∀ v ∈ E, ∃ v' ∈ E, semi A σ v' = v := by
  let f : E → E := fun v => ⟨semi A σ v.1, h v.1 v.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : semi A σ (a.1 - b.1) = 0 := by
      rw [semi_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hab)
    have := (semi_eq_zero_iff A σ _).mp h1
    exact Subtype.ext (sub_eq_zero.mp this)
  have hs := Finite.injective_iff_surjective.mp hf
  intro v hv
  obtain ⟨a, ha⟩ := hs ⟨v, hv⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

theorem semi_mem_orth {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} (A : gsp 2 K) (σ : K ≃+* K)
    (h : ∀ v ∈ E, semi A σ v ∈ E) : ∀ w ∈ orth E, semi A σ w ∈ orth E := by
  intro w hw
  rw [mem_orth] at hw ⊢
  intro u hu
  obtain ⟨u', hu', rfl⟩ := exists_semi_mem A σ h u hu
  rw [spForm_semi, hw u' hu', map_zero, mul_zero]

theorem inQ_cf {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {x : StatedSp 2 K} (hx : InQ E x)
    (A : gsp 2 K) (σ : K ≃+* K) (h : ∀ v ∈ E, semi A σ v ∈ E) : InQ E (cf A σ x) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨w, rfl⟩ := exists_semi_eq A σ v
    have := h _ (hx.1 w)
    have e1 : act (cf A σ x) (semi A σ w) = semi A σ (act x w) := cf_mulVec_semi A σ x w
    rw [e1, ← semi_sub]
    exact h _ (hx.1 w)
  · obtain ⟨v', hv', rfl⟩ := exists_semi_mem A σ h v hv
    have e1 : act (cf A σ x) (semi A σ v') = semi A σ (act x v') := cf_mulVec_semi A σ x v'
    rw [e1, ← semi_sub]
    exact semi_mem_orth A σ h _ (hx.2 v' hv')

end Invariance

theorem tvS_mem_QE {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {e : Fin 2 ⊕ Fin 2 → K} (heE : e ∈ E)
    (heo : e ∈ orth E) (c : K) : tvS e c ∈ QE E := by
  have hact : ∀ v, act (tvS e c) v - v = (c * spForm 2 K v e) • e := by
    intro v
    show mx ((tvS e c : StatedSp 2 K) : GL _ K) *ᵥ v - v = _
    rw [mx_tvS_mulVec]
    abel
  refine ⟨fun v => ?_, fun v _ => ?_⟩
  · rw [hact]; exact E.smul_mem _ heE
  · rw [hact]; exact (orth E).smul_mem _ heo

theorem epsS_mem_QE {E : Submodule K (Fin 2 ⊕ Fin 2 → K)} {e w : Fin 2 ⊕ Fin 2 → K} (heE : e ∈ E)
    (heo : e ∈ orth E) (hwE : w ∈ E) (h : spForm 2 K e w = 0) : epsS e w h ∈ QE E := by
  have hact : ∀ v, act (epsS e w h) v - v = spForm 2 K v e • w + spForm 2 K v w • e := by
    intro v
    show mx ((epsS e w h : StatedSp 2 K) : GL _ K) *ᵥ v - v = _
    rw [mx_epsS_mulVec]
    abel
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [hact]; exact E.add_mem (E.smul_mem _ hwE) (E.smul_mem _ heE)
  · rw [hact]
    have hve : spForm 2 K v e = 0 := (mem_orth.mp heo) v hv
    rw [hve, zero_smul, zero_add]
    exact (orth E).smul_mem _ heo

open CFSG.RankThree.PartTwo.KFacts in
theorem cf_pow (A : gsp 2 K) (σ : K ≃+* K) (x : StatedSp 2 K) (n : ℕ) :
    cf A σ x ^ n = cf A σ (x ^ n) := (map_pow (cf A σ) x n).symm

open CFSG.RankThree.PartTwo.KFacts in
theorem eq_one_of_fixes_QE [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    {u : StatedSp 2 K} (hu : u ^ p = 1) (hu1 : u ≠ 1) {z : MulAut (StatedProj (StatedSp 2 K))}
    {s : ℕ} (hs : z ^ s = 1) (hsp : ¬ p ∣ s) (hzu : z (proj 2 K u) = proj 2 K u)
    (hfix : ∀ x ∈ QE (fixSp u), z (proj 2 K x) = proj 2 K x) : z = 1 := by
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp
  obtain ⟨A, σ, hz⟩ := psp4_odd_automorphism_normal_form hodd z
  have hfixcf : ∀ x ∈ QE (fixSp u), cf A σ x = x := by
    intro x hx
    apply eq_of_proj_eq (p := p)
    · rw [cf_pow, (InQ.pow_eq_one hx hp : x ^ p = 1), map_one]
    · exact InQ.pow_eq_one hx hp
    · rw [← conjAut_fieldAut_proj, ← hz]; exact hfix x hx
  have hcfu : cf A σ u = u := by
    apply eq_of_proj_eq (p := p)
    · rw [cf_pow, hu, map_one]
    · exact hu
    · rw [← conjAut_fieldAut_proj, ← hz]; exact hzu
  set E := fixSp u with hE
  have hΦE : ∀ v ∈ E, semi A σ v ∈ E := by
    intro v hv
    rw [hE, mem_fixSp] at hv ⊢
    have := cf_mulVec_semi A σ u v
    rw [hcfu] at this
    exact this.trans (by rw [show mx (u : GL _ K) *ᵥ v = act u v from rfl, hv])
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := mx (u : GL _ K) with hM
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := M - 1 with hN
  have hMp : M ^ p = 1 := by
    have := congrArg (fun g : StatedSp 2 K => mx (g : GL (Fin 2 ⊕ Fin 2) K)) hu
    simpa [hM, mx] using this
  have hNne : N ≠ 0 := by
    intro h0
    apply hu1
    have : M = 1 := sub_eq_zero.mp h0
    apply Subtype.ext
    apply Units.ext
    simpa [hM, mx] using this
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute p (Commute.one_right M), hMp, one_pow, sub_self]
  obtain ⟨e, he0, hNe, v, hv⟩ := exists_mem_ker_range_of_nilpotent hNp hNne
  have hNv : ∀ v, N *ᵥ v = act u v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have heE : e ∈ E := by
    rw [hE, mem_fixSp]
    have := hNv e
    rw [hNe] at this
    exact (sub_eq_zero.mp this.symm)
  have heo : e ∈ orth E := by
    rw [← hv, hNv]
    exact act_sub_mem_orth_fixSp u v
  obtain ⟨l, hl, hl2, hσ⟩ := fix_tvS A σ he0 ⊤
    (fun c _ => hfixcf _ (tvS_mem_QE heE heo c))
  have hσ1 : σ = 1 := RingEquiv.ext fun c => hσ c trivial
  have hμ : ((multiplier 2 K A : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl2
    exact hμ (by rw [← hl2]; ring)
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    apply hp
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff K p 2).mp this))
  have hsemiE : ∀ w ∈ E, semi A σ w = l • w := by
    intro w hw
    have hew : spForm 2 K e w = 0 := spForm_isRefl _ _ ((mem_orth.mp heo) w hw)
    have hmem := epsS_mem_QE heE heo hw hew
    have h1 := hfixcf _ hmem
    have hsw : spForm 2 K (semi A σ e) (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w) = 0 := by
      rw [map_smul, spForm_semi, hew, map_zero, mul_zero, smul_zero]
    rw [cf_epsS A σ e w hew hsw] at h1
    have h3 := eps_vec_of_epsS_eq h1
    have hΦe : semi A σ e = l • e := hl
    have h4 : ∀ x, spForm 2 K x e • (l • (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w)) +
        spForm 2 K x (l • (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w)) • e =
        spForm 2 K x e • w + spForm 2 K x w • e := by
      intro x
      have := h3 x
      rw [hΦe] at this
      simp only [map_smul, smul_eq_mul] at this ⊢
      rw [← this]
      module
    have h5 : l • (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w) = w :=
      eq_of_eps_vec h2K he0 h4
    rw [smul_smul] at h5
    have h8 : (l * ((multiplier 2 K A : Kˣ) : K)⁻¹) ≠ 0 := mul_ne_zero hl0 (inv_ne_zero hμ)
    calc semi A σ w = ((l * ((multiplier 2 K A : Kˣ) : K)⁻¹)⁻¹ *
          (l * ((multiplier 2 K A : Kˣ) : K)⁻¹)) • semi A σ w := by
          rw [inv_mul_cancel₀ h8, one_smul]
      _ = (l * ((multiplier 2 K A : Kˣ) : K)⁻¹)⁻¹ • ((l * ((multiplier 2 K A : Kˣ) : K)⁻¹) •
            semi A σ w) := by rw [mul_smul]
      _ = (l * ((multiplier 2 K A : Kˣ) : K)⁻¹)⁻¹ • w := by rw [h5]
      _ = l • w := by
          congr 1
          rw [← hl2]
          field_simp
  subst hσ1
  have hA1 : ∀ w, semi A 1 w = mx (A : GL _ K) *ᵥ w := fun w => rfl
  have hinv : mx ((A : GL _ K)⁻¹) * mx (A : GL _ K) = 1 := by
    simp only [mx]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : mx (A : GL _ K) * M = M * mx (A : GL _ K) := by
    have h1 := congrArg (fun g : StatedSp 2 K => mx (g : GL _ K)) hcfu
    simp only [coe_cf] at h1
    have hmap : (mx (u : GL _ K)).map ⇑(1 : K ≃+* K) = mx (u : GL _ K) := by
      ext i j; rfl
    rw [hmap] at h1
    calc mx (A : GL _ K) * M = (mx (A : GL _ K) * M * mx ((A : GL _ K)⁻¹)) * mx (A : GL _ K) := by
          rw [mul_assoc, mul_assoc, hinv, mul_one]
      _ = M * mx (A : GL _ K) := by rw [hM, h1]
  set A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := l⁻¹ • mx (A : GL _ K) with hA'
  have hAN : A' * N = N * A' := by
    rw [hA', hN, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, mul_one, one_mul, hcomm]
  have hker : ∀ w, N *ᵥ w = 0 → A' *ᵥ w = w := by
    intro w hw
    have hwE : w ∈ E := by
      rw [hE, mem_fixSp]
      have := hNv w
      rw [hw] at this
      exact sub_eq_zero.mp this.symm
    have := hsemiE w hwE
    rw [hA1] at this
    rw [hA', Matrix.smul_mulVec, this, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hzA : z = conjAut 2 K A := by rw [hz, map_one, mul_one]
  have hAs : conjAut 2 K (A ^ s) = 1 := by rw [map_pow, ← hzA, hs]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one (by norm_num : 1 ≤ 2) hAs
  have hAsM : (mx (A : GL _ K)) ^ s = (c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => mx g) hc
    simp only [mx, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.coe_scalar] at this
    rw [mx, this, smul_one_eq_diagonal]
    rfl
  have hA's : A' ^ s = 1 := by
    have hpow : ∀ k : ℕ, A' ^ k *ᵥ e = e := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hker e hNe, ih]
    have h1 : A' ^ s = ((l⁻¹) ^ s * (c : K)) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [hA', smul_pow, hAsM, smul_smul]
    have h2 : ((l⁻¹) ^ s * (c : K)) • e = e := by
      have := hpow s
      rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      exact this
    have h3 : (l⁻¹) ^ s * (c : K) = 1 := by
      have : ((l⁻¹) ^ s * (c : K) - 1) • e = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right he0)
    rw [h1, h3, one_smul]
  have hm : (s : K) ≠ 0 := fun h => hsp ((CharP.cast_eq_zero_iff K p s).mp h)
  have hA'1 : A' = 1 :=
    OddAut.eq_one_of_commute_nilpotent_ker hAN hNp hker hA's hm
  have hAl : mx (A : GL _ K) = l • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have := congrArg (fun X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => l • X) hA'1
    simpa [hA', smul_smul, mul_inv_cancel₀ hl0] using this
  have hAeq : A = ⟨GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0),
      scalar_mem_gsp _⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, ← smul_one_eq_diagonal]
    exact hAl
  rw [hzA, hAeq]
  exact conjAut_scalar_eq_one _

section CaseA

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.RankThree.PartTwo.KFacts

variable {Y : Type} [Group Y]

theorem fix_of_commute_conj (hcen : Subgroup.center Y = ⊥) {z : MulAut Y} {g : Y}
    (h : MulAut.conj g * z = z * MulAut.conj g) : z g = g := by
  have hinj := mulAut_conj_injective_of_center_bot hcen
  apply hinj
  have h1 := mulAut_conj_conj z g
  rw [← h1, ← h, mul_assoc, mul_inv_cancel, mul_one]

theorem isPGroup_map_QE {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (E : Submodule K (Fin 2 ⊕ Fin 2 → K)) : IsPGroup p ↥((QE E).map (proj 2 K)) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : StatedProj (StatedSp 2 K)) ^ p ^ 1 = 1
  rw [pow_one, ← hxg, ← map_pow, InQ.pow_eq_one hx hp, map_one]

theorem caseA [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥)
    {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) p V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    {u : StatedSp 2 K} (hu : u ^ p = 1) (hu1 : u ≠ 1)
    (hv : MulAut.conj (proj 2 K u) ∈ V) : False := by
  classical
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp
  have hg0 : proj 2 K u ≠ 1 := by
    intro h
    apply hu1
    apply eq_of_proj_eq (p := p) hu (one_pow p)
    rw [h, map_one]
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hv1 : MulAut.conj (proj 2 K u) ≠ 1 := by
    intro h
    apply hg0
    apply hinj
    rw [h, map_one]
  have hzu : ∀ z ∈ Z, z (proj 2 K u) = proj 2 K u := fun z hz =>
    fix_of_commute_conj hcen (h2.2.2.2.2.2.2.2.2 _ hv z hz)
  set M : Subgroup (StatedProj (StatedSp 2 K)) := (QE (fixSp u)).map (proj 2 K) with hM
  have hMle : M ≤ fixSub (MulAut.conj (proj 2 K u)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← commute_of_inQ hx]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hMinv : ∀ z ∈ Z, ∀ c ∈ M, z c ∈ M := by
    intro z hz c hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨A, σ, hzAσ⟩ := psp4_odd_automorphism_normal_form hodd z
    have hcfu : cf A σ u = u := by
      apply eq_of_proj_eq (p := p)
      · rw [cf_pow, hu, map_one]
      · exact hu
      · rw [← conjAut_fieldAut_proj, ← hzAσ]; exact hzu z hz
    have hΦE : ∀ v ∈ fixSp u, semi A σ v ∈ fixSp u := by
      intro v hv
      rw [mem_fixSp] at hv ⊢
      have := cf_mulVec_semi A σ u v
      rw [hcfu] at this
      exact this.trans (by rw [show mx (u : GL _ K) *ᵥ v = act u v from rfl, hv])
    refine ⟨cf A σ x, inQ_cf hx A σ hΦE, ?_⟩
    rw [hzAσ]
    exact (conjAut_fieldAut_proj A σ x).symm
  have hMp : OddAut.NoOddNormal M p := OddAut.noOddNormal_of_isPGroup (isPGroup_map_QE hp _)
  have hfix := OddAut.fix_step hcen h2 h3 hv hv1 hMle hMinv hMp
  obtain ⟨-, -, -, -, -, hZodd, hZcop, hZbot, -⟩ := h2
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hdvd : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime (orderOf (z : MulAut (StatedProj (StatedSp 2 K)))) p :=
    Nat.Coprime.coprime_dvd_left hdvd hZcop
  have hsp : ¬ p ∣ orderOf (z : MulAut (StatedProj (StatedSp 2 K))) := by
    intro h
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
  have hz : (z : MulAut (StatedProj (StatedSp 2 K))) = 1 :=
    eq_one_of_fixes_QE hp hu hu1 (pow_orderOf_eq_one _) hsp (hzu z z.2) fun x hx =>
      hfix z z.2 _ ⟨x, hx, rfl⟩
  exact hz1 (Subtype.ext hz)

end CaseA

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
