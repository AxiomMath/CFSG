module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.GH74.GLS.Stage2.OddAut.CoprimeCrit

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut

structure HermGram {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι K) : Prop where
  herm : (G.map h.bar)ᵀ = G
  det_ne : G.det ≠ 0
  map_eq : ∀ σ : K ≃+* K, G.map σ = G

section Form

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

theorem B_herm (hG : HermGram h G) (x y : ι → K) :
    h.bar (gramForm h G x y) = gramForm h G y x := by
  have := (gramForm_isSymm h hG.herm).eq x y
  simpa using this

theorem B_eq_zero_comm (hG : HermGram h G) {x y : ι → K} (hxy : gramForm h G x y = 0) :
    gramForm h G y x = 0 := by
  rw [← B_herm hG, hxy, map_zero]

end Form

section Act

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

abbrev mx (g : GL ι K) : Matrix ι ι K := (g : Matrix ι ι K)

@[expose] def act (g : gramSU h G) (v : ι → K) : ι → K := mx (g : GL ι K) *ᵥ v

theorem act_mul (x y : gramSU h G) (v : ι → K) : act (x * y) v = act x (act y v) := by
  unfold act
  simp only [mx, Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec]

theorem act_one (v : ι → K) : act (1 : gramSU h G) v = v := by
  unfold act
  simp

theorem act_inv_act (x : gramSU h G) (v : ι → K) : act x⁻¹ (act x v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (x : gramSU h G) (v : ι → K) : act x (act x⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_add (x : gramSU h G) (v w : ι → K) : act x (v + w) = act x v + act x w := by
  unfold act
  rw [Matrix.mulVec_add]

theorem act_sub (x : gramSU h G) (v w : ι → K) : act x (v - w) = act x v - act x w := by
  unfold act
  rw [Matrix.mulVec_sub]

theorem act_smul (x : gramSU h G) (c : K) (v : ι → K) : act x (c • v) = c • act x v := by
  unfold act
  rw [Matrix.mulVec_smul]

theorem act_zero (x : gramSU h G) : act x (0 : ι → K) = 0 := by
  unfold act
  rw [Matrix.mulVec_zero]

theorem B_act (x : gramSU h G) (v w : ι → K) :
    gramForm h G (act x v) (act x w) = gramForm h G v w :=
  (mem_gramSU_iff_isometry.mp x.2).1 v w

theorem act_ext {x y : gramSU h G} (hxy : ∀ v, act x v = act y v) : x = y := by
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hxy v)

@[expose] def orthU (h : UnitaryFieldData p f K) (G : Matrix ι ι K) (E : Submodule K (ι → K)) :
    Submodule K (ι → K) where
  carrier := {w | ∀ e ∈ E, gramForm h G e w = 0}
  add_mem' := fun {a b} ha hb e he => by rw [map_add, ha e he, hb e he, add_zero]
  zero_mem' := fun e _ => by rw [map_zero]
  smul_mem' := fun c {a} ha e he => by
    rw [map_smul, ha e he, smul_eq_mul, mul_zero]

omit [DecidableEq ι] in
theorem mem_orthU {E : Submodule K (ι → K)} {w : ι → K} :
    w ∈ orthU h G E ↔ ∀ e ∈ E, gramForm h G e w = 0 := Iff.rfl

theorem eq_zero_of_forall_B (hG : HermGram h G) {y : ι → K}
    (hy : ∀ v, gramForm h G v y = 0) : y = 0 :=
  gramForm_separatingLeft h hG.det_ne y fun v => B_eq_zero_comm hG (hy v)

end Act

section QE

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

@[expose] def InQ (E : Submodule K (ι → K)) (x : gramSU h G) : Prop :=
  (∀ v, act x v - v ∈ E) ∧ ∀ v ∈ E, act x v - v ∈ orthU h G E

theorem fix_orth (hG : HermGram h G) {E : Submodule K (ι → K)} {x : gramSU h G}
    (hx : ∀ v, act x v - v ∈ E) {w : ι → K} (hw : w ∈ orthU h G E) : act x w = w := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_B hG
  intro v
  have h1 : gramForm h G v (act x w) = gramForm h G (act x⁻¹ v) w := by
    conv_lhs => rw [← act_act_inv x v]
    rw [B_act]
  have h2 : act x⁻¹ v - v ∈ E := by
    have := E.neg_mem (hx (act x⁻¹ v))
    rwa [act_act_inv, neg_sub] at this
  have h3 : gramForm h G (act x⁻¹ v - v) w = 0 := (mem_orthU.mp hw) _ h2
  rw [map_sub, h1]
  simpa [map_sub] using h3

theorem InQ.one (E : Submodule K (ι → K)) : InQ E (1 : gramSU h G) :=
  ⟨fun v => by simp [act_one], fun v _ => by simp [act_one]⟩

theorem InQ.mul (hG : HermGram h G) {E : Submodule K (ι → K)} {x y : gramSU h G} (hx : InQ E x)
    (hy : InQ E y) : InQ E (x * y) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have : act (x * y) v - v = (act x (act y v) - act y v) + (act y v - v) := by
      rw [act_mul]; abel
    rw [this]
    exact E.add_mem (hx.1 _) (hy.1 v)
  · have hyv : act y v = v + (act y v - v) := by abel
    have h1 : act x (act y v - v) = act y v - v := fix_orth hG hx.1 (hy.2 v hv)
    have : act (x * y) v - v = (act x v - v) + (act y v - v) := by
      rw [act_mul]
      conv_lhs => rw [hyv]
      rw [act_add, h1]; abel
    rw [this]
    exact (orthU h G E).add_mem (hx.2 v hv) (hy.2 v hv)

theorem InQ.inv (hG : HermGram h G) {E : Submodule K (ι → K)} {x : gramSU h G} (hx : InQ E x) :
    InQ E x⁻¹ := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have := E.neg_mem (hx.1 (act x⁻¹ v))
    rwa [act_act_inv, neg_sub] at this
  · have hd : act x (act x v - v) = act x v - v := fix_orth hG hx.1 (hx.2 v hv)
    have h1 : act x (v - (act x v - v)) = v := by
      rw [act_sub, hd]; abel
    have h2 : act x⁻¹ v = v - (act x v - v) := by
      conv_lhs => rw [← h1]
      rw [act_inv_act]
    rw [h2]
    have := (orthU h G E).neg_mem (hx.2 v hv)
    convert this using 1
    abel

@[expose] def QE (hG : HermGram h G) (E : Submodule K (ι → K)) : Subgroup (gramSU h G) where
  carrier := {x | InQ E x}
  mul_mem' := InQ.mul hG
  one_mem' := InQ.one E
  inv_mem' := InQ.inv hG

end QE

section QEp

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

theorem pow_succ_mulVec (N : Matrix ι ι K) (k : ℕ) (v : ι → K) :
    N ^ (k + 1) *ᵥ v = N *ᵥ (N ^ k *ᵥ v) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]

theorem mx_sub_one_mulVec (x : gramSU h G) (v : ι → K) :
    (mx (x : GL ι K) - 1) *ᵥ v = act x v - v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

theorem InQ.pow_eq_one [Nonempty ι] (hG : HermGram h G) {E : Submodule K (ι → K)}
    {x : gramSU h G} (hx : InQ E x) [Fact p.Prime] [CharP K p] (hp : p ≠ 2) : x ^ p = 1 := by
  set M : Matrix ι ι K := mx (x : GL ι K) with hM
  set N : Matrix ι ι K := M - 1 with hN
  have hNv : ∀ v, N *ᵥ v = act x v - v := fun v => mx_sub_one_mulVec x v
  have h3 : N ^ 3 = 0 := by
    by_contra hne
    obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hne
    apply hv
    have hv1 : N *ᵥ v ∈ E := by rw [hNv]; exact hx.1 v
    have hv2 : N *ᵥ (N *ᵥ v) ∈ orthU h G E := by rw [hNv]; exact hx.2 _ hv1
    have e1 : N ^ 3 *ᵥ v = N *ᵥ (N *ᵥ (N *ᵥ v)) := by
      rw [pow_succ_mulVec, pow_succ_mulVec, pow_succ_mulVec, pow_zero, Matrix.one_mulVec]
    rw [e1, hNv (N *ᵥ (N *ᵥ v)), fix_orth hG hx.1 hv2, sub_self]
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

@[expose] def fixU (u : gramSU h G) : Submodule K (ι → K) :=
  LinearMap.ker (Matrix.mulVecLin (mx (u : GL ι K) - 1))

theorem mem_fixU {u : gramSU h G} {w : ι → K} : w ∈ fixU u ↔ act u w = w := by
  rw [fixU, LinearMap.mem_ker, Matrix.mulVecLin_apply, mx_sub_one_mulVec, sub_eq_zero]

theorem act_sub_mem_orthU_fixU (u : gramSU h G) (v : ι → K) :
    act u v - v ∈ orthU h G (fixU u) := by
  rw [mem_orthU]
  intro e he
  rw [mem_fixU] at he
  have h1 : gramForm h G e (act u v) = gramForm h G (act u⁻¹ e) v := by
    conv_lhs => rw [← act_act_inv u e]
    rw [B_act]
  have h2 : act u⁻¹ e = e := by
    calc act u⁻¹ e = act u⁻¹ (act u e) := by rw [he]
      _ = e := act_inv_act u e
  rw [map_sub, h1, h2, sub_self]

theorem commute_of_inQ (hG : HermGram h G) {u x : gramSU h G} (hx : InQ (fixU u) x) :
    x * u = u * x := by
  apply act_ext
  intro v
  rw [act_mul, act_mul]
  have hn : act u v - v ∈ orthU h G (fixU u) := act_sub_mem_orthU_fixU u v
  have hd : act x v - v ∈ fixU u := hx.1 v
  have h1 : act x (act u v) = act x v + (act u v - v) := by
    have : act u v = v + (act u v - v) := by abel
    conv_lhs => rw [this]
    rw [act_add, fix_orth hG hx.1 hn]
  have h2 : act u (act x v) = act x v + (act u v - v) := by
    have hx' : act x v = v + (act x v - v) := by abel
    conv_lhs => rw [hx']
    rw [act_add, mem_fixU.mp hd]
    abel
  rw [h1, h2]

end QEp

section Semi

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

@[expose] def semi (A : GL ι K) (σ : K ≃+* K) (v : ι → K) : ι → K := mx A *ᵥ (⇑σ ∘ v)

theorem semi_add (A : GL ι K) (σ : K ≃+* K) (v w : ι → K) :
    semi A σ (v + w) = semi A σ v + semi A σ w := by
  unfold semi
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem semi_sub (A : GL ι K) (σ : K ≃+* K) (v w : ι → K) :
    semi A σ (v - w) = semi A σ v - semi A σ w := by
  unfold semi
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp

theorem semi_smul (A : GL ι K) (σ : K ≃+* K) (c : K) (v : ι → K) :
    semi A σ (c • v) = σ c • semi A σ v := by
  unfold semi
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem semi_zero (A : GL ι K) (σ : K ≃+* K) : semi A σ 0 = 0 := by
  unfold semi
  have : (⇑σ ∘ (0 : ι → K)) = 0 := by
    funext i; simp
  rw [this, Matrix.mulVec_zero]

theorem exists_semi_eq (A : GL ι K) (σ : K ≃+* K) (v : ι → K) : ∃ w, semi A σ w = v := by
  refine ⟨fun i => σ.symm ((mx A⁻¹ *ᵥ v) i), ?_⟩
  unfold semi
  have : (⇑σ ∘ fun i => σ.symm ((mx A⁻¹ *ᵥ v) i)) = mx A⁻¹ *ᵥ v := by
    funext i; simp
  rw [this, Matrix.mulVec_mulVec]
  simp only [mx, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem semi_eq_zero_iff (A : GL ι K) (σ : K ≃+* K) (v : ι → K) : semi A σ v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have h1 : mx A⁻¹ *ᵥ semi A σ v = ⇑σ ∘ v := by
      unfold semi
      rw [Matrix.mulVec_mulVec]
      simp only [mx, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hv, Matrix.mulVec_zero] at h1
    funext i
    have := congrFun h1 i
    simpa using this.symm
  · rintro rfl
    exact semi_zero A σ

theorem B_comp_coord (hG : HermGram h G) (σ : K ≃+* K) (v w : ι → K) :
    gramForm h G (⇑σ ∘ v) (⇑σ ∘ w) = σ (gramForm h G v w) := by
  simp only [gramForm_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Function.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hab : σ (G a b) = G a b := by
    have := congrFun (congrFun (hG.map_eq σ) a) b
    simpa using this
  rw [hab, map_bar_comm]

theorem B_semi (hG : HermGram h G) (A : GL ι K) (σ : K ≃+* K) {μ : K}
    (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G) (v w : ι → K) :
    gramForm h G (semi A σ v) (semi A σ w) = μ * σ (gramForm h G v w) := by
  unfold semi
  rw [gramForm_mulVec, hA, gramForm_smul_gram, B_comp_coord hG]

section Invariance

variable [Finite K]

theorem exists_semi_mem {E : Submodule K (ι → K)} (A : GL ι K) (σ : K ≃+* K)
    (hE : ∀ v ∈ E, semi A σ v ∈ E) : ∀ v ∈ E, ∃ v' ∈ E, semi A σ v' = v := by
  let g : E → E := fun v => ⟨semi A σ v.1, hE v.1 v.2⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : semi A σ (a.1 - b.1) = 0 := by
      rw [semi_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hab)
    have := (semi_eq_zero_iff A σ _).mp h1
    exact Subtype.ext (sub_eq_zero.mp this)
  have hs := Finite.injective_iff_surjective.mp hg
  intro v hv
  obtain ⟨a, ha⟩ := hs ⟨v, hv⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

theorem semi_mem_orthU (hG : HermGram h G) {E : Submodule K (ι → K)} (A : GL ι K) (σ : K ≃+* K)
    {μ : K} (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G) (hE : ∀ v ∈ E, semi A σ v ∈ E) :
    ∀ w ∈ orthU h G E, semi A σ w ∈ orthU h G E := by
  intro w hw
  rw [mem_orthU] at hw ⊢
  intro u hu
  obtain ⟨u', hu', rfl⟩ := exists_semi_mem A σ hE u hu
  rw [B_semi hG A σ hA, hw u' hu', map_zero, mul_zero]

theorem inQ_conj (hG : HermGram h G) {E : Submodule K (ι → K)} (A : GL ι K) (σ : K ≃+* K)
    {μ : K} (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G) (hE : ∀ v ∈ E, semi A σ v ∈ E)
    {x y : gramSU h G} (hxy : ∀ w, act y (semi A σ w) = semi A σ (act x w)) (hx : InQ E x) :
    InQ E y := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨w, rfl⟩ := exists_semi_eq A σ v
    rw [hxy, ← semi_sub]
    exact hE _ (hx.1 w)
  · obtain ⟨v', hv', rfl⟩ := exists_semi_mem A σ hE v hv
    rw [hxy, ← semi_sub]
    exact semi_mem_orthU hG A σ hA hE _ (hx.2 v' hv')

end Invariance

end Semi

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
