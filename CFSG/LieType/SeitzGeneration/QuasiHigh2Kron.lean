module

public import CFSG.LieType.SeitzGeneration.HyperIrrGen
public import CFSG.LieType.SeitzGeneration.HyperIrrNoncentral

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh2

open Matrix CFSG.LieType.SeitzGeneration
open scoped commutatorElement

section Pi

variable {G : Type*} [Group G] {ι : Type*} [DecidableEq ι]

theorem pi_commutatorElement_apply (h h' : ι → G) (k : ι) : (⁅h, h'⁆) k = ⁅h k, h' k⁆ := by
  simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]

@[expose] def coordSub (H : Subgroup (ι → G)) (i₀ : ι) (J : Finset ι) : Subgroup G where
  carrier := {x | ∃ h ∈ H, (∀ j ∈ J, h j = 1) ∧ h i₀ = x}
  mul_mem' := by
    rintro _ _ ⟨h, hH, hJ, rfl⟩ ⟨h', hH', hJ', rfl⟩
    exact ⟨h * h', H.mul_mem hH hH', fun j hj => by simp [hJ j hj, hJ' j hj], rfl⟩
  one_mem' := ⟨1, H.one_mem, fun _ _ => rfl, rfl⟩
  inv_mem' := by
    rintro _ ⟨h, hH, hJ, rfl⟩
    exact ⟨h⁻¹, H.inv_mem hH, fun j hj => by simp [hJ j hj], rfl⟩

theorem coordSub_eq_top (hperf : commutator G = ⊤) (H : Subgroup (ι → G)) (i₀ : ι)
    (h1 : ∀ g : G, ∃ h ∈ H, h i₀ = g)
    (h2 : ∀ j, j ≠ i₀ → ∀ g : G, ∃ h ∈ H, h j = 1 ∧ h i₀ = g) :
    ∀ J : Finset ι, i₀ ∉ J → coordSub H i₀ J = ⊤ := by
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _
    rw [eq_top_iff]
    intro g _
    obtain ⟨h, hH, rfl⟩ := h1 g
    exact ⟨h, hH, fun j hj => absurd hj (Finset.notMem_empty j), rfl⟩
  | insert j J hjJ ih =>
    intro hi
    have hij : j ≠ i₀ := fun h => hi (h ▸ Finset.mem_insert_self _ _)
    have hiJ : i₀ ∉ J := fun h => hi (Finset.mem_insert_of_mem h)
    have hJ := ih hiJ
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨h, hH, hhJ, rfl⟩ : a ∈ coordSub H i₀ J := hJ ▸ Subgroup.mem_top a
    obtain ⟨h', hH', hh'j, rfl⟩ := h2 j hij b
    refine ⟨⁅h, h'⁆, ?_, fun k hk => ?_, pi_commutatorElement_apply h h' i₀⟩
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hH hH') (H.inv_mem hH)) (H.inv_mem hH')
    · rw [pi_commutatorElement_apply]
      rcases Finset.mem_insert.1 hk with rfl | hk
      · rw [hh'j, commutatorElement_one_right]
      · rw [hhJ k hk, commutatorElement_one_left]

theorem mulSingle_mem_of_perfect [Fintype ι] (hperf : commutator G = ⊤) (H : Subgroup (ι → G))
    (i₀ : ι) (h1 : ∀ g : G, ∃ h ∈ H, h i₀ = g)
    (h2 : ∀ j, j ≠ i₀ → ∀ g : G, ∃ h ∈ H, h j = 1 ∧ h i₀ = g) (g : G) :
    Pi.mulSingle i₀ g ∈ H := by
  have htop := coordSub_eq_top hperf H i₀ h1 h2 (Finset.univ.erase i₀) (Finset.notMem_erase _ _)
  obtain ⟨h, hH, hJ, hg⟩ : g ∈ coordSub H i₀ (Finset.univ.erase i₀) := htop ▸ Subgroup.mem_top g
  convert hH using 1
  funext k
  by_cases hk : k = i₀
  · subst hk
    rw [Pi.mulSingle_eq_same, hg]
  · rw [Pi.mulSingle_eq_of_ne hk, hJ k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩)]

theorem mem_center_of_apply_mem {α : MulAut G} {x : G} (h : α x ∈ Subgroup.center G) :
    x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  have h1 := h (α g)
  rw [← map_mul, ← map_mul] at h1
  exact α.injective h1

theorem mulSingle_mem_of_twisted {p : ℕ} (hperf : commutator G = ⊤)
    (hqs : ∀ N : Subgroup G, N.Normal → ∀ a ∈ N, a ∉ Subgroup.center G → N = ⊤)
    (α : MulAut G) (hαp : α ^ p = 1)
    (hα : ∀ m : ℕ, 0 < m → m < p → ∃ v : G, v * (α ^ m) v⁻¹ ∉ Subgroup.center G)
    (H : Subgroup (Fin p → G)) (hconst : ∀ u : G, (fun _ => u) ∈ H)
    (htw : ∀ v : G, (fun k : Fin p => (α ^ (k : ℕ)) v) ∈ H) (i : Fin p) (g : G) :
    Pi.mulSingle i g ∈ H := by
  have : NeZero p := ⟨Nat.pos_iff_ne_zero.1 (Fin.pos i)⟩
  refine mulSingle_mem_of_perfect hperf H i (fun g => ⟨_, hconst g, rfl⟩) ?_ g
  intro j hji g
  set M := coordSub H i {j} with hM
  have hMn : M.Normal := by
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨h, hH, hj, rfl⟩ := hx
    refine ⟨(fun _ => y) * h * (fun _ => y⁻¹), H.mul_mem (H.mul_mem (hconst y) hH) (hconst _),
      fun k hk => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 hk]
      simp [hj j (Finset.mem_singleton_self j)]
    · simp
  set m : Fin p := j - i with hmdef
  have hm0 : (m : ℕ) ≠ 0 := by
    intro h0
    apply hji
    have : m = 0 := Fin.ext (by rw [h0, Fin.val_zero])
    rw [hmdef, sub_eq_zero] at this
    exact this
  obtain ⟨v, hv⟩ := hα m (Nat.pos_of_ne_zero hm0) m.2
  have hjim : α ^ (j : ℕ) = α ^ (i : ℕ) * α ^ (m : ℕ) := by
    rw [← pow_add, pow_eq_pow_mod (i + m : ℕ) hαp]
    congr 1
    have h1 : i + m = j := by rw [hmdef]; abel
    rw [← h1, Fin.val_add]
  have hMv : (α ^ (i : ℕ)) (v * (α ^ (m : ℕ)) v⁻¹) ∈ M := by
    refine ⟨(fun k : Fin p => (α ^ (k : ℕ)) v) * (fun _ => ((α ^ (j : ℕ)) v)⁻¹),
      H.mul_mem (htw v) (hconst _), fun k hk => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 hk]
      simp
    · simp only [Pi.mul_apply, map_mul, hjim, MulAut.mul_apply, map_inv]
  have hMtop := hqs M hMn _ hMv (fun hc => hv (mem_center_of_apply_mem hc))
  obtain ⟨h, hH, hj, hi⟩ : g ∈ M := hMtop ▸ Subgroup.mem_top g
  exact ⟨h, hH, hj j (Finset.mem_singleton_self j), hi⟩

end Pi

section Block

variable {F : Type*} [Field F] {p : ℕ}

structure OrthDecomp (Q : Fin p → Matrix (Fin p) (Fin p) F) : Prop where
  mul_self : ∀ k, Q k * Q k = Q k
  mul_ne : ∀ j k, j ≠ k → Q j * Q k = 0
  sum_eq : ∑ k, Q k = 1

theorem kr_sum_left {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin p) (Fin p) F)
    (B : Matrix (Fin p) (Fin p) F) : kr (∑ i ∈ s, A i) B = ∑ i ∈ s, kr (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kr_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, kr_add_left, ih]

@[expose] noncomputable def blockMat (Q : Fin p → Matrix (Fin p) (Fin p) F)
    (X : Fin p → Matrix (Fin p) (Fin p) F) : Matrix (Fin (p * p)) (Fin (p * p)) F :=
  ∑ k, kr (Q k) (X k)

theorem blockMat_mul {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q)
    (X Y : Fin p → Matrix (Fin p) (Fin p) F) :
    blockMat Q X * blockMat Q Y = blockMat Q (fun k => X k * Y k) := by
  classical
  unfold blockMat
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [kr_mul, hQ.mul_self]
  · intro k _ hkj
    rw [kr_mul, hQ.mul_ne j k (Ne.symm hkj), kr_zero_left]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem blockMat_const {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q)
    (u : Matrix (Fin p) (Fin p) F) : blockMat Q (fun _ => u) = kr 1 u := by
  rw [blockMat, ← kr_sum_left, hQ.sum_eq]

theorem blockMat_one {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q) :
    blockMat Q (fun _ => 1) = 1 := by
  rw [blockMat_const hQ, kr_one]

theorem blockMat_mulSingle {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q) (i : Fin p)
    (g : Matrix (Fin p) (Fin p) F) :
    blockMat Q (Pi.mulSingle i g) = 1 + kr (Q i) (g - 1) := by
  classical
  have h : ∀ k, kr (Q k) ((Pi.mulSingle i g : Fin p → Matrix (Fin p) (Fin p) F) k) =
      kr (Q k) 1 + (if k = i then kr (Q k) (g - 1) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [Pi.mulSingle_eq_same, if_pos rfl, ← kr_add_right]
      congr 1
      abel
    · rw [Pi.mulSingle_eq_of_ne hk, if_neg hk, add_zero]
  unfold blockMat
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), ← kr_sum_left, hQ.sum_eq, kr_one]

@[expose] noncomputable def blockHom {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q) :
    (Fin p → SpecialLinearGroup (Fin p) F) →* GL (Fin (p * p)) F where
  toFun X := ⟨blockMat Q (fun k => (X k : Matrix (Fin p) (Fin p) F)),
    blockMat Q (fun k => ((X k)⁻¹ : SpecialLinearGroup (Fin p) F)), by
      rw [blockMat_mul hQ]
      simp only [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
      exact blockMat_one hQ, by
      rw [blockMat_mul hQ]
      simp only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
      exact blockMat_one hQ⟩
  map_one' := Units.ext (by
    show blockMat Q (fun k => ((1 : Fin p → SpecialLinearGroup (Fin p) F) k :
      Matrix (Fin p) (Fin p) F)) = 1
    simp only [Pi.one_apply, Matrix.SpecialLinearGroup.coe_one]
    exact blockMat_one hQ)
  map_mul' X Y := Units.ext (by
    show blockMat Q (fun k => ((X * Y) k : Matrix (Fin p) (Fin p) F)) =
      blockMat Q (fun k => (X k : Matrix (Fin p) (Fin p) F)) *
        blockMat Q (fun k => (Y k : Matrix (Fin p) (Fin p) F))
    rw [blockMat_mul hQ]
    simp only [Pi.mul_apply, Matrix.SpecialLinearGroup.coe_mul])

theorem coe_blockHom {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q)
    (X : Fin p → SpecialLinearGroup (Fin p) F) :
    ((blockHom hQ X : GL (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      blockMat Q (fun k => (X k : Matrix (Fin p) (Fin p) F)) := rfl

theorem kr_mul_blockMat_comm {Q : Fin p → Matrix (Fin p) (Fin p) F} (σ : Fin p ≃ Fin p)
    {T C : Matrix (Fin p) (Fin p) F} (hT : ∀ k, T * Q k = Q (σ k) * T)
    {X : Fin p → Matrix (Fin p) (Fin p) F} (hX : ∀ k, C * X k = X (σ k) * C) :
    kr T C * blockMat Q X = blockMat Q X * kr T C := by
  unfold blockMat
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ k, kr T C * kr (Q k) (X k) = ∑ k, kr (Q (σ k)) (X (σ k)) * kr T C := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [kr_mul, kr_mul, hT, hX]
    _ = ∑ k, kr (Q k) (X k) * kr T C :=
        Equiv.sum_comp σ (fun k => kr (Q k) (X k) * kr T C)

theorem kr_one_mul_blockMat_comm {Q : Fin p → Matrix (Fin p) (Fin p) F}
    {W : Matrix (Fin p) (Fin p) F} (hW : ∀ k, W * Q k = Q k * W)
    (X : Fin p → Matrix (Fin p) (Fin p) F) :
    kr W 1 * blockMat Q X = blockMat Q X * kr W 1 := by
  unfold blockMat
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kr_mul, kr_mul, hW, Matrix.one_mul, Matrix.mul_one]

end Block

section Families

variable {F : Type*} [Field F] {p : ℕ}

@[expose] noncomputable def shiftEquiv (hp : 0 < p) : Fin p ≃ Fin p :=
  Equiv.ofBijective (shiftIdx hp) (shiftIdx_injective hp).bijective_of_finite

theorem shiftEquiv_apply (hp : 0 < p) (k : Fin p) : shiftEquiv hp k = shiftIdx hp k := rfl

theorem orthDecomp_single :
    OrthDecomp (fun k : Fin p => (Matrix.single k k (1 : F) : Matrix (Fin p) (Fin p) F)) where
  mul_self k := by rw [Matrix.single_mul_single_same, mul_one]
  mul_ne j k h := Matrix.single_mul_single_of_ne 1 j j k h 1
  sum_eq := Matrix.sum_single_one

theorem shiftMat_mul_single (hp : 0 < p) (k : Fin p) :
    shiftMat p F * Matrix.single k k 1 =
      Matrix.single (shiftIdx hp k) (shiftIdx hp k) 1 * shiftMat p F := by
  ext a b
  by_cases hb : b = k
  · subst hb
    rw [Matrix.mul_single_apply_same 1 b b a (shiftMat p F), mul_one]
    by_cases ha : a = shiftIdx hp b
    · subst ha
      rw [Matrix.single_mul_apply_same 1 (shiftIdx hp b) (shiftIdx hp b) b (shiftMat p F),
        one_mul]
    · rw [Matrix.single_mul_apply_of_ne 1 (shiftIdx hp b) (shiftIdx hp b) a b ha (shiftMat p F),
        shiftMat_apply hp, if_neg ha]
  · rw [Matrix.mul_single_apply_of_ne 1 k k a b hb (shiftMat p F)]
    by_cases ha : a = shiftIdx hp k
    · subst ha
      rw [Matrix.single_mul_apply_same 1 (shiftIdx hp k) (shiftIdx hp k) b (shiftMat p F),
        one_mul, shiftMat_apply hp, if_neg]
      intro h
      exact hb (shiftIdx_injective hp h).symm
    · rw [Matrix.single_mul_apply_of_ne 1 (shiftIdx hp k) (shiftIdx hp k) a b ha (shiftMat p F)]

theorem diagonal_mul_single (d : Fin p → F) (k : Fin p) :
    Matrix.diagonal d * Matrix.single k k 1 = Matrix.single k k 1 * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h
  · rw [← h.1, ← h.2]; ring
  · ring

@[expose] noncomputable def fourierProj (ε : F) (j : Fin p) : Matrix (Fin p) (Fin p) F :=
  (p : F)⁻¹ • Matrix.of fun (a b : Fin p) => ε ^ ((j : ℕ) * (a : ℕ)) * ε⁻¹ ^ ((j : ℕ) * (b : ℕ))

theorem fourierProj_apply (ε : F) (j a b : Fin p) :
    fourierProj ε j a b = (p : F)⁻¹ * (ε ^ ((j : ℕ) * (a : ℕ)) * ε⁻¹ ^ ((j : ℕ) * (b : ℕ))) := rfl

theorem pow_mod_mul {y : F} (hy : y ^ p = 1) (x a : ℕ) : y ^ (x % p * a) = y ^ (x * a) := by
  rw [pow_mul, pow_mul, ← pow_eq_pow_mod x hy]

theorem sum_fin_pow_root_eq_zero {y : F} (hy : y ^ p = 1) (hy1 : y ≠ 1) :
    ∑ l : Fin p, y ^ (l : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => y ^ l)]
  exact geom_sum_root_eq_zero hy hy1

theorem inv_pow_mul_pow_eq_one_iff {ε : F} (hε : IsPrimitiveRoot ε p) (j k : Fin p) :
    ε⁻¹ ^ (j : ℕ) * ε ^ (k : ℕ) = 1 ↔ j = k := by
  have hε0 : ε ≠ 0 := hε.ne_zero (by have := j.2; omega)
  constructor
  · intro h
    rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hε0)] at h
    exact Fin.ext (hε.pow_inj j.2 k.2 h)
  · rintro rfl
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hε0)]

theorem root_pow_eq_one {ε : F} (hεp : ε ^ p = 1) (j k : ℕ) :
    (ε⁻¹ ^ j * ε ^ k) ^ p = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j p, mul_comm k p, pow_mul, pow_mul, inv_pow, hεp,
    inv_one, one_pow, one_pow, one_mul]

theorem orthDecomp_fourierProj (hpF : (p : F) ≠ 0) {ε : F} (hε : IsPrimitiveRoot ε p) :
    OrthDecomp (fourierProj (p := p) ε) := by
  have hεp : ε ^ p = 1 := hε.pow_eq_one
  have hsum : ∀ j k a b : Fin p, (fourierProj ε j * fourierProj ε k) a b =
      (p : F)⁻¹ * (p : F)⁻¹ * (ε ^ ((j : ℕ) * (a : ℕ)) * ε⁻¹ ^ ((k : ℕ) * (b : ℕ))) *
          ∑ l : Fin p, (ε⁻¹ ^ (j : ℕ) * ε ^ (k : ℕ)) ^ (l : ℕ) := by
    intro j k a b
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [fourierProj_apply, fourierProj_apply, mul_pow, ← pow_mul, ← pow_mul]
    ring
  refine ⟨fun k => ?_, fun j k h => ?_, ?_⟩
  · ext a b
    rw [hsum, (inv_pow_mul_pow_eq_one_iff hε k k).2 rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, fourierProj_apply]
    field_simp
  · ext a b
    rw [hsum, sum_fin_pow_root_eq_zero (root_pow_eq_one hεp _ _)
      (fun h' => h ((inv_pow_mul_pow_eq_one_iff hε j k).1 h')), mul_zero, Matrix.zero_apply]
  · ext a b
    rw [Matrix.sum_apply, Matrix.one_apply]
    have h1 : ∑ j : Fin p, fourierProj ε j a b =
        (p : F)⁻¹ * ∑ j : Fin p, (ε⁻¹ ^ (b : ℕ) * ε ^ (a : ℕ)) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fourierProj_apply, mul_pow, ← pow_mul, ← pow_mul]
      ring
    rw [h1]
    by_cases hab : a = b
    · subst hab
      rw [(inv_pow_mul_pow_eq_one_iff hε a a).2 rfl, if_pos rfl]
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      exact inv_mul_cancel₀ hpF
    · rw [sum_fin_pow_root_eq_zero (root_pow_eq_one hεp _ _)
        (fun h' => hab ((inv_pow_mul_pow_eq_one_iff hε b a).1 h').symm), if_neg hab, mul_zero]

theorem fourierProj_zero [NeZero p] (ε : F) : fourierProj ε (0 : Fin p) = projF := by
  ext a b
  rw [fourierProj_apply, projF, Matrix.smul_apply, onesM, Matrix.of_apply, Fin.val_zero]
  simp

theorem fourierProj_mul_shiftMat (hp : 0 < p) {ε : F} (hεp : ε ^ p = 1) (j : Fin p) :
    fourierProj ε j * shiftMat p F = ε⁻¹ ^ (j : ℕ) • fourierProj ε j := by
  have hεip : ε⁻¹ ^ p = 1 := by rw [inv_pow, hεp, inv_one]
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (shiftIdx hp b)]
  · rw [shiftMat_apply hp, if_pos rfl, mul_one, Matrix.smul_apply, fourierProj_apply,
      fourierProj_apply, smul_eq_mul]
    have h1 : ε⁻¹ ^ ((j : ℕ) * (shiftIdx hp b : ℕ)) =
        ε⁻¹ ^ (j : ℕ) * ε⁻¹ ^ ((j : ℕ) * (b : ℕ)) := by
      rw [shiftIdx, mul_comm (j : ℕ), pow_mod_mul hεip, ← pow_add]
      congr 1
      ring
    rw [h1]
    ring
  · intro l _ hl
    rw [shiftMat_apply hp, if_neg hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem shiftMat_mul_fourierProj (hp : 0 < p) {ε : F} (hεp : ε ^ p = 1) (hε0 : ε ≠ 0)
    (j : Fin p) : shiftMat p F * fourierProj ε j = ε⁻¹ ^ (j : ℕ) • fourierProj ε j := by
  ext a b
  obtain ⟨l₀, hl₀⟩ := ((shiftIdx_injective hp).bijective_of_finite).2 a
  rw [Matrix.mul_apply, Finset.sum_eq_single l₀]
  · rw [shiftMat_apply hp, if_pos hl₀.symm, one_mul, Matrix.smul_apply, fourierProj_apply,
      fourierProj_apply, smul_eq_mul]
    have h1 : ε ^ ((j : ℕ) * (a : ℕ)) = ε ^ (j : ℕ) * ε ^ ((j : ℕ) * (l₀ : ℕ)) := by
      rw [← hl₀, shiftIdx, mul_comm (j : ℕ), pow_mod_mul hεp, ← pow_add]
      congr 1
      ring
    have hj1 : ε⁻¹ ^ (j : ℕ) * ε ^ (j : ℕ) = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hε0)]
    rw [h1]
    linear_combination (-(p : F)⁻¹ * ε ^ ((j : ℕ) * (l₀ : ℕ)) * ε⁻¹ ^ ((j : ℕ) * (b : ℕ))) * hj1
  · intro l _ hl
    rw [shiftMat_apply hp, if_neg (fun h => hl (shiftIdx_injective hp (h.symm.trans hl₀.symm))),
      zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem shiftMat_comm_fourierProj (hp : 0 < p) {ε : F} (hεp : ε ^ p = 1) (hε0 : ε ≠ 0)
    (j : Fin p) : shiftMat p F * fourierProj ε j = fourierProj ε j * shiftMat p F := by
  rw [shiftMat_mul_fourierProj hp hεp hε0, fourierProj_mul_shiftMat hp hεp]

theorem charMat_mul_fourierProj (hp : 0 < p) {ε : F} (hεp : ε ^ p = 1) (hε0 : ε ≠ 0)
    (j : Fin p) :
    charMat p ε * fourierProj ε j = fourierProj ε (shiftIdx hp j) * charMat p ε := by
  have hεip : ε⁻¹ ^ p = 1 := by rw [inv_pow, hεp, inv_one]
  ext a b
  rw [charMat, Matrix.diagonal_mul, Matrix.mul_diagonal, fourierProj_apply, fourierProj_apply,
    shiftIdx]
  simp only
  rw [pow_mod_mul hεp, pow_mod_mul hεip]
  have h1 : ε ^ (((j : ℕ) + 1) * (a : ℕ)) = ε ^ (a : ℕ) * ε ^ ((j : ℕ) * (a : ℕ)) := by
    rw [← pow_add]; congr 1; ring
  have h2 : ε⁻¹ ^ (((j : ℕ) + 1) * (b : ℕ)) = ε⁻¹ ^ (b : ℕ) * ε⁻¹ ^ ((j : ℕ) * (b : ℕ)) := by
    rw [← pow_add]; congr 1; ring
  have hb1 : ε⁻¹ ^ (b : ℕ) * ε ^ (b : ℕ) = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hε0)]
  rw [h1, h2]
  linear_combination (-(p : F)⁻¹ * ε ^ (a : ℕ) * ε ^ ((j : ℕ) * (a : ℕ)) *
    ε⁻¹ ^ ((j : ℕ) * (b : ℕ))) * hb1

end Families

section Twist

variable {F : Type*} [Field F] {p : ℕ}

theorem conjUnit_mul_apply (g h : GL (Fin p) F) (x : SpecialLinearGroup (Fin p) F) :
    conjUnit (g * h) x = conjUnit g (conjUnit h x) := by
  apply Subtype.ext
  rw [conjUnit_coe, conjUnit_coe, conjUnit_coe, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem conjUnit_one_apply (x : SpecialLinearGroup (Fin p) F) : conjUnit (1 : GL (Fin p) F) x = x := by
  apply Subtype.ext
  rw [conjUnit_coe, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def conjAutSL (g : GL (Fin p) F) : MulAut (SpecialLinearGroup (Fin p) F) where
  toFun := conjUnit g
  invFun := conjUnit g⁻¹
  left_inv x := by
    show conjUnit g⁻¹ (conjUnit g x) = x
    rw [← conjUnit_mul_apply, inv_mul_cancel, conjUnit_one_apply]
  right_inv x := by
    show conjUnit g (conjUnit g⁻¹ x) = x
    rw [← conjUnit_mul_apply, mul_inv_cancel, conjUnit_one_apply]
  map_mul' := map_mul (conjUnit g)

theorem conjAutSL_apply (g : GL (Fin p) F) (x : SpecialLinearGroup (Fin p) F) :
    conjAutSL g x = conjUnit g x := rfl

theorem conjAutSL_pow_apply (g : GL (Fin p) F) (k : ℕ) (x : SpecialLinearGroup (Fin p) F) :
    (conjAutSL g ^ k) x = conjUnit (g ^ k) x := by
  induction k with
  | zero => rw [pow_zero, pow_zero, MulAut.one_apply, conjUnit_one_apply]
  | succ k ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, ih, conjAutSL_apply, conjUnit_mul_apply]

theorem conjUnit_eq_self_of_commute {g : GL (Fin p) F} {x : SpecialLinearGroup (Fin p) F}
    (h : (g : Matrix (Fin p) (Fin p) F) * x = x * g) : conjUnit g x = x := by
  apply Subtype.ext
  rw [conjUnit_coe, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem conjAutSL_pow_eq_one {g : GL (Fin p) F} {c : F}
    (hg : ((g ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = c • 1) : conjAutSL g ^ p = 1 := by
  ext x
  rw [conjAutSL_pow_apply, MulAut.one_apply,
    conjUnit_eq_self_of_commute (by rw [hg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one])]

theorem coe_conjAutSL_pow (g : GL (Fin p) F) (k : ℕ) (x : SpecialLinearGroup (Fin p) F) :
    (((conjAutSL g ^ k) x : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      ((g ^ k : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * x *
        (((g ^ k)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  rw [conjAutSL_pow_apply, conjUnit_coe]

theorem compMat_mulVec_single {c : F} {t : ℕ} (ht : t + 1 < p) :
    compMat p c *ᵥ Pi.single (⟨t, by omega⟩ : Fin p) 1 = Pi.single ⟨t + 1, ht⟩ 1 := by
  ext a
  rw [mulVec_single_apply, compMat, Matrix.of_apply, Pi.single_apply]
  simp only [Nat.mod_eq_of_lt ht]
  by_cases ha : (a : ℕ) = t + 1
  · rw [if_pos ha, if_neg (by omega), if_pos (Fin.ext ha)]
  · rw [if_neg ha, if_neg (fun h => ha (by rw [h]))]

theorem compMat_pow_mulVec_single_zero {c : F} :
    ∀ (m : ℕ) (hm : m < p),
      (compMat p c ^ m) *ᵥ Pi.single (⟨0, by omega⟩ : Fin p) 1 = Pi.single ⟨m, hm⟩ 1
  | 0, _ => by rw [pow_zero, Matrix.one_mulVec]
  | m + 1, hm => by
    rw [pow_succ', ← Matrix.mulVec_mulVec, compMat_pow_mulVec_single_zero m (by omega),
      compMat_mulVec_single hm]

theorem exists_noncentral_twist {Cu : GL (Fin p) F} {c : F}
    (hC : (Cu : Matrix (Fin p) (Fin p) F) = compMat p c) {m : ℕ} (hm0 : 0 < m) (hm : m < p) :
    ∃ v : SpecialLinearGroup (Fin p) F,
      v * (conjAutSL Cu ^ m) v⁻¹ ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) := by
  have h0m : (⟨0, by omega⟩ : Fin p) ≠ ⟨m, hm⟩ := fun h => by
    have := congrArg Fin.val h
    simp only at this
    omega
  set v := SpecialLinearGroup.transvection h0m (1 : F) with hv
  refine ⟨v, fun hc => ?_⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  set e0 : Fin p → F := Pi.single (⟨0, by omega⟩ : Fin p) 1 with he0
  set em : Fin p → F := Pi.single (⟨m, hm⟩ : Fin p) 1 with hem
  have hCm : ((Cu ^ m : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *ᵥ e0 = em := by
    rw [Units.val_pow_eq_pow_val, hC, he0, hem, compMat_pow_mulVec_single_zero m hm]
  have hCmi : (((Cu ^ m)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *ᵥ em = e0 := by
    rw [← hCm, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hvi : ((v⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) *ᵥ e0 = e0 := by
    rw [hv, SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
    have : e0 ⟨m, hm⟩ = 0 := by rw [he0, Pi.single_apply, if_neg (Ne.symm h0m)]
    rw [this, mul_zero]
    ext a
    simp
  have hvm : (v : Matrix (Fin p) (Fin p) F) *ᵥ em = em + e0 := by
    rw [hv, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec]
    have : em ⟨m, hm⟩ = 1 := by rw [hem, Pi.single_apply, if_pos rfl]
    rw [this, mul_one]
    rfl
  have key : (scalar (Fin p) r) *ᵥ em = em + e0 := by
    rw [hr, Matrix.SpecialLinearGroup.coe_mul, coe_conjAutSL_pow]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCmi, ← Matrix.mulVec_mulVec, hvi, hCm,
      hvm]
  have h0 := congrFun key ⟨0, by omega⟩
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.add_apply, hem, he0, Pi.single_apply,
    Pi.single_apply, if_neg h0m, if_pos rfl, mul_zero, zero_add] at h0
  exact zero_ne_one h0

end Twist

section Transvections

variable {F : Type*} [Field F] {p : ℕ}

theorem coe_commutator_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : SpecialLinearGroup n F} {A B : Matrix n n F} (hX : (X : Matrix n n F) = 1 + A)
    (hY : (Y : Matrix n n F) = 1 + B) (hA : A * A = 0) (hB : B * B = 0) (hBA : B * A = 0) :
    ((⁅X, Y⁆ : SpecialLinearGroup n F) : Matrix n n F) = 1 + A * B := by
  have hinv : ∀ {Z : SpecialLinearGroup n F} {N : Matrix n n F}, (Z : Matrix n n F) = 1 + N →
      N * N = 0 → ((Z⁻¹ : SpecialLinearGroup n F) : Matrix n n F) = 1 - N := by
    intro Z N hZ hN
    have h1 : (Z : Matrix n n F) * (1 - N) = 1 := by
      rw [hZ, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hN, sub_zero,
        sub_add_cancel]
    calc ((Z⁻¹ : SpecialLinearGroup n F) : Matrix n n F)
        = ((Z⁻¹ : SpecialLinearGroup n F) : Matrix n n F) * ((Z : Matrix n n F) * (1 - N)) := by
          rw [h1, Matrix.mul_one]
      _ = ((Z⁻¹ * Z : SpecialLinearGroup n F) : Matrix n n F) * (1 - N) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
      _ = 1 - N := by rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have h1 : A * (A * B) = 0 := by rw [← Matrix.mul_assoc, hA, Matrix.zero_mul]
  have h2 : B * (A * B) = 0 := by rw [← Matrix.mul_assoc, hBA, Matrix.zero_mul]
  have h3 : A * (B * A) = 0 := by rw [hBA, Matrix.mul_zero]
  have h4 : A * (B * B) = 0 := by rw [hB, Matrix.mul_zero]
  have h5 : A * (B * (A * B)) = 0 := by rw [h2, Matrix.mul_zero]
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hX, hY, hinv hX hA, hinv hY hB]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc, hA, hB, hBA, h1, h2, h3, h4, h5, Matrix.mul_zero,
    Matrix.zero_mul, smul_zero, add_zero, zero_add, sub_zero, zero_sub]
  abel

theorem single_mul_projF_mul_single (i k : Fin p) :
    Matrix.single i i (1 : F) * projF * Matrix.single k k 1 =
      (p : F)⁻¹ • Matrix.single i k 1 := by
  rw [projF, Matrix.mul_smul, Matrix.smul_mul, Matrix.single_mul_mul_single, onesM,
    Matrix.of_apply, mul_one, mul_one]

theorem eq_top_of_blocks (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)}
    (hB : ∀ (i j l : Fin p), j ≠ l → ∀ c : F, ∃ s ∈ K',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        1 + c • kr (Matrix.single i i 1) (Matrix.single j l 1))
    (hM : ∀ (j l : Fin p), j ≠ l → ∀ c : F, ∃ s ∈ K',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) = 1 + c • kr projF (Matrix.single j l 1)) :
    K' = ⊤ := by
  have htA : ∀ (i k j l : Fin p) (hjl : j ≠ l)
      (hne : finProdFinEquiv (i, j) ≠ finProdFinEquiv (k, l)) (c : F),
      SpecialLinearGroup.transvection hne c ∈ K' := by
    intro i k j l hjl hne c
    obtain ⟨m, hmj, hml⟩ := exists_ne_pair hp3 j l
    obtain ⟨l', hl'j, hl'm⟩ := exists_ne_pair hp3 j m
    obtain ⟨X₁, hX₁, hX₁e⟩ := hB i j l' (Ne.symm hl'j) ((p : F) * c)
    obtain ⟨X₂, hX₂, hX₂e⟩ := hM l' m hl'm 1
    obtain ⟨X₃, hX₃, hX₃e⟩ := hB k m l hml 1
    set A₁ : Matrix (Fin (p * p)) (Fin (p * p)) F :=
      ((p : F) * c) • kr (Matrix.single i i 1) (Matrix.single j l' 1) with hA₁
    set B₁ : Matrix (Fin (p * p)) (Fin (p * p)) F :=
      (1 : F) • kr projF (Matrix.single l' m 1) with hB₁
    have hA₁A₁ : A₁ * A₁ = 0 := by
      rw [hA₁, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 j l' j hl'j 1, kr_zero_right, smul_zero,
        smul_zero]
    have hB₁B₁ : B₁ * B₁ = 0 := by
      rw [hB₁, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 l' m l' (Ne.symm hl'm) 1, kr_zero_right, smul_zero,
        smul_zero]
    have hB₁A₁ : B₁ * A₁ = 0 := by
      rw [hB₁, hA₁, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 l' m j hmj 1, kr_zero_right, smul_zero, smul_zero]
    have hc₁ := coe_commutator_one_add hX₁e hX₂e hA₁A₁ hB₁B₁ hB₁A₁
    set A₂ := A₁ * B₁ with hA₂
    have hA₂e : A₂ = ((p : F) * c) • kr (Matrix.single i i 1 * projF) (Matrix.single j m 1) := by
      rw [hA₂, hA₁, hB₁, one_smul, Matrix.smul_mul, kr_mul, Matrix.single_mul_single_same,
        mul_one]
    set B₂ : Matrix (Fin (p * p)) (Fin (p * p)) F :=
      (1 : F) • kr (Matrix.single k k 1) (Matrix.single m l 1) with hB₂
    have hA₂A₂ : A₂ * A₂ = 0 := by
      rw [hA₂e, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 j m j hmj 1, kr_zero_right, smul_zero, smul_zero]
    have hB₂B₂ : B₂ * B₂ = 0 := by
      rw [hB₂, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 m l m (Ne.symm hml) 1, kr_zero_right, smul_zero,
        smul_zero]
    have hB₂A₂ : B₂ * A₂ = 0 := by
      rw [hB₂, hA₂e, Matrix.smul_mul, Matrix.mul_smul, kr_mul,
        Matrix.single_mul_single_of_ne 1 m l j (Ne.symm hjl) 1, kr_zero_right, smul_zero,
        smul_zero]
    have hc₂ := coe_commutator_one_add hc₁ hX₃e hA₂A₂ hB₂B₂ hB₂A₂
    have heq : ⁅⁅X₁, X₂⁆, X₃⁆ = SpecialLinearGroup.transvection hne c := by
      apply Subtype.ext
      rw [hc₂, SpecialLinearGroup.transvection_coe, hA₂e, hB₂, one_smul, Matrix.smul_mul, kr_mul,
        Matrix.single_mul_single_same, mul_one, single_mul_projF_mul_single, kr_smul_left,
        smul_smul, mul_comm (p : F) c, mul_assoc, mul_inv_cancel₀ hpF, mul_one, kr_single,
        Matrix.smul_single, smul_eq_mul, mul_one]
    rw [← heq]
    have hm1 : ⁅X₁, X₂⁆ ∈ K' := by
      rw [commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem hX₁ hX₂) (K'.inv_mem hX₁)) (K'.inv_mem hX₂)
    rw [commutatorElement_def]
    exact K'.mul_mem (K'.mul_mem (K'.mul_mem hm1 hX₃) (K'.inv_mem hm1)) (K'.inv_mem hX₃)
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin (p * p)) (K := F)
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  obtain ⟨⟨i, j⟩, hα⟩ := finProdFinEquiv.surjective t.i
  obtain ⟨⟨k, l⟩, hβ⟩ := finProdFinEquiv.surjective t.j
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
  have hij : finProdFinEquiv (i, j) ≠ finProdFinEquiv (k, l) := by rw [hα, hβ]; exact t.hij
  have hcast : SpecialLinearGroup.transvection t.hij t.c =
      SpecialLinearGroup.transvection hij t.c := by
    apply Subtype.ext
    rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, hα, hβ]
  rw [hcast]
  by_cases hjl : j = l
  · subst hjl
    have hik : i ≠ k := fun h => hij (by rw [h])
    obtain ⟨m, hmj, -⟩ := exists_ne_pair hp3 j j
    have h1 : finProdFinEquiv (i, j) ≠ finProdFinEquiv (i, m) := fun h =>
      hmj (by simpa using (congrArg Prod.snd (finProdFinEquiv.injective h)).symm)
    have h2 : finProdFinEquiv (i, m) ≠ finProdFinEquiv (k, j) := fun h =>
      hik (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
    have hx1 : SpecialLinearGroup.transvection h1 t.c ∈ K' := htA i i j m (Ne.symm hmj) h1 t.c
    have hx2 : SpecialLinearGroup.transvection h2 (1 : F) ∈ K' := htA i k m j hmj h2 1
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection h1 h2 hij t.c (1 : F)
    rw [mul_one] at hcomm
    rw [← hcomm, commutatorElement_def]
    exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx1 hx2) (K'.inv_mem hx1)) (K'.inv_mem hx2)
  · exact htA i k j l hjl hij t.c

end Transvections

section Generation

variable {F : Type*} [Field F] {p : ℕ}

theorem coe_mulSingle_fun (i : Fin p) (g : SpecialLinearGroup (Fin p) F) :
    (fun k => ((Pi.mulSingle i g : Fin p → SpecialLinearGroup (Fin p) F) k :
      Matrix (Fin p) (Fin p) F)) = Pi.mulSingle i (g : Matrix (Fin p) (Fin p) F) := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk, Matrix.SpecialLinearGroup.coe_one]

theorem eq_top_of_kron_families (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0) {ε : F}
    (hε : IsPrimitiveRoot ε p) {Cu : GL (Fin p) F} {c : F}
    (hC : (Cu : Matrix (Fin p) (Fin p) F) = compMat p c)
    (hCp : ((Cu ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = c • 1)
    {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)}
    (hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K')
    (hE : ∀ v : SpecialLinearGroup (Fin p) F, ∃ s ∈ K',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        blockMat (fun k => Matrix.single k k 1)
          (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)))
    (hP : ∀ v : SpecialLinearGroup (Fin p) F, ∃ s ∈ K',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        blockMat (fourierProj ε)
          (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F))) :
    K' = ⊤ := by
  have : NeZero p := ⟨by omega⟩
  have hperf : commutator (SpecialLinearGroup (Fin p) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hp3)).commutator_eq_top
  have hqs : ∀ N : Subgroup (SpecialLinearGroup (Fin p) F), N.Normal → ∀ a ∈ N,
      a ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) → N = ⊤ := by
    intro N hN a haN ha
    haveI := hN
    exact eq_top_of_normal_of_not_mem_center hp3 haN ha
  have hαp := conjAutSL_pow_eq_one hCp
  have hα : ∀ m : ℕ, 0 < m → m < p → ∃ v : SpecialLinearGroup (Fin p) F,
      v * (conjAutSL Cu ^ m) v⁻¹ ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) :=
    fun m hm0 hm => exists_noncentral_twist hC hm0 hm
  have hfam : ∀ {Q : Fin p → Matrix (Fin p) (Fin p) F} (hQ : OrthDecomp Q),
      (∀ v : SpecialLinearGroup (Fin p) F, ∃ s ∈ K',
        (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
          blockMat Q (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F))) →
      ∀ (i : Fin p) (g : SpecialLinearGroup (Fin p) F), ∃ s ∈ K',
        (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
          1 + kr (Q i) ((g : Matrix (Fin p) (Fin p) F) - 1) := by
    intro Q hQ htw i g
    set H : Subgroup (Fin p → SpecialLinearGroup (Fin p) F) :=
      (K'.map Matrix.SpecialLinearGroup.toGL).comap (blockHom hQ) with hH
    have hmem : ∀ X, X ∈ H ↔ ∃ s ∈ K', (s : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        blockMat Q (fun k => (X k : Matrix (Fin p) (Fin p) F)) := by
      intro X
      constructor
      · rintro ⟨s, hs, hse⟩
        refine ⟨s, hs, ?_⟩
        rw [← coe_blockHom hQ X, ← hse]
        rfl
      · rintro ⟨s, hs, hse⟩
        exact ⟨s, hs, Units.ext (by rw [coe_blockHom]; exact hse)⟩
    have hconst : ∀ u : SpecialLinearGroup (Fin p) F, (fun _ => u) ∈ H := fun u =>
      (hmem _).2 ⟨dHom u, hd u, by rw [coe_dHom, blockMat_const hQ]⟩
    have htw' : ∀ v : SpecialLinearGroup (Fin p) F,
        (fun k : Fin p => (conjAutSL Cu ^ (k : ℕ)) v) ∈ H := fun v => (hmem _).2 (htw v)
    have h := mulSingle_mem_of_twisted hperf hqs (conjAutSL Cu) hαp hα H hconst htw' i g
    obtain ⟨s, hs, hse⟩ := (hmem _).1 h
    exact ⟨s, hs, by rw [hse, coe_mulSingle_fun, blockMat_mulSingle hQ]⟩
  have htr : ∀ (Q : Matrix (Fin p) (Fin p) F) (j l : Fin p) (hjl : j ≠ l) (c : F),
      1 + kr Q (((SpecialLinearGroup.transvection hjl c : SpecialLinearGroup (Fin p) F) :
        Matrix (Fin p) (Fin p) F) - 1) = 1 + c • kr Q (Matrix.single j l 1) := by
    intro Q j l hjl c
    rw [SpecialLinearGroup.transvection_coe, add_sub_cancel_left, ← kr_smul_right,
      Matrix.smul_single, smul_eq_mul, mul_one]
  refine eq_top_of_blocks hp3 hpF (fun i j l hjl c => ?_) (fun j l hjl c => ?_)
  · obtain ⟨s, hs, hse⟩ := hfam orthDecomp_single hE i (SpecialLinearGroup.transvection hjl c)
    exact ⟨s, hs, by rw [hse, htr]⟩
  · obtain ⟨s, hs, hse⟩ := hfam (orthDecomp_fourierProj hpF hε) hP 0
      (SpecialLinearGroup.transvection hjl c)
    exact ⟨s, hs, by rw [hse, htr, fourierProj_zero]⟩

end Generation

end CFSG.LieType.SeitzGeneration.QuasiHigh2
