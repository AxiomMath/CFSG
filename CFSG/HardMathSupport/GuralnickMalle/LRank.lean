module

public import CFSG.HardMathSupport.GuralnickMalle.SLnNatural2F
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral
public import CFSG.Open.StatedAPI

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open
open Module

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def unipotentEnd (a : GL (Fin n) K) : Module.End K (Fin n → K) :=
  (glNaturalRep n K a : Module.End K (Fin n → K)) - 1

@[expose] noncomputable def unipotentAlgebra (A : Subgroup (GL (Fin n) K)) :
    Submodule K (Module.End K (Fin n → K)) :=
  Submodule.span K (unipotentEnd '' (A : Set (GL (Fin n) K)))

theorem glNaturalRep_injective (n : ℕ) (K : Type) [Field K] :
    Function.Injective (glNaturalRep n K) := by
  intro a b h
  have h' : ((Matrix.GeneralLinearGroup.toLin a : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) =
      ((Matrix.GeneralLinearGroup.toLin b : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) := by
    simpa [glNaturalRep] using h
  exact (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).injective
    (Units.ext h')

theorem unipotentEnd_injective (n : ℕ) (K : Type) [Field K] :
    Function.Injective (unipotentEnd (n := n) (K := K)) := by
  intro a b h
  apply glNaturalRep_injective n K
  have h' : (glNaturalRep n K a : Module.End K (Fin n → K)) + 1 =
      (glNaturalRep n K b : Module.End K (Fin n → K)) + 1 := by
    simpa [unipotentEnd] using congrArg (fun f : Module.End K (Fin n → K) => f + 1) h
  simpa using h'

theorem card_le_pow_finrank_unipotentAlgebra {p : ℕ} [Finite K]
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    Nat.card A ≤ Nat.card K ^ finrank K (unipotentAlgebra A) := by
  haveI : Finite (Module.End K (Fin n → K)) :=
    Finite.of_injective (fun f : Module.End K (Fin n → K) => (f : (Fin n → K) → (Fin n → K)))
      (fun f g h => LinearMap.ext fun x => congrFun h x)
  haveI : Finite (unipotentAlgebra A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Module.Finite K (unipotentAlgebra A) := inferInstance
  let f : A → unipotentAlgebra A := fun a =>
    ⟨unipotentEnd (a : GL (Fin n) K),
      Submodule.subset_span ⟨(a : GL (Fin n) K), a.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro a b h
    have h' : unipotentEnd (a : GL (Fin n) K) = unipotentEnd (b : GL (Fin n) K) :=
      congrArg Subtype.val h
    exact Subtype.ext (unipotentEnd_injective n K h')
  have hcard : Nat.card A ≤ Nat.card (unipotentAlgebra A) :=
    Nat.card_le_card_of_injective f hinj
  have hmod : Nat.card (unipotentAlgebra A) =
      Nat.card K ^ finrank K (unipotentAlgebra A) :=
    Module.natCard_eq_pow_finrank (K := K) (V := unipotentAlgebra A)
  rw [hmod] at hcard
  exact hcard

theorem unipotentAlgebra_mul_mem {A : Subgroup (GL (Fin n) K)}
    {x y : Module.End K (Fin n → K)}
    (hx : x ∈ unipotentAlgebra A) (hy : y ∈ unipotentAlgebra A) :
    x * y ∈ unipotentAlgebra A := by
  have hSS : ∀ a b : A, unipotentEnd (a : GL (Fin n) K) * unipotentEnd (b : GL (Fin n) K) ∈
      unipotentAlgebra A := by
    intro a b
    have hidentity : unipotentEnd (a : GL (Fin n) K) * unipotentEnd (b : GL (Fin n) K) =
        (glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) *
            glNaturalRep n K (b : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) + 1 := by
      rw [unipotentEnd, unipotentEnd]
      rw [mul_sub, sub_mul, sub_mul, mul_one, one_mul, one_mul]
      abel
    have hmap : (glNaturalRep n K (((a * b : A) : GL (Fin n) K)) :
        Module.End K (Fin n → K)) =
        glNaturalRep n K (a : GL (Fin n) K) * glNaturalRep n K (b : GL (Fin n) K) := by
      simpa using map_mul (glNaturalRep n K) (a : GL (Fin n) K) (b : GL (Fin n) K)
    have hmem : unipotentEnd (((a * b : A) : GL (Fin n) K)) -
        unipotentEnd (a : GL (Fin n) K) - unipotentEnd (b : GL (Fin n) K) ∈
        unipotentAlgebra A := by
      exact sub_mem (sub_mem
        (Submodule.subset_span ⟨((a * b : A) : GL (Fin n) K), (a * b).2, rfl⟩)
        (Submodule.subset_span ⟨(a : GL (Fin n) K), a.2, rfl⟩))
        (Submodule.subset_span ⟨(b : GL (Fin n) K), b.2, rfl⟩)
    have hmem' : ((glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) *
            glNaturalRep n K (b : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) + 1) ∈ unipotentAlgebra A := by
      convert hmem using 1
      simp only [unipotentEnd, hmap, neg_one_smul]
      abel
    rwa [hidentity]
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y ∈ unipotentAlgebra A)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx' hy'
    rcases hx' with ⟨a, ha, rfl⟩
    rcases hy' with ⟨b, hb, rfl⟩
    exact hSS ⟨a, ha⟩ ⟨b, hb⟩
  · intro y _; simp
  · intro x _; simp
  · intro x y z _ _ _ hxz hyz; rw [add_mul]; exact add_mem hxz hyz
  · intro x y z _ _ _ hxy hxz; rw [mul_add]; exact add_mem hxy hxz
  · intro c x y _ _ hxy; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hxy
  · intro c x y _ _ hxy; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hxy

theorem unipotentAlgebra_commute {A : Subgroup (GL (Fin n) K)}
    (hAc : IsMulCommutative A) {x y : Module.End K (Fin n → K)}
    (hx : x ∈ unipotentAlgebra A) (hy : y ∈ unipotentAlgebra A) : Commute x y := by
  have hScomm : ∀ a b : A, Commute (unipotentEnd (a : GL (Fin n) K))
      (unipotentEnd (b : GL (Fin n) K)) := by
    intro a b
    have hab : (a : GL (Fin n) K) * (b : GL (Fin n) K) =
        (b : GL (Fin n) K) * (a : GL (Fin n) K) :=
      congrArg Subtype.val (hAc.is_comm.comm a b)
    have hmap : (glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) *
        glNaturalRep n K (b : GL (Fin n) K) =
        glNaturalRep n K (b : GL (Fin n) K) * glNaturalRep n K (a : GL (Fin n) K) := by
      rw [← map_mul, ← map_mul, hab]
    have hidentity1 : unipotentEnd (a : GL (Fin n) K) * unipotentEnd (b : GL (Fin n) K) =
        (glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) *
            glNaturalRep n K (b : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) + 1 := by
      rw [unipotentEnd, unipotentEnd]
      rw [mul_sub, sub_mul, sub_mul, mul_one, one_mul, one_mul]
      abel
    have hidentity2 : unipotentEnd (b : GL (Fin n) K) * unipotentEnd (a : GL (Fin n) K) =
        (glNaturalRep n K (b : GL (Fin n) K) : Module.End K (Fin n → K)) *
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) + 1 := by
      rw [unipotentEnd, unipotentEnd]
      rw [mul_sub, sub_mul, sub_mul, mul_one, one_mul, one_mul]
      abel
    calc unipotentEnd (a : GL (Fin n) K) * unipotentEnd (b : GL (Fin n) K)
        = (glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) *
            glNaturalRep n K (b : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) + 1 := hidentity1
      _ = glNaturalRep n K (b : GL (Fin n) K) * glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (a : GL (Fin n) K) -
            glNaturalRep n K (b : GL (Fin n) K) + 1 := by rw [hmap]
      _ = unipotentEnd (b : GL (Fin n) K) * unipotentEnd (a : GL (Fin n) K) := by
          rw [hidentity2]; abel
  refine Submodule.span_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx' hy'
    rcases hx' with ⟨a, ha, rfl⟩
    rcases hy' with ⟨b, hb, rfl⟩
    exact hScomm ⟨a, ha⟩ ⟨b, hb⟩
  · intro y _; exact Commute.zero_left y
  · intro x _; exact Commute.zero_right x
  · intro x y z _ _ _ hxz hyz; exact hxz.add_left hyz
  · intro x y z _ _ _ hxy hxz; exact hxy.add_right hxz
  · intro c x y _ _ hxy; exact hxy.smul_left c
  · intro c x y _ _ hxy; exact hxy.smul_right c

theorem unipotentAlgebra_isNilpotent {p : ℕ} [CharP K p] (hp : p.Prime)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A)
    {x : Module.End K (Fin n → K)} (hx : x ∈ unipotentAlgebra A) : IsNilpotent x := by
  rcases n with _ | n
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI : CharP (Module.End K (Fin (n + 1) → K)) p := by
      refine Module.charP_end (R := K) (M := Fin (n + 1) → K) ⟨fun _ => (1 : K), ?_⟩
      rw [Ideal.torsionOf_eq_bot_iff_of_isTorsionFree]
      intro h
      have := congrFun h ⟨0, Nat.succ_pos n⟩
      simpa using this
    haveI : Fact p.Prime := ⟨hp⟩
    have hgen : ∀ a : A, IsNilpotent (unipotentEnd (a : GL (Fin (n + 1)) K)) := by
      intro a
      have ha : (glNaturalRep (n + 1) K (a : GL (Fin (n + 1)) K) :
          Module.End K (Fin (n + 1) → K)) ^ p = 1 := by
        simpa using congrArg (glNaturalRep (n + 1) K) (hA.2 (a : GL (Fin (n + 1)) K) a.2)
      refine ⟨p, ?_⟩
      rw [unipotentEnd, sub_pow_char_of_commute p (Commute.one_right _), ha, one_pow, sub_self]
    have hcomm : ∀ x ∈ unipotentAlgebra A, ∀ y ∈ unipotentAlgebra A, Commute x y :=
      fun _ hx _ hy => unipotentAlgebra_commute (A := A) hA.1 hx hy
    refine Submodule.span_induction (p := fun x _ => IsNilpotent x) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hgen ⟨a, ha⟩
    · exact IsNilpotent.zero
    · intro x y hx' hy' hxN hyN
      exact (hcomm x hx' y hy').isNilpotent_add hxN hyN
    · intro c x _ hxN
      exact hxN.smul c

theorem iInf_ker_unipotentAlgebra (A : Subgroup (GL (Fin n) K)) :
    (⨅ f : unipotentAlgebra A,
      LinearMap.ker (f : Module.End K (Fin n → K))) =
      fixSubGen (glNaturalRep n K) A := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv
    rw [mem_fixSubGen]
    intro a ha
    have h := hv ⟨unipotentEnd (a : GL (Fin n) K),
      Submodule.subset_span ⟨(a : GL (Fin n) K), ha, rfl⟩⟩
    have h' : (glNaturalRep n K (a : GL (Fin n) K) : Module.End K (Fin n → K)) v - v = 0 := by
      simpa [unipotentEnd] using h
    exact sub_eq_zero.mp h'
  · intro hv f
    refine Submodule.span_induction (p := fun f _ => f v = 0) ?_ ?_ ?_ ?_ f.2
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      simp [unipotentEnd, hv a ha]
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro c x _ hx
      simp [hx]

@[expose] noncomputable def blockEquiv (n d : ℕ) (h : d ≤ n) :
    Fin d ⊕ Fin (n - d) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[expose] noncomputable def blockMatrix (n d : ℕ) (K : Type) [Field K] (h : d ≤ n)
    (B : Matrix (Fin d) (Fin (n - d)) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.reindexRingEquiv K (blockEquiv n d h)
    (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K) B
      (0 : Matrix (Fin (n - d)) (Fin d) K) (1 : Matrix (Fin (n - d)) (Fin (n - d)) K))

theorem blockMatrix_mul (n d : ℕ) (K : Type) [Field K] (h : d ≤ n)
    (B B' : Matrix (Fin d) (Fin (n - d)) K) :
    blockMatrix n d K h B * blockMatrix n d K h B' =
      blockMatrix n d K h (B + B') := by
  simp only [blockMatrix]
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_add, add_comm]

theorem det_blockMatrix (n d : ℕ) (K : Type) [Field K] (h : d ≤ n)
    (B : Matrix (Fin d) (Fin (n - d)) K) :
    (blockMatrix n d K h B).det = 1 := by
  rw [blockMatrix]
  simp only [Matrix.coe_reindexRingEquiv]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

@[expose] noncomputable def blockHom (n d : ℕ) (K : Type) [Field K] (h : d ≤ n) :
    Multiplicative (Matrix (Fin d) (Fin (n - d)) K) →* GL (Fin n) K where
  toFun B := Matrix.GeneralLinearGroup.mkOfDetNeZero (blockMatrix n d K h B.toAdd)
    (by rw [det_blockMatrix]; exact one_ne_zero)
  map_one' := by
    apply Units.ext
    simp [blockMatrix, Matrix.fromBlocks_one]
  map_mul' B B' := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, toAdd_mul]
    exact (blockMatrix_mul n d K h B.toAdd B'.toAdd).symm

theorem blockHom_injective (n d : ℕ) (K : Type) [Field K] (h : d ≤ n) :
    Function.Injective (blockHom n d K h) := by
  intro B B' hBB
  have hm : blockMatrix n d K h B.toAdd = blockMatrix n d K h B'.toAdd := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hBB
    simpa [blockHom] using this
  have hm' : Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K) B.toAdd
      (0 : Matrix (Fin (n - d)) (Fin d) K) (1 : Matrix (Fin (n - d)) (Fin (n - d)) K) =
      Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K) B'.toAdd
        (0 : Matrix (Fin (n - d)) (Fin d) K) (1 : Matrix (Fin (n - d)) (Fin (n - d)) K) := by
    have hm'' : (Matrix.reindexRingEquiv K (blockEquiv n d h))
        (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K) B.toAdd
          (0 : Matrix (Fin (n - d)) (Fin d) K) (1 : Matrix (Fin (n - d)) (Fin (n - d)) K)) =
        (Matrix.reindexRingEquiv K (blockEquiv n d h))
          (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K) B'.toAdd
            (0 : Matrix (Fin (n - d)) (Fin d) K) (1 : Matrix (Fin (n - d)) (Fin (n - d)) K)) := by
      simpa [blockMatrix] using hm
    exact (Matrix.reindexRingEquiv K (blockEquiv n d h)).injective hm''
  apply Multiplicative.toAdd.injective
  ext i j
  have := congrFun (congrFun hm' (Sum.inl i)) (Sum.inr j)
  simpa using this

@[expose] noncomputable def blockUnipotent (n d : ℕ) (K : Type) [Field K] :
    Subgroup (GL (Fin n) K) :=
  if h : d ≤ n then (blockHom n d K h).range else ⊥

theorem blockUnipotent_eq_range (n d : ℕ) (K : Type) [Field K] (h : d ≤ n) :
    blockUnipotent n d K = (blockHom n d K h).range := by
  rw [blockUnipotent, dif_pos h]

theorem blockUnipotent_eq_bot (n d : ℕ) (K : Type) [Field K] (h : ¬ d ≤ n) :
    blockUnipotent n d K = ⊥ := by
  rw [blockUnipotent, dif_neg h]

theorem blockUnipotent_isElemAbelian (n d p : ℕ) (K : Type) [Field K] [CharP K p]
    (hp : p.Prime) : IsElemAbelian p (blockUnipotent n d K) := by
  by_cases h : d ≤ n
  · rw [blockUnipotent_eq_range n d K h]
    constructor
    · haveI : IsMulCommutative (Multiplicative (Matrix (Fin d) (Fin (n - d)) K)) :=
        ⟨⟨fun a b => by
          apply Multiplicative.toAdd.injective
          simp [add_comm]⟩⟩
      infer_instance
    · intro x hx
      rcases MonoidHom.mem_range.1 hx with ⟨B, rfl⟩
      have hB : (p : ℕ) • B.toAdd = 0 := by
        ext i j
        simp [Matrix.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero]
      have hpow : B ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, hB]
      rw [← map_pow, hpow, map_one]
  · rw [blockUnipotent_eq_bot n d K h]
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      have ha : (a : GL (Fin n) K) = 1 := Subgroup.mem_bot.mp a.2
      have hb : (b : GL (Fin n) K) = 1 := Subgroup.mem_bot.mp b.2
      exact Subtype.ext (by simp [ha, hb])
    · intro x hx
      have hx1 : (x : GL (Fin n) K) = 1 := Subgroup.mem_bot.mp hx
      rw [hx1, one_pow]

theorem blockUnipotent_le_statedSL (n d : ℕ) (K : Type) [Field K] :
    blockUnipotent n d K ≤ StatedSL n K := by
  intro x hx
  by_cases h : d ≤ n
  · rw [blockUnipotent_eq_range n d K h] at hx
    rcases MonoidHom.mem_range.1 hx with ⟨B, rfl⟩
    exact CFSG.Open.StatedAPI.mem_statedSL_of_det (by
      change (blockMatrix n d K h B.toAdd).det = 1
      exact det_blockMatrix n d K h B.toAdd)
  · rw [blockUnipotent_eq_bot n d K h] at hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact one_mem _

theorem blockUnipotent_card (n d : ℕ) (K : Type) [Field K] [Finite K] :
    Nat.card (blockUnipotent n d K) = Nat.card K ^ (d * (n - d)) := by
  by_cases h : d ≤ n
  · rw [blockUnipotent_eq_range n d K h]
    have hinj : Function.Injective (blockHom n d K h) := blockHom_injective n d K h
    calc Nat.card (blockHom n d K h).range =
          Nat.card (Multiplicative (Matrix (Fin d) (Fin (n - d)) K)) :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
      _ = Nat.card (Matrix (Fin d) (Fin (n - d)) K) :=
        Nat.card_congr Multiplicative.toAdd
      _ = Nat.card K ^ (Nat.card (Fin (n - d)) * Nat.card (Fin d)) :=
        Matrix.card_matrix
      _ = Nat.card K ^ (d * (n - d)) := by simp [mul_comm]
  · rw [blockUnipotent_eq_bot n d K h, Subgroup.card_bot]
    have hnd : n - d = 0 := by omega
    rw [hnd, mul_zero, pow_zero]

theorem exists_elemAbelian_card_eq (n d p : ℕ) (K : Type) [Field K] [Finite K] [CharP K p]
    (hp : p.Prime) (h : d ≤ n) :
    ∃ A : Subgroup (GL (Fin n) K), IsElemAbelian p A ∧
      Nat.card A = Nat.card K ^ (d * (n - d)) ∧ A ≤ StatedSL n K :=
  ⟨blockUnipotent n d K, blockUnipotent_isElemAbelian n d p K hp,
    blockUnipotent_card n d K, blockUnipotent_le_statedSL n d K⟩

theorem mul_sub_le_sq_div_four {d n : ℕ} (h : d ≤ n) :
    d * (n - d) ≤ n ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  have hn : n = d + (n - d) := by omega
  rw [hn, Nat.add_sub_cancel_left]
  calc d * (n - d) * 4 = 4 * d * (n - d) := by ring
    _ ≤ (d + (n - d)) ^ 2 := four_mul_le_sq_add d (n - d)

theorem half_mul_half (n : ℕ) : (n / 2) * (n - n / 2) = n ^ 2 / 4 := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by
    have := Nat.mod_lt n (by norm_num : 0 < 2); omega
  rcases hr with hr | hr <;> rw [hn, hr]
  · simp only [Nat.add_zero]
    have h1 : (2 * (n / 2)) / 2 = n / 2 := Nat.mul_div_right (n / 2) (by norm_num : 0 < 2)
    have h2 : 2 * (n / 2) - n / 2 = n / 2 := by omega
    rw [h1, h2]
    have h3 : (2 * (n / 2)) ^ 2 = 4 * ((n / 2) * (n / 2)) := by ring
    rw [h3]
    exact (Nat.mul_div_right ((n / 2) * (n / 2)) (by norm_num : 0 < 4)).symm
  · have h1 : (2 * (n / 2) + 1) / 2 = n / 2 := by
      rw [Nat.mul_add_div (by norm_num : 0 < 2) (n / 2) 1]; norm_num
    have h2 : 2 * (n / 2) + 1 - n / 2 = n / 2 + 1 := by omega
    rw [h1, h2]
    have h3 : (2 * (n / 2) + 1) ^ 2 = 4 * ((n / 2) * (n / 2 + 1)) + 1 := by ring
    rw [h3, Nat.mul_add_div (by norm_num : 0 < 4) ((n / 2) * (n / 2 + 1)) 1]
    norm_num

theorem exists_elemAbelian_card_eq_statedSL' (n p : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K p] (hp : p.Prime) :
    ∃ A : Subgroup (StatedSL n K), IsElemAbelian p A ∧
      Nat.card A = Nat.card K ^ (n ^ 2 / 4) := by
  obtain ⟨A, hAe, hAcard, hAle⟩ :=
    exists_elemAbelian_card_eq n (n / 2) p K hp (Nat.div_le_self n 2)
  refine ⟨A.subgroupOf (StatedSL n K), hAe.subgroupOf (StatedSL n K), ?_⟩
  have hcard : Nat.card (A.subgroupOf (StatedSL n K)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv
  rw [hcard, hAcard, half_mul_half]

end CFSG.HardMathSupport.GuralnickMalle
