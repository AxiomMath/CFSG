module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLBlocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.TwoA.Base.ElemAut

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

variable (n K) in
abbrev conjProj : SpecialLinearGroup (Fin n) K →* MulAut (projectiveSL n K) :=
  (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)

theorem mul_conj_mul_inv {T : Type*} [Group T] (φ : MulAut T) (x : T) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem conjAut_mul_conjProj_mul_inv (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    conjAut n K A * conjProj n K g * (conjAut n K A)⁻¹ =
      conjProj n K (CatalogueBHigherLinearAction.slConjugation n K A g) := by
  rw [MonoidHom.comp_apply, mul_conj_mul_inv, conjAut_proj]
  rfl

theorem eq_of_proj_eq_of_pow_char {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    {x y : SpecialLinearGroup (Fin n) K} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (h : proj n K x = proj n K y) : x = y := by
  rw [proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  set z := x⁻¹ * y with hz
  have hzc : z ∈ center _ := scalars_le_center n K h
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : (x * z) ^ p = x ^ p * z ^ p :=
      (Commute.mul_pow (mem_center_iff.mp hzc x) p)
    rw [← hyz, hy, hx, one_mul] at h1
    exact h1.symm
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
  · exact Subsingleton.elim _ _
  have hcp : (c : K) ^ p = 1 := by
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) i i) hzp
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hc,
      one_apply_eq] at h2
    rwa [← map_pow, scalar_apply, diagonal_apply_eq] at h2
  have hc1 : (c : K) = 1 := by
    have h3 : ((c : K) - 1) ^ p = 0 := by rw [sub_pow_char, hcp, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h3)
  have hz1 : z = 1 := Subtype.ext (by rw [hc, hc1, map_one]; rfl)
  rw [hyz, hz1, mul_one]

theorem transvection_pow_char {p : ℕ} [CharP K p] {i j : Fin n} (hij : i ≠ j) (c : K) :
    (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) ^ p = 1 := by
  have key : ∀ m : ℕ, (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) ^ m =
      SpecialLinearGroup.transvection hij ((m : K) * c) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, Nat.cast_zero, zero_mul, SpecialLinearGroup.transvection_coeff_zero]
    | succ m ih =>
      rw [pow_succ, ih]
      apply Subtype.ext
      change transvection i j ((m : K) * c) * transvection i j c =
        transvection i j (((m + 1 : ℕ) : K) * c)
      rw [transvection_mul_transvection_same i j hij, Nat.cast_succ, add_one_mul]
  rw [key, CharP.cast_eq_zero, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem commute_single_apply {D : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (h : D * single i j (1 : K) = single i j 1 * D) :
    D j j = D i i ∧ (∀ k, k ≠ i → D k i = 0) ∧ ∀ l, l ≠ j → D j l = 0 := by
  have e : ∀ k l, (D * single i j (1 : K)) k l = (single i j (1 : K) * D) k l := fun k l => by
    rw [h]
  refine ⟨?_, fun k hk => ?_, fun l hl => ?_⟩
  · have := e i j
    simp only [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at this
    exact this.symm
  · have := e k j
    simp only [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hk] at this
    exact this
  · have := e i l
    simp only [single_mul_apply_same, one_mul, mul_single_apply_of_ne _ _ _ _ _ hl] at this
    exact this.symm

theorem isSubnormal_subgroupOf_of_normalizes {G : Type*} [Group G] {A C H : Subgroup G}
    (hAC : A ≤ C) (hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hC : (C.subgroupOf H).IsSubnormal) :
    (A.subgroupOf H).IsSubnormal := by
  refine IsSubnormal.step _ (C.subgroupOf H) (subgroupOf_mono H hAC) hC ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
  have hy : (((y : C.subgroupOf H) : H) : G) ∈ C := mem_subgroupOf.1 y.2
  simpa using hn _ hy _ hx

theorem isSubnormal_inf_subgroupOf {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (H : Subgroup G) : ((N ⊓ H).subgroupOf H).IsSubnormal := by
  refine Normal.isSubnormal ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf, mem_inf] at hx ⊢
  exact ⟨‹N.Normal›.conj_mem _ hx.1 _, by simpa using mul_mem (mul_mem y.2 hx.2) (inv_mem y.2)⟩

variable (K) in
@[expose] def signMat (J : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i ∈ J then -1 else 1

theorem signMat_mul_self (J : Finset (Fin n)) : signMat K J * signMat K J = 1 := by
  rw [signMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp

theorem det_signMat (J : Finset (Fin n)) : (signMat K J).det = (-1) ^ J.card := by
  rw [signMat, det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem signMat_eq (J : Finset (Fin n)) : signMat K J = (2 : K) • compInd K J - 1 := by
  ext i j
  rw [signMat, compInd, Matrix.sub_apply, Matrix.smul_apply, one_apply, diagonal_apply,
    diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ J <;> simp [hi]; norm_num
  · simp [hij]

theorem commute_signMat_iff (h2 : (2 : K) ≠ 0) (J : Finset (Fin n)) (D : Matrix (Fin n) (Fin n) K) :
    signMat K J * D = D * signMat K J ↔ compInd K J * D = D * compInd K J := by
  rw [signMat_eq]
  constructor
  · intro h
    have h' : (2 : K) • (compInd K J * D) = (2 : K) • (D * compInd K J) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      have := congrArg (· + D) h
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        sub_add_cancel] at this
      exact this
    exact smul_right_injective _ h2 h'
  · intro h
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, h]

variable (K) in
@[expose] def signSL (J : Finset (Fin n)) (hJ : Even J.card) : SpecialLinearGroup (Fin n) K :=
  ⟨signMat K J, by rw [det_signMat, hJ.neg_one_pow]⟩

theorem coe_signSL (J : Finset (Fin n)) (hJ : Even J.card) :
    ((signSL K J hJ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = signMat K J :=
  rfl

theorem signSL_mul_self (J : Finset (Fin n)) (hJ : Even J.card) :
    signSL K J hJ * signSL K J hJ = 1 :=
  Subtype.ext (signMat_mul_self J)

theorem signSL_mem_coordBlock (J : Finset (Fin n)) (hJ : Even J.card) :
    signSL K J hJ ∈ coordBlock K J := by
  rw [mem_coordBlock_iff]
  intro i j hij
  rw [coe_signSL, signMat, diagonal_apply]
  by_cases h : i = j
  · subst h
    have hi : i ∉ J := by tauto
    simp [hi]
  · simp [h]

@[expose] def slReindex {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] (R : Type*) [CommRing R] (e : m ≃ m') :
    SpecialLinearGroup m R ≃* SpecialLinearGroup m' R where
  toFun A := ⟨reindex e e A, by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm A, by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext ((reindexAlgEquiv R R e).map_mul A B)

@[expose] def slRingEquiv {m : Type*} [Fintype m] [DecidableEq m] {R S : Type*} [CommRing R]
    [CommRing S] (e : R ≃+* S) : SpecialLinearGroup m R ≃* SpecialLinearGroup m S where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' A B := map_mul _ A B

theorem exists_sl_galoisField [Finite K] (hK : ringChar K ≠ 2) :
    ∃ p f : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < f ∧
      Nonempty (SpecialLinearGroup (Fin 2) K ≃* SL(2, GaloisField p f)) := by
  have := Fintype.ofFinite K
  set p := ringChar K with hpdef
  have hp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, -, hcard⟩ := FiniteField.card K p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  refine ⟨p, f, inferInstance, hK, f.pos, ⟨slRingEquiv
    (GaloisField.algEquivGaloisField p f (by rw [Nat.card_eq_fintype_card, hcard])).toRingEquiv⟩⟩

section PairSlice

variable {a b : Fin n}

theorem even_card_pair (hab : a ≠ b) : Even ({a, b} : Finset (Fin n)).card := by
  rw [Finset.card_pair hab]
  exact even_two

theorem exists_not_mem_pair (hn : 3 ≤ n) (a b : Fin n) :
    ∃ k, k ∉ ({a, b} : Finset (Fin n)) := by
  by_contra h
  push Not at h
  have h1 := Finset.card_le_card (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => h k)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_insert_le a ({b} : Finset (Fin n))
  rw [Finset.card_singleton] at h2
  omega

theorem proj_injOn_coordBlock {J : Finset (Fin n)} {k : Fin n} (hk : k ∉ J)
    {g h : SpecialLinearGroup (Fin n) K} (hg : g ∈ coordBlock K J) (hh : h ∈ coordBlock K J)
    (e : proj n K g = proj n K h) : g = h := by
  rw [proj_eq_proj_iff] at e
  obtain ⟨c, -, hc⟩ := mem_scalars.1 e
  have hm : g⁻¹ * h ∈ coordBlock K J := mul_mem (inv_mem hg) hh
  have hkk := (mem_coordBlock_iff.1 hm) k k (Or.inl hk)
  simp only [hc, scalar_apply, diagonal_apply_eq, ↓reduceIte] at hkk
  have h1 : g⁻¹ * h = 1 := Subtype.ext (by rw [hc, hkk, map_one]; rfl)
  exact inv_mul_eq_one.1 h1

variable (K) in
@[expose] def pairSlice (a b : Fin n) : Subgroup (MulAut (projectiveSL n K)) :=
  (coordBlock K {a, b}).map (conjProj n K)

variable (K) in
@[expose] def pairInvolution (hab : a ≠ b) : MulAut (projectiveSL n K) :=
  conjProj n K (signSL K {a, b} (even_card_pair hab))

theorem pairInvolution_mem (hab : a ≠ b) : pairInvolution K hab ∈ pairSlice K a b :=
  ⟨_, signSL_mem_coordBlock _ _, rfl⟩

theorem conjProj_coordBlock_injective (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (a b : Fin n) : Function.Injective ((conjProj n K).comp (coordBlock K {a, b}).subtype) := by
  obtain ⟨k, hk⟩ := exists_not_mem_pair hn a b
  intro g h e
  exact Subtype.ext (proj_injOn_coordBlock hk g.2 h.2 (hinj e))

@[expose] def pairSliceEquiv (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (a b : Fin n) : coordBlock K {a, b} ≃* pairSlice K a b :=
  (MonoidHom.ofInjective (conjProj_coordBlock_injective hn hinj a b)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]; rfl))

theorem coe_pairSliceEquiv (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (g : coordBlock K {a, b}) :
    ((pairSliceEquiv hn hinj a b g : pairSlice K a b) : MulAut (projectiveSL n K)) =
      conjProj n K g :=
  rfl

theorem center_coordBlock_pair (hab : a ≠ b) :
    center (coordBlock K {a, b}) =
      zpowers (⟨signSL K {a, b} (even_card_pair hab), signSL_mem_coordBlock _ _⟩ :
        coordBlock K {a, b}) := by
  set J : Finset (Fin n) := {a, b} with hJ
  set s : coordBlock K J :=
    ⟨signSL K J (even_card_pair hab), signSL_mem_coordBlock J (even_card_pair hab)⟩ with hs
  apply le_antisymm
  · intro c hc
    have hca : a ∈ J := by simp [hJ]
    have hcb : b ∈ J := by simp [hJ]
    have htr : ∀ {i j : Fin n} (hij : i ≠ j), i ∈ J → j ∈ J →
        SpecialLinearGroup.transvection hij (1 : K) ∈ coordBlock K J := by
      intro i j hij hi hj
      rw [mem_coordBlock_iff]
      intro k l hkl
      rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
      have : ¬ (i = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        tauto
      simp [this]
    have hcomm : ∀ {i j : Fin n} (hij : i ≠ j), i ∈ J → j ∈ J →
        (c : Matrix (Fin n) (Fin n) K) * single i j 1 =
          single i j 1 * (c : Matrix (Fin n) (Fin n) K) := by
      intro i j hij hi hj
      have h1 : (1 + single i j (1 : K)) * (c : Matrix (Fin n) (Fin n) K) =
          (c : Matrix (Fin n) (Fin n) K) * (1 + single i j (1 : K)) :=
        congrArg (fun g : coordBlock K J => ((g : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) (mem_center_iff.1 hc ⟨_, htr hij hi hj⟩)
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h1
      exact (add_left_cancel h1).symm
    obtain ⟨h1, h2, -⟩ := commute_single_apply (hcomm hab hca hcb)
    obtain ⟨-, h3, -⟩ := commute_single_apply (hcomm hab.symm hcb hca)
    set x := (c : Matrix (Fin n) (Fin n) K) a a with hx
    have hJmem : ∀ i, i ∈ J ↔ i = a ∨ i = b := fun i => by simp [hJ]
    have hcd : (c : Matrix (Fin n) (Fin n) K) = diagonal fun i => if i ∈ J then x else 1 := by
      ext i j
      rw [diagonal_apply]
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · simp only [hi, ↓reduceIte]
        rcases (hJmem i).1 hi with hia | hib <;> rcases (hJmem j).1 hj with hja | hjb
        · rw [hia, hja]
          simp [hx]
        · rw [hia, hjb, h3 a hab]
          simp [hab]
        · rw [hib, hja, h2 b hab.symm]
          simp [hab.symm]
        · rw [hib, hjb, h1]
          simp
      · rw [(mem_coordBlock_iff.1 c.2) i j (Or.inr hj)]
        have : i ≠ j := fun h => hj (h ▸ hi)
        simp [this]
      · rw [(mem_coordBlock_iff.1 c.2) i j (Or.inl hi)]
        by_cases h : i = j
        · subst h
          simp [hi]
        · simp [h]
      · rw [(mem_coordBlock_iff.1 c.2) i j (Or.inl hi)]
        by_cases h : i = j
        · subst h
          simp [hi]
        · simp [h]
    have hdet : x ^ 2 = 1 := by
      have := ((c : SpecialLinearGroup (Fin n) K)).2
      rw [hcd, det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.card_pair hab] at this
      exact this
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 hfac with h | h
    · have h : x = 1 := sub_eq_zero.1 h
      have : c = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hcd, h]
        change (diagonal fun i => if i ∈ J then (1 : K) else 1) = 1
        simp
      rw [this]
      exact one_mem _
    · have h : x = -1 := eq_neg_of_add_eq_zero_left h
      have : c = s := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hcd, h]
        rfl
      rw [this]
      exact mem_zpowers s
  · rw [zpowers_le]
    refine mem_center_iff.2 fun g => ?_
    apply Subtype.ext
    apply Subtype.ext
    change (g : Matrix (Fin n) (Fin n) K) * signMat K J = signMat K J * g
    have hg := g.2
    obtain ⟨hg1, hg2⟩ := hg
    have : compInd K J * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) *
        compInd K J := by rw [hg1, hg2]
    rw [signMat_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, this]

theorem conj_range_normal {T : Type*} [Group T] :
    (MulAut.conj : T →* MulAut T).range.Normal :=
  ⟨fun _ ⟨x, hx⟩ φ => ⟨φ x, by rw [← hx, mul_conj_mul_inv]⟩⟩

theorem commute_compInd_of_mem {J : Finset (Fin n)} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ coordBlock K J) :
    compInd K J * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * compInd K J :=
  by rw [hg.1, hg.2]

theorem pairSlice_le_range :
    pairSlice K a b ≤ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨_, rfl⟩

theorem pairSlice_le_centralizer (hab : a ≠ b) :
    pairSlice K a b ≤ centralizer ({pairInvolution K hab} : Set _) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_singleton_iff, pairInvolution, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (g : Matrix (Fin n) (Fin n) K) * signMat K {a, b} = signMat K {a, b} * g
  rw [signMat_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, commute_compInd_of_mem hg]

theorem orderOf_pairInvolution (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hab : a ≠ b) : orderOf (pairInvolution K hab) = 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨k, hk⟩ := exists_not_mem_pair hn a b
  apply orderOf_eq_prime
  · rw [pow_two, pairInvolution, ← map_mul, signSL_mul_self, map_one]
  · intro h1
    have h3 : proj n K (signSL K {a, b} (even_card_pair hab)) = 1 :=
      hinj (by rw [map_one]; exact h1)
    obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 h3
    have ha := congrFun (congrFun hc a) a
    have hk' := congrFun (congrFun hc k) k
    rw [coe_signSL, signMat, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at ha hk'
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, ↓reduceIte] at ha
    simp only [hk, ↓reduceIte] at hk'
    rw [← hk'] at ha
    exact h2 (by linear_combination -ha)

@[expose] def pairSliceEquivSL (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hab : a ≠ b) : pairSlice K a b ≃* SpecialLinearGroup (Fin 2) K :=
  (pairSliceEquiv hn hinj a b).symm.trans ((coordBlockEquiv {a, b}).symm.trans
    (slReindex K (finCongr (Finset.card_pair hab))))

theorem isQuasisimple_pairSlice [Finite K] (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hab : a ≠ b) (h4 : 4 ≤ Nat.card K) : IsQuasisimple (pairSlice K a b) :=
  LocalCores.isQuasisimple_of_mulEquiv (pairSliceEquiv hn hinj a b)
    (isQuasisimple_coordBlock (by rw [Finset.card_pair hab]) (Or.inr h4))

theorem center_pairSlice (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hab : a ≠ b) :
    (center (pairSlice K a b)).map (pairSlice K a b).subtype =
      zpowers (pairInvolution K hab) := by
  rw [← map_center_eq (pairSliceEquiv hn hinj a b), center_coordBlock_pair hab, Subgroup.map_map,
    MonoidHom.map_zpowers]
  rfl

theorem conjAut_mul_mem_pairSlice {D : GL (Fin n) K}
    (hD : compInd K {a, b} * (D : Matrix (Fin n) (Fin n) K) = D * compInd K {a, b})
    {x : MulAut (projectiveSL n K)} (hx : x ∈ pairSlice K a b) :
    conjAut n K D * x * (conjAut n K D)⁻¹ ∈ pairSlice K a b := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [conjAut_mul_conjProj_mul_inv]
  refine ⟨_, conj_mem_coordBlock (D := (D : Matrix (Fin n) (Fin n) K))
    (Di := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (by rw [← Units.val_mul,
      mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    hD hg (CatalogueBHigherLinearAction.slConjugation_matrix n K D g), rfl⟩

theorem conjAut_mem_normalizer_pairSlice {D : GL (Fin n) K}
    (hD : compInd K {a, b} * (D : Matrix (Fin n) (Fin n) K) = D * compInd K {a, b}) :
    conjAut n K D ∈ normalizer (pairSlice K a b : Set (MulAut (projectiveSL n K))) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h1 : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDi : compInd K {a, b} * Mi = Mi * compInd K {a, b} := by
    calc compInd K {a, b} * Mi = (Mi * M) * compInd K {a, b} * Mi := by rw [h2, Matrix.one_mul]
      _ = Mi * (M * compInd K {a, b}) * Mi := by simp only [Matrix.mul_assoc]
      _ = Mi * (compInd K {a, b} * M) * Mi := by rw [hD]
      _ = Mi * compInd K {a, b} := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conjAut_mul_mem_pairSlice hD hx, fun hx => ?_⟩
  have := conjAut_mul_mem_pairSlice hDi hx
  have e : conjAut n K D⁻¹ * (conjAut n K D * x * (conjAut n K D)⁻¹) * (conjAut n K D⁻¹)⁻¹ = x := by
    rw [map_inv, inv_inv]
    group
  rwa [e] at this

theorem pairBlock_of_commute {p : ℕ} [Fact p.Prime] [CharP K p]
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hab : a ≠ b) {D : GL (Fin n) K}
    (hc : ∀ x ∈ pairSlice K a b, conjAut n K D * x = x * conjAut n K D) :
    (D : Matrix (Fin n) (Fin n) K) a a = (D : Matrix (Fin n) (Fin n) K) b b ∧
      (D : Matrix (Fin n) (Fin n) K) a b = 0 ∧ (D : Matrix (Fin n) (Fin n) K) b a = 0 := by
  have hmem : ∀ {i j : Fin n} (hij : i ≠ j), i ∈ ({a, b} : Finset (Fin n)) →
      j ∈ ({a, b} : Finset (Fin n)) →
      SpecialLinearGroup.transvection hij (1 : K) ∈ coordBlock K {a, b} := by
    intro i j hij hi hj
    rw [mem_coordBlock_iff]
    intro k l hkl
    rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
    have : ¬ (i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      tauto
    simp [this]
  have key : ∀ {i j : Fin n} (hij : i ≠ j), i ∈ ({a, b} : Finset (Fin n)) →
      j ∈ ({a, b} : Finset (Fin n)) →
      (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
        single i j 1 * (D : Matrix (Fin n) (Fin n) K) := by
    intro i j hij hi hj
    set tr := SpecialLinearGroup.transvection hij (1 : K) with htr
    have h1 := hc _ ⟨tr, hmem hij hi hj, rfl⟩
    have h2 : conjAut n K D * conjProj n K tr * (conjAut n K D)⁻¹ = conjProj n K tr := by
      rw [h1, mul_inv_cancel_right]
    rw [conjAut_mul_conjProj_mul_inv] at h2
    have h3 := eq_of_proj_eq_of_pow_char (p := p)
      (by rw [← map_pow, transvection_pow_char, map_one]) (transvection_pow_char hij 1)
      (hinj h2)
    have h4 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      h3
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      SpecialLinearGroup.transvection_coe] at h4
    set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
    set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hMi
    have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have htr' : (tr : Matrix (Fin n) (Fin n) K) = 1 + single i j 1 := rfl
    rw [htr'] at h4
    have h5 : M * (1 + single i j (1 : K)) = (1 + single i j (1 : K)) * M := by
      calc M * (1 + single i j (1 : K)) = M * (1 + single i j 1) * Mi * M := by
            rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
        _ = (1 + single i j (1 : K)) * M := by rw [h4]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h5
    exact add_left_cancel h5
  have ha : a ∈ ({a, b} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a, b} : Finset (Fin n)) := by simp
  obtain ⟨e1, e2, -⟩ := commute_single_apply (key hab ha hb)
  obtain ⟨-, e3, -⟩ := commute_single_apply (key hab.symm hb ha)
  exact ⟨e1.symm, e3 a hab, e2 b hab.symm⟩

theorem pairSlice_isPComponent [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (h4 : 4 ≤ Nat.card K) {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    (hab : a ≠ b) :
    IsPComponent 2 ((pairSlice K a b).subgroupOf
      (B ⊓ centralizer ({pairInvolution K hab} : Set _))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set J : Finset (Fin n) := {a, b} with hJ
  set s₀ := signSL K J (even_card_pair hab) with hs₀
  set u := pairInvolution K hab with hu
  set S := pairSlice K a b with hS
  set H := B ⊓ centralizer ({u} : Set (MulAut (projectiveSL n K))) with hH
  set Inn := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hInn
  set C₁ := (centralizer ({s₀} : Set (SpecialLinearGroup (Fin n) K))).map (conjProj n K) with hC₁
  have hInnN : Inn.Normal := conj_range_normal
  have hSH : S ≤ H := le_inf (pairSlice_le_range.trans hB) (pairSlice_le_centralizer hab)
  have hSC₁ : S ≤ C₁ := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g, mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
    change (g : Matrix (Fin n) (Fin n) K) * signMat K J = signMat K J * g
    rw [signMat_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, commute_compInd_of_mem hg]
  have hnS : ∀ c ∈ C₁, ∀ x ∈ S, c * x * c⁻¹ ∈ S := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨g, hg, rfl⟩
    have hh' : (h : Matrix (Fin n) (Fin n) K) * signMat K J = signMat K J * h :=
      congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K))
        (mem_centralizer_singleton_iff.1 hh)
    have hcomp : compInd K J * (h : Matrix (Fin n) (Fin n) K) = h * compInd K J :=
      (commute_signMat_iff h2 J _).1 hh'.symm
    have hD1 : (h : Matrix (Fin n) (Fin n) K) *
        ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hD2 : ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (h : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨h * g * h⁻¹, conj_mem_coordBlock hD1 hD2 hcomp hg
      (by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]), ?_⟩
    simp only [map_mul, map_inv]
  have hC₁C₂ : C₁ ≤ Inn ⊓ H := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨_, rfl⟩, hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hu, pairInvolution, ← map_mul, ← map_mul, ← hs₀, mem_centralizer_singleton_iff.1 hh]
  have hnC₁ : ∀ c ∈ Inn ⊓ H, ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁ := by
    rintro c ⟨⟨y, rfl⟩, -, hcu⟩ _ ⟨h, hh, rfl⟩
    obtain ⟨h₁, rfl⟩ := proj_surjective n K y
    have hcu' : conjProj n K (h₁ * s₀ * h₁⁻¹) = conjProj n K s₀ := by
      have := mem_centralizer_singleton_iff.1 hcu
      simp only [hu, pairInvolution] at this
      change conjProj n K h₁ * conjProj n K s₀ = conjProj n K s₀ * conjProj n K h₁ at this
      rw [map_mul, map_mul, map_inv, this, mul_inv_cancel_right]
    have hz := proj_eq_proj_iff.1 (hinj hcu').symm
    set z := s₀⁻¹ * (h₁ * s₀ * h₁⁻¹) with hzdef
    have hzc : z ∈ center _ := scalars_le_center n K hz
    have e1 : h₁ * s₀ * h₁⁻¹ = s₀ * z := by rw [hzdef, mul_inv_cancel_left]
    have hhs : h * s₀ = s₀ * h := mem_centralizer_singleton_iff.1 hh
    refine ⟨h₁ * h * h₁⁻¹, mem_centralizer_singleton_iff.2 ?_, by
      simp only [map_mul, map_inv]
      rfl⟩
    set X := h₁ * h * h₁⁻¹ with hX
    have key : X * (h₁ * s₀ * h₁⁻¹) = (h₁ * s₀ * h₁⁻¹) * X := by
      calc X * (h₁ * s₀ * h₁⁻¹) = h₁ * (h * s₀) * h₁⁻¹ := by rw [hX]; group
        _ = h₁ * (s₀ * h) * h₁⁻¹ := by rw [hhs]
        _ = (h₁ * s₀ * h₁⁻¹) * X := by rw [hX]; group
    rw [e1] at key
    have hXz : X * z = z * X := mem_center_iff.1 hzc X
    apply mul_right_cancel (b := z)
    calc X * s₀ * z = X * (s₀ * z) := mul_assoc _ _ _
      _ = s₀ * z * X := key
      _ = s₀ * X * z := by rw [mul_assoc, ← hXz, ← mul_assoc]
  have hC₂ : ((Inn ⊓ H).subgroupOf H).IsSubnormal := isSubnormal_inf_subgroupOf H
  have hC₁s : (C₁.subgroupOf H).IsSubnormal := isSubnormal_subgroupOf_of_normalizes hC₁C₂ hnC₁ hC₂
  have hSs : (S.subgroupOf H).IsSubnormal := isSubnormal_subgroupOf_of_normalizes hSC₁ hnS hC₁s
  have heven : Even (Nat.card S) := by
    rw [even_iff_two_dvd, ← orderOf_pairInvolution hK hn hinj hab]
    exact Subgroup.orderOf_dvd_natCard S (pairInvolution_mem hab)
  exact isPComponent_two_of_quasisimple hSH (isQuasisimple_pairSlice hn hinj hab h4) hSs heven

end PairSlice

end CFSG.ComponentClassification.Burgoyne.PSL