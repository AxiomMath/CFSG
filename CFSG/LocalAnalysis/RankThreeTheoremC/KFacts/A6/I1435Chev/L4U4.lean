module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Setup
public import CFSG.RankThree.CentralLift.LinearRootRelations
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4SplitThree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Four

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (diagGL coe_diagGL det_diagGL)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat pairMat_one pairMat_mul
  pairMat_transpose pairMat_apply_pair pairMat_apply_of_ne isSupp_pairMat pairGL coe_pairGL)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435 (isPSolvable_of_equiv)

section PairMat

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] {a b : ι}

theorem pairMat_mul_diagonal (g : Matrix (Fin 2) (Fin 2) R) {d : ι → R} (hd : d a = d b) :
    pairMat a b g * diagonal d = diagonal d * pairMat a b g := by
  ext x y
  rw [mul_diagonal, diagonal_mul]
  by_cases hxy : (x = a ∨ x = b) ∧ (y = a ∨ y = b)
  · have hdxy : d x = d y := by
      obtain ⟨hx, hy⟩ := hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hd]
    rw [hdxy, mul_comm]
  · have h1 : x ∉ ({a, b} : Set ι) ∨ y ∉ ({a, b} : Set ι) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [isSupp_pairMat g x y h1]
    by_cases hxy' : x = y
    · subst hxy'
      rw [one_apply_eq, one_mul, mul_one]
    · rw [one_apply_ne hxy', zero_mul, mul_zero]

theorem pairMat_injective (hab : a ≠ b) : Function.Injective (pairMat (R := R) a b) := by
  intro g g' h
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab g
  obtain ⟨g1', g2', g3', g4'⟩ := pairMat_apply_pair hab g'
  have e : ∀ x y, pairMat a b g x y = pairMat a b g' x y := fun x y => by rw [h]
  ext x y
  fin_cases x <;> fin_cases y
  · exact g1.symm.trans ((e a a).trans g1')
  · exact g2.symm.trans ((e a b).trans g2')
  · exact g3.symm.trans ((e b a).trans g3')
  · exact g4.symm.trans ((e b b).trans g4')

theorem pairMat_eq_one_of_eq_scalar {x : ι} (hxa : x ≠ a) (hxb : x ≠ b)
    {g : Matrix (Fin 2) (Fin 2) R} {c : R} (h : scalar ι c = pairMat a b g) :
    pairMat a b g = 1 := by
  have hc : c = 1 := by
    have := congrFun (congrFun h x) x
    rw [pairMat_apply_of_ne hxa hxb, one_apply_eq, scalar_apply, diagonal_apply_eq] at this
    exact this
  rw [← h, hc, map_one]

theorem pairMat_map (g : Matrix (Fin 2) (Fin 2) R) {φ : R → R} (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (pairMat a b g).map φ = pairMat a b (g.map φ) := by
  ext x y
  simp only [Matrix.map_apply, pairMat, of_apply, one_apply]
  split_ifs <;> simp_all

end PairMat

section Torus

variable {L : Type} [Field L] {ω : Lˣ}

@[expose] def wPow (ω : Lˣ) (c : ZMod 3) : Lˣ := ω ^ c.val

theorem wPow_add (hω : orderOf ω = 3) (x y : ZMod 3) :
    wPow ω (x + y) = wPow ω x * wPow ω y := by
  rw [wPow, wPow, wPow, ← pow_add, ZMod.val_add]
  have h := pow_mod_orderOf ω (x.val + y.val)
  rwa [hω] at h

theorem wPow_injective (hω : orderOf ω = 3) : Function.Injective (wPow ω) := by
  intro x y h
  have := pow_injOn_Iio_orderOf (x := ω) (by rw [hω]; exact ZMod.val_lt x)
    (by rw [hω]; exact ZMod.val_lt y) h
  exact ZMod.val_injective 3 this

theorem wPow_zero : wPow ω 0 = 1 := by
  rw [wPow, ZMod.val_zero, pow_zero]

theorem wPow_pow_three (hω : orderOf ω = 3) (c : ZMod 3) : wPow ω c ^ 3 = 1 := by
  have h : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  rw [wPow, ← pow_mul, mul_comm, pow_mul, h, one_pow]

@[expose] def ext4 (a : Fin 3 → ZMod 3) : Fin 4 → ZMod 3 := ![a 0, a 1, a 2, -(a 0 + a 1 + a 2)]

theorem ext4_add (a b : Fin 3 → ZMod 3) (i : Fin 4) : ext4 (a + b) i = ext4 a i + ext4 b i := by
  fin_cases i <;> simp [ext4] <;> ring

theorem ext4_pigeon (a : Fin 3 → ZMod 3) : ∃ i j : Fin 4, i ≠ j ∧ ext4 a i = ext4 a j :=
  Fintype.exists_ne_map_eq_of_card_lt (ext4 a) (by simp)

theorem eq_zero_of_ext4 : ∀ a : Fin 3 → ZMod 3, ext4 a 1 = ext4 a 0 → ext4 a 2 = ext4 a 0 →
    ext4 a 3 = ext4 a 0 → a = 0 := by
  decide

@[expose] noncomputable def tor (ω : Lˣ) (a : Fin 3 → ZMod 3) : GL (Fin 4) L :=
  diagGL 4 fun i => wPow ω (ext4 a i)

theorem tor_add (hω : orderOf ω = 3) (a b : Fin 3 → ZMod 3) :
    tor ω (a + b) = tor ω a * tor ω b := by
  rw [tor, tor, tor, ← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, ext4_add, wPow_add hω]

theorem prod_tor (hω : orderOf ω = 3) (a : Fin 3 → ZMod 3) :
    ∏ i, wPow ω (ext4 a i) = 1 := by
  rw [Fin.prod_univ_four]
  show wPow ω (a 0) * wPow ω (a 1) * wPow ω (a 2) * wPow ω (-(a 0 + a 1 + a 2)) = 1
  rw [← wPow_add hω, ← wPow_add hω, ← wPow_add hω, add_neg_cancel, wPow_zero]

theorem det_tor (hω : orderOf ω = 3) (a : Fin 3 → ZMod 3) :
    ((tor ω a : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L).det = 1 := by
  rw [tor, det_diagGL, ← Units.coe_prod, prod_tor hω, Units.val_one]

@[expose] noncomputable def torHom (hω : orderOf ω = 3) :
    Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 4) L :=
  MonoidHom.mk' (fun a => tor ω a.toAdd) fun a b => tor_add hω a.toAdd b.toAdd

theorem eq_zero_of_tor_mem_scalars (hω : orderOf ω = 3) {a : Fin 3 → ZMod 3}
    (h : tor ω a ∈ StatedScalars (Fin 4) L) : a = 0 := by
  obtain ⟨s, hs⟩ := h
  have hent : ∀ i : Fin 4, wPow ω (ext4 a i) = s := by
    intro i
    apply Units.ext
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) i i) hs
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, tor, coe_diagGL] using
      this.symm
  have e : ∀ i : Fin 4, ext4 a i = ext4 a 0 := fun i =>
    wPow_injective hω ((hent i).trans (hent 0).symm)
  exact eq_zero_of_ext4 a (e 1) (e 2) (e 3)

end Torus

section Witness

variable {L : Type} [Field L] [Finite L] {ω : Lˣ}

theorem witness_of_blocks (hω : orderOf ω = 3) (H : Subgroup (GL (Fin 4) L))
    (hdiag : ∀ a, tor ω a ∈ H)
    (hblock : ∀ i j : Fin 4, i ≠ j → ∃ C : Subgroup H, ¬ CFSG.HallHigman.IsPSolvable 3 C ∧
      (∀ c ∈ C, ∀ d : Fin 4 → Lˣ, d i = d j →
        (c : GL (Fin 4) L) * diagGL 4 d = diagGL 4 d * c) ∧
      (∀ c ∈ C, (c : GL (Fin 4) L) ∈ StatedScalars (Fin 4) L → c = 1)) :
    Witness (StatedProj H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : H →* StatedProj H := QuotientGroup.mk' _
  let θ : Multiplicative (Fin 3 → ZMod 3) →* StatedProj H :=
    π.comp ((torHom hω).codRestrict H fun a => hdiag a.toAdd)
  have hθ : ∀ a, θ a = π ⟨tor ω a.toAdd, hdiag _⟩ := fun a => rfl
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hθ] at ha
    have h1 : tor ω a.toAdd ∈ StatedScalars (Fin 4) L :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ha)
    have h2 := eq_zero_of_tor_mem_scalars hω h1
    exact Multiplicative.toAdd.injective h2
  refine ⟨θ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_eq_fintype_card]
    rfl
  · rintro _ ⟨a, rfl⟩ -
    left
    obtain ⟨i, j, hij, hext⟩ := ext4_pigeon a.toAdd
    obtain ⟨C, hC, hcomm, hscal⟩ := hblock i j hij
    have hπC : Function.Injective (π.comp C.subtype) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have h1 : ((c : H) : GL (Fin 4) L) ∈ StatedScalars (Fin 4) L :=
        Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hc)
      exact Subtype.ext (hscal c c.2 h1)
    have hle : (π.comp C.subtype).range ≤ centralizer ({θ a} : Set (StatedProj H)) := by
      rintro _ ⟨c, rfl⟩
      rw [mem_centralizer_singleton_iff, hθ]
      show π ((c : H) * ⟨tor ω a.toAdd, hdiag _⟩) = π (⟨tor ω a.toAdd, hdiag _⟩ * (c : H))
      congr 1
      apply Subtype.ext
      exact hcomm c c.2 _ (by rw [hext])
    intro hs
    have h1 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      hs hle
    exact hC (isPSolvable_of_equiv (MonoidHom.ofInjective hπC).symm h1)

end Witness

section Linear

variable {F : Type} [Field F]

@[expose] noncomputable def slBlock {i j : Fin 4} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 2) F →* StatedSL 4 F :=
  (pairGL hij).codRestrict (StatedSL 4 F) fun g => by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, coe_pairGL]
    exact CFSG.RankThree.CentralLift.LinearRoots.det_pairMat hij g

theorem coe_slBlock {i j : Fin 4} (hij : i ≠ j) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((slBlock hij g : StatedSL 4 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      pairMat i j (g : Matrix (Fin 2) (Fin 2) F) := rfl

theorem slBlock_injective {i j : Fin 4} (hij : i ≠ j) :
    Function.Injective (slBlock (F := F) hij) := by
  intro g g' h
  have h1 := congrArg (fun x : StatedSL 4 F => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  simp only [coe_slBlock] at h1
  exact Subtype.ext (pairMat_injective hij h1)

theorem exists_third (i j : Fin 4) : ∃ x : Fin 4, x ≠ i ∧ x ≠ j := by
  revert i j
  decide

variable [Finite F] [CharP F 2]

theorem witness_projSL4 (h3 : 3 ∣ Nat.card F - 1) : Witness (StatedProj (StatedSL 4 F)) := by
  obtain ⟨ω, hω⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one h3
  have h4 : 4 ≤ Nat.card F := by
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := h3
    rcases k with _ | k
    · omega
    · omega
  refine witness_of_blocks hω _ (fun a => ?_) fun i j hij => ?_
  · rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    exact det_tor hω a
  refine ⟨(slBlock hij).range, ?_, ?_, ?_⟩
  · intro hs
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_three_sl2 h4
      (isPSolvable_of_equiv (MonoidHom.ofInjective (slBlock_injective hij)).symm hs)
  · rintro _ ⟨g, rfl⟩ d hd
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_slBlock, coe_diagGL]
    exact pairMat_mul_diagonal _ (congrArg Units.val hd)
  · rintro _ ⟨g, rfl⟩ ⟨s, hs⟩
    obtain ⟨x, hxi, hxj⟩ := exists_third i j
    have h1 : scalar (Fin 4) (s : F) = pairMat i j (g : Matrix (Fin 2) (Fin 2) F) := by
      rw [← coe_slBlock hij g, ← hs, Matrix.GeneralLinearGroup.coe_scalar]
    have h2 := pairMat_eq_one_of_eq_scalar hxi hxj h1
    have h3 : g = 1 := Subtype.ext (pairMat_injective hij (h2.trans (pairMat_one hij).symm))
    rw [h3, map_one]

end Linear

section Unitary

variable {L : Type} [Field L] [Finite L] {ℓ f : ℕ}

open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (PSUThree.mem_statedSU_iff
  PSUThree.diagGL_mem)

@[expose] noncomputable def suToSL (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) :
    StatedSU 2 (ℓ ^ f) L →* Matrix.SpecialLinearGroup (Fin 2) L where
  toFun g := ⟨((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L),
    ((PSUThree.mem_statedSU_iff hℓ hL (by norm_num) _).1 g.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def suBlock (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) {i j : Fin 4}
    (hij : i ≠ j) : StatedSU 2 (ℓ ^ f) L →* StatedSU 4 (ℓ ^ f) L :=
  ((pairGL hij).comp (suToSL hℓ hL)).codRestrict (StatedSU 4 (ℓ ^ f) L) fun g => by
    have hg := (PSUThree.mem_statedSU_iff hℓ hL (by norm_num) _).1 g.2
    have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
    rw [PSUThree.mem_statedSU_iff hℓ hL (by norm_num), MonoidHom.comp_apply, coe_pairGL]
    refine ⟨CFSG.RankThree.CentralLift.LinearRoots.det_pairMat hij _, ?_⟩
    show ((pairMat i j ((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)).map (· ^ ℓ ^ f))ᵀ *
      pairMat i j ((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1
    rw [pairMat_map (R := L) (φ := fun x : L => x ^ ℓ ^ f) _ (zero_pow hq0) (one_pow _),
      pairMat_transpose hij, ← pairMat_mul hij, hg.2, pairMat_one hij]

theorem coe_suBlock (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) {i j : Fin 4} (hij : i ≠ j)
    (g : StatedSU 2 (ℓ ^ f) L) :
    (((suBlock hℓ hL hij g : StatedSU 4 (ℓ ^ f) L) : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) =
      pairMat i j ((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := rfl

theorem suBlock_injective (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) {i j : Fin 4}
    (hij : i ≠ j) : Function.Injective (suBlock hℓ hL hij) := by
  intro g g' h
  have h1 := congrArg
    (fun x : StatedSU 4 (ℓ ^ f) L => ((x : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)) h
  simp only [coe_suBlock] at h1
  exact Subtype.ext (Units.ext (pairMat_injective hij h1))

theorem witness_projSU4 {f : ℕ} (hf : 2 ≤ f) (hL : Nat.card L = (2 ^ f) ^ 2)
    (h3 : 3 ∣ 2 ^ f + 1) : Witness (StatedProj (StatedSU 4 (2 ^ f) L)) := by
  have hq0 : 2 ^ f ≠ 0 := pow_ne_zero _ two_ne_zero
  obtain ⟨ω, hω⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one
      (F := L) (d := 3) (by
        rw [hL, show (2 ^ f) ^ 2 - 1 = (2 ^ f) ^ 2 - 1 ^ 2 by norm_num, Nat.pow_two_sub_pow_two]
        exact Dvd.dvd.mul_right h3 _)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f L :=
    ⟨Nat.prime_two, by omega, by rw [hL]; ring⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_exists_su2_equiv hU
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ f) hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSU : ¬ CFSG.HallHigman.IsPSolvable 3 (StatedSU 2 (2 ^ f) L) := fun hs =>
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_three_sl2 hF4
      (isPSolvable_of_equiv e.symm hs)
  refine witness_of_blocks hω _ (fun a => ?_) fun i j hij => ?_
  · refine PSUThree.diagGL_mem hq0 _ (fun i => ?_) (prod_tor hω a)
    obtain ⟨k, hk⟩ := h3
    rw [hk, pow_mul, wPow_pow_three hω, one_pow]
  refine ⟨(suBlock Nat.prime_two hL hij).range, ?_, ?_, ?_⟩
  · intro hs
    exact hSU (isPSolvable_of_equiv
      (MonoidHom.ofInjective (suBlock_injective Nat.prime_two hL hij)).symm hs)
  · rintro _ ⟨g, rfl⟩ d hd
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_suBlock, coe_diagGL]
    exact pairMat_mul_diagonal _ (congrArg Units.val hd)
  · rintro _ ⟨g, rfl⟩ ⟨s, hs⟩
    obtain ⟨x, hxi, hxj⟩ := exists_third i j
    have h1 : scalar (Fin 4) (s : L) =
        pairMat i j ((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      rw [← coe_suBlock Nat.prime_two hL hij g, ← hs, Matrix.GeneralLinearGroup.coe_scalar]
    have h2 := pairMat_eq_one_of_eq_scalar hxi hxj h1
    have h3 : g = 1 := Subtype.ext (Units.ext (pairMat_injective hij
      (h2.trans (pairMat_one hij).symm)))
    rw [h3, map_one]

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Four
