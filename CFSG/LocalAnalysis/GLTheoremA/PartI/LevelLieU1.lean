module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import all CFSG.Fischer.F4
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def mM5 (x : M5) : Matrix (Fin 5) (Fin 5) F4 := ((x : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)

theorem gramSU_idGram_eq : gramSU hF4 (idGram F4 5) = StatedSU 5 (2 ^ 1) F4 := by
  ext g
  rw [mem_gramSU_iff_unitary, mem_primeFormUnitary, mem_M5_iff]
  simp only [idGram, Units.val_one, Matrix.mul_one, hF4_bar, bar_apply, pow_one]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[expose] noncomputable def eGram : M5 ≃* gramSU hF4 (idGram F4 5) :=
  MulEquiv.subgroupCongr gramSU_idGram_eq.symm

@[expose] noncomputable def conjM5 (A : primeFormUnitary hF4 (idGram F4 5)) : M5 ≃* M5 :=
  (eGram.trans (primeFormConjSU hF4 (idGram F4 5) A)).trans eGram.symm

theorem conjM5_apply (A : primeFormUnitary hF4 (idGram F4 5)) (x : M5) :
    ((conjM5 A x : M5) : GL (Fin 5) F4) = (A : GL (Fin 5) F4) * (x : GL (Fin 5) F4) *
      (A : GL (Fin 5) F4)⁻¹ := rfl

theorem center_M5_eq_bot : Subgroup.center M5 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hw : equivM5.symm z ∈ Subgroup.center SU52 := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply equivM5.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (equivM5 g)
  rw [center_SU52_eq_bot, Subgroup.mem_bot] at hw
  calc z = equivM5 (equivM5.symm z) := (MulEquiv.apply_symm_apply _ _).symm
    _ = 1 := by rw [hw, map_one]

theorem eq_one_of_conj_eq_one {z : M5} (h : MulAut.conj z = 1) : z = 1 := by
  have hz : z ∈ Subgroup.center M5 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut M5 => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [center_M5_eq_bot, Subgroup.mem_bot] at hz
  exact hz

theorem fixSubgroup_conj_eq {G : Type} [Group G] (s : G) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer {s} := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have : s * x = x * s := by
      calc s * x = s * x * s⁻¹ * s := by group
        _ = x * s := by rw [h]
    exact this.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_conj_of_pow_three (α : MulAut M5) (hα : α ^ 3 = 1) :
    ∃ s : M5, α = MulAut.conj s := by
  set β : MulAut SU52 := MulAut.congr equivM5.symm α with hβdef
  have hβy : ∀ y : SU52, β y = equivM5.symm (α (equivM5 y)) := fun y => rfl
  have hβ : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, hα, map_one]
  have hF : fieldFactor β = 1 := by
    have h3 : fieldFactor β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    have h2 : fieldFactor β ^ Nat.card (F4 ≃+* F4) = 1 := pow_card_eq_one'
    rw [card_ringEquiv_F4] at h2
    have := (pow_gcd_eq_one (a := fieldFactor β)).2 ⟨h3, h2⟩
    rwa [show Nat.gcd 3 2 = 1 from rfl, pow_one] at this
  obtain ⟨s, hs⟩ := (fieldFactor_eq_one_iff β).1 hF
  refine ⟨equivM5 s, ?_⟩
  apply MulEquiv.ext
  intro x
  have hx := congrArg (fun φ : MulAut SU52 => φ (equivM5.symm x)) hs
  simp only [MulAut.conj_apply] at hx
  rw [hβy, MulEquiv.apply_symm_apply] at hx
  rw [MulAut.conj_apply]
  have := congrArg equivM5 hx
  rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at this
  exact this

theorem F4_omega_primitive : IsPrimitiveRoot F4.ω 3 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem mem_primeFormUnitary_of_M5 (s : M5) :
    (s : GL (Fin 5) F4) ∈ primeFormUnitary hF4 (idGram F4 5) := by
  have h : (s : GL (Fin 5) F4) ∈ gramSU hF4 (idGram F4 5) := by
    rw [gramSU_idGram_eq]
    exact s.2
  exact ((mem_gramSU_iff_unitary hF4).1 h).1

theorem exists_diag (s : M5) (hs : s ^ 3 = 1) :
    ∃ P : primeFormUnitary hF4 (idGram F4 5), ∃ d : Fin 5 → F4,
      ((((P : GL (Fin 5) F4))⁻¹ * (s : GL (Fin 5) F4) * (P : GL (Fin 5) F4) : GL (Fin 5) F4) :
        Matrix (Fin 5) (Fin 5) F4) = Matrix.diagonal d := by
  let sU : primeFormUnitary hF4 (idGram F4 5) :=
    ⟨(s : GL (Fin 5) F4), mem_primeFormUnitary_of_M5 s⟩
  have hsU3 : sU ^ 3 = 1 := by
    apply Subtype.ext
    have h := congrArg (fun t : M5 => (t : GL (Fin 5) F4)) hs
    simpa using h
  have hcomm : ∀ x ∈ Subgroup.zpowers sU, ∀ y ∈ Subgroup.zpowers sU, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl sU).zpow_zpow k l).eq
  have hpow : ∀ x ∈ Subgroup.zpowers sU, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h3 : sU ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hsU3
    rw [← zpow_natCast, Nat.cast_ofNat, ← zpow_mul, mul_comm, zpow_mul, h3, one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m hF4
    F4_omega_primitive (by norm_num) (Subgroup.zpowers sU) hcomm hpow
  refine ⟨P, fun i => ((((P : GL (Fin 5) F4))⁻¹ * (s : GL (Fin 5) F4) * (P : GL (Fin 5) F4) :
    GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) i i, ?_⟩
  have hd := hP sU (Subgroup.mem_zpowers sU)
  have hmat : ((((P : GL (Fin 5) F4))⁻¹ * (s : GL (Fin 5) F4) * (P : GL (Fin 5) F4) :
      GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
      ((((P⁻¹ * sU * P : primeFormUnitary hF4 (idGram F4 5))) : GL (Fin 5) F4) :
        Matrix (Fin 5) (Fin 5) F4) := rfl
  rw [hmat]
  exact hd.diagonal_diag.symm

@[expose] def permMat (σ : Equiv.Perm (Fin 5)) : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.of fun a b => if a = σ b then 1 else 0

theorem permMat_mul_apply (σ : Equiv.Perm (Fin 5)) (M : Matrix (Fin 5) (Fin 5) F4) (a b : Fin 5) :
    (permMat σ * M) a b = M (σ.symm a) b := by
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm a)]
  · simp
  · intro c _ hc
    rw [if_neg]
    intro h
    exact hc (by rw [h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem swap_symm_eq (j : Fin 5) : (Equiv.swap j (4 : Fin 5)).symm = Equiv.swap j 4 :=
  Equiv.symm_swap _ _

theorem permMat_transpose_mul (σ : Equiv.Perm (Fin 5)) :
    (permMat σ).transpose * permMat σ = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permMat, Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ a)]
  · simp [σ.injective.eq_iff]
  · intro c _ hc
    rw [if_neg (fun h => hc h), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permMat_swap_mul_self (j : Fin 5) :
    permMat (Equiv.swap j 4) * permMat (Equiv.swap j 4) = 1 := by
  ext a b
  rw [permMat_mul_apply, swap_symm_eq, Matrix.one_apply]
  simp only [permMat, Matrix.of_apply, Equiv.swap_apply_self]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab, if_neg]
    intro h
    apply hab
    have := congrArg (Equiv.swap j 4) h
    simpa using this

theorem permMat_swap_map (j : Fin 5) :
    (permMat (Equiv.swap j 4)).map hF4.bar = permMat (Equiv.swap j 4) := by
  ext a b
  simp only [permMat, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · exact map_one hF4.bar
  · exact map_zero hF4.bar

theorem permMat_swap_unitary (j : Fin 5) :
    ((permMat (Equiv.swap j 4)).map hF4.bar).transpose * permMat (Equiv.swap j 4) = 1 := by
  rw [permMat_swap_map]
  exact permMat_transpose_mul _

@[expose] def permGL (j : Fin 5) : GL (Fin 5) F4 :=
  ⟨permMat (Equiv.swap j 4), permMat (Equiv.swap j 4), permMat_swap_mul_self j,
    permMat_swap_mul_self j⟩

theorem permGL_mem (j : Fin 5) : permGL j ∈ primeFormUnitary hF4 (idGram F4 5) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one, permGL, Units.val_mk]
  exact permMat_swap_unitary j

theorem permMat_swap_diag (j : Fin 5) (d : Fin 5 → F4) :
    permMat (Equiv.swap j 4) * Matrix.diagonal d * permMat (Equiv.swap j 4) =
      Matrix.diagonal (fun i => d (Equiv.swap j 4 i)) := by
  ext a b
  rw [Matrix.mul_assoc, permMat_mul_apply, Matrix.diagonal_mul, swap_symm_eq]
  by_cases hab : a = b <;> simp [hab, Matrix.diagonal_apply, permMat]

@[expose] def permU (j : Fin 5) : primeFormUnitary hF4 (idGram F4 5) := ⟨permGL j, permGL_mem j⟩

theorem pattern5 : ∀ a b c d e : F4, a * a * a = 1 → b * b * b = 1 → c * c * c = 1 →
    d * d * d = 1 → e * e * e = 1 → a * b * c * d * e = 1 →
    ((∀ i : Fin 5, ![a, b, c, d, e] i = 1) ∨
     (∃ j : Fin 5, ∃ μ : F4, (μ ≠ 1 ∧ μ * μ * μ = 1) ∧
        ∀ i : Fin 5, ![a, b, c, d, e] i = if i = j then μ * μ else μ) ∨
     (∀ x : F4, [a, b, c, d, e].count x ≤ 3)) := by
  decide

theorem F4_cube_cases : ∀ μ : F4, μ ≠ 1 → μ * μ * μ = 1 → μ = F4.ω ∨ μ = F4.ω + 1 := by
  decide

theorem card_filter_eq_count (d : Fin 5 → F4) (x : F4) :
    (Finset.univ.filter fun i => d i = x).card = [d 0, d 1, d 2, d 3, d 4].count x := by
  simp only [Finset.card_filter, Fin.sum_univ_five, List.count_cons, List.count_nil]
  simp only [beq_iff_eq]
  split_ifs <;> simp_all

theorem normal_form (s : M5) (hs : s ^ 3 = 1) :
    s = 1 ∨ (∃ τ : M5 ≃* M5, τ s = yM5 ∨ τ s = yM5⁻¹) ∨
    (∃ τ : M5 ≃* M5, ∃ d : Fin 5 → F4,
      mM5 (τ s) = Matrix.diagonal d ∧
      ∀ x : F4, (Finset.univ.filter fun i => d i = x).card ≤ 3) := by
  obtain ⟨P, d, hPd⟩ := exists_diag s hs
  set τ0 : M5 ≃* M5 := conjM5 P⁻¹ with hτ0
  have hM : mM5 (τ0 s) = Matrix.diagonal d := by
    rw [← hPd, hτ0]
    simp only [mM5, conjM5_apply, Subgroup.coe_inv, inv_inv]
  have h3 : (τ0 s) ^ 3 = 1 := by rw [← map_pow, hs, map_one]
  have hdiag3 : (Matrix.diagonal d) ^ 3 = 1 := by
    have h := congrArg mM5 h3
    simp only [mM5, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one] at h
    rwa [← hM]
  have hd3 : ∀ i, d i * d i * d i = 1 := by
    intro i
    have h := congrFun (congrFun hdiag3 i) i
    rw [Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at h
    simpa [pow_three, mul_assoc] using h
  have hdet : ∏ i, d i = 1 := by
    have h1 : (mM5 (τ0 s)).det = 1 := (mem_M5_iff.1 (τ0 s).2).1
    rwa [hM, Matrix.det_diagonal] at h1
  have hprod : d 0 * d 1 * d 2 * d 3 * d 4 = 1 := by
    rw [← Fin.prod_univ_five]
    exact hdet
  have hvec : ![d 0, d 1, d 2, d 3, d 4] = d := by
    funext i
    fin_cases i <;> rfl
  rcases pattern5 (d 0) (d 1) (d 2) (d 3) (d 4) (hd3 0) (hd3 1) (hd3 2) (hd3 3) (hd3 4) hprod
    with h | ⟨j, μ, ⟨hμ1, hμ3⟩, hpat⟩ | hcnt
  · left
    rw [hvec] at h
    have hd1 : d = fun _ => 1 := funext h
    have hτ1 : τ0 s = 1 := by
      apply Subtype.ext
      apply Units.ext
      show mM5 (τ0 s) = 1
      rw [hM, hd1]
      simp
    exact τ0.injective (hτ1.trans (map_one τ0).symm)
  · right; left
    rw [hvec] at hpat
    have hd : d = fun i => if i = j then μ * μ else μ := funext hpat
    have hconj : ∀ x : M5, mM5 (conjM5 (permU j) x) = permMat (Equiv.swap j 4) * mM5 x *
        permMat (Equiv.swap j 4) := by
      intro x
      simp only [mM5, conjM5_apply]
      rfl
    refine ⟨τ0.trans (conjM5 (permU j)), ?_⟩
    have hτs : mM5 ((τ0.trans (conjM5 (permU j))) s) =
        permMat (Equiv.swap j 4) * Matrix.diagonal d * permMat (Equiv.swap j 4) := by
      rw [MulEquiv.trans_apply, hconj, hM]
    have hdiag : (fun i => d (Equiv.swap j 4 i)) = fun i => if i = 4 then μ * μ else μ := by
      funext i
      rw [hd]
      by_cases hi : i = 4
      · subst hi
        simp
      · have hne : Equiv.swap j 4 i ≠ j := by
          intro h
          apply hi
          have := congrArg (Equiv.swap j 4) h
          simpa using this
        simp [hi, hne]
    have hτs' : mM5 ((τ0.trans (conjM5 (permU j))) s) =
        Matrix.diagonal (fun i => if i = 4 then μ * μ else μ) := by
      rw [hτs, permMat_swap_diag, hdiag]
    rcases F4_cube_cases μ hμ1 hμ3 with rfl | rfl
    · left
      apply Subtype.ext
      apply Units.ext
      show mM5 _ = Dm
      rw [hτs']
      congr 1
      funext i
      fin_cases i <;> decide
    · right
      apply Subtype.ext
      apply Units.ext
      show mM5 _ = Dm'
      rw [hτs']
      congr 1
      funext i
      fin_cases i <;> decide
  · right; right
    refine ⟨τ0, d, hM, fun x => ?_⟩
    rw [card_filter_eq_count]
    exact hcnt x

theorem kLevel_le_two_of_chev {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  rw [if_pos h]
  norm_num

theorem catalog_ambiguous_of_u4two {S : Type} [Group S]
    (h : catalogIs S CFSG.LocalAnalysis.GLTheoremA.S9.isU4two) : catalogIs S (ambiguousChev 3) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two h
  exact ⟨.lie ⟨.twistedA 3 q, hv⟩, ⟨hq, rfl⟩, ⟨e⟩⟩

theorem pSimple_map_equiv {G G' : Type} [Group G] [Group G'] (p : ℕ) (e : G ≃* G')
    (K : Subgroup G) : Nonempty (PSimple p (K.map e.toMonoidHom) ≃* PSimple p K) := by
  let eK : ↥K ≃* ↥(K.map e.toMonoidHom) := K.equivMapOfInjective e.toMonoidHom e.injective
  have hO : (GLAPPrimeCore p ↥K).map eK.toMonoidHom = GLAPPrimeCore p ↥(K.map e.toMonoidHom) :=
    glaPPrimeCore_map_iso p eK
  let pq : PQuot p (K.map e.toMonoidHom) ≃* PQuot p K :=
    (QuotientGroup.congr (GLAPPrimeCore p ↥K) (GLAPPrimeCore p ↥(K.map e.toMonoidHom)) eK hO).symm
  exact ⟨QuotientGroup.congr _ _ pq (Subgroup.map_center_eq pq)⟩

theorem map_centralizer_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (s : G) :
    (Subgroup.centralizer {s}).map e.toMonoidHom = Subgroup.centralizer {e s} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e s = e s * e y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    change e (e.symm x * s) = e (s * e.symm x)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx

theorem glaPComponent_map_centralizer (τ : M5 ≃* M5) (s : M5) (I : Subgroup M5)
    (hI : GLAPComponent 3 (Subgroup.centralizer {s}) I) :
    GLAPComponent 3 (Subgroup.centralizer {τ s}) (I.map τ.toMonoidHom) := by
  have h := glaPComponent_map_mulEquiv Nat.prime_three τ hI
  rwa [map_centralizer_equiv] at h

theorem centralizer_inv_eq {G : Type} [Group G] (s : G) :
    Subgroup.centralizer {s⁻¹} = Subgroup.centralizer {s} := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff (a := x) (b := s)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU
