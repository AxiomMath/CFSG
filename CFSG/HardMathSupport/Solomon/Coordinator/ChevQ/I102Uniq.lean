module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.CartanConj
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace I102UniqAux

section Generic

open CFSG.Open

@[expose] def ThreeUniq4 (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, IsPGroup 3 P → ∀ E F : Subgroup G, E ≤ P → F ≤ P →
    IsElemAbelian 3 E → IsElemAbelian 3 F → Nat.card E = 3 ^ 4 → Nat.card F = 3 ^ 4 → E = F

theorem isElemAbelian_map' {X Y : Type*} [Group X] [Group Y] {p : ℕ} {E : Subgroup X} (f : X →* Y)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨?_, ?_⟩
  · haveI := hE.1
    infer_instance
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_comap' {X Y : Type*} [Group X] [Group Y] {p : ℕ} {E : Subgroup Y} (f : X →* Y)
    (hf : Function.Injective f) (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa using h
  · apply hf
    rw [map_pow, hE.2 _ hx, map_one]

theorem threeUniq4_of_injective {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (hφ : Function.Injective φ) (hY : ThreeUniq4 Y) : ThreeUniq4 X := by
  intro P hP E F hEP hFP hE hF hEc hFc
  have hP' : IsPGroup 3 (P.map φ) := hP.map φ
  have hEc' : Nat.card (E.map φ) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hφ, hEc]
  have hFc' : Nat.card (F.map φ) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hφ, hFc]
  exact Subgroup.map_injective hφ
    (hY _ hP' _ _ (Subgroup.map_mono hEP) (Subgroup.map_mono hFP) (isElemAbelian_map' φ hE)
      (isElemAbelian_map' φ hF) hEc' hFc')

theorem threeUniq4_of_range {X G : Type*} [Group X] [Group G] [Finite X] [Finite G] (φ : X →* G)
    (hφ : Function.Injective φ)
    (hord : (Nat.card G).factorization 3 = (Nat.card X).factorization 3)
    (hX : ThreeUniq4 X) : ThreeUniq4 G := by
  intro P hP E F hEP hFP hE hF hEc hFc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_conj_le_range_of_factorization φ hφ hord P hP
  set c : G →* G := (MulAut.conj g).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hPr : P.map c ≤ φ.range := hg
  have hEr : E.map c ≤ φ.range := (Subgroup.map_mono hEP).trans hPr
  have hFr : F.map c ≤ φ.range := (Subgroup.map_mono hFP).trans hPr
  have hE1 : ((E.map c).comap φ).map φ = E.map c := Subgroup.map_comap_eq_self hEr
  have hF1 : ((F.map c).comap φ).map φ = F.map c := Subgroup.map_comap_eq_self hFr
  have hP1 : ((P.map c).comap φ).map φ = P.map c := Subgroup.map_comap_eq_self hPr
  have hPp : IsPGroup 3 ((P.map c).comap φ) :=
    (hP.map c).comap_of_injective φ hφ
  have hEc1 : Nat.card ((E.map c).comap φ) = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective hφ, hE1, Subgroup.card_map_of_injective hcinj, hEc]
  have hFc1 : Nat.card ((F.map c).comap φ) = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective hφ, hF1, Subgroup.card_map_of_injective hcinj, hFc]
  have hmain := hX _ hPp ((E.map c).comap φ) ((F.map c).comap φ)
    (Subgroup.comap_mono (Subgroup.map_mono hEP)) (Subgroup.comap_mono (Subgroup.map_mono hFP))
    (isElemAbelian_comap' φ hφ (isElemAbelian_map' c hE))
    (isElemAbelian_comap' φ hφ (isElemAbelian_map' c hF)) hEc1 hFc1
  have h2 : E.map c = F.map c := by
    rw [← hE1, ← hF1, hmain]
  exact Subgroup.map_injective hcinj h2

theorem conj_injective_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Function.Injective (MulAut.conj : H →* MulAut H)) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' h
  apply e.injective
  apply hH
  ext x
  have := congrArg (fun φ : MulAut G => e (φ (e.symm x))) h
  simpa [MulAut.conj_apply] using this

theorem sylowForm_of_threeUniq4 {S : Type} [Group S]
    (hS : Function.Injective (MulAut.conj : S →* MulAut S)) (hU : ThreeUniq4 S)
    (P : Sylow 3 (MulAut S)) (E F : Subgroup (MulAut S))
    (hEP : E ≤ (P : Subgroup (MulAut S))) (hFP : F ≤ (P : Subgroup (MulAut S)))
    (hE : IsElemAbelian 3 E) (hF : IsElemAbelian 3 F) (hEc : Nat.card E = 3 ^ 4)
    (hFc : Nat.card F = 3 ^ 4) (hEi : E ≤ (MulAut.conj : S →* MulAut S).range)
    (hFi : F ≤ (MulAut.conj : S →* MulAut S).range) : E = F := by
  set ι : S →* MulAut S := MulAut.conj with hι
  have hEm : (E.comap ι).map ι = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hEi
  have hFm : (F.comap ι).map ι = F := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hFi
  have hP : IsPGroup 3 ((P : Subgroup (MulAut S)).comap ι) :=
    P.isPGroup'.comap_of_injective ι hS
  have hEc' : Nat.card (E.comap ι) = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective hS, hEm, hEc]
  have hFc' : Nat.card (F.comap ι) = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective hS, hFm, hFc]
  have h := hU _ hP (E.comap ι) (F.comap ι) (Subgroup.comap_mono hEP) (Subgroup.comap_mono hFP)
    (isElemAbelian_comap' ι hS hE) (isElemAbelian_comap' ι hS hF) hEc' hFc'
  rw [← hEm, ← hFm, h]

theorem factorization_eq_of_not_dvd_index {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ¬ 3 ∣ H.index) : (Nat.card G).factorization 3 = (Nat.card H).factorization 3 := by
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hIne : H.index ≠ 0 := by
    intro h0
    have h1 := Subgroup.card_mul_index H
    rw [h0, mul_zero] at h1
    exact hGpos.ne' h1.symm
  have hHne : Nat.card H ≠ 0 := (Nat.card_pos).ne'
  rw [← Subgroup.card_mul_index H, Nat.factorization_mul hHne hIne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h, add_zero]

theorem exists_fixed_subfield' (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq2 : 2 ≤ q) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k K), Nat.card k = q ∧
      ringChar k = ringChar K ∧ ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hKcard⟩ := FiniteField.card K (ringChar K)
  have hpr' : Fact (ringChar K).Prime := ⟨hpr⟩
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hKcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨i, -, hqi⟩ := (Nat.dvd_prime_pow hpr).1 hdvd
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hqi
    omega
  have hkcard : Nat.card (GaloisField (ringChar K) i) = q := by
    rw [GaloisField.card (ringChar K) i hi, hqi]
  obtain ⟨ιk⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq (ℓ := ringChar K)
    (f := i) (hkcard.trans hqi) (by rw [hqi] at hK; exact hK)
  letI : Algebra (GaloisField (ringChar K) i) K := ιk.toAlgebra
  refine ⟨GaloisField (ringChar K) i, inferInstance, inferInstance, inferInstance, hkcard, ?_, ?_⟩
  · exact ringChar.eq _ _
  · intro c
    rw [hσ]
    have hc : c ^ q = c := by
      rw [← hkcard]
      haveI : Fintype (GaloisField (ringChar K) i) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [← map_pow, hc]

theorem factorization_three_ordF4_four : (ordF4 4).factorization 3 = 6 := by
  have h : ordF4 4 = 3 ^ 6 * 26076578222004040399585280000 := by
    norm_num [ordF4]
  rw [h, Nat.factorization_def _ Nat.prime_three,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_three_ordF4_sixtyfour : (ordF4 64).factorization 3 = 10 := by
  have h : ordF4 64 = 3 ^ 10 *
      141266783907742785224820346152931087709054993256412400364433441914566554659108820090880000 := by
    norm_num [ordF4]
  rw [h, Nat.factorization_def _ Nat.prime_three,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_three_729 : (((4 : ℕ) - 1) ^ 4 * 9).factorization 3 = 6 := by
  have h : ((4 : ℕ) - 1) ^ 4 * 9 = 3 ^ 6 := by norm_num
  rw [h, Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem factorization_three_63 : (((64 : ℕ) - 1) ^ 4 * 9).factorization 3 = 10 := by
  have h : ((64 : ℕ) - 1) ^ 4 * 9 = 3 ^ 10 * 2401 := by norm_num
  rw [h, Nat.factorization_def _ Nat.prime_three,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end Generic

section Weyl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice

set_option linter.unusedSectionVars false

theorem wordProd_smul_wordMat (τ : Tag) (l : List (Fin τ.rank)) (u : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • u = (wordMat τ l).mulVec u := by
  rw [wordProd_smul]
  induction l with
  | nil => rw [List.foldr_nil, wordMat_nil, Matrix.one_mulVec]
  | cons i l ih =>
    rw [List.foldr_cons, ih, wordMat_cons, ← Matrix.mulVec_mulVec, reflMat_mulVec]

theorem weylMatrix_wordProd (τ : Tag) (l : List (Fin τ.rank)) :
    weylMatrix ((coxeterSystem τ).wordProd l) = wordMat τ l := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul_wordMat, Matrix.mulVec_single_one]
  rfl

theorem wordMat_eq_toMat' (τ : Tag) (l : List (Fin τ.rank)) {L : List (List ℤ)}
    (h : lword τ.rank (cartanList τ) (l.map Fin.val) = L) : wordMat τ l = toMat τ.rank L := by
  rw [← h, toMat_lword τ (toMat_cartanList τ)]

@[expose] def wordX : List (Fin Tag.F4.rank) := [0, 1]

@[expose] def wordY : List (Fin Tag.F4.rank) := [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

@[expose] def matX : List (List ℤ) := [[0, -1, 1, 0], [1, -1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def matY : List (List ℤ) := [[1, 0, 0, -1], [0, 1, 0, -2], [0, 0, 1, -3], [0, 0, 1, -2]]

@[expose] def gX : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd wordX

@[expose] def gY : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd wordY

theorem weylMatrix_gX : weylMatrix gX = toMat Tag.F4.rank matX := by
  rw [gX, weylMatrix_wordProd]
  exact wordMat_eq_toMat' Tag.F4 _ (by decide +kernel)

theorem weylMatrix_gY : weylMatrix gY = toMat Tag.F4.rank matY := by
  rw [gY, weylMatrix_wordProd]
  exact wordMat_eq_toMat' Tag.F4 _ (by decide +kernel)

@[expose] def sylList (w : List Bool) : List (List ℤ) :=
  w.foldr (fun b acc => lmul Tag.F4.rank (if b then matY else matX) acc) (lid Tag.F4.rank)

@[expose] def sylWords : List (List Bool) :=
  [[], [false], [false, false], [true], [false, true], [false, false, true], [true, true],
    [false, true, true], [false, false, true, true]]

@[expose] def sylS : List (Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) :=
  sylWords.map fun w => toMat Tag.F4.rank (sylList w)

@[expose] def mX : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ := toMat Tag.F4.rank matX

@[expose] def mY : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ := toMat Tag.F4.rank matY

theorem sylS_one : (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∈ sylS := by
  decide +kernel

theorem mX_cube : mX * mX * mX = 1 := by
  unfold mX; decide +kernel

theorem mY_cube : mY * mY * mY = 1 := by
  unfold mY; decide +kernel

theorem sylS_mulX : ∀ M ∈ sylS, mX * M ∈ sylS := by
  unfold mX; decide +kernel

theorem sylS_mulY : ∀ M ∈ sylS, mY * M ∈ sylS := by
  unfold mY; decide +kernel

theorem sylS_card : sylS.toFinset.card = 9 := by
  decide +kernel

theorem gX_cube : gX ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_gX, weylMatrix_one, pow_succ, pow_succ, pow_one]
  exact mX_cube

theorem gY_cube : gY ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_gY, weylMatrix_one, pow_succ, pow_succ, pow_one]
  exact mY_cube

@[expose] def Pw : Subgroup (WeylGroup Tag.F4) :=
  Subgroup.closure ({gX, gY} : Set (WeylGroup Tag.F4))

theorem weylMatrix_mem_sylS {x : WeylGroup Tag.F4} (hx : x ∈ Pw) : weylMatrix x ∈ sylS := by
  induction hx using Subgroup.closure_induction_left with
  | one => rw [weylMatrix_one]; exact sylS_one
  | mul_left a ha y _ ih =>
    rcases ha with rfl | rfl
    · rw [weylMatrix_mul, weylMatrix_gX]; exact sylS_mulX _ ih
    · rw [weylMatrix_mul, weylMatrix_gY]; exact sylS_mulY _ ih
  | inv_mul_cancel a ha y _ ih =>
    have e : ∀ b : WeylGroup Tag.F4, b ^ 3 = 1 → b⁻¹ = b * b := fun b hb =>
      inv_eq_of_mul_eq_one_right (by
        rw [show b * (b * b) = b ^ 3 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]; exact hb)
    rcases ha with rfl | rfl
    · rw [e _ gX_cube, mul_assoc, weylMatrix_mul, weylMatrix_mul, weylMatrix_gX]
      exact sylS_mulX _ (sylS_mulX _ ih)
    · rw [e _ gY_cube, mul_assoc, weylMatrix_mul, weylMatrix_mul, weylMatrix_gY]
      exact sylS_mulY _ (sylS_mulY _ ih)

@[expose] def sylProd (w : List Bool) : WeylGroup Tag.F4 :=
  (w.map fun b => if b then gY else gX).prod

theorem sylProd_mem (w : List Bool) : sylProd w ∈ Pw := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
  cases b
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem weylMatrix_sylProd (w : List Bool) :
    weylMatrix (sylProd w) = toMat Tag.F4.rank (sylList w) := by
  induction w with
  | nil =>
    rw [sylProd, List.map_nil, List.prod_nil, weylMatrix_one, sylList, List.foldr_nil, toMat_lid]
  | cons b w ih =>
    have hl : sylList (b :: w) = lmul Tag.F4.rank (if b then matY else matX) (sylList w) := rfl
    have hp : sylProd (b :: w) = (if b then gY else gX) * sylProd w := by
      rw [sylProd, List.map_cons, List.prod_cons]; rfl
    rw [hp, weylMatrix_mul, ih, hl, toMat_lmul]
    cases b
    · simp [weylMatrix_gX, matX, mX]
    · simp [weylMatrix_gY, matY, mY]

theorem weylMatrix_image_Pw :
    weylMatrix '' (Pw : Set (WeylGroup Tag.F4)) = (sylS.toFinset : Set _) := by
  ext M
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using weylMatrix_mem_sylS hx
  · intro hM
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hM)
    exact ⟨sylProd w, sylProd_mem w, weylMatrix_sylProd w⟩

theorem card_Pw : Nat.card Pw = 9 := by
  have h1 : Nat.card Pw = Nat.card (weylMatrix '' (Pw : Set (WeylGroup Tag.F4))) :=
    (Nat.card_image_of_injective weylMatrix_injective _).symm
  rw [h1, weylMatrix_image_Pw, Nat.card_coe_set_eq, Set.ncard_coe_finset, sylS_card]

@[expose] def fixes (M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (β : Fin Tag.F4.rank → ZMod 3) : Prop :=
  (M.map (Int.cast : ℤ → ZMod 3)).transpose.mulVec β = β

instance (M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (β : Fin Tag.F4.rank → ZMod 3) :
    Decidable (fixes M β) := by
  unfold fixes
  infer_instance

theorem count_single : ∀ M ∈ sylS, M ≠ 1 →
    (Finset.univ.filter fun β : Fin Tag.F4.rank → ZMod 3 => fixes M β).card ≤ 9 := by
  decide +kernel

theorem count_all :
    (Finset.univ.filter fun β : Fin Tag.F4.rank → ZMod 3 => ∀ M ∈ sylS, fixes M β).card ≤ 3 := by
  decide +kernel

end Weyl

section Torus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders CFSG.Open

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

@[expose] def theta (ζ : Kˣ) (a : ZMod 3) : Kˣ := ζ ^ a.val

theorem theta_zero (ζ : Kˣ) : theta ζ 0 = 1 := by
  simp [theta]

theorem theta_add {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (a b : ZMod 3) :
    theta ζ (a + b) = theta ζ a * theta ζ b := by
  unfold theta
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hζ).symm

@[expose] def thetaHom {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : Multiplicative (ZMod 3) →* Kˣ where
  toFun a := theta ζ (Multiplicative.toAdd a)
  map_one' := theta_zero ζ
  map_mul' _ _ := theta_add hζ _ _

theorem theta_zpow {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (a : ZMod 3) (n : ℤ) :
    theta ζ a ^ n = theta ζ ((n : ZMod 3) * a) := by
  have h := map_zpow (thetaHom hζ) (Multiplicative.ofAdd a) n
  rw [← ofAdd_zsmul, zsmul_eq_mul] at h
  exact h.symm

theorem theta_sum {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    theta ζ (∑ i ∈ s, f i) = ∏ i ∈ s, theta ζ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, theta_add hζ, ih]

theorem theta_injective {ζ : Kˣ} (hζ : orderOf ζ = 3) : Function.Injective (theta ζ) := by
  intro a b h
  unfold theta at h
  rw [pow_inj_mod, hζ, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective 3 h

theorem exists_theta_eq {ζ : Kˣ} (hζ : orderOf ζ = 3) {x : Kˣ} (hx : x ^ 3 = 1) :
    ∃ a : ZMod 3, theta ζ a = x := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : (ζ : K) ≠ 1 := by
    intro h
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    omega
  have hz3 : (ζ : K) ^ 3 = 1 := by
    have := congrArg Units.val hζ3
    simpa using this
  have hx3 : (x : K) ^ 3 = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have hz2 : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have h1 : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by
      linear_combination hz3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hζ1
    · exact h
  have hprod : ((x : K) - 1) * (((x : K) - ζ) * ((x : K) - (ζ : K) ^ 2)) = 0 := by
    linear_combination hx3 + ((x : K) - (x : K) ^ 2) * hz2 + ((x : K) - 1) * hz3
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨0, ?_⟩
    have : x = 1 := Units.ext (sub_eq_zero.1 h)
    rw [this, theta_zero]
  · rcases mul_eq_zero.1 h with h | h
    · refine ⟨1, ?_⟩
      have : x = ζ := Units.ext (sub_eq_zero.1 h)
      rw [this]
      have hv : (1 : ZMod 3).val = 1 := rfl
      simp [theta, hv]
    · refine ⟨2, ?_⟩
      have h2 : (x : K) = (ζ : K) ^ 2 := sub_eq_zero.1 h
      have : x = ζ ^ 2 := Units.ext (by simpa using h2)
      rw [this]
      have hv : (2 : ZMod 3).val = 2 := rfl
      simp [theta, hv]

@[expose] def dotZ (u : Fin Tag.F4.rank → ZMod 3) (x : Fin Tag.F4.rank → ℤ) : ZMod 3 :=
  ∑ i, (x i : ZMod 3) * u i

theorem rootChar_theta {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Fin Tag.F4.rank → ZMod 3)
    (x : Fin Tag.F4.rank → ℤ) :
    rootChar (fun i => theta ζ (u i)) x = theta ζ (dotZ u x) := by
  unfold rootChar dotZ
  rw [theta_sum hζ]
  exact Finset.prod_congr rfl fun i _ => theta_zpow hζ _ _

theorem fixes_of_dotZ {w : WeylGroup Tag.F4} {β : Fin Tag.F4.rank → ZMod 3}
    (h : ∀ v : Fin Tag.F4.rank → ℤ, dotZ β (w • v) = dotZ β v) : fixes (weylMatrix w) β := by
  funext j
  have h1 := h (Pi.single j 1)
  have h2 : dotZ β (Pi.single j 1) = β j := by
    simp [dotZ, Pi.single_apply]
  rw [h2] at h1
  rw [← h1]
  simp only [dotZ, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
    weylMatrix_apply]

@[expose] noncomputable def Psi {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.F4.rank → ZMod 3) →* ModGL Tag.F4 K where
  toFun u := rootDiagUnit Tag.F4 (fun i => theta ζ (Multiplicative.toAdd u i))
  map_one' := by
    have : (fun i => theta ζ (Multiplicative.toAdd
        (1 : Multiplicative (Fin Tag.F4.rank → ZMod 3)) i)) = 1 := by
      funext i
      exact theta_zero ζ
    rw [this]
    exact rootDiagUnit_one
  map_mul' u v := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    exact theta_add hζ _ _

theorem Psi_apply {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin Tag.F4.rank → ZMod 3)) :
    Psi (K := K) hζ u = rootDiagUnit Tag.F4 (fun i => theta ζ (Multiplicative.toAdd u i)) := rfl

theorem Psi_injective {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Function.Injective (Psi (K := K) hζ) := by
  intro u v h
  have h' := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h
  have : Multiplicative.toAdd u = Multiplicative.toAdd v := by
    funext i
    exact theta_injective hζ' (congrFun h' i)
  exact this

theorem exists_Psi_of_mem_torus {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    {x : ModGL Tag.F4 K} (hx : x ∈ torusGroup Tag.F4 K) (hx3 : x ^ 3 = 1) :
    ∃ u : Multiplicative (Fin Tag.F4.rank → ZMod 3), Psi (K := K) hζ u = x := by
  obtain ⟨c, rfl⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom hx
  have hc3 : c ^ 3 = 1 := by
    have h1 : rootDiagUnitHom Tag.F4 K (c ^ 3) = rootDiagUnitHom Tag.F4 K 1 := by
      rw [map_pow, map_one]
      exact hx3
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1
  have h : ∀ i, ∃ a : ZMod 3, theta ζ a = c i := fun i =>
    exists_theta_eq hζ' (by simpa using congrFun hc3 i)
  choose b hb using h
  refine ⟨Multiplicative.ofAdd b, ?_⟩
  rw [Psi_apply]
  change rootDiagUnit Tag.F4 _ = rootDiagUnit Tag.F4 c
  congr 1
  funext i
  exact hb i

theorem rho_surjective_and_ker :
    Function.Surjective (weylQuotientHom Tag.F4 K) ∧
      (weylQuotientHom Tag.F4 K).ker =
        (torusGroup Tag.F4 K).subgroupOf (monomialSubgroup Tag.F4 K) := by
  obtain ⟨-, ⟨ρ, hsurj, hmaps, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient Tag.F4 K
  have h : ρ = weylQuotientHom Tag.F4 K := by
    ext g
    exact (weylQuotientHom_eq (hmaps g)).symm
  subst h
  exact ⟨hsurj, hker⟩

@[expose] noncomputable def Qsub (K : Type) [Field K] : Subgroup (ModGL Tag.F4 K) :=
  ((Pw).comap (weylQuotientHom Tag.F4 K)).map (monomialSubgroup Tag.F4 K).subtype

theorem Qsub_le_monomial : Qsub K ≤ monomialSubgroup Tag.F4 K := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

theorem mem_Qsub {g : ModGL Tag.F4 K} :
    g ∈ Qsub K ↔ ∃ n : ↥(monomialSubgroup Tag.F4 K), (n : ModGL Tag.F4 K) = g ∧
      weylQuotientHom Tag.F4 K n ∈ Pw := by
  simp [Qsub, Subgroup.mem_map, Subgroup.mem_comap]

theorem rho_eq_of_decomp {n : ↥(monomialSubgroup Tag.F4 K)} {w : WeylGroup Tag.F4}
    {k : ModGL Tag.F4 K} (hk : k ∈ torusGroup Tag.F4 K)
    (h : (n : ModGL Tag.F4 K) = k * canonicalRep (coxeterSystem Tag.F4) K w) :
    weylQuotientHom Tag.F4 K n = w := by
  apply weylQuotientHom_eq
  rw [h]
  have := (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := K) w)
  rwa [one_mul] at this

theorem Psi_mem_range {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin Tag.F4.rank → ZMod 3)) :
    Psi (K := K) hζ u ∈ (rootDiagUnitHom Tag.F4 K).range :=
  ⟨_, rfl⟩

theorem fixes_of_commute {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) {e : ModGL Tag.F4 K}
    {w : WeylGroup Tag.F4} {k : ModGL Tag.F4 K} (hk : k ∈ torusGroup Tag.F4 K)
    (he : e = k * canonicalRep (coxeterSystem Tag.F4) K w) {β : Fin Tag.F4.rank → ZMod 3}
    (hc : e * Psi hζ (Multiplicative.ofAdd β) = Psi hζ (Multiplicative.ofAdd β) * e) :
    fixes (weylMatrix w) β := by
  set d := Psi (K := K) hζ (Multiplicative.ofAdd β) with hd
  set n := canonicalRep (coxeterSystem Tag.F4) K w with hn
  have hkd : k * d = d * k := by
    obtain ⟨c, hc'⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom hk
    have hc'' : ∃ c', rootDiagUnitHom Tag.F4 K c' = d :=
      Psi_mem_range (K := K) hζ (Multiplicative.ofAdd β)
    obtain ⟨c', hc'''⟩ := hc''
    rw [← hc', ← hc''', ← map_mul, ← map_mul, mul_comm]
  have hnd : n * d = d * n := by
    apply mul_left_cancel (a := k)
    rw [he] at hc
    calc k * (n * d) = k * n * d := by group
      _ = d * (k * n) := hc
      _ = (d * k) * n := by group
      _ = (k * d) * n := by rw [hkd]
      _ = k * (d * n) := by group
  have hconj : rootDiagUnit Tag.F4 (fun i => theta ζ (β i)) =
      n * rootDiagUnit Tag.F4 (fun i => theta ζ (β i)) * n⁻¹ := by
    have : d = rootDiagUnit Tag.F4 (fun i => theta ζ (β i)) := rfl
    rw [← this]
    calc d = d * n * n⁻¹ := by group
      _ = n * d * n⁻¹ := by rw [hnd]
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).1 hconj
  refine fixes_of_dotZ fun v => ?_
  have h1 := hchar v
  rw [rootChar_theta hζ, rootChar_theta hζ] at h1
  exact theta_injective hζ' h1

theorem rho_ker_mem_torus {n : ↥(monomialSubgroup Tag.F4 K)}
    (hn : weylQuotientHom Tag.F4 K n = 1) : (n : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K := by
  have h := (rho_surjective_and_ker (K := K)).2
  have h2 : n ∈ (weylQuotientHom Tag.F4 K).ker := hn
  rw [h] at h2
  exact h2

@[expose] noncomputable def rhoE {E : Subgroup (ModGL Tag.F4 K)}
    (hEN : E ≤ monomialSubgroup Tag.F4 K) : ↥E →* WeylGroup Tag.F4 :=
  (weylQuotientHom Tag.F4 K).comp (Subgroup.inclusion hEN)

theorem rhoE_apply {E : Subgroup (ModGL Tag.F4 K)} (hEN : E ≤ monomialSubgroup Tag.F4 K)
    (x : ↥E) : rhoE hEN x = weylQuotientHom Tag.F4 K (Subgroup.inclusion hEN x) := rfl

theorem exists_decomp {E : Subgroup (ModGL Tag.F4 K)} (hEN : E ≤ monomialSubgroup Tag.F4 K)
    (x : ↥E) : ∃ k : ModGL Tag.F4 K, k ∈ torusGroup Tag.F4 K ∧
      (x : ModGL Tag.F4 K) = k * canonicalRep (coxeterSystem Tag.F4) K (rhoE hEN x) := by
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets (hEN x.2)
  refine ⟨k, hk, ?_⟩
  have hρ : rhoE hEN x = w :=
    rho_eq_of_decomp (n := Subgroup.inclusion hEN x) hk hxk
  rw [hρ]
  exact hxk

theorem card_ker_le_fix {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    {E : Subgroup (ModGL Tag.F4 K)} (hEN : E ≤ monomialSubgroup Tag.F4 K)
    (hEel : IsElemAbelian 3 E) (P : (Fin Tag.F4.rank → ZMod 3) → Prop) [DecidablePred P]
    (hP : ∀ β, (∀ g ∈ (rhoE hEN).range, fixes (weylMatrix g) β) → P β) :
    Nat.card (rhoE hEN).ker ≤ (Finset.univ.filter P).card := by
  classical
  have hex : ∀ x : ↥(rhoE hEN).ker, ∃ u : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      Psi (K := K) hζ u = ((x : ↥E) : ModGL Tag.F4 K) := by
    intro x
    have hx1 : rhoE hEN (x : ↥E) = 1 := x.2
    have hxN : weylQuotientHom Tag.F4 K (Subgroup.inclusion hEN (x : ↥E)) = 1 := hx1
    exact exists_Psi_of_mem_torus hζ hζ' (rho_ker_mem_torus hxN) (hEel.2 _ (x : ↥E).2)
  choose u hu using hex
  have hfix : ∀ x : ↥(rhoE hEN).ker, P (Multiplicative.toAdd (u x)) := by
    intro x
    apply hP
    rintro g ⟨z, rfl⟩
    obtain ⟨k, hk, hzk⟩ := exists_decomp hEN z
    refine fixes_of_commute (e := (z : ModGL Tag.F4 K)) hζ hζ' hk hzk ?_
    rw [ofAdd_toAdd, hu x]
    exact congrArg Subtype.val (hEel.1.is_comm.comm z (x : ↥E))
  let f : ↥(rhoE hEN).ker → (Finset.univ.filter P) := fun x =>
    ⟨Multiplicative.toAdd (u x), Finset.mem_filter.2 ⟨Finset.mem_univ _, hfix x⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Multiplicative.toAdd (u x) = Multiplicative.toAdd (u y) := congrArg Subtype.val hxy
    have h2 : u x = u y := h1
    apply Subtype.ext
    apply Subtype.ext
    rw [← hu x, ← hu y, h2]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥(Finset.univ.filter P)), Fintype.card_coe] at h
  exact h

theorem le_Psi_range {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    {E : Subgroup (ModGL Tag.F4 K)} (hE : E ≤ Qsub K) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 4) : E ≤ (Psi (K := K) hζ).range := by
  classical
  have hEN : E ≤ monomialSubgroup Tag.F4 K := hE.trans Qsub_le_monomial
  have hPw : ∀ g ∈ (rhoE hEN).range, g ∈ Pw := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn, hnP⟩ := mem_Qsub.1 (hE x.2)
    have : n = Subgroup.inclusion hEN x := Subtype.ext hn
    rw [rhoE_apply, ← this]
    exact hnP
  by_cases hB : (rhoE hEN).range = ⊥
  · intro x hx
    have hx1 : rhoE hEN ⟨x, hx⟩ = 1 := by
      have : rhoE hEN ⟨x, hx⟩ ∈ (rhoE hEN).range := ⟨_, rfl⟩
      rw [hB] at this
      exact this
    have hxN : weylQuotientHom Tag.F4 K (Subgroup.inclusion hEN ⟨x, hx⟩) = 1 := hx1
    obtain ⟨u, hu⟩ := exists_Psi_of_mem_torus hζ hζ' (rho_ker_mem_torus hxN) (hEel.2 x hx)
    exact ⟨u, hu⟩
  · exfalso
    have hcard := Subgroup.card_ker_mul_card_range (rhoE hEN)
    have hEc' : Nat.card E = 81 := by rw [hEc]; norm_num
    rw [hEc'] at hcard
    have hBdvd : Nat.card (rhoE hEN).range ∣ 9 := by
      rw [← card_Pw]
      exact Subgroup.card_dvd_of_le (fun g hg => hPw g hg)
    have hBne : Nat.card (rhoE hEN).range ≠ 1 := fun h => hB (Subgroup.card_eq_one.1 h)
    obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
    have hM : weylMatrix (g : WeylGroup Tag.F4) ∈ sylS := weylMatrix_mem_sylS (hPw g g.2)
    have hM1 : weylMatrix (g : WeylGroup Tag.F4) ≠ 1 := fun h =>
      hg1 (Subtype.ext (weylMatrix_injective (h.trans weylMatrix_one.symm)))
    have h9 : Nat.card (rhoE hEN).ker ≤ 9 :=
      (card_ker_le_fix hζ hζ' hEN hEel (fun β => fixes (weylMatrix (g : WeylGroup Tag.F4)) β)
        (fun β hβ => hβ g g.2)).trans (count_single _ hM hM1)
    have hB39 : Nat.card (rhoE hEN).range = 3 ∨ Nat.card (rhoE hEN).range = 9 := by
      have h32 : Nat.card (rhoE hEN).range ∣ 3 ^ 2 := by
        have h9e : (3 : ℕ) ^ 2 = 9 := by norm_num
        rw [h9e]
        exact hBdvd
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h32
      interval_cases i
      · exact absurd (by simpa using hi') hBne
      · left; simpa using hi'
      · right; simpa using hi'
    rcases hB39 with h3 | h9'
    · rw [h3] at hcard
      omega
    · have hBP : (rhoE hEN).range = Pw :=
        Subgroup.eq_of_le_of_card_ge (fun g hg => hPw g hg) (by rw [card_Pw, h9'])
      have h3le : Nat.card (rhoE hEN).ker ≤ 3 := by
        refine (card_ker_le_fix hζ hζ' hEN hEel (fun β => ∀ M ∈ sylS, fixes M β) ?_).trans
          count_all
        intro β hβ M hM'
        have hM2 : M ∈ weylMatrix '' (Pw : Set (WeylGroup Tag.F4)) := by
          rw [weylMatrix_image_Pw]
          exact List.mem_toFinset.2 hM'
        obtain ⟨g', hg', rfl⟩ := hM2
        exact hβ g' (by rw [hBP]; exact hg')
      rw [h9'] at hcard
      omega

end Torus

section Orders

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

theorem card_Qsub : Nat.card ↥(Qsub K) = (Nat.card K - 1) ^ 4 * 9 := by
  obtain ⟨hsurj, hker⟩ := rho_surjective_and_ker (K := K)
  set ρ := weylQuotientHom Tag.F4 K with hρ
  have hQ : Nat.card ↥(Qsub K) = Nat.card ↥(Pw.comap ρ) :=
    Subgroup.card_map_of_injective (monomialSubgroup Tag.F4 K).subtype_injective
  have hidx : (Pw.comap ρ).index = Pw.index := Subgroup.index_comap_of_surjective Pw hsurj
  have h1 : Nat.card ρ.ker * Nat.card (WeylGroup Tag.F4) =
      Nat.card ↥(monomialSubgroup Tag.F4 K) := Subgroup.card_ker_mul_card_of_surjective hsurj
  have h2 : Nat.card ↥(Pw.comap ρ) * (Pw.comap ρ).index =
      Nat.card ↥(monomialSubgroup Tag.F4 K) := Subgroup.card_mul_index _
  have h3 : Nat.card Pw * Pw.index = Nat.card (WeylGroup Tag.F4) := Subgroup.card_mul_index _
  have hpos : 0 < Pw.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have h4 : Nat.card ↥(Pw.comap ρ) = Nat.card ρ.ker * Nat.card Pw := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(Pw.comap ρ) * Pw.index
        = Nat.card ↥(Pw.comap ρ) * (Pw.comap ρ).index := by rw [hidx]
      _ = Nat.card ↥(monomialSubgroup Tag.F4 K) := h2
      _ = Nat.card ρ.ker * Nat.card (WeylGroup Tag.F4) := h1.symm
      _ = Nat.card ρ.ker * (Nat.card Pw * Pw.index) := by rw [h3]
      _ = Nat.card ρ.ker * Nat.card Pw * Pw.index := by ring
  have h5 : Nat.card ρ.ker = (Nat.card K - 1) ^ 4 := by
    rw [hker, ← card_torusGroup_F4 (K := K)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [hQ, h4, h5, card_Pw]

theorem exists_cube_root (h3 : 3 ∣ Nat.card K - 1) : ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ orderOf ζ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype Kˣ := Fintype.ofFinite _
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    exact h3
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨ζ, by rw [← hζ]; exact pow_orderOf_eq_one ζ, hζ⟩

theorem card_Psi_range {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Nat.card (Psi (K := K) hζ).range = 3 ^ 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (Psi_injective hζ hζ')).toEquiv,
    Nat.card_congr (Multiplicative.toAdd)]
  simp [Nat.card_eq_fintype_card]
  decide

theorem core_unique {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    {E F : Subgroup (ModGL Tag.F4 K)} (hE : E ≤ Qsub K) (hF : F ≤ Qsub K)
    (hEel : IsElemAbelian 3 E) (hFel : IsElemAbelian 3 F) (hEc : Nat.card E = 3 ^ 4)
    (hFc : Nat.card F = 3 ^ 4) : E = F := by
  have h1 : E = (Psi (K := K) hζ).range :=
    Subgroup.eq_of_le_of_card_ge (le_Psi_range hζ hζ' hE hEel hEc)
      (by rw [card_Psi_range hζ hζ', hEc])
  have h2 : F = (Psi (K := K) hζ).range :=
    Subgroup.eq_of_le_of_card_ge (le_Psi_range hζ hζ' hF hFel hFc)
      (by rw [card_Psi_range hζ hζ', hFc])
  rw [h1, h2]

theorem threeUniq4_Qsub {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    ThreeUniq4 ↥(Qsub K) := by
  intro P hP E F hEP hFP hE hF hEc hFc
  apply Subgroup.map_injective (Qsub K).subtype_injective
  refine core_unique hζ hζ' (Subgroup.map_subtype_le E) (Subgroup.map_subtype_le F)
    (isElemAbelian_map' _ hE) (isElemAbelian_map' _ hF) ?_ ?_
  · rw [Subgroup.card_map_of_injective (Qsub K).subtype_injective, hEc]
  · rw [Subgroup.card_map_of_injective (Qsub K).subtype_injective, hFc]

theorem Qsub_le_adjointGroup : Qsub K ≤ adjointGroup Tag.F4 K :=
  Qsub_le_monomial.trans monomialSubgroup_le_adjointGroup'

theorem threeUniq4_adjointF4 (h3 : 3 ∣ Nat.card K - 1)
    (hord : (ordF4 (Nat.card K)).factorization 3 = ((Nat.card K - 1) ^ 4 * 9).factorization 3) :
    ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root h3
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  refine threeUniq4_of_range (Subgroup.inclusion Qsub_le_adjointGroup)
    (Subgroup.inclusion_injective _) ?_ (threeUniq4_Qsub hζ hζ')
  rw [card_adjointGroup_F4, card_Qsub]
  exact hord

end Orders

section Assembly

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem threeUniq4_adjointF4_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
  refine threeUniq4_adjointF4 (by rw [hK] <;> norm_num) ?_
  rw [hK]
  exact factorization_three_ordF4_four.trans factorization_three_729.symm

theorem threeUniq4_adjointF4_sixtyfour {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) :
    ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
  refine threeUniq4_adjointF4 (by rw [hK] <;> norm_num) ?_
  rw [hK]
  exact factorization_three_ordF4_sixtyfour.trans factorization_three_63.symm

@[expose] noncomputable def baseChangeHom {τ : Tag} {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (f : K₁ →+* K₂) : adjointGroup τ K₁ →* adjointGroup τ K₂ :=
  ((baseChangeGL (τ := τ) f).comp (adjointGroup τ K₁).subtype).codRestrict _ fun g =>
    CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem f g.2

theorem baseChangeHom_injective {τ : Tag} {K₁ K₂ : Type} [Field K₁] [Field K₂] (f : K₁ →+* K₂) :
    Function.Injective (baseChangeHom (τ := τ) f) := fun g g' h =>
  Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val h))

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Lang.AnisoE6

theorem threeUniq4_adjointF4_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)] <;> norm_num
  obtain ⟨f⟩ := nonempty_ringHom_of_card_sq (ℓ := 2) (f := 1) (k := K) (K := GaloisField 2 2)
    (by rw [hK]; norm_num) (by rw [hK4]; norm_num)
  exact threeUniq4_of_injective (baseChangeHom f) (baseChangeHom_injective f)
    (threeUniq4_adjointF4_four hK4)

theorem threeUniq4_adjointF4_eight {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) : ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK64 : Nat.card (GaloisField 2 6) = 64 := by
    rw [GaloisField.card 2 6 (by norm_num)]
    norm_num
  obtain ⟨f⟩ := nonempty_ringHom_of_card_sq (ℓ := 2) (f := 3) (k := K) (K := GaloisField 2 6)
    (by rw [hK]; norm_num) (by rw [hK64]; norm_num)
  exact threeUniq4_of_injective (baseChangeHom f) (baseChangeHom_injective f)
    (threeUniq4_adjointF4_sixtyfour hK64)

theorem threeUniq4_adjointE6 {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hF : ThreeUniq4 ↥(adjointGroup Tag.F4 K)) : ThreeUniq4 ↥(adjointGroup Tag.E6 K) := by
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  refine threeUniq4_of_range (e6F4Embed K) (e6F4Embed_injective K) ?_ hF
  have hc : Nat.card ↥(e6FixedF4 K) = Nat.card ↥(adjointGroup Tag.F4 K) :=
    (Nat.card_congr (CFSG.LieType.SeitzGeneration.ExcHighThree.e6FixedF4Equiv K).toEquiv).symm
  rw [factorization_eq_of_not_dvd_index _ (not_dvd_three_index_e6FixedF4 K hK), hc]

theorem threeUniq4_twistedE6 {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k) (hK : Nat.card K = (Nat.card k) ^ 2)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hq : Nat.card k % 3 = 1) (hq2 : 2 ≤ Nat.card k)
    (hF : ThreeUniq4 ↥(adjointGroup Tag.F4 k)) : ThreeUniq4 ↥(twistedE6RootGroup K σ) := by
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (ModGL Tag.F4 k) := finite_modGL
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hn, hkcard⟩ := FiniteField.card k (ringChar k)
  have hℓ : (ringChar k).Prime := hn
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hkq : Nat.card k = ringChar k ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hkcard
  have hGcard : Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (Nat.card k) := by
    rw [CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq hℓ hf σ
      (by rw [hkq] at hK; exact hK) (by intro c; rw [hσ c, hkq]), ← hkq]
  have hFcard : Nat.card (adjointGroup Tag.F4 k) = ordF4 (Nat.card k) :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.card_adjointGroup_F4_eq k
  have hord : (Nat.card (twistedE6RootGroup K σ)).factorization 3 =
      (Nat.card (adjointGroup Tag.F4 k)).factorization 3 := by
    rw [hGcard, hFcard]
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.factorization_three_ordTwistedE6 hq hq2
  have hφ : Function.Injective
      ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) :=
    (phiG_injective σ hfix).comp (MulEquiv.injective _)
  exact threeUniq4_of_range _ hφ hord hF

end Assembly

end I102UniqAux

section Final

open CFSG.TauCetiBridge TauCeti I102UniqAux CFSG.LieType.SeitzGeneration CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem gen2318RankFourSylowUniq_holds : Gen2318RankFourSylowUniq := by
  intro S _ _ d hd hiso P E F hEP hFP hE hF hEc hFc hEi hFi
  obtain ⟨eS⟩ := hiso
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    have hd' : IsTwoPow q 2 := hd
    obtain ⟨hq1, hq2⟩ := hd'
    obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
    have hK4 : Nat.card K = 4 := by
      rw [hK, PrimePower.card_def, hq1, hq2] <;> norm_num
    have hU := threeUniq4_adjointF4_four hK4
    have hUS : ThreeUniq4 S :=
      threeUniq4_of_injective (eS.trans eC).toMonoidHom (eS.trans eC).injective hU
    exact sylowForm_of_threeUniq4 (conj_injective_of_equiv eS (conj_injective_cat_F4 q hv)) hUS
      P E F hEP hFP hE hF hEc hFc hEi hFi
  | E6 q =>
    have hd' : IsTwoPow q 1 ∨ IsTwoPow q 3 := hd
    obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    have hq2 : q.p = 2 := by
      rcases hd' with h | h <;> exact h.1
    haveI : CharP K 2 := hq2 ▸ hKc
    have hKc' : Nat.card K = 2 ∨ Nat.card K = 8 := by
      rw [hK, PrimePower.card_def, hq2]
      rcases hd' with h | h
      · left; rw [h.2]; norm_num
      · right; rw [h.2]; norm_num
    have hF4 : ThreeUniq4 ↥(adjointGroup Tag.F4 K) := by
      rcases hKc' with h | h
      · exact threeUniq4_adjointF4_two h
      · exact threeUniq4_adjointF4_eight h
    have hmod : Nat.card K % 3 = 2 := by
      rcases hKc' with h | h <;> rw [h]
    have hU := threeUniq4_adjointE6 hmod hF4
    have hUS : ThreeUniq4 S :=
      threeUniq4_of_injective (eS.trans eC).toMonoidHom (eS.trans eC).injective hU
    exact sylowForm_of_threeUniq4 (conj_injective_of_equiv eS (conj_injective_cat_E6 q hv)) hUS
      P E F hEP hFP hE hF hEc hFc hEi hFi
  | _ => exact absurd hd (by simp [IsRankFourIndex])

theorem twE6FourSylowRankUnique_holds : TwE6FourSylowRankUnique := by
  intro S _ _ d hd hiso P E F hEP hFP hE hF hEc hFc hEi hFi
  obtain ⟨eS⟩ := hiso
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hd' : IsTwoPow q 2 := hd
    obtain ⟨hq1, hq2⟩ := hd'
    obtain ⟨K, _, σ, hK, hσ, ⟨eC⟩⟩ := exists_catEquiv_twistedE6 q hv
    haveI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
    have hqc : q.p ^ q.exponent = 4 := by
      rw [hq1, hq2]
      norm_num
    obtain ⟨k, _, _, _, hk, hkchar, hfix⟩ :=
      exists_fixed_subfield' (q.p ^ q.exponent) K σ (by rw [hK]) hσ
        (by rw [hqc]; norm_num)
    have hk4 : Nat.card k = 4 := by rw [hk, hqc]
    have hF4 : ThreeUniq4 ↥(adjointGroup Tag.F4 k) := threeUniq4_adjointF4_four hk4
    have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
    have hKk : Nat.card K = (Nat.card k) ^ 2 := by rw [hk]; exact hK
    have hU := threeUniq4_twistedE6 σ hσk hKk hfix (by rw [hk4]) (by rw [hk4]; norm_num) hF4
    have hUS : ThreeUniq4 S :=
      threeUniq4_of_injective (eS.trans eC).toMonoidHom (eS.trans eC).injective hU
    exact sylowForm_of_threeUniq4
      (conj_injective_of_equiv eS (conj_injective_cat_twistedE6 q hv)) hUS
      P E F hEP hFP hE hF hEc hFc hEi hFi
  | _ => exact absurd hd (by simp [IsTwistedE6FourIndex])

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
