module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixLagrangianRadical
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigherModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl MatrixExtension

abbrev SixBits : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

@[expose] def utMat (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, a, c; 0, 1, b; 0, 0, 1]

@[expose] def symMat (x : SixBits) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![x.1, x.2.2.2.1, x.2.2.2.2.1; x.2.2.2.1, x.2.1, x.2.2.2.2.2;
    x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1]

@[expose] def symCoord (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : SixBits :=
  (B 0 0, B 1 1, B 2 2, B 0 1, B 0 2, B 1 2)

theorem symMat_symCoord {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : Bᵀ = B) :
    symMat (symCoord B) = B := by
  have h : ∀ i j, B j i = B i j := fun i j => congrFun (congrFun hB i) j
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact h _ _

theorem utMat_of_isUnitriangular {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsUnitriangular A) :
    A = utMat (A 0 1) (A 1 2) (A 0 2) := by
  have hl : ∀ i j : Fin 3, j < i → A i j = 0 := fun i j h => hA.1 h
  have hd := hA.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [utMat, hd, hl 1 0 (by decide), hl 2 0 (by decide), hl 2 1 (by decide)]

theorem card_fixed_utMat_le : ∀ a b c : ZMod 2, utMat a b c ≠ 1 →
    (Finset.univ.filter fun x : SixBits =>
      utMat a b c * symMat x * (utMat a b c)ᵀ = symMat x).card ≤ 16 := by
  decide

set_option synthInstance.maxSize 4096 in
theorem card_fixed_two_utMat_le : ∀ a b c a' b' c' : ZMod 2, utMat a b c ≠ 1 →
    utMat a' b' c' ≠ 1 → utMat a b c ≠ utMat a' b' c' → utMat a b c * utMat a b c = 1 →
    utMat a' b' c' * utMat a' b' c' = 1 →
    utMat a b c * utMat a' b' c' = utMat a' b' c' * utMat a b c →
    (Finset.univ.filter fun x : SixBits =>
      utMat a b c * symMat x * (utMat a b c)ᵀ = symMat x ∧
        utMat a' b' c' * symMat x * (utMat a' b' c')ᵀ = symMat x).card ≤ 8 := by
  decide

theorem card_fixed_le_sixteen {M : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hM : IsUnitriangular M)
    (hM1 : M ≠ 1) :
    (Finset.univ.filter fun x : SixBits => M * symMat x * Mᵀ = symMat x).card ≤ 16 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, M = utMat a b c := ⟨_, _, _, utMat_of_isUnitriangular hM⟩
  exact card_fixed_utMat_le a b c hM1

theorem card_fixed_two_le_eight {M M' : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hM : IsUnitriangular M) (hM' : IsUnitriangular M') (hM1 : M ≠ 1) (hM'1 : M' ≠ 1)
    (hne : M ≠ M') (hsq : M * M = 1) (hsq' : M' * M' = 1) (hcomm : M * M' = M' * M) :
    (Finset.univ.filter fun x : SixBits =>
      M * symMat x * Mᵀ = symMat x ∧ M' * symMat x * M'ᵀ = symMat x).card ≤ 8 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, M = utMat a b c := ⟨_, _, _, utMat_of_isUnitriangular hM⟩
  obtain ⟨a', b', c', rfl⟩ : ∃ a b c, M' = utMat a b c :=
    ⟨_, _, _, utMat_of_isUnitriangular hM'⟩
  exact card_fixed_two_utMat_le a b c a' b' c' hM1 hM'1 hne hsq hsq' hcomm

theorem utMat_mul_self (a : ZMod 2) : utMat a 0 0 * utMat a 0 0 = 1 := by
  fin_cases a <;> decide

theorem utMat_mul_self' (b : ZMod 2) : utMat 0 b 0 * utMat 0 b 0 = 1 := by
  fin_cases b <;> decide

theorem utMat_not_commute : utMat 1 0 0 * utMat 0 1 0 ≠ utMat 0 1 0 * utMat 1 0 0 := by
  decide

theorem isUnitriangular_utMat (a b c : ZMod 2) : IsUnitriangular (utMat a b c) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [utMat]
  · fin_cases i <;> simp [utMat]

theorem card_unitriangularGL_le : Nat.card (unitriangularGL 3 (ZMod 2)) ≤ 8 := by
  have hinj : Function.Injective fun A : unitriangularGL 3 (ZMod 2) =>
      (((A : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1,
        ((A : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2,
        ((A : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) := by
    intro A A' h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    apply Units.ext
    rw [utMat_of_isUnitriangular A.2, utMat_of_isUnitriangular A'.2, h.1, h.2.1, h.2.2]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := ZMod 2 × ZMod 2 × ZMod 2), Fintype.card_prod,
    Fintype.card_prod, ZMod.card] at this

@[expose] def involutionUnit {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A * A = 1) :
    GL (Fin 3) (ZMod 2) :=
  ⟨A, A, hA, hA⟩

theorem not_commute_unitriangularGL : ¬ ∀ x ∈ unitriangularGL 3 (ZMod 2),
    ∀ y ∈ unitriangularGL 3 (ZMod 2), x * y = y * x := by
  intro h
  have h1 := h (involutionUnit (utMat_mul_self 1)) (isUnitriangular_utMat 1 0 0)
    (involutionUnit (utMat_mul_self' 1)) (isUnitriangular_utMat 0 1 0)
  exact utMat_not_commute (congrArg Units.val h1)

theorem card_le_four_of_le_unitriangularGL {F : Subgroup (GL (Fin 3) (ZMod 2))}
    (hF : F ≤ unitriangularGL 3 (ZMod 2)) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    Nat.card F ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have hdvd := Subgroup.card_dvd_of_le hF
  have hle := card_unitriangularGL_le
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · rw [mul_zero] at hk
      exact absurd hk (Nat.card_pos (α := unitriangularGL 3 (ZMod 2))).ne'
    · rfl
    · nlinarith
  rw [hk1, mul_one] at hk
  have hEq : F = unitriangularGL 3 (ZMod 2) := Subgroup.eq_of_le_of_card_ge hF hk.le
  subst hEq
  exact not_commute_unitriangularGL hcomm

section General

variable {n : ℕ}

theorem unipotent_le_stabilizer :
    unipotent n (ZMod 2) ≤ stabilizer n (ZMod 2) (lagrangianZero n) := by
  have key : ∀ g ∈ unipotent n (ZMod 2), ∀ v ∈ lagrangianZero n,
      spMatrixOf g *ᵥ v ∈ lagrangianZero n := by
    rintro g ⟨A, C, hA, -, hg⟩ v hv
    rw [spMatrixOf, hg]
    exact blockMat_mulVec_mem_isoFlag hA.1 C hv
  intro g hg
  exact mem_stabilizer_of_mulVec_mem (key g hg) (key g⁻¹ (inv_mem hg))

theorem lagrangianLevi_mem_unitriangularGL {g : StatedSp n (ZMod 2)}
    (hg : g ∈ unipotent n (ZMod 2)) :
    lagrangianLevi n ⟨g, unipotent_le_stabilizer hg⟩ ∈ unitriangularGL n (ZMod 2) := by
  obtain ⟨A, C, hA, -, hgA⟩ := id hg
  rw [mem_unitriangularGL, coe_lagrangianLevi]
  change IsUnitriangular (((g : GL (Fin n ⊕ Fin n) (ZMod 2)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))).toBlocks₁₁
  rw [hgA, blockMat, toBlocks_fromBlocks₁₁]
  exact hA

theorem toBlocks₁₂_tauSym (B : Multiplicative (binarySymMatrices n)) :
    (spMatrixOf (tauSym n B)).toBlocks₁₂ = (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [spMatrixOf_tauSym, toBlocks_fromBlocks₁₂]

theorem card_range_tauSym (n : ℕ) : Nat.card (tauSym n).range = 2 ^ (n * (n + 1) / 2) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (tauSym_injective (n := n))).toEquiv]
  exact SymplecticCoverHigher.card_binarySymMatrices n

theorem congr_eq_of_commute {E : Subgroup (StatedSp n (ZMod 2))}
    (hE : E ≤ stabilizer n (ZMod 2) (lagrangianZero n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {B : Multiplicative (binarySymMatrices n)}
    (hB : tauSym n B ∈ E) {y : StatedSp n (ZMod 2)} (hy : y ∈ E) :
    (lagrangianLevi n ⟨y, hE hy⟩ : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (lagrangianLevi n ⟨y, hE hy⟩ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h1 := conj_tauSym_of_mem_stabilizer (hE hy) B
  rw [hcomm y hy _ hB, mul_inv_cancel_right] at h1
  have h2 := congrArg (fun C : Multiplicative (binarySymMatrices n) =>
    ((Multiplicative.toAdd C : binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2)))
    (tauSym_injective h1)
  simp only [toAdd_ofAdd] at h2
  exact h2.symm

end General

theorem le_range_tauSym_or_card_le {E : Subgroup (StatedSp 3 (ZMod 2))}
    (hE : E ≤ unipotent 3 (ZMod 2)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) :
    E ≤ (tauSym 3).range ∨ Nat.card E ≤ 32 := by
  classical
  have hEP : E ≤ stabilizer 3 (ZMod 2) (lagrangianZero 3) := hE.trans unipotent_le_stabilizer
  let f : E →* GL (Fin 3) (ZMod 2) := (lagrangianLevi 3).comp (Subgroup.inclusion hEP)
  have hfapp : ∀ y : E, f y = lagrangianLevi 3 ⟨y, hEP y.2⟩ := fun y => rfl
  have hker : ∀ x : E, x ∈ f.ker ↔ (x : StatedSp 3 (ZMod 2)) ∈ (tauSym 3).range := by
    intro x
    rw [MonoidHom.mem_ker, hfapp, ← MonoidHom.mem_ker, ker_lagrangianLevi,
      Subgroup.mem_subgroupOf]
  have hcard : Nat.card E = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hFU : f.range ≤ unitriangularGL 3 (ZMod 2) := by
    rintro _ ⟨y, rfl⟩
    exact lagrangianLevi_mem_unitriangularGL (hE y.2)
  have hFcomm : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hcomm x x.2 y y.2))
  have hF4 := card_le_four_of_le_unitriangularGL hFU hFcomm
  have hkerT : ∀ T : Finset SixBits, (∀ x : SixBits, (∀ A ∈ f.range,
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x * (A : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
        symMat x) → x ∈ T) → Nat.card f.ker ≤ T.card := by
    intro T hT
    have hmem : ∀ x : f.ker,
        symCoord (spMatrixOf ((x : E) : StatedSp 3 (ZMod 2))).toBlocks₁₂ ∈ T := by
      intro x
      obtain ⟨B, hB⟩ := (hker x).1 x.2
      apply hT
      rintro _ ⟨y, rfl⟩
      have hBE : tauSym 3 B ∈ E := by
        rw [hB]
        exact (x : E).2
      rw [← hB, toBlocks₁₂_tauSym, symMat_symCoord (binarySym_transpose B.toAdd)]
      exact congr_eq_of_commute hEP hcomm hBE y.2
    have hinj : Function.Injective fun x : f.ker => (⟨_, hmem x⟩ : T) := by
      intro x x' hxx
      have h := congrArg Subtype.val hxx
      obtain ⟨B, hB⟩ := (hker x).1 x.2
      obtain ⟨B', hB'⟩ := (hker x').1 x'.2
      simp only at h
      rw [← hB, ← hB', toBlocks₁₂_tauSym, toBlocks₁₂_tauSym] at h
      have h2 := congrArg symMat h
      rw [symMat_symCoord (binarySym_transpose _), symMat_symCoord (binarySym_transpose _)] at h2
      have h3 : B = B' := Multiplicative.toAdd.injective (Subtype.ext h2)
      apply Subtype.ext
      apply Subtype.ext
      rw [← hB, ← hB', h3]
    calc Nat.card f.ker ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
      _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rcases Subgroup.bot_or_exists_ne_one f.range with h1 | ⟨A, hA, hA1⟩
  · left
    intro x hx
    have hx' : f ⟨x, hx⟩ = 1 := by
      have : f ⟨x, hx⟩ ∈ f.range := ⟨_, rfl⟩
      rwa [h1, Subgroup.mem_bot] at this
    exact (hker ⟨x, hx⟩).1 hx'
  right
  have hsqF : ∀ a ∈ f.range, a * a = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x x.2), map_one]
  by_cases h3 : Nat.card f.range ≤ 2
  · have hk := hkerT (Finset.univ.filter fun x : SixBits =>
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x *
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = symMat x)
      (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx A hA⟩)
    have h16 := card_fixed_le_sixteen (hFU hA) (fun h => hA1 (Units.ext h))
    rw [hcard]
    calc Nat.card f.ker * Nat.card f.range ≤ 16 * 2 := Nat.mul_le_mul (hk.trans h16) h3
      _ = 32 := by norm_num
  push Not at h3
  have : Fintype f.range := Fintype.ofFinite _
  obtain ⟨A', -, hA'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, ⟨A, hA⟩} : Finset f.range)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_two h3)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hA'
  have hk := hkerT (Finset.univ.filter fun x : SixBits =>
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x *
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = symMat x ∧
        ((A' : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x *
          ((A' : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = symMat x)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx A hA, hx A' A'.2⟩)
  have h8 := card_fixed_two_le_eight (hFU hA) (hFU A'.2) (fun h => hA1 (Units.ext h))
    (fun h => hA'.1 (Subtype.ext (Units.ext h)))
    (fun h => hA'.2 (Subtype.ext (Units.ext h).symm))
    (congrArg Units.val (hsqF A hA)) (congrArg Units.val (hsqF _ A'.2))
    (congrArg Units.val (hFcomm A hA _ A'.2))
  rw [hcard]
  calc Nat.card f.ker * Nat.card f.range ≤ 8 * 4 := Nat.mul_le_mul (hk.trans h8) hF4
    _ = 32 := by norm_num

theorem card_le_of_le_unipotent {E : Subgroup (StatedSp 3 (ZMod 2))}
    (hE : E ≤ unipotent 3 (ZMod 2)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 64 ∧ (Nat.card E = 64 → E = (tauSym 3).range) := by
  have h64 : Nat.card (tauSym 3).range = 64 := card_range_tauSym 3
  rcases le_range_tauSym_or_card_le hE hcomm hsq with h | h
  · have hle := Subgroup.card_le_of_le h
    rw [h64] at hle
    exact ⟨hle, fun hE64 => Subgroup.eq_of_le_of_card_ge h (by rw [h64, hE64])⟩
  · exact ⟨by omega, fun hE64 => by omega⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
