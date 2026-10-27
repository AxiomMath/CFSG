module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt41
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

namespace Lemma41aL3

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.CentralCover

section Abstract

variable {S X H : Type*} [Group S] [Group X] [Group H]

theorem commute_of_map_commute (ρ : S →* X) (hker : ρ.ker ≤ center S)
    (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1) {s : S}
    (hs : ρ s * ρ a = ρ a * ρ s) : s * a = a * s := by
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : S, ζ = s * a * s⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hζ : ζ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hζdef]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hs
  have hζc : ∀ g : S, g * ζ = ζ * g := Subgroup.mem_center_iff.mp (hker hζ)
  have hζ3 := h3 ζ hζ
  have ht : s * a * s⁻¹ = ζ * a := by
    rw [hζdef, inv_mul_cancel_right]
  have hsq : ζ * ζ = 1 := by
    have h1 : (s * a * s⁻¹) * (s * a * s⁻¹) = 1 := by
      calc (s * a * s⁻¹) * (s * a * s⁻¹) = s * (a * a) * s⁻¹ := by group
        _ = 1 := by rw [ha]; group
    rw [ht] at h1
    have h2 : ζ * a * (ζ * a) = ζ * ζ * (a * a) := by
      calc ζ * a * (ζ * a) = ζ * (a * ζ) * a := by group
        _ = ζ * (ζ * a) * a := by rw [hζc a]
        _ = ζ * ζ * (a * a) := by group
    rw [h2, ha, mul_one] at h1
    exact h1
  have hζ1 : ζ = 1 := by
    rw [pow_succ, pow_two, hsq, one_mul] at hζ3
    exact hζ3
  have : s * a * s⁻¹ = a := by rw [ht, hζ1, one_mul]
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem exists_normal_quotient_equiv (ρ : S →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center S) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1)
    (φ : H →* S) (hφ : Function.Injective φ) (hrange : φ.range = centralizer ({a} : Set S)) :
    ∃ (N : Subgroup H) (_ : N.Normal), Nat.card N = Nat.card ρ.ker ∧
      Nonempty (↥(centralizer ({ρ a} : Set X)) ≃* H ⧸ N) := by
  let Φ : H →* X := ρ.comp φ
  have hmem : ∀ h : H, φ h * a = a * φ h := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mp (hrange ▸ ⟨h, rfl⟩)
  have hrangeΦ : Φ.range = centralizer ({ρ a} : Set X) := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show ρ (φ h) * ρ a = ρ a * ρ (φ h)
      rw [← map_mul, ← map_mul, hmem h]
    · intro hy
      obtain ⟨s, rfl⟩ := hρ y
      have hs := Subgroup.mem_centralizer_singleton_iff.mp hy
      have hs' : s ∈ centralizer ({a} : Set S) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_map_commute ρ hker h3 ha hs)
      rw [← hrange] at hs'
      obtain ⟨h, rfl⟩ := hs'
      exact ⟨h, rfl⟩
  refine ⟨Φ.ker, inferInstance, ?_, ⟨?_⟩⟩
  · refine Nat.card_eq_of_bijective (fun h : Φ.ker => (⟨φ h, h.2⟩ : ρ.ker)) ⟨?_, ?_⟩
    · intro h h' hh
      exact Subtype.ext (hφ (congrArg Subtype.val hh))
    · rintro ⟨ζ, hζ⟩
      have hc : ζ ∈ centralizer ({a} : Set S) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hker hζ) a).symm
      rw [← hrange] at hc
      obtain ⟨h, rfl⟩ := hc
      exact ⟨⟨h, hζ⟩, rfl⟩
  · exact (MulEquiv.subgroupCongr hrangeΦ.symm).trans (QuotientGroup.quotientKerEquivRange Φ).symm

end Abstract

section Blocks

variable {F : Type} [Field F]

@[expose] def blkMat (A : Matrix (Fin 2) (Fin 2) F) (d : F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem blkMat_mul (A B : Matrix (Fin 2) (Fin 2) F) (d e : F) :
    blkMat A d * blkMat B e = blkMat (A * B) (d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blkMat_one : blkMat (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem det_blkMat (A : Matrix (Fin 2) (Fin 2) F) (d : F) : (blkMat A d).det = A.det * d := by
  simp [blkMat, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem ulBlock_blkMat (A : Matrix (Fin 2) (Fin 2) F) (d : F) : ulBlock (blkMat A d) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ulBlock, blkMat]

@[expose] noncomputable def blkMon : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 3) (Fin 3) F where
  toFun A := blkMat A A.det⁻¹
  map_one' := by simp [blkMat_one]
  map_mul' A B := by rw [blkMat_mul, Matrix.det_mul, mul_inv]

@[expose] noncomputable def blk : GL (Fin 2) F →* GL (Fin 3) F := Units.map blkMon

theorem coe_blk (A : GL (Fin 2) F) :
    ((blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (A : Matrix (Fin 2) (Fin 2) F) (A : Matrix (Fin 2) (Fin 2) F).det⁻¹ := rfl

theorem det_ne_zero_gl (A : GL (Fin 2) F) : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det _ |>.mp A.isUnit).ne_zero

theorem det_blk (A : GL (Fin 2) F) :
    ((blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [coe_blk, det_blkMat, mul_inv_cancel₀ (det_ne_zero_gl A)]

theorem ulBlock_blk (A : GL (Fin 2) F) :
    ulBlock ((blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [coe_blk, ulBlock_blkMat]

theorem blk_injective : Function.Injective (blk : GL (Fin 2) F →* GL (Fin 3) F) := by
  intro A B h
  apply Units.ext
  have := congrArg (fun g : GL (Fin 3) F => ulBlock (g : Matrix (Fin 3) (Fin 3) F)) h
  simpa only [ulBlock_blk] using this

theorem blk_commute_negDiag3 (A : GL (Fin 2) F) :
    blk A * negDiag3 F = negDiag3 F * blk A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negDiag3, coe_blk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_blk_of_commute (h2 : (2 : F) ≠ 0) {y : GL (Fin 3) F}
    (hy : y * negDiag3 F = negDiag3 F * y) (hdet : (y : Matrix (Fin 3) (Fin 3) F).det = 1) :
    ∃ A : GL (Fin 2) F, blk A = y := by
  have hb := block_eq_zero_of_commute_negDiag h2 (congrArg Units.val hy : _)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F, (y : Matrix (Fin 3) (Fin 3) F) = M :=
    ⟨_, rfl⟩
  rw [hM] at hb hdet
  obtain ⟨h02, h12, h20, h21⟩ := hb
  have hdet3 : M.det = (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 2 2 := by
    rw [Matrix.det_fin_three, h02, h12, h20, h21]
    ring
  have hne : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet3
    rw [hdet3] at hdet
    exact zero_ne_one hdet
  have hM22 : M 2 2 = (M 0 0 * M 1 1 - M 0 1 * M 1 0)⁻¹ := by
    rw [hdet3] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  have hdetU : (ulBlock M).det ≠ 0 := by
    simpa [ulBlock, Matrix.det_fin_two] using hne
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (ulBlock M) hdetU, Units.ext ?_⟩
  rw [coe_blk, hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.GeneralLinearGroup.mkOfDetNeZero, ulBlock, Matrix.det_fin_two,
      h02, h12, h20, h21, hM22]

theorem exists_phi (h2 : (2 : F) ≠ 0) (S : Subgroup (GL (Fin 3) F))
    (hS : ∀ A : GL (Fin 3) F, A ∈ S ↔ (A : Matrix (Fin 3) (Fin 3) F).det = 1)
    {a : S} (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ φ : GL (Fin 2) F →* S, Function.Injective φ ∧ φ.range = centralizer ({a} : Set S) := by
  have hdet : ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := (hS _).mp a.2
  have hsq : (a : GL (Fin 3) F) * a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hne : (a : GL (Fin 3) F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 hsq hne hdet
  let ψ : GL (Fin 2) F →* GL (Fin 3) F := (MulAut.conj P).toMonoidHom.comp blk
  have hψ : ∀ A, ψ A = P * blk A * P⁻¹ := fun A => rfl
  have hψS : ∀ A, ψ A ∈ S := by
    intro A
    rw [hS, hψ, Units.val_mul, Units.val_mul, Matrix.det_units_conj, det_blk]
  have hψinj : Function.Injective ψ := (MulAut.conj P).injective.comp blk_injective
  refine ⟨ψ.codRestrict S hψS, fun A B h => hψinj (congrArg Subtype.val h), ?_⟩
  have ha' : (a : GL (Fin 3) F) = P * negDiag3 F * P⁻¹ := by rw [← hP]; group
  ext s
  constructor
  · rintro ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show ψ A * (a : GL (Fin 3) F) = (a : GL (Fin 3) F) * ψ A
    rw [ha', hψ]
    calc P * blk A * P⁻¹ * (P * negDiag3 F * P⁻¹) = P * (blk A * negDiag3 F) * P⁻¹ := by group
      _ = P * (negDiag3 F * blk A) * P⁻¹ := by rw [blk_commute_negDiag3]
      _ = P * negDiag3 F * P⁻¹ * (P * blk A * P⁻¹) := by group
  · intro hs
    have hs' : (s : GL (Fin 3) F) * a = a * s :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hs)
    have hyc : (P⁻¹ * s * P) * negDiag3 F = negDiag3 F * (P⁻¹ * s * P) := by
      rw [← hP]
      calc P⁻¹ * (s : GL (Fin 3) F) * P * (P⁻¹ * a * P) = P⁻¹ * (s * a) * P := by group
        _ = P⁻¹ * (a * s) * P := by rw [hs']
        _ = P⁻¹ * a * P * (P⁻¹ * s * P) := by group
    have hydet : ((P⁻¹ * (s : GL (Fin 3) F) * P : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']
      exact (hS _).mp s.2
    obtain ⟨A, hA⟩ := exists_blk_of_commute h2 hyc hydet
    refine ⟨A, Subtype.ext ?_⟩
    show ψ A = s
    rw [hψ, hA]
    group

end Blocks

section Kernel

theorem card_rootsOfUnity_three (F : Type) [Field F] [Finite F] :
    Nat.card (rootsOfUnity 3 F) = 1 ∨ Nat.card (rootsOfUnity 3 F) = 3 := by
  have hle : Nat.card (rootsOfUnity 3 F) ≤ 3 := card_rootsOfUnity F 3
  have hpos : 0 < Nat.card (rootsOfUnity 3 F) := Nat.card_pos
  have h2 : ¬ 2 ∣ Nat.card (rootsOfUnity 3 F) := by
    intro h
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity 3 F) 2 h
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity 3 (g : Fˣ)).mp g.2)
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    omega
  omega

theorem card_ker_statedProjMk (F : Type) [Field F] [Finite F] :
    Nat.card (statedProjMk (StatedSL 3 F)).ker = 1 ∨
      Nat.card (statedProjMk (StatedSL 3 F)).ker = 3 := by
  have h1 : (statedProjMk (StatedSL 3 F)).ker =
      (center (Matrix.SpecialLinearGroup (Fin 3) F)).map
        (specialLinearGroupEquivStatedSL 3 F :
          Matrix.SpecialLinearGroup (Fin 3) F →* StatedSL 3 F) := by
    rw [map_center_eq_statedScalars, QuotientGroup.ker_mk']
  have h2 : Nat.card ((center (Matrix.SpecialLinearGroup (Fin 3) F)).map
        (specialLinearGroupEquivStatedSL 3 F :
          Matrix.SpecialLinearGroup (Fin 3) F →* StatedSL 3 F)) =
      Nat.card (center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.card_map_of_injective (specialLinearGroupEquivStatedSL 3 F).injective
  have h3 : Nat.card (center (Matrix.SpecialLinearGroup (Fin 3) F)) =
      Nat.card (rootsOfUnity 3 F) := by
    simpa using Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0).toEquiv
  rw [h1, h2, h3]
  exact card_rootsOfUnity_three F

end Kernel

section Main

variable {F : Type} [Field F] [Finite F]

theorem exists_centralizer_quotient (hodd : Odd (Nat.card F))
    {w : StatedProj (StatedSL 3 F)} (hw : orderOf w = 2) :
    ∃ (N : Subgroup (GL (Fin 2) F)) (_ : N.Normal), (Nat.card N = 1 ∨ Nat.card N = 3) ∧
      Nonempty (↥(centralizer ({w} : Set (StatedProj (StatedSL 3 F)))) ≃* GL (Fin 2) F ⧸ N) := by
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  obtain ⟨φ, hφ, hrange⟩ := exists_phi h2 (StatedSL 3 F) (fun A => linConj_mem_statedSL A) ha ha1
  obtain ⟨N, hN, hcard, hiso⟩ := exists_normal_quotient_equiv (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (ker_statedProjMk_le_center _)
    (fun z hz => linConj_ker_pow_three z hz) ha φ hφ hrange
  refine ⟨N, hN, ?_, hiso⟩
  rw [hcard]
  exact card_ker_statedProjMk F

end Main

end Lemma41aL3

theorem ivk_4_1a_L3 : IVK_4_1a_L3 := by
  intro K _ _ p n hp hp2 hK z hz
  rcases hK with ⟨-, F, hF, hFin, hcardF, ⟨e⟩⟩ | ⟨h1, -⟩
  · have hodd : Odd (Nat.card F) := by
      rw [hcardF]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hw : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
    obtain ⟨N, hN, hcard, ⟨iso⟩⟩ := Lemma41aL3.exists_centralizer_quotient hodd hw
    exact ⟨F, hF, hFin, N, hN, hcardF, hcard, ⟨(centralizerEquiv e z).trans iso⟩⟩
  · exact absurd h1 (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
