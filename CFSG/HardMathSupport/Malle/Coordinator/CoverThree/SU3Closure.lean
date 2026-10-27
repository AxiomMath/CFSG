module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.ToralCount
public import CFSG.LieType.SeitzGeneration.UnitaryHyperToral
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem pow_nine_eq_one_of_cube_central_su (h : UnitaryFieldData ℓ f K) (hq : 2 < ℓ ^ f)
    (x : unitarySU ℓ f K 3) (hx : x ^ 3 ∈ Subgroup.center (unitarySU ℓ f K 3)) :
    x ^ 9 = 1 := by
  rw [CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := h) hq,
    mem_unitaryScalars] at hx
  obtain ⟨c, -, hc3, hc⟩ := hx
  apply Subtype.ext
  rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul]
  change (((x ^ 3) ^ 3 : unitarySU ℓ f K 3) : GL (Fin 3) K) = 1
  rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]

theorem su3_closure_centralizers (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    (h9 : 9 ∣ ℓ ^ f + 1) (P : Subgroup (unitarySU ℓ f K 3)) (hPc : IsMulCommutative P)
    (hP : Nat.card P = 27)
    (hPZ : Nat.card (P ⊓ Subgroup.center (unitarySU ℓ f K 3) :
      Subgroup (unitarySU ℓ f K 3)) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center (unitarySU ℓ f K 3)) :
    Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ x ∈ P,
      x ∉ Subgroup.center (unitarySU ℓ f K 3) ∧ g * x = x * g} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hq2 : 2 < ℓ ^ f := by
    have := Nat.le_of_dvd (by positivity) h9
    omega
  have hF9 : 9 ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq]
    have h1 : 1 ≤ ℓ ^ f := by omega
    have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      zify [h1, h2]
      ring
    rw [h3]
    exact Dvd.dvd.mul_right h9 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_nine hF9
  have : NeZero 9 := ⟨by norm_num⟩
  have hle : unitarySU ℓ f K 3 ≤ primeFormUnitary h (idGram K 3) :=
    unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K 3)) := P.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hGexp : ∀ u ∈ G, u ^ 9 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, pow_nine_eq_one_of_cube_central_su h hq2 x (hP3 x hx), map_one]
  obtain ⟨P0, hP0⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hζ h9 G hGcomm
    hGexp
  let Pg : GL (Fin 3) K := (P0 : GL (Fin 3) K)
  let Dg : P → GL (Fin 3) K := fun x =>
    Pg⁻¹ * (((x : unitarySU ℓ f K 3)) : GL (Fin 3) K) * Pg
  have hdiag : ∀ x : P,
      ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    fun x => hP0 (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : P, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin 3 → P →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : P) (c : Fin 3),
      ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((Dg x)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hcube : ∀ (x : P) (a b : Fin 3), χ a x ^ 3 = χ b x ^ 3 := by
    intro x a b
    have hx3 : (x : unitarySU ℓ f K 3) ^ 3 ∈ Subgroup.center (unitarySU ℓ f K 3) := hP3 x x.2
    rw [CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := h) hq2,
      mem_unitaryScalars] at hx3
    obtain ⟨c0, -, -, hc⟩ := hx3
    have hD3 : Dg (x ^ 3) = GeneralLinearGroup.scalar (Fin 3) c0 := by
      show Pg⁻¹ * ((((x : unitarySU ℓ f K 3) ^ 3 : unitarySU ℓ f K 3)) : GL (Fin 3) K) * Pg = _
      rw [hc, mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have hc' : ∀ c : Fin 3, χ c x ^ 3 = (c0 : K) := by
      intro c
      rw [← map_pow]
      change ((Dg (x ^ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) c c = _
      rw [hD3, GeneralLinearGroup.coe_scalar]
      simp
    rw [hc' a, hc' b]
  set Z : Subgroup P := (P ⊓ Subgroup.center (unitarySU ℓ f K 3)).subgroupOf P with hZ
  have hZcard : Nat.card Z = 3 := by
    have h1 : Nat.card Z = Nat.card (P ⊓ Subgroup.center (unitarySU ℓ f K 3) :
        Subgroup (unitarySU ℓ f K 3)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    omega
  have hpair : ∀ i : Fin 2, ∃ x : P, (x : unitarySU ℓ f K 3) ∉ Subgroup.center (unitarySU ℓ f K 3) ∧
      ∀ A : Matrix (Fin 2) (Fin 2) K,
        blockMat (2 + 1) i A * ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * blockMat (2 + 1) i A := by
    intro i
    obtain ⟨x, hxZ, hxe⟩ := exists_notMem_eq_of_hom (χ i.castSucc) (χ i.succ)
      (fun x => hcube x _ _) hP Z hZcard
    refine ⟨x, fun hc => hxZ (Subgroup.mem_subgroupOf.mpr ⟨x.2, hc⟩), fun A => ?_⟩
    have hD : ((Dg x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      hxe A
  refine eq_top_of_blocks_mem (n := 2) h hq P0 _ fun i y A hA => ?_
  obtain ⟨x, hxc, hxD⟩ := hpair i
  refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K 3), x.2, hxc, ?_⟩
  apply Subtype.ext
  have hYD : ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Dg x =
      Dg x * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hA]
    exact hxD A
  have hxeq : (((x : unitarySU ℓ f K 3)) : GL (Fin 3) K) = Pg * Dg x * Pg⁻¹ := by
    simp [Dg, mul_assoc]
  show (Pg * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Pg⁻¹) *
      (((x : unitarySU ℓ f K 3)) : GL (Fin 3) K) =
    (((x : unitarySU ℓ f K 3)) : GL (Fin 3) K) *
      (Pg * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Pg⁻¹)
  rw [hxeq]
  calc Pg * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Pg⁻¹ * (Pg * Dg x * Pg⁻¹)
      = Pg * (((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Dg x) * Pg⁻¹ := by group
    _ = Pg * (Dg x * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K)) * Pg⁻¹ := by rw [hYD]
    _ = Pg * Dg x * Pg⁻¹ * (Pg * ((y : unitarySU ℓ f K 3) : GL (Fin 3) K) * Pg⁻¹) := by group

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
