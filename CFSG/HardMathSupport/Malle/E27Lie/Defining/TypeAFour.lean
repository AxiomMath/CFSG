module

public import CFSG.HardMathSupport.Malle.Proving.E27UnipotentCube
public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.Adapters.LinearCatalog
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Unitriangular
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Foote.E27 TauCeti

variable {K : Type*} [Field K]

theorem card_le_card_ker_of_range_le_ker {A C : Type*} [AddGroup A] [AddGroup C] [Finite A]
    (f : A →+ A) (g : A →+ C) (hg : Function.Surjective g) (h : f.range ≤ g.ker) :
    Nat.card C ≤ Nat.card f.ker := by
  have h1 := AddSubgroup.card_ker_mul_card_range g
  rw [AddMonoidHom.range_eq_top_of_surjective _ hg, AddSubgroup.card_top] at h1
  have h2 := AddSubgroup.card_ker_mul_card_range f
  have h3 : Nat.card f.range ≤ Nat.card g.ker := AddSubgroup.card_le_of_le h
  have hpos : 0 < Nat.card g.ker := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card g.ker * Nat.card C = Nat.card f.ker * Nat.card f.range := by rw [h1, h2]
    _ ≤ Nat.card f.ker * Nat.card g.ker := Nat.mul_le_mul_left _ h3
    _ = Nat.card g.ker * Nat.card f.ker := mul_comm _ _

theorem mul_apply_zero_two {X Y : Matrix (Fin 4) (Fin 4) K} (hX : X ∈ strictUpper 4 K)
    (hY : Y ∈ strictUpper 4 K) : (X * Y) 0 2 = X 0 1 * Y 1 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hX 0 0 le_rfl, hY 2 2 le_rfl, hY 3 2 (by decide)]
  ring

theorem mul_apply_one_three {X Y : Matrix (Fin 4) (Fin 4) K} (hX : X ∈ strictUpper 4 K)
    (hY : Y ∈ strictUpper 4 K) : (X * Y) 1 3 = X 1 2 * Y 2 3 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hX 1 0 (by decide), hX 1 1 le_rfl, hY 3 3 le_rfl]
  ring

theorem pow_four_le_card_ker_adStrict_four [Finite K] {X : Matrix (Fin 4) (Fin 4) K}
    (hX : X ∈ strictUpper 4 K) (h12 : X 1 2 = 0) :
    Nat.card K ^ 4 ≤ Nat.card (adStrict hX).ker := by
  obtain ⟨α, β, hαβ, hne⟩ : ∃ α β : K, α * X 0 1 = β * X 2 3 ∧ (α ≠ 0 ∨ β ≠ 0) := by
    by_cases h : X 0 1 = 0 ∧ X 2 3 = 0
    · exact ⟨1, 0, by rw [h.1, h.2]; ring, Or.inl one_ne_zero⟩
    · refine ⟨X 2 3, X 0 1, mul_comm _ _, ?_⟩
      by_contra hc
      push Not at hc
      exact h ⟨hc.2, hc.1⟩
  let ℓ : strictUpper 4 K →+ K :=
    { toFun := fun M => α * (M : Matrix (Fin 4) (Fin 4) K) 0 2 +
        β * (M : Matrix (Fin 4) (Fin 4) K) 1 3
      map_zero' := by simp
      map_add' := fun M M' => by
        simp only [AddSubgroup.coe_add, Matrix.add_apply]
        ring }
  let Φ : strictUpper 4 K →+ (Fin (4 - 1) → K) × K := (superdiag 4 K).prod ℓ
  have hΦ : Function.Surjective Φ := by
    rintro ⟨v, c⟩
    obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := 4) (K := K) v
    rcases hne with hα | hβ
    · let E : strictUpper 4 K := ⟨single 0 2 ((c - ℓ M₀) / α), strict_single (by decide) _⟩
      refine ⟨M₀ + E, Prod.ext ?_ ?_⟩
      · show superdiag 4 K (M₀ + E) = v
        rw [map_add, hM₀]
        conv_rhs => rw [← add_zero v]
        congr 1
        funext i
        fin_cases i <;> (rw [superdiag_apply]; simp [E])
      · show ℓ (M₀ + E) = c
        rw [map_add]
        simp only [ℓ, E, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        simp
        field_simp
        ring
    · let E : strictUpper 4 K := ⟨single 1 3 ((c - ℓ M₀) / β), strict_single (by decide) _⟩
      refine ⟨M₀ + E, Prod.ext ?_ ?_⟩
      · show superdiag 4 K (M₀ + E) = v
        rw [map_add, hM₀]
        conv_rhs => rw [← add_zero v]
        congr 1
        funext i
        fin_cases i <;> (rw [superdiag_apply]; simp [E])
      · show ℓ (M₀ + E) = c
        rw [map_add]
        simp only [ℓ, E, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        simp
        field_simp
        ring
  have hrange : (adStrict hX).range ≤ Φ.ker := by
    rintro _ ⟨Y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    refine Prod.ext ?_ ?_
    · exact AddMonoidHom.mem_ker.mp (range_adStrict_le hX ⟨Y, rfl⟩)
    · show α * (X * (Y : Matrix (Fin 4) (Fin 4) K) - (Y : Matrix (Fin 4) (Fin 4) K) * X) 0 2 +
        β * (X * (Y : Matrix (Fin 4) (Fin 4) K) - (Y : Matrix (Fin 4) (Fin 4) K) * X) 1 3 = 0
      rw [Matrix.sub_apply, Matrix.sub_apply, mul_apply_zero_two hX Y.2, mul_apply_zero_two Y.2 hX,
        mul_apply_one_three hX Y.2, mul_apply_one_three Y.2 hX, h12]
      linear_combination ((Y : Matrix (Fin 4) (Fin 4) K) 1 2) * hαβ
  have := card_le_card_ker_of_range_le_ker _ _ hΦ hrange
  rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (4 - 1)), Fintype.card_fin]
    at this
  calc Nat.card K ^ 4 = Nat.card K ^ (4 - 1) * Nat.card K := by rw [← pow_succ]
    _ ≤ _ := this

theorem coe_eq_of_mem_unitriangular_four {A : SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ unitriangular 4 K) :
    (A : Matrix (Fin 4) (Fin 4) K) =
      !![1, (A : Matrix (Fin 4) (Fin 4) K) 0 1, (A : Matrix (Fin 4) (Fin 4) K) 0 2,
        (A : Matrix (Fin 4) (Fin 4) K) 0 3;
        0, 1, (A : Matrix (Fin 4) (Fin 4) K) 1 2, (A : Matrix (Fin 4) (Fin 4) K) 1 3;
        0, 0, 1, (A : Matrix (Fin 4) (Fin 4) K) 2 3;
        0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hA.2] <;> exact hA.1 _ _ (by decide)

theorem det_unitriangular_four (a b c d e f : K) :
    (!![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem mem_unitriangular_four (a b c d e f : K) (h) :
    (⟨!![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1], h⟩ : SpecialLinearGroup (Fin 4) K) ∈
      unitriangular 4 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  · fin_cases i <;> simp

theorem det_conj_zero_one (c : K) :
    (!![0, -1, 0, 0; 1, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rfl

theorem det_conj_two_three (c : K) :
    (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, c] : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem exists_conj_of_zero_one {A : SpecialLinearGroup (Fin 4) K} (hA : A ∈ unitriangular 4 K)
    (h01 : (A : Matrix (Fin 4) (Fin 4) K) 0 1 = 0) (h12 : (A : Matrix (Fin 4) (Fin 4) K) 1 2 ≠ 0) :
    ∃ g B : SpecialLinearGroup (Fin 4) K, B ∈ unitriangular 4 K ∧
      (B : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ B * g = g * A := by
  set a := (A : Matrix (Fin 4) (Fin 4) K) with ha
  have hAe := coe_eq_of_mem_unitriangular_four hA
  rw [← ha] at hAe
  set c := -(a 0 2 / a 1 2) with hc
  have hmat : (!![1, 0, -a 1 2, -a 1 3; 0, 1, 0, a 0 3 + c * a 1 3; 0, 0, 1, a 2 3; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) K) * !![0, -1, 0, 0; 1, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, -1, 0, 0; 1, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * a := by
    conv_rhs => rw [hAe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h01, hc]
    field_simp
    ring
  exact ⟨⟨_, det_conj_zero_one c⟩, ⟨_, det_unitriangular_four _ _ _ _ _ _⟩,
    mem_unitriangular_four _ _ _ _ _ _ _, by simp, Subtype.ext hmat⟩

theorem exists_conj_of_two_three {A : SpecialLinearGroup (Fin 4) K} (hA : A ∈ unitriangular 4 K)
    (h23 : (A : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) (h12 : (A : Matrix (Fin 4) (Fin 4) K) 1 2 ≠ 0) :
    ∃ g B : SpecialLinearGroup (Fin 4) K, B ∈ unitriangular 4 K ∧
      (B : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ B * g = g * A := by
  set a := (A : Matrix (Fin 4) (Fin 4) K) with ha
  have hAe := coe_eq_of_mem_unitriangular_four hA
  rw [← ha] at hAe
  set c := a 1 3 / a 1 2 with hc
  have hmat : (!![1, a 0 1, c * a 0 2 - a 0 3, a 0 2; 0, 1, 0, a 1 2; 0, 0, 1, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) K) * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, c] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, c] * a := by
    conv_rhs => rw [hAe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h23, hc] <;>
      field_simp
    ring
  exact ⟨⟨_, det_conj_two_three c⟩, ⟨_, det_unitriangular_four _ _ _ _ _ _⟩,
    mem_unitriangular_four _ _ _ _ _ _ _, by simp, Subtype.ext hmat⟩

theorem card_centralizer_proj_eq_of_mul_eq {n : ℕ} {A B g : SpecialLinearGroup (Fin n) K}
    (h : B * g = g * A) :
    Nat.card (Subgroup.centralizer ({proj n K B} : Set (projectiveSL n K))) =
      Nat.card (Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) := by
  have hB : B = g * A * g⁻¹ := eq_mul_inv_of_mul_eq h
  have := card_centralizer_map_equiv (MulAut.conj (proj n K g)) (proj n K A)
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hB] at this
  exact this

theorem three_le_card_of_charP_three [Finite K] [CharP K 3] : 3 ≤ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  calc 3 = Nat.card (ZMod 3) := by rw [Nat.card_eq_fintype_card, ZMod.card]
    _ ≤ Nat.card K := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl 3) K).injective

theorem dvd81_card_centralizer_of_one_two [Finite K] [CharP K 3]
    {B : SpecialLinearGroup (Fin 4) K} (hB : B ∈ unitriangular 4 K)
    (h12 : (B : Matrix (Fin 4) (Fin 4) K) 1 2 = 0) :
    81 ∣ Nat.card (Subgroup.centralizer ({proj 4 K B} : Set (projectiveSL 4 K))) := by
  have hX12 : ((B : Matrix (Fin 4) (Fin 4) K) - 1) 1 2 = 0 := by
    rw [Matrix.sub_apply, h12, Matrix.one_apply_ne (by decide), sub_zero]
  have h1 := pow_four_le_card_ker_adStrict_four (strict_of_mem hB) hX12
  have h2 := card_ker_adStrict_le_card_unitriangular_inf_centralizer hB
  have h3 := card_unitriangular_inf_centralizer_le_card_proj (n := 4) B
  have hK : 81 ≤ Nat.card K ^ 4 :=
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left three_le_card_of_charP_three 4
  have hd := dvd81_card_projUnitriangular_inf_centralizer_of_le (n := 4) (by norm_num)
    (hK.trans (h1.trans (h2.trans h3)))
  exact hd.trans (Subgroup.card_dvd_of_le inf_le_right)

theorem dvd81_card_centralizer_four [Finite K] [CharP K 3] {A : SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ unitriangular 4 K) (h3 : proj 4 K A ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({proj 4 K A} : Set (projectiveSL 4 K))) := by
  by_cases h12 : (A : Matrix (Fin 4) (Fin 4) K) 1 2 = 0
  · exact dvd81_card_centralizer_of_one_two hA h12
  by_cases h01 : (A : Matrix (Fin 4) (Fin 4) K) 0 1 = 0
  · obtain ⟨g, B, hB, hB12, hBg⟩ := exists_conj_of_zero_one hA h01 h12
    rw [← card_centralizer_proj_eq_of_mul_eq hBg]
    exact dvd81_card_centralizer_of_one_two hB hB12
  by_cases h23 : (A : Matrix (Fin 4) (Fin 4) K) 2 3 = 0
  · obtain ⟨g, B, hB, hB12, hBg⟩ := exists_conj_of_two_three hA h23 h12
    rw [← card_centralizer_proj_eq_of_mul_eq hBg]
    exact dvd81_card_centralizer_of_one_two hB hB12
  exact absurd h3 (Proving.proj_pow_three_ne_one_four hA h01 h12 h23)

theorem false_of_typeA_three_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower)
    (hv : (LieTypeIndex.A 3 q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.A 3 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField q.p q.exponent
  have : CharP F 3 := hp ▸ (inferInstance : CharP F q.p)
  let ψ : ↥K ≃* projectiveSL 4 F :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F)
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 3 (n := 4) (by norm_num)
  refine h.false_of_centralizer_kill hz ψ (P : Subgroup (projectiveSL 4 F))
    P.card_eq_multiplicity fun s hs hs3 _ => ?_
  rw [hP] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact dvd81_card_centralizer_four hA hs3

end CFSG.HardMathSupport.Malle.E27Lie
