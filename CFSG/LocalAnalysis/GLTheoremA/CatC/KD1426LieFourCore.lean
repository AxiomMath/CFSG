module

public import CFSG.GroupTheory.HuppertProduct.CubeIdentity
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open Matrix CFSG.Open CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

noncomputable def cubeScalar (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) (b : B) : Kˣ :=
  (exists_scalar_of_mem_zPi hK hq hτ hτ1 (hB b b.2)).choose

theorem cubeScalar_spec (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) (b : B) :
    (b : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (cubeScalar hK hq hτ hτ1 hB b) :=
  ((exists_scalar_of_mem_zPi hK hq hτ hτ1 (hB b b.2)).choose_spec.2).symm

theorem cubeScalar_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) :
    cubeScalar hK hq hτ hτ1 hB (1 : B) = 1 := by
  apply scalar_injective_three
  rw [map_one]
  simpa using (cubeScalar_spec hK hq hτ hτ1 hB (1 : B)).symm

theorem cube_mul_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K) (b c : B) :
    ((b * c : B) : GL (Fin 3) K) ^ 3 =
      (b : GL (Fin 3) K) ^ 3 * (c : GL (Fin 3) K) ^ 3 := by
  have hzc : ⁅(c : GL (Fin 3) K), (b : GL (Fin 3) K)⁆ ∈ zPi π 3 (p ^ f) K :=
    hBc c c.2 b b.2
  have hzcS : ⁅(c : GL (Fin 3) K), (b : GL (Fin 3) K)⁆ ∈ StatedScalars (Fin 3) K :=
    mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hzc
  have hcb : Commute (c : GL (Fin 3) K) ⁅(c : GL (Fin 3) K), (b : GL (Fin 3) K)⁆ :=
    (commute_of_mem_statedScalars hzcS (c : GL (Fin 3) K) : _)
  have hzpow : ⁅(c : GL (Fin 3) K), (b : GL (Fin 3) K)⁆ ^ 3 = 1 := by
    rw [Commute.commutatorElement_pow_left hcb 3]
    have hc3S : ((c : GL (Fin 3) K) ^ 3) ∈ StatedScalars (Fin 3) K :=
      mem_statedScalars_of_mem_zPi hK hq hτ hτ1 (hB c c.2)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (commute_of_mem_statedScalars hc3S (b : GL (Fin 3) K)).symm
  have hzb : Commute ⁅(c : GL (Fin 3) K), (b : GL (Fin 3) K)⁆ (b : GL (Fin 3) K) :=
    (commute_of_mem_statedScalars hzcS (b : GL (Fin 3) K)).symm
  change ((b : GL (Fin 3) K) * (c : GL (Fin 3) K)) ^ 3 =
    (b : GL (Fin 3) K) ^ 3 * (c : GL (Fin 3) K) ^ 3
  rw [CFSG.GroupTheory.HuppertProduct.mul_pow_three_of_commute hzb hcb.symm, hzpow, one_mul]

theorem cubeScalar_mul (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K) (b c : B) :
    cubeScalar hK hq hτ hτ1 hB (b * c) =
      cubeScalar hK hq hτ hτ1 hB b * cubeScalar hK hq hτ hτ1 hB c := by
  apply scalar_injective_three
  rw [map_mul, ← cubeScalar_spec hK hq hτ hτ1 hB (b * c),
    ← cubeScalar_spec hK hq hτ hτ1 hB b, ← cubeScalar_spec hK hq hτ hτ1 hB c]
  exact cube_mul_eq hK hq hτ hτ1 hB hBc b c

theorem exists_cube_split_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9) :
    ∃ b ∈ B, b ∉ zPi π 3 (p ^ f) K ∧ ∃ μ : Kˣ,
      (b : GL (Fin 3) K) ^ 3 = (GeneralLinearGroup.scalar (Fin 3) μ) ^ 3 := by
  classical
  haveI : Finite K := hK.finite
  set Z : Subgroup (GL (Fin 3) K) := zPi π 3 (p ^ f) K with hZdef
  set cubes : Subgroup Kˣ := (powMonoidHom (3 : ℕ) : Kˣ →* Kˣ).range with hcubes
  have hquot : Nat.card (Kˣ ⧸ cubes) = 3 := by
    haveI : IsCyclic Kˣ := inferInstance
    have hindex : cubes.index = Nat.card (powMonoidHom (3 : ℕ) : Kˣ →* Kˣ).ker :=
      Subgroup.index_range
    rw [← Subgroup.index_eq_card, hindex, IsCyclic.card_powMonoidHom_ker]
    have hcard : Nat.card K = piCard π (p ^ f) := hK.card
    have h3dvd : 3 ∣ Nat.card K - 1 := by
      cases π
      · change p ^ f % 3 = 2 at hq
        rw [hcard]
        simp only [piCard, Bool.cond_false]
        have hq' : p ^ f ≡ 2 [MOD 3] := by
          simpa [Nat.ModEq] using hq
        have hsq : (p ^ f) ^ 2 ≡ 1 [MOD 3] := by
          have h2 : (2 : ℕ) ^ 2 ≡ 1 [MOD 3] := by decide
          exact (hq'.pow 2).trans h2
        exact hsq.symm.dvd'
      · change p ^ f % 3 = 1 at hq
        rw [hcard]
        simp only [piCard, Bool.cond_true]
        omega
    have hunits : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units (α := K)
    rw [hunits]
    exact Nat.gcd_eq_right h3dvd
  let ψ : B →* Kˣ :=
    { toFun := cubeScalar hK hq hτ hτ1 hB
      map_one' := cubeScalar_one hK hq hτ hτ1 hB
      map_mul' := cubeScalar_mul hK hq hτ hτ1 hB hBc }
  let φ : B →* Kˣ ⧸ cubes := (QuotientGroup.mk' cubes).comp ψ
  have hZker : Z.subgroupOf B ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' cubes) (cubeScalar hK hq hτ hτ1 hB z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨η, hη, hzη⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
    refine ⟨η, ?_⟩
    show η ^ 3 = cubeScalar hK hq hτ hτ1 hB z
    apply scalar_injective_three
    rw [map_pow, ← cubeScalar_spec hK hq hτ hτ1 hB z,
      show ((z : B) : GL (Fin 3) K) = B.subtype z from rfl, ← hzη]
  have hrange : Nat.card φ.range ≤ 3 := by
    calc Nat.card φ.range ≤ Nat.card (⊤ : Subgroup (Kˣ ⧸ cubes)) :=
          Subgroup.card_le_of_le le_top
      _ = Nat.card (Kˣ ⧸ cubes) := Subgroup.card_top
      _ = 3 := hquot
  have hBcard : Nat.card B = 9 * Nat.card Z := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := B)
    rw [inf_of_le_left hZB, hB9] at h
    exact h.symm
  have hlt : Nat.card (Z.subgroupOf B) < Nat.card φ.ker := by
    have hZcard : Nat.card (Z.subgroupOf B) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv
    have hker := Subgroup.card_ker_mul_card_range φ
    have hBle : Nat.card B ≤ 3 * Nat.card φ.ker := by
      rw [← hker]
      calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
            Nat.mul_le_mul_left _ hrange
        _ = 3 * Nat.card φ.ker := by ring
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    rw [hZcard]
    omega
  have hne : Z.subgroupOf B ≠ φ.ker := by
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨b, hbker, hbZ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hZker hne)
  have hbZ' : b.1 ∉ Z := fun hb' => hbZ (by simpa [Subgroup.mem_subgroupOf] using hb')
  rw [MonoidHom.mem_ker] at hbker
  have hψ : ψ b ∈ cubes := by
    simpa only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] using hbker
  obtain ⟨μ, hμ⟩ := hψ
  refine ⟨b.1, b.2, hbZ', μ, ?_⟩
  have hμ' : cubeScalar hK hq hτ hτ1 hB b = μ ^ 3 := by
    change ψ b = μ ^ 3
    rw [← hμ]
    rfl
  rw [cubeScalar_spec hK hq hτ hτ1 hB b, hμ', map_pow]

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
