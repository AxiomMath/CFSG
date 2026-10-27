module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBIClassical
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier GriessAllModelsStatement)
open CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover
open scoped commutatorElement

theorem lbi_exists_cube_root {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hc]; exact h)
  refine ⟨ω, ?_, by rw [← hω]; exact pow_orderOf_eq_one ω⟩
  intro h1
  rw [h1, orderOf_one] at hω
  omega

theorem lbi_det_statedSL {K : Type} [Field K] :
    ∀ s ∈ StatedSL 3 K, (s : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  lbi_det_of_closure (fun _ hA => hA)

theorem lbi_det_statedSU {K : Type} [Field K] (q : ℕ) :
    ∀ s ∈ StatedSU 3 q K, (s : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  lbi_det_of_closure (fun _ hA => hA.1)

theorem lbi_scalar_det {K : Type} [Field K] (ω : Kˣ) (h3 : ω ^ 3 = 1) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar]
  simp [h3]

theorem lbi_scalar_mem_statedSL {K : Type} [Field K] (ω : Kˣ) (h3 : ω ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ StatedSL 3 K :=
  Subgroup.subset_closure (lbi_scalar_det ω h3)

theorem lbi_scalar_mem_statedSU {K : Type} [Field K] (q : ℕ) (hq0 : q ≠ 0) (ω : Kˣ)
    (h3 : ω ^ 3 = 1) (hq : ω ^ (q + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨lbi_scalar_det ω h3, ?_⟩
  have h : (ω : K) ^ q * ω = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hq
    simpa [pow_succ] using this
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, h]
  · simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hij, zero_pow hq0]

theorem lbi_L3 (hG : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (h3 : IsPGroup 3 (Subgroup.center Y))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 3 K)) :
    LocalBalance.IsExtremalType Y ∨ LocalBalance.IsSLThreeEps Y := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hn⟩ := FiniteField.card' K
  have hadm : StatedLieAdmissible .PSL 3 p n := ⟨hp, n.pos, by norm_num, by simp, by simp⟩
  have hLie : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSL 3 p n :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hn],
      ⟨e⟩⟩⟩
  obtain ⟨-, ⟨eH⟩⟩ := hG _ .PSL 3 p n hLie
  obtain ⟨hfin, hdvd⟩ := lbi_card_table_L3 p n
  have : Finite (CFSG.Blueprint.Multiplier.generic .PSL 3 p n ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 p n) := hfin
  obtain ⟨ω, hω1, hω3⟩ := lbi_exists_cube_root (K := K) (by omega)
  have hperf : Group.IsPerfect ↥(StatedSL 3 K) := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (le_refl 3)
    exact Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 K).surjective
  rcases lbi_family hq h3 (StatedSL 3 K) lbi_det_statedSL hperf ω hω1
    (lbi_scalar_mem_statedSL ω hω3) e eH hdvd with hbot | hiso
  · left
    have e' : Y ≃* Y ⧸ Subgroup.center Y :=
      (QuotientGroup.quotientBot (G := Y)).symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    exact Or.inl ⟨K, inferInstance, inferInstance, hK, ⟨e'.trans e⟩⟩
  · right
    exact Or.inl ⟨K, inferInstance, inferInstance, hK, hiso⟩

theorem lbi_scalar_injective {K : Type} [Field K] {c c' : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin 3) c = Matrix.GeneralLinearGroup.scalar (Fin 3) c') :
    c = c' := by
  have := congrArg (fun s : Matrix.GeneralLinearGroup (Fin 3) K =>
    (s : Matrix (Fin 3) (Fin 3) K) 0 0) h
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.coe_scalar] using this

theorem lbi_U3_two {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 2)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 3 2 K)) : False := by
  classical
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K) := StatedSU 3 2 K
  have hS216 : Nat.card S = 216 := by
    have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.card_statedSU_three_two_of_card_four
      (K := K) (by simpa using hK)
    simpa using this
  obtain ⟨ω, hω1, hω3⟩ := lbi_exists_cube_root (K := K) (by rw [hK]; norm_num)
  have hωS : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ S :=
    lbi_scalar_mem_statedSU 2 (by norm_num) ω hω3 (by simpa using hω3)
  let θ : ↥S →* Y ⧸ Subgroup.center Y := e.symm.toMonoidHom.comp (statedProjMk S)
  have hθker : θ.ker = (statedProjMk S).ker := by
    ext w
    simp only [MonoidHom.mem_ker]
    exact e.symm.map_eq_one_iff
  have hθ : Function.Surjective θ := e.symm.surjective.comp (statedProjMk_surjective S)
  have hexp : ∀ w ∈ (statedProjMk S).ker, w ^ 3 = 1 := lbi_proj_exp S (lbi_det_statedSU 2)
  have hge : 3 ≤ Nat.card (statedProjMk S).ker :=
    lbi_card_ge_three _ hexp _ (lbi_scalar_mem_ker S ω hωS) (lbi_scalar_ne_one S ω hω1 hωS)
  have hle : Nat.card (statedProjMk S).ker ≤ 3 := by
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Kˣ →* Matrix.GeneralLinearGroup (Fin 3) K) := fun a b h => lbi_scalar_injective h
    have hsc : Nat.card (StatedScalars (Fin 3) K) = 3 := by
      show Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Kˣ →* Matrix.GeneralLinearGroup (Fin 3) K).range = 3
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
      norm_num
    have hmap : ((statedProjMk S).ker.map S.subtype) ≤ StatedScalars (Fin 3) K := by
      rintro _ ⟨w, hw, rfl⟩
      rw [statedProjMk, QuotientGroup.ker_mk'] at hw
      exact Subgroup.mem_subgroupOf.1 hw
    have := Subgroup.card_le_of_le hmap
    rwa [Subgroup.card_map_of_injective S.subtype_injective, hsc] at this
  have hk3 : Nat.card θ.ker = 3 := by rw [hθker]; exact le_antisymm hle hge
  have hcS := Subgroup.card_ker_mul_card_of_surjective hθ
  rw [hk3, hS216] at hcS
  have hX : Nat.card (Y ⧸ Subgroup.center Y) = 72 := by omega
  exact CFSG.Quasithin.Background.Harris.OrdinaryProofs.not_isSimpleGroup_of_card_72 hX hq.2

theorem lbi_U3 (hG : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (h3 : IsPGroup 3 (Subgroup.center Y))
    {K : Type} [Field K] [Finite K] {q : ℕ} (hKq : Nat.card K = q ^ 2) (hq3 : q % 3 = 2)
    (hq8 : q ≠ 8) (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 3 q K)) :
    LocalBalance.IsExtremalType Y ∨ LocalBalance.IsSLThreeEps Y := by
  classical
  by_cases hq2 : q = 2
  · subst hq2
    exact (lbi_U3_two hq hKq e).elim
  have hq0 : q ≠ 0 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hn⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp⟩
  have hqd : q ∣ p ^ (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card] at hn
    rw [← hn, hKq]
    exact Dvd.intro_left _ (by ring)
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hq3
    · exact h
  have hadm : StatedLieAdmissible .PSU 3 p m := ⟨hp, hm, le_refl 3, by simpa using hq2⟩
  have hLie : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSU 3 p m :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hKq, ⟨e⟩⟩⟩
  obtain ⟨-, ⟨eH⟩⟩ := hG _ .PSU 3 p m hLie
  obtain ⟨hfin, hdvd⟩ := lbi_card_table_U3 p m
  have : Finite (CFSG.Blueprint.Multiplier.generic .PSU 3 p m ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 3 p m) := hfin
  have hsq : (p ^ m) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
  obtain ⟨ω, hω1, hω3⟩ := lbi_exists_cube_root (K := K) (by rw [hKq]; omega)
  have hω : ω ^ (p ^ m + 1) = 1 := by
    obtain ⟨c, hc⟩ : 3 ∣ p ^ m + 1 := by omega
    rw [hc, pow_mul, hω3, one_pow]
  have hperf : Group.IsPerfect ↥(StatedSU 3 (p ^ m) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hKq (n := 3) (le_refl 3) (by simpa using hq2)
  rcases lbi_family hq h3 (StatedSU 3 (p ^ m) K) (lbi_det_statedSU _) hperf ω hω1
    (lbi_scalar_mem_statedSU _ hq0 ω hω3 hω) e eH hdvd with hbot | hiso
  · left
    have e' : Y ≃* Y ⧸ Subgroup.center Y :=
      (QuotientGroup.quotientBot (G := Y)).symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    exact Or.inr ⟨K, inferInstance, inferInstance, _, hKq, hq3, hq8, ⟨e'.trans e⟩⟩
  · right
    exact Or.inr ⟨K, inferInstance, inferInstance, _, hKq, hq3, hq8, hiso⟩

theorem lbiInput6_1_of_griess (hG : GriessAllModelsStatement) : LocalBalance.Lemma510Ns.Input6_1 := by
  intro Y _ _ hq h3 hext
  rcases hext with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hKq, hq3, hq8, ⟨e⟩⟩
  · exact lbi_L3 hG hq h3 hK e
  · exact lbi_U3 hG hq h3 hKq hq3 hq8 e

end CFSG.HardMathSupport.Solomon.Coordinator
