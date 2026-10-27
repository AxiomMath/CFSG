module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36NatStabHat
public import CFSG.Quasithin.MS93.MSPQuad
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAlt6

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

private theorem isGomiModelFix_nat_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {T : Subgroup ↥Γ}
    {m : Multiplicative (ι → K)} :
    IsGomiModelFix (FFModel.nat Γ) T m ↔ ∀ t ∈ T,
      (((t : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
        (Multiplicative.toAdd m) = Multiplicative.toAdd m := by
  unfold IsGomiModelFix
  refine forall₂_congr fun t _ => ?_
  change natAct Γ t m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (ι → K))) ↔ _
  rw [Subgroup.mem_bot, mul_inv_eq_one]
  change Multiplicative.ofAdd _ = m ↔ _
  exact Equiv.apply_eq_iff_eq_symm_apply Multiplicative.ofAdd

section SL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable (K : Type) [Field K]

private theorem exists_sl3_unitri (a b c : K) : ∃ t : Matrix.SpecialLinearGroup (Fin 3) K,
    (t : Matrix (Fin 3) (Fin 3) K) = !![1, a, b; 0, 1, c; 0, 0, 1] :=
  ⟨⟨_, by simp [Matrix.det_fin_three]⟩, rfl⟩

variable {K} in
private theorem mem_unitriangular_of_coe_eq {t : Matrix.SpecialLinearGroup (Fin 3) K} {a b c : K}
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = !![1, a, b; 0, 1, c; 0, 0, 1]) :
    t ∈ unitriangular 3 K := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [ht]
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [ht]
    fin_cases i <;> simp

private theorem sl3_fix_iff (v : Fin 3 → K) :
    (∀ u ∈ unitriangular 3 K, (u : Matrix (Fin 3) (Fin 3) K).mulVec v = v) ↔
      v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    obtain ⟨t01, ht01⟩ := exists_sl3_unitri K 1 0 0
    obtain ⟨t12, ht12⟩ := exists_sl3_unitri K 0 0 1
    have h1 := congrFun (h t01 (mem_unitriangular_of_coe_eq ht01)) 0
    have h2 := congrFun (h t12 (mem_unitriangular_of_coe_eq ht12)) 1
    rw [ht01] at h1
    rw [ht12] at h2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ u hu
    obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hu
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, mul_zero, add_zero]
    fin_cases i
    · simp [hdiag 0]
    · simp [hlow 1 0 (by decide), h1]
    · simp [hlow 2 0 (by decide), h2]

private theorem exists_sylow_statedSL3 [CharP K 2] [Finite K] : ∃ T₀ : Sylow 2 ↥(StatedSL 3 K),
    ∀ x, specialLinearGroupEquivStatedSL 3 K x ∈ (T₀ : Subgroup ↥(StatedSL 3 K)) ↔
      x ∈ unitriangular 3 K := by
  set e := specialLinearGroupEquivStatedSL 3 K
  obtain ⟨U, hU⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, fun x => ?_⟩
  show e x ∈ (U : Subgroup _).map e.toMonoidHom ↔ _
  rw [hU]
  exact ⟨fun ⟨y, hy, hyx⟩ => (e.injective hyx) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

variable {K} in
private theorem sl3_isGomiModelFix_iff {T₀ : Subgroup ↥(StatedSL 3 K)}
    (hT : ∀ x, specialLinearGroupEquivStatedSL 3 K x ∈ T₀ ↔ x ∈ unitriangular 3 K)
    (m : Multiplicative (Fin 3 → K)) :
    IsGomiModelFix (FFModel.nat (StatedSL 3 K)) T₀ m ↔
      Multiplicative.toAdd m 1 = 0 ∧ Multiplicative.toAdd m 2 = 0 := by
  rw [isGomiModelFix_nat_iff, ← sl3_fix_iff]
  constructor
  · intro h u hu
    exact h (specialLinearGroupEquivStatedSL 3 K u) ((hT u).mpr hu)
  · intro h t ht
    obtain ⟨u, rfl⟩ := (specialLinearGroupEquivStatedSL 3 K).surjective t
    exact h u ((hT u).mp ht)

variable {K} in
private theorem sl3_not_mem_normalizer {T₀ : Subgroup ↥(StatedSL 3 K)}
    (hT : ∀ x, specialLinearGroupEquivStatedSL 3 K x ∈ T₀ ↔ x ∈ unitriangular 3 K)
    {P12 : Matrix.SpecialLinearGroup (Fin 3) K}
    (hP12 : (P12 : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0]) :
    specialLinearGroupEquivStatedSL 3 K P12 ∉ Subgroup.normalizer (T₀ : Set ↥(StatedSL 3 K)) := by
  set e := specialLinearGroupEquivStatedSL 3 K
  intro hN
  obtain ⟨T12, hT12⟩ := exists_sl3_unitri K 0 0 1
  have hPP : P12 * P12 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hP12]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h := (Subgroup.mem_normalizer_iff.mp hN (e T12)).mp
    ((hT T12).mpr (mem_unitriangular_of_coe_eq hT12))
  have hinv : (e P12)⁻¹ = e P12 := by rw [← map_inv e, inv_eq_of_mul_eq_one_right hPP]
  change e P12 * e T12 * (e P12)⁻¹ ∈ T₀ at h
  rw [hinv, ← map_mul e, ← map_mul e, hT] at h
  have h21 := (mem_unitriangular.mp h).1 2 1 (by decide)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP12, hT12] at h21
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h21

theorem gomiNatStabModel_sl3 [CharP K 2] [Finite K] :
    GomiNatStabModel (FFModel.nat (StatedSL 3 K)) := by
  refine ⟨FFModel.nat_faithful _, ?_⟩
  set e := specialLinearGroupEquivStatedSL 3 K
  obtain ⟨T₀, hT⟩ := exists_sylow_statedSL3 K
  obtain ⟨P12, hP12⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 3) K,
      (t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩, rfl⟩
  obtain ⟨P01, hP01⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 3) K,
      (t : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] :=
    ⟨⟨_, by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩, rfl⟩
  refine ⟨T₀, e P12, e P01, Multiplicative.ofAdd ![1, 0, 0], sl3_not_mem_normalizer hT hP12,
    fun m' _ hm' => ?_, Subgroup.mem_top _, (sl3_isGomiModelFix_iff hT _).mpr ⟨rfl, rfl⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (sl3_isGomiModelFix_iff hT m').mp hm'
    refine (sl3_isGomiModelFix_iff hT _).mpr ?_
    change ((P12 : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd m')) 1 = 0 ∧
      ((P12 : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd m')) 2 = 0
    rw [hP12]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]
  · intro h
    obtain ⟨h1, -⟩ := (sl3_isGomiModelFix_iff hT _).mp h
    change ((P01 : Matrix (Fin 3) (Fin 3) K).mulVec ![1, 0, 0]) 1 = 0 at h1
    rw [hP01] at h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1

end SL3

section Sp4

open CFSG.Quasithin.MS93.MSP
open scoped Matrix

theorem gomiNatStabModel_sp4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    GomiNatStabModel (FFModel.nat (StatedSp 2 K)) := by
  refine ⟨FFModel.nat_faithful _, ?_⟩
  obtain ⟨S, hS⟩ := exists_sylow_sylS (F := K)
  have hfix : ∀ m : Multiplicative (Fin 2 ⊕ Fin 2 → K), IsGomiModelFix (FFModel.nat (StatedSp 2 K))
      (S : Subgroup (Sp4 K)) m ↔ Multiplicative.toAdd m ∈ pt₀ K := fun m => by
    rw [isGomiModelFix_nat_iff, hS, ← fixSp_sylS, mem_fixSp]
  obtain ⟨g, hgP, hgB⟩ := SetLike.not_le_iff_exists.mp (not_P₂_le_borel (F := K))
  obtain ⟨g', -, hg'⟩ := SetLike.not_le_iff_exists.mp (P₁_not_le_P₂ (F := K))
  obtain ⟨v, hv, hgv⟩ : ∃ v ∈ pt₀ K, mat g' *ᵥ v ∉ pt₀ K := by
    by_contra h
    push Not at h
    exact hg' (mem_stab_of_le h)
  refine ⟨S, g, g', Multiplicative.ofAdd v, fun hN => hgB ?_, fun m' _ hm' => ?_,
    Subgroup.mem_top _, (hfix _).mpr hv, fun h => hgv ((hfix _).mp h)⟩
  · rw [← normalizer_sylS, ← hS]
    exact hN
  · exact (hfix _).mpr (mulVec_mem_of_mem_stab hgP ((hfix m').mp hm'))

end Sp4

section Alt6

open CFSG.Quasithin.G6 CFSG.Quasithin.H13.Lem1227Eq CFSG.Quasithin.H13.A6 Equiv

private theorem alt6_natStab_checks :
    (swap 0 2 * swap 0 1 : Perm (Fin 6)) ∉ QA6list ∧
      (∀ x : PermMod 6, PM (Multiplicative.toAdd x) →
        PM (Multiplicative.toAdd (permAct 6 (swap 0 2 * swap 0 1) x))) ∧
      Multiplicative.ofAdd ![(0 : ZMod 2), 0, 0, 0, 1, 1] ∈ coreMod 6 ∧
      PM (Multiplicative.toAdd (Multiplicative.ofAdd ![(0 : ZMod 2), 0, 0, 0, 1, 1])) ∧
      ¬ PM (Multiplicative.toAdd (permAct 6 (swap 0 4 * swap 1 5)
        (Multiplicative.ofAdd ![(0 : ZMod 2), 0, 0, 0, 1, 1]))) :=
  ⟨by decide +kernel, by decide +kernel, mem_coreMod.mpr (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

private theorem alt6_natStab_mem :
    (swap 0 2 * swap 0 1 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) ∧
      (swap 0 4 * swap 1 5 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
  ⟨Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel),
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem gomiNatStabModel_alt6 : GomiNatStabModel (FFModel.altDn 6) := by
  obtain ⟨hc3, hc3fix, hm, hmfix, hmove⟩ := alt6_natStab_checks
  refine ⟨FFC.altDn_faithful (by norm_num), ?_⟩
  obtain ⟨-, hS2, hSi⟩ := isSylowTwoOf_S6
  have hSi' : ¬ 2 ∣ S6.index := by
    rwa [show (S6.subgroupOf ⊤).index = S6.index from Subgroup.relIndex_top_right S6] at hSi
  have hfix : ∀ m ∈ coreMod 6, IsGomiModelFix (FFModel.altDn 6) S6 m ↔
      PM (Multiplicative.toAdd m) := fun m hm => by
    rw [← mem_Msub_S6, mem_Msub]
    exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩
  refine ⟨hS2.toSylow hSi', ⟨swap 0 2 * swap 0 1, alt6_natStab_mem.1⟩,
    ⟨swap 0 4 * swap 1 5, alt6_natStab_mem.2⟩,
    Multiplicative.ofAdd ![0, 0, 0, 0, 1, 1], fun h => ?_, fun m' hm' hfm' => ?_, hm,
    (hfix _ hm).mpr hmfix, fun h => hmove ((hfix _ (permAct_mem_coreMod _ hm)).mp h)⟩
  · rw [IsPGroup.toSylow_coe] at h
    have h' : (⟨swap 0 2 * swap 0 1, alt6_natStab_mem.1⟩ : Alt6) ∈
        Subgroup.normalizer ((S6 : Subgroup Alt6) : Set Alt6) := h
    rw [normalizer_S6] at h'
    have h'' : (swap 0 2 * swap 0 1 : Perm (Fin 6)) ∈ Dsub := Subgroup.mem_subgroupOf.1 h'
    exact hc3 (mem_Dsub.1 h'')
  · exact (hfix _ (permAct_mem_coreMod _ hm')).mpr (hc3fix _ ((hfix m' hm').mp hfm'))

end Alt6

open scoped Pointwise in
theorem gomiFact36NatStab_holds : GomiFact36NatStab := by
  intro W _ _ _ L T I Z hT h
  rcases h with ⟨a, ha, K, _, _, hK, hR⟩ | ⟨a, ha, K, _, _, hK, hR⟩ | hR |
    ⟨K, _, _, Γ₀, hK, hdet, hhat, hcen, hR⟩
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two ha hK
    exact natStab_of_gomiNatStabModel (gomiNatStabModel_sl3 K) hR hT
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    exact natStab_of_gomiNatStabModel (gomiNatStabModel_sp4 K) hR hT
  · exact natStab_of_gomiNatStabModel gomiNatStabModel_alt6 hR hT
  · exact natStab_of_gomiNatStabModel (gomiNatStabModel_tripleA6 hK hdet hhat hcen) hR hT

end CFSG.GroupTheory

end
