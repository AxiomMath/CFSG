module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {K : Type} [Field K]

theorem upperTriangular_eq_unitriangular_of_natCard_eq_two (hK : Nat.card K = 2) (n : ℕ) :
    upperTriangular n K = unitriangular n K := by
  refine le_antisymm (fun A hA => ⟨hA, fun i => ?_⟩) (unitriangular_le_upperTriangular n K)
  have hdet : ∏ j, (A : Matrix (Fin n) (Fin n) K) j j = 1 := by
    rw [← Matrix.det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.1 hA)]
    exact A.2
  rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((A : Matrix (Fin n) (Fin n) K) i i) with h | h
  · rw [Finset.prod_eq_zero (f := fun j => (A : Matrix (Fin n) (Fin n) K) j j)
      (Finset.mem_univ i) h] at hdet
    exact absurd hdet zero_ne_one
  · exact h

theorem normalizer_projUnitriangular_of_natCard_eq_two [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (n : ℕ) :
    normalizer (projUnitriangular n K : Set (projectiveSL n K)) = projUnitriangular n K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2, projUpperTriangular,
    upperTriangular_eq_unitriangular_of_natCard_eq_two hK n, projUnitriangular]

theorem normalizer_le_of_isPGroup_of_card_eq [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {n : ℕ} (hn : 1 ≤ n) {S : Subgroup (projectiveSL n K)} (hS : IsPGroup 2 S)
    (hSc : Nat.card S = Nat.card (projUnitriangular n K)) :
    normalizer (S : Set (projectiveSL n K)) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 hn
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have hTc : Nat.card (T : Subgroup (projectiveSL n K)) = Nat.card S := by
    rw [hSc, ← hU₀, Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hTS : (T : Subgroup (projectiveSL n K)) = S := (eq_of_le_of_card_ge hST hTc.le).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL n K) U₀ T
  have hmem : ∀ x, x ∈ S ↔ g⁻¹ * x * g ∈ projUnitriangular n K := by
    intro x
    rw [← hTS, ← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hU₀]
    rfl
  intro x hx
  rw [hmem]
  have key : ∀ u, u ∈ projUnitriangular n K ↔ g * u * g⁻¹ ∈ S := fun u => by
    rw [hmem, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
  have hN : g⁻¹ * x * g ∈ normalizer (projUnitriangular n K : Set (projectiveSL n K)) := by
    rw [mem_normalizer_iff]
    intro u
    rw [key, mem_normalizer_iff.1 hx, hmem,
      show g⁻¹ * (x * (g * u * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * u * (g⁻¹ * x * g)⁻¹ by group]
  rwa [normalizer_projUnitriangular_of_natCard_eq_two hK] at hN

theorem card_projectiveSL_five_of_card_two (hK : Nat.card K = 2) :
    Nat.card (projectiveSL 5 K) = 9999360 := by
  rw [← Nat.card_congr (Equiv.ofBijective (proj 5 K)
    ⟨proj_injective_of_natCard_eq_two hK, proj_surjective 5 K⟩),
    card_specialLinearGroup_five_of_card_two hK]

theorem pointRadical_inf_blockSL_compl_eq_bot (hK : Nat.card K = 2) {n : ℕ} (c : Fin n) :
    pointRadical (K := K) c ⊓ blockSL (K := K) ({c}ᶜ : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxL⟩ := mem_inf.1 hx
  obtain ⟨r, -, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hxV
  obtain ⟨B, hB, hBr⟩ := mem_blockSL.1 hxL
  have hBr' := proj_injective_of_natCard_eq_two hK hBr
  have hr : pointRadElem c r = 1 := by
    rw [← pointRadElem_update_eq c r 0]
    have h0 : Function.update r c 0 = 0 := by
      ext j
      by_cases hj : j = c
      · rw [hj, Function.update_self, Pi.zero_apply]
      · rw [Function.update_of_ne hj, Pi.zero_apply]
        have h1 := pointRadMat_apply_row_of_ne c r hj
        have h2 : (B : Matrix (Fin n) (Fin n) K) c j = (1 : Matrix (Fin n) (Fin n) K) c j :=
          hB c j (Or.inl (by simp))
        rw [hBr', coe_pointRadElem, h1, Matrix.one_apply_ne (Ne.symm hj)] at h2
        exact h2
    rw [h0, pointRadElem_zero]
  rw [hr, map_one]
  exact one_mem _

end Model

section InG

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem mem_of_mem_normalizer_of_card_eq [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) {Q₀ : Subgroup G} (hQL : Q₀ ≤ L) (hQc : Nat.card Q₀ = 2 ^ 10)
    {y : G} (hyL : y ∈ L) (hyN : y ∈ normalizer (Q₀ : Set G)) : y ∈ Q₀ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set S : Subgroup (projectiveSL 5 K) := (Q₀.subgroupOf L).map e.toMonoidHom with hSdef
  have hSc : Nat.card S = 2 ^ 10 := by
    rw [hSdef, card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv, hQc]
  have hSU : Nat.card S = Nat.card (projUnitriangular 5 K) := by
    rw [hSc, card_projUnitriangular, hK]
  have hS : IsPGroup 2 S := IsPGroup.of_card hSc
  have hmem : ∀ x : L, e x ∈ S ↔ (x : G) ∈ Q₀ := fun x => by
    rw [hSdef, mem_map_equiv, MulEquiv.symm_apply_apply, mem_subgroupOf]
  have heN : e ⟨y, hyL⟩ ∈ normalizer (S : Set (projectiveSL 5 K)) := by
    rw [mem_normalizer_iff]
    intro s
    obtain ⟨x, rfl⟩ := e.surjective s
    rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
    exact mem_normalizer_iff.1 hyN x
  have h := normalizer_le_of_isPGroup_of_card_eq hK (by norm_num) hS hSU heN
  exact (hmem _).1 h

theorem card_modelToG_pointRadical (hK : Nat.card K = 2) {n : ℕ}
    (e : L ≃* projectiveSL n K) (c : Fin n) :
    Nat.card (modelToG e (pointRadical (K := K) c)) = 2 ^ (n - 1) := by
  have hcc : c ∉ ({c}ᶜ : Finset (Fin n)) := by simp
  rw [natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
    Finset.card_singleton, Fintype.card_fin]

theorem modelToG_pointRadical_inf_eq_bot (hK : Nat.card K = 2) {n : ℕ}
    (e : L ≃* projectiveSL n K) (c : Fin n) :
    modelToG e (pointRadical (K := K) c) ⊓ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) =
      ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hx1
  obtain ⟨b, hb, hba⟩ := (mem_modelToG e).1 hx2
  have hab : b = a := e.symm.injective (Subtype.ext hba)
  have h1 : a ∈ pointRadical (K := K) c ⊓ blockSL (K := K) ({c}ᶜ : Finset (Fin n)) :=
    mem_inf.2 ⟨ha, hab ▸ hb⟩
  rw [pointRadical_inf_blockSL_compl_eq_bot hK c, mem_bot] at h1
  rw [h1, map_one]
  exact one_mem _

theorem exists_two_subgroup_le_pointRadical_sup_levi [Finite G] (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) (c : Fin 5) :
    ∃ Q₀ : Subgroup G, Q₀ ≤ modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ∧ Nat.card Q₀ = 2 ^ 10 := by
  set H := modelToG e (pointRadical (K := K) c) ⊔
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hH
  have hcard : Nat.card H = 2 ^ 4 * 20160 := by
    rw [hH, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (modelToG_le_normalizer e (blockSL_compl_le_normalizer_pointRadical c))
      (disjoint_iff.2 (modelToG_pointRadical_inf_eq_bot hK e c)),
      card_modelToG_pointRadical hK e c, (modelToG_blockSL_compl_facts e hK c).2.2.2.1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 10)
    (by rw [hcard]; norm_num)
  exact ⟨Q.map H.subtype, map_subtype_le _, by rw [card_map_of_injective H.subtype_injective, hQ]⟩

theorem card_centralizer_eq_of_le_sup [Finite G] (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (hle : centralizer ({t} : Set G) ≤ L ⊔ zpowers t) :
    Nat.card (centralizer ({t} : Set G)) = 2 ^ 11 * 9765 := by
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have hzt : zpowers t ≤ centralizer ({t} : Set G) :=
    (zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl)
  have heq : centralizer ({t} : Set G) = L ⊔ zpowers t := le_antisymm hle (sup_le hLt hzt)
  have hzL : zpowers t ≤ centralizer (L : Set G) := (zpowers_le).2 htC
  rw [heq, card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hzL
    (inf_zpowers_eq_bot hset.center_eq_bot htC ht), Nat.card_congr e.toEquiv,
    card_projectiveSL_five_of_card_two hK, Nat.card_zpowers, ht]
  norm_num

theorem card_le_of_isPGroup_of_le_centralizer [Finite G] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (hle : centralizer ({t} : Set G) ≤ L ⊔ zpowers t)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPt : P ≤ centralizer ({t} : Set G)) :
    Nat.card P ≤ 2 ^ 11 := by
  have hdvd : Nat.card P ∣ 2 ^ 11 * 9765 := by
    rw [← card_centralizer_eq_of_le_sup hset hK e ht htC hle]
    exact Subgroup.card_dvd_of_le hPt
  exact card_le_two_pow_of_isPGroup_of_dvd hP (by decide) hdvd

end InG

end CFSG.SeitzReduction.LinearPilot
