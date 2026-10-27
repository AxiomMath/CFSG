module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenFacts
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenTCLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Gen
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
open scoped commutatorElement

instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

@[expose] noncomputable def planeDZ : Subgroup Gmat := Subgroup.closure ({dG, zG} : Set Gmat)

@[expose] noncomputable def planeDX : Subgroup Gmat := Subgroup.closure ({dG, xG} : Set Gmat)

@[expose] noncomputable def planeDY : Subgroup Gmat := Subgroup.closure ({dG, y7G} : Set Gmat)

@[expose] noncomputable def heisS : Subgroup Gmat := Subgroup.closure ({xG, eG} : Set Gmat)

@[expose] noncomputable def pGrp : Subgroup Gmat := Subgroup.zpowers dG ⊔ heisS

theorem comm_fin2 {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    ∀ i j : Fin 2, (![a, b] : Fin 2 → G) i * (![a, b] : Fin 2 → G) j =
      (![a, b] : Fin 2 → G) j * (![a, b] : Fin 2 → G) i := by
  intro i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact h | exact h.symm

theorem comm_fin3 {G : Type*} [Group G] {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) :
    ∀ i j : Fin 3, (![a, b, c] : Fin 3 → G) i * (![a, b, c] : Fin 3 → G) j =
      (![a, b, c] : Fin 3 → G) j * (![a, b, c] : Fin 3 → G) i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact hab | exact hab.symm | exact hac | exact hac.symm | exact hbc | exact hbc.symm

theorem pow_fin2 {G : Type*} [Group G] {a b : G} {p : ℕ} (ha : a ^ p = 1) (hb : b ^ p = 1) :
    ∀ i : Fin 2, (![a, b] : Fin 2 → G) i ^ p = 1 := by
  intro i; fin_cases i <;> first | exact ha | exact hb

theorem pow_fin3 {G : Type*} [Group G] {a b c : G} {p : ℕ} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hc : c ^ p = 1) : ∀ i : Fin 3, (![a, b, c] : Fin 3 → G) i ^ p = 1 := by
  intro i; fin_cases i <;> first | exact ha | exact hb | exact hc

theorem conj_of_mul_eq {G : Type*} [Group G] {g a b : G} (h : g * a = b * g) :
    g * a * g⁻¹ = b := by
  rw [h]; group

theorem conj_of_comm {G : Type*} [Group G] {g a : G} (h : a * g = g * a) : g * a * g⁻¹ = a := by
  rw [← h]; group

theorem tG_inv : tG⁻¹ = tG := inv_eq_of_mul_eq_one_right tG_sq

theorem eG_dG_comm : eG * dG = dG * eG := dG_eG_comm.symm
theorem eG_zG_comm : eG * zG = zG * eG := zG_eG_comm.symm
theorem xG_dG_comm : xG * dG = dG * xG := dG_xG_comm.symm
theorem xG_zG_comm : xG * zG = zG * xG := zG_xG_comm.symm
theorem tG_xG_comm : tG * xG = xG * tG := xG_tG_comm.symm

theorem zG_xG_commute : Commute zG xG := zG_xG_comm
theorem zG_eG_commute : Commute zG eG := zG_eG_comm

theorem comm_xG_eG : ⁅xG, eG⁆ = (zG ^ 3)⁻¹ := by
  have h1 : xG * eG = (zG ^ 3)⁻¹ * (eG * xG) := by
    rw [eG_xG]; group
  rw [commutatorElement_def, h1]; group

theorem xG_mem_heisS : xG ∈ heisS := Subgroup.subset_closure (Set.mem_insert _ _)

theorem eG_mem_heisS : eG ∈ heisS :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem zG_mem_heisS : zG ∈ heisS := by
  have hmem : ⁅xG, eG⁆ ∈ heisS := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ xG_mem_heisS eG_mem_heisS)
      (Subgroup.inv_mem _ xG_mem_heisS)) (Subgroup.inv_mem _ eG_mem_heisS)
  rw [comm_xG_eG] at hmem
  have h6 : zG ^ 6 * zG = 1 := by rw [← pow_succ]; exact zG_pow
  have hz : zG = ((zG ^ 3)⁻¹) ^ 2 := by
    calc zG = (zG ^ 6)⁻¹ := (inv_eq_of_mul_eq_one_right h6).symm
      _ = ((zG ^ 3) ^ 2)⁻¹ := by rw [← pow_mul]
      _ = ((zG ^ 3)⁻¹) ^ 2 := (inv_pow _ _).symm
  rw [hz]
  exact Subgroup.pow_mem _ hmem 2

theorem heisS_isPGroup : IsPGroup 7 heisS := by
  refine CFSG.AGLEmbedding.Norton.MON11_13.isPGroup_closure_of_central_commutator Nat.prime_seven
    xG_pow eG_pow ?_ ?_
  · rw [comm_xG_eG]
    exact (Commute.pow_left zG_xG_commute 3).inv_left
  · rw [comm_xG_eG]
    exact (Commute.pow_left zG_eG_commute 3).inv_left

theorem dG_mem_normalizer_heisS : dG ∈ Subgroup.normalizer (heisS : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  exact mem_normalizer_closure_pair (a := xG) (b := eG)
    (by rw [conj_of_comm xG_dG_comm]; exact xG_mem_heisS)
    (by rw [conj_of_comm eG_dG_comm]; exact eG_mem_heisS)

theorem pGrp_isPGroup : IsPGroup 7 pGrp := by
  have hz : IsPGroup 7 (Subgroup.zpowers dG) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime dG_pow dG_ne_one]; simp)
  refine IsPGroup.to_sup_of_normal_right' hz heisS_isPGroup ?_
  rw [Subgroup.zpowers_le]
  exact dG_mem_normalizer_heisS

theorem dG_mem_DZ : dG ∈ planeDZ := Subgroup.subset_closure (Set.mem_insert _ _)
theorem zG_mem_DZ : zG ∈ planeDZ :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
theorem dG_mem_DX : dG ∈ planeDX := Subgroup.subset_closure (Set.mem_insert _ _)
theorem xG_mem_DX : xG ∈ planeDX :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
theorem dG_mem_DY : dG ∈ planeDY := Subgroup.subset_closure (Set.mem_insert _ _)
theorem yG_mem_DY : y7G ∈ planeDY :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem dG_mem_pGrp : dG ∈ pGrp := Subgroup.mem_sup_left (Subgroup.mem_zpowers dG)
theorem heisS_le_pGrp : heisS ≤ pGrp := le_sup_right
theorem xG_mem_pGrp : xG ∈ pGrp := heisS_le_pGrp xG_mem_heisS
theorem eG_mem_pGrp : eG ∈ pGrp := heisS_le_pGrp eG_mem_heisS
theorem zG_mem_pGrp : zG ∈ pGrp := heisS_le_pGrp zG_mem_heisS

theorem yG_mem_heisS : y7G ∈ heisS := by
  rw [y7G_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ eG_mem_heisS eG_mem_heisS) xG_mem_heisS

theorem yG_mem_pGrp : y7G ∈ pGrp := heisS_le_pGrp yG_mem_heisS

theorem planeDZ_le : planeDZ ≤ pGrp := by
  rw [planeDZ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact dG_mem_pGrp
  · exact zG_mem_pGrp

theorem planeDX_le : planeDX ≤ pGrp := by
  rw [planeDX, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact dG_mem_pGrp
  · exact xG_mem_pGrp

theorem planeDY_le : planeDY ≤ pGrp := by
  rw [planeDY, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact dG_mem_pGrp
  · exact yG_mem_pGrp

theorem zG_yG_comm : zG * y7G = y7G * zG := by
  rw [y7G_eq]
  exact ((zG_eG_commute.mul_right zG_eG_commute).mul_right zG_xG_commute).eq

theorem dG_yG_comm : dG * y7G = y7G * dG := by
  rw [y7G_eq]
  have he : Commute dG eG := dG_eG_comm
  have hx : Commute dG xG := dG_xG_comm
  exact ((he.mul_right he).mul_right hx).eq

theorem eG_yG : eG * y7G = y7G * zG ^ 3 * eG := by
  have hzx : zG ^ 3 * xG = xG * zG ^ 3 := (Commute.pow_left zG_xG_commute 3).eq
  rw [y7G_eq]
  calc eG * (eG * eG * xG) = eG * eG * (eG * xG) := by simp [mul_assoc]
    _ = eG * eG * (zG ^ 3 * xG * eG) := by rw [eG_xG]
    _ = eG * eG * (zG ^ 3 * xG) * eG := by simp [mul_assoc]
    _ = eG * eG * (xG * zG ^ 3) * eG := by rw [hzx]
    _ = (eG * eG * xG) * zG ^ 3 * eG := by simp [mul_assoc]

theorem pairDZ_indep : ∀ c : Fin 2 → ZMod 7,
    ((List.finRange 2).map fun k => (![dG, zG] : Fin 2 → Gmat) k ^ (c k).val).prod = 1 → c = 0 := by
  intro c hc
  have := seven_indep ![c 0, c 1, 0] (by simpa [List.finRange_succ] using hc)
  funext i
  fin_cases i
  · simpa using congrFun this 0
  · simpa using congrFun this 1

theorem eG_mem_C_DZ : eG ∈ Subgroup.centralizer (planeDZ : Set Gmat) :=
  mem_centralizer_closure_pair dG_eG_comm zG_eG_comm

theorem zG_mem_C_DX : zG ∈ Subgroup.centralizer (planeDX : Set Gmat) :=
  mem_centralizer_closure_pair dG_zG_comm xG_zG_comm

theorem zG_mem_C_DY : zG ∈ Subgroup.centralizer (planeDY : Set Gmat) :=
  mem_centralizer_closure_pair dG_zG_comm zG_yG_comm.symm

theorem rank_DZ_two : 2 ≤ CFSG.Open.pRank 7 planeDZ := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 2) ![dG, zG]
    (comm_fin2 dG_zG_comm) (pow_fin2 dG_pow zG_pow) pairDZ_indep (H := planeDZ) ?_
  intro i
  fin_cases i
  · exact dG_mem_DZ
  · exact zG_mem_DZ

theorem rank_DZ_three : 3 ≤ CFSG.Open.pRank 7 (planeDZ ⊔ (pGrp ⊓ Subgroup.centralizer (planeDZ : Set Gmat))) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 3) ![dG, zG, eG]
    (comm_fin3 dG_zG_comm dG_eG_comm zG_eG_comm) (pow_fin3 dG_pow zG_pow eG_pow) seven_indep
    (H := planeDZ ⊔ (pGrp ⊓ Subgroup.centralizer (planeDZ : Set Gmat))) ?_
  intro i
  fin_cases i
  · exact Subgroup.mem_sup_left dG_mem_DZ
  · exact Subgroup.mem_sup_left zG_mem_DZ
  · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨eG_mem_pGrp, eG_mem_C_DZ⟩)

theorem rank_DX_two : 2 ≤ CFSG.Open.pRank 7 planeDX := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 2) ![dG, xG]
    (comm_fin2 dG_xG_comm) (pow_fin2 dG_pow xG_pow)
    (indep_two_of_not_pow dG xG dG_pow xG_pow dG_ne_one xG_ne_dG_pow) (H := planeDX) ?_
  intro i
  fin_cases i
  · exact dG_mem_DX
  · exact xG_mem_DX

theorem tG_xG_tG : tG * xG * tG = xG := by
  calc tG * xG * tG = (xG * tG) * tG := by rw [tG_xG_comm]
    _ = xG * (tG * tG) := by rw [mul_assoc]
    _ = xG := by rw [tG_sq, mul_one]

theorem rank_DX_three : 3 ≤ CFSG.Open.pRank 7 (planeDX ⊔ (pGrp ⊓ Subgroup.centralizer (planeDX : Set Gmat))) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 3) ![dG, xG, zG]
    (comm_fin3 dG_xG_comm dG_zG_comm xG_zG_comm) (pow_fin3 dG_pow xG_pow zG_pow)
    (indep_three_of_involution (by norm_num) dG xG zG tG dG_pow xG_pow zG_pow dG_ne_one
      zG_ne_one tG_sq tG_dG tG_xG_tG tG_zG xG_ne_dG_pow)
    (H := planeDX ⊔ (pGrp ⊓ Subgroup.centralizer (planeDX : Set Gmat))) ?_
  intro i
  fin_cases i
  · exact Subgroup.mem_sup_left dG_mem_DX
  · exact Subgroup.mem_sup_left xG_mem_DX
  · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨zG_mem_pGrp, zG_mem_C_DX⟩)

theorem rank_DY_two : 2 ≤ CFSG.Open.pRank 7 planeDY := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 2) ![dG, y7G]
    (comm_fin2 dG_yG_comm) (pow_fin2 dG_pow y7G_pow)
    (indep_two_of_not_pow dG y7G dG_pow y7G_pow dG_ne_one yG_ne_dG_pow) (H := planeDY) ?_
  intro i
  fin_cases i
  · exact dG_mem_DY
  · exact yG_mem_DY

theorem rank_DY_three : 3 ≤ CFSG.Open.pRank 7 (planeDY ⊔ (pGrp ⊓ Subgroup.centralizer (planeDY : Set Gmat))) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep Nat.prime_seven (n := 3) ![dG, y7G, zG]
    (comm_fin3 dG_yG_comm dG_zG_comm zG_yG_comm.symm) (pow_fin3 dG_pow y7G_pow zG_pow)
    (indep_three_of_heisenberg dG y7G zG eG 3 (by norm_num) zG_yG_comm.symm zG_pow zG_ne_one
      eG_yG eG_zG_comm eG_dG_comm pairDZ_indep)
    (H := planeDY ⊔ (pGrp ⊓ Subgroup.centralizer (planeDY : Set Gmat))) ?_
  intro i
  fin_cases i
  · exact Subgroup.mem_sup_left dG_mem_DY
  · exact Subgroup.mem_sup_left yG_mem_DY
  · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨zG_mem_pGrp, zG_mem_C_DY⟩)

theorem tG_mem_N_DZ : tG ∈ Subgroup.normalizer (planeDZ : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine mem_normalizer_closure_pair (a := dG) (b := zG) ?_ ?_
  · rw [tG_inv, tG_dG]; exact dG_mem_DZ
  · rw [tG_inv, tG_zG]; exact Subgroup.inv_mem _ zG_mem_DZ

theorem eG_mem_N_DZ : eG ∈ Subgroup.normalizer (planeDZ : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine mem_normalizer_closure_pair (a := dG) (b := zG) ?_ ?_
  · rw [conj_of_comm dG_eG_comm]; exact dG_mem_DZ
  · rw [conj_of_comm zG_eG_comm]; exact zG_mem_DZ

theorem xG_mem_N_DZ : xG ∈ Subgroup.normalizer (planeDZ : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine mem_normalizer_closure_pair (a := dG) (b := zG) ?_ ?_
  · rw [conj_of_comm dG_xG_comm]; exact dG_mem_DZ
  · rw [conj_of_comm zG_xG_comm]; exact zG_mem_DZ

theorem iG_mem_N_DY : iG ∈ Subgroup.normalizer (planeDY : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine mem_normalizer_closure_pair (a := dG) (b := y7G) ?_ ?_
  · rw [conj_of_comm dG_iG_comm]; exact dG_mem_DY
  · rw [conj_of_comm yG_iG_comm]; exact yG_mem_DY

theorem gG_mem_N_DX : gG ∈ Subgroup.normalizer (planeDX : Set Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine mem_normalizer_closure_pair (a := dG) (b := xG) ?_ ?_
  · rw [conj_of_mul_eq gG_dG]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ xG_mem_DX 3) dG_mem_DX
  · rw [conj_of_mul_eq gG_xG]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ xG_mem_DX 6) (Subgroup.pow_mem _ dG_mem_DX 3)

theorem tcGenDatum_seven_gmat : CFSG.AGLEmbedding.TCGenDatum Gmat 7 := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine ⟨3, ![planeDZ, planeDX, planeDY], pGrp,
    Set.range fun i : Fin Gen7.gen7Gens.size => gw Gen7.gen7Gens[i], pGrp_isPGroup, ?_, ?_,
    Gen7.closure_gen7_eq_top, ?_⟩
  · intro i
    fin_cases i
    · exact planeDZ_le
    · exact planeDX_le
    · exact planeDY_le
  · intro i
    fin_cases i
    · exact ⟨rank_DZ_two, rank_DZ_three⟩
    · exact ⟨rank_DX_two, rank_DX_three⟩
    · exact ⟨rank_DY_two, rank_DY_three⟩
  · rintro _ ⟨i, rfl⟩
    obtain ⟨i, hi⟩ := i
    have h5 : i < 5 := by simpa [Gen7.gen7Gens] using hi
    interval_cases i
    · exact ⟨0, tG_mem_N_DZ⟩
    · exact ⟨0, eG_mem_N_DZ⟩
    · exact ⟨0, xG_mem_N_DZ⟩
    · exact ⟨2, iG_mem_N_DY⟩
    · exact ⟨1, gG_mem_N_DX⟩

theorem matrix_act0 : ∀ a b : ZMod 7, a + b * 3 = a → a * 3 + b * 6 = b → a = 0 ∧ b = 0 := by
  decide

theorem act_d : gG * dG * gG⁻¹ = dG * xG ^ 3 := by
  have h1 : gG * dG * gG⁻¹ = xG ^ 3 * dG := conj_of_mul_eq gG_dG
  rw [h1]
  exact (Commute.pow_left (Commute.symm (show Commute dG xG from dG_xG_comm)) 3).eq

theorem act_x : gG * xG * gG⁻¹ = dG ^ 3 * xG ^ 6 := by
  have h1 : gG * xG * gG⁻¹ = xG ^ 6 * dG ^ 3 := conj_of_mul_eq gG_xG
  rw [h1]
  exact ((Commute.pow_pow (Commute.symm (show Commute dG xG from dG_xG_comm)) 6 3)).eq

theorem val_one_seven : (1 : ZMod 7).val = 1 := by decide
theorem val_three_seven : (3 : ZMod 7).val = 3 := by decide
theorem val_six_seven : (6 : ZMod 7).val = 6 := by decide

@[expose] noncomputable def moduleDX : ModuleSpec Gmat 7 where
  n := 2
  m := 1
  a := ![dG, xG]
  g := ![gG]
  M := fun _ => !![1, 3; 3, 6]
  comm := comm_fin2 dG_xG_comm
  pow := pow_fin2 dG_pow xG_pow
  indep := indep_two_of_not_pow dG xG dG_pow xG_pow dG_ne_one xG_ne_dG_pow
  act := by
    intro j i
    fin_cases j
    fin_cases i
    · simpa [List.finRange_succ, val_one_seven, val_three_seven] using act_d
    · simpa [List.finRange_succ, val_three_seven, val_six_seven] using act_x

theorem noFun_aux : ∀ v : Fin 2 → ZMod 7, Matrix.vecMul v !![1, 3; 3, 6] = v → v = 0 := by
  intro v h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
  have hv1 : v 1 = 0 := by
    rcases h0 with h0 | h0
    · exact h0
    · exact absurd h0 (by decide)
  have := matrix_act0 (v 0) (v 1) (by rw [hv1]; ring) (by rw [hv1] at h1 ⊢; linear_combination h1)
  funext i
  fin_cases i
  · exact this.1
  · exact this.2

theorem moduleDX_noFun : moduleDX.NoFun := fun v hv => noFun_aux v (hv ⟨0, Nat.zero_lt_one⟩)

theorem noAlt_aux : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 7), B.transpose = -B →
    (!![1, 3; 3, 6] : Matrix (Fin 2) (Fin 2) (ZMod 7)).transpose * B * !![1, 3; 3, 6] = B →
    B = 0 := by
  decide +kernel

theorem moduleDX_noAlt : moduleDX.NoAlt := fun B hB hM => noAlt_aux B hB (hM ⟨0, Nat.zero_lt_one⟩)

theorem coverPointDatum_seven_gmat : CFSG.AGLEmbedding.CoverPointDatum Gmat 7 := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine ⟨moduleDX, 1, ![dG], fun _ => 4, fun _ => ![tG, eG, xG, iG], fun _ _ => 1,
    Or.inr ⟨le_refl 2, moduleDX_noAlt⟩, moduleDX_noFun, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    exact ⟨Subgroup.subset_closure ⟨⟨0, Nat.zero_lt_two⟩, rfl⟩, dG_ne_one⟩
  · intro j i
    fin_cases j
    fin_cases i
    · show tG * dG * tG⁻¹ = dG ^ 1
      rw [tG_inv, tG_dG, pow_one]
    · show eG * dG * eG⁻¹ = dG ^ 1
      rw [conj_of_comm dG_eG_comm, pow_one]
    · show xG * dG * xG⁻¹ = dG ^ 1
      rw [conj_of_comm dG_xG_comm, pow_one]
    · show iG * dG * iG⁻¹ = dG ^ 1
      rw [conj_of_comm dG_iG_comm, pow_one]
  · have hle : Set.range (fun i : Fin Gen7.gen7Gens.size => gw Gen7.gen7Gens[i]) ⊆
        Set.range moduleDX.g ∪ ⋃ j : Fin 1, Set.range ((fun _ => ![tG, eG, xG, iG]) j) := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨i, hi⟩ := i
      have h5 : i < 5 := by simpa [Gen7.gen7Gens] using hi
      interval_cases i
      · exact Or.inr (Set.mem_iUnion.2 ⟨0, ⟨0, rfl⟩⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨0, ⟨1, rfl⟩⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨0, ⟨2, rfl⟩⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨0, ⟨3, rfl⟩⟩)
      · exact Or.inl ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    rw [eq_top_iff, ← Gen7.closure_gen7_eq_top]
    exact Subgroup.closure_mono hle

theorem coverWeakGen_seven_gmat : CFSG.AGLEmbedding.CoverWeakGen Gmat 7 := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  exact CFSG.AGLEmbedding.coverWeakGen_of_coverPointDatum (by norm_num) coverPointDatum_seven_gmat

theorem weakCoreClause_seven_gmat : ∀ S : Sylow 7 Gmat,
    CFSG.Open.GLBWeakCore 7 (S : Subgroup Gmat) = ⊤ ∨ CFSG.AGLEmbedding.KlingenAlt 7 Gmat S := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  exact fun S => Or.inl (CFSG.AGLEmbedding.weakCoreOfTC Gmat 7 tcGenDatum_seven_gmat S)

end CFSG.AGLEmbedding.Norton.MON5_7
