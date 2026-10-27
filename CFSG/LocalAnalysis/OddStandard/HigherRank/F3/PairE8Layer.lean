module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE8Norm
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Data

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi

variable {F : Type} [Field F]


theorem mem_stdRankOne_e8_iff_gen {β : Fin (Tag.rank .E8) → ℤ} (hβ : IsRoot .E8 β)
    (r : ↥(adjointGroup .E8 F)) :
    r ∈ stdRankOne (e8Datum F) β ↔ (r : ModGL .E8 F) ∈ rootRankOneGroup .E8 F β := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := F) (rootOperatorFamily .E8) hβ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E8 F hβ).1
  change r ∈ rootGroup (rootOperatorFamily .E8) F β ⊔
    rootGroup (rootOperatorFamily .E8) F (-β) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL]

theorem map_rankOne_e8 (j : Fin (Tag.rank .E8)) :
    (CFSG.LieType.CurtisTits.rankOne (e8Datum F).rootGroup j).map (adjointGroup .E8 F).subtype =
      rootRankOneGroup .E8 F (Pi.single j 1) := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_stdRankOne_e8_iff_gen (isRoot_single .E8 j) r).1 hr
  · intro hx
    have hxa : x ∈ adjointGroup .E8 F := by
      obtain ⟨A, rfl⟩ := hx
      exact rootSL2_mem_adjointGroup _ _
    exact ⟨⟨x, hxa⟩, (mem_stdRankOne_e8_iff_gen (isRoot_single .E8 j) ⟨x, hxa⟩).2 hx, rfl⟩

theorem xUnit_mem_rootRankOne_e8 (j : Fin (Tag.rank .E8)) (c : F) :
    xUnit .E8 F j c ∈ rootRankOneGroup .E8 F (Pi.single j 1) ∧
      yUnit .E8 F j c ∈ rootRankOneGroup .E8 F (Pi.single j 1) := by
  have hβ := isRoot_single .E8 j
  constructor
  · rw [← pinnedX_single _ F j c, (exceptional_Lang_root_rank_one_torus_transport .E8 F hβ).1]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [← pinnedX_neg_single _ F j c, (exceptional_Lang_root_rank_one_torus_transport .E8 F hβ).1]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩)

@[expose] noncomputable def layerE7 (F : Type) [Field F] : Subgroup ↥(adjointGroup .E8 F) :=
  ⨆ i : Fin 7, CFSG.LieType.CurtisTits.rankOne (e8Datum F).rootGroup i.castSucc

theorem subsystemGroup_le_map_layerE7 :
    subsystemGroup .E8 F JE8 ≤ (layerE7 F).map (adjointGroup .E8 F).subtype := by
  rw [subsystemGroup, Subgroup.closure_le]
  have hle : ∀ j ∈ JE8, rootRankOneGroup .E8 F (Pi.single j 1) ≤
      (layerE7 F).map (adjointGroup .E8 F).subtype := by
    intro j hj
    obtain ⟨i, hi⟩ : ∃ i : Fin 7, i.castSucc = j :=
      ⟨⟨j.val, by have : j.val ≤ 6 := hj; omega⟩, Fin.ext rfl⟩
    rw [← map_rankOne_e8]
    refine Subgroup.map_mono ?_
    rw [← hi]
    exact le_iSup
      (fun i : Fin 7 => CFSG.LieType.CurtisTits.rankOne (e8Datum F).rootGroup i.castSucc) i
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · exact hle j hj (xUnit_mem_rootRankOne_e8 _ c).1
  · exact hle j hj (xUnit_mem_rootRankOne_e8 _ c).2

theorem conj_mem_subsystemGroup_e8 {J : Set (Fin (Tag.rank .E8))} {t : ModGL .E8 F}
    (ht : t ∈ torusGroup .E8 F) {η : ModGL .E8 F} (hη : η ∈ subsystemGroup .E8 F J) :
    t * η * t⁻¹ ∈ subsystemGroup .E8 F J := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E8 F b
  induction hη using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hg
    · rw [hx]
      exact xUnit_mem_subsystemGroup hj _
    · rw [hy]
      exact yUnit_mem_subsystemGroup hj _
  | one => simp
  | mul g₁ g₂ _ _ h₁ h₂ =>
    have : rootDiagUnit .E8 b * (g₁ * g₂) * (rootDiagUnit .E8 b)⁻¹ =
        (rootDiagUnit .E8 b * g₁ * (rootDiagUnit .E8 b)⁻¹) *
          (rootDiagUnit .E8 b * g₂ * (rootDiagUnit .E8 b)⁻¹) := by group
    rw [this]
    exact mul_mem h₁ h₂
  | inv g _ h =>
    have : rootDiagUnit .E8 b * g⁻¹ * (rootDiagUnit .E8 b)⁻¹ =
        (rootDiagUnit .E8 b * g * (rootDiagUnit .E8 b)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem h

theorem exists_mul_of_mem_levi_e8 {J : Set (Fin (Tag.rank .E8))} {u : ModGL .E8 F}
    (hu : u ∈ parabolicLevi .E8 F J) :
    ∃ t ∈ torusGroup .E8 F, ∃ η ∈ subsystemGroup .E8 F J, u = t * η := by
  let P : Subgroup (ModGL .E8 F) :=
    { carrier := {x | ∃ t ∈ torusGroup .E8 F, ∃ η ∈ subsystemGroup .E8 F J, x = t * η}
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, η₁, hη₁, rfl⟩ ⟨t₂, ht₂, η₂, hη₂, rfl⟩
        refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, (t₂⁻¹ * η₁ * t₂) * η₂, ?_, ?_⟩
        · have := conj_mem_subsystemGroup_e8 (J := J) (inv_mem ht₂) hη₁
          rw [inv_inv] at this
          exact mul_mem this hη₂
        · group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, η, hη, rfl⟩
        refine ⟨t⁻¹, inv_mem ht, t * η⁻¹ * t⁻¹, ?_, ?_⟩
        · exact conj_mem_subsystemGroup_e8 ht (inv_mem hη)
        · group }
  have hle : parabolicLevi .E8 F J ≤ P :=
    sup_le (fun t ht => ⟨t, ht, 1, one_mem _, by simp⟩)
      (fun η hη => ⟨1, one_mem _, η, hη, by simp⟩)
  exact hle hu

theorem rootChar_thetaE8_eq_one_of_commute {a : Fin (Tag.rank .E8) → Fˣ}
    (h : rootDiagUnit .E8 a * rootSL2 .E8 F thetaE8 (uSL 1) =
      rootSL2 .E8 F thetaE8 (uSL 1) * rootDiagUnit .E8 a) :
    rootChar (τ := .E8) a thetaE8 = 1 := by
  set ε : ℤ := (pinnedData .E8 thetaE8).2.2 with hε
  have hcne : ε • (1 : F) ≠ 0 := by
    rcases pinnedSign_eq .E8 thetaE8 with h1 | h1 <;> simp [hε, h1]
  rw [rootSL2_uSL_eq] at h
  have h2 : rootDiagUnit .E8 a * pinnedX .E8 F thetaE8 (ε • (1 : F)) * (rootDiagUnit .E8 a)⁻¹ =
      pinnedX .E8 F thetaE8 (ε • (1 : F)) := by
    rw [h, mul_inv_cancel_right]
  rw [rootDiagUnit_conj_pinnedX a isRoot_thetaE8] at h2
  have h3 := pinnedX_injective (τ := .E8) (R := F) thetaE8 h2
  have h4 : ((rootChar (τ := .E8) a thetaE8 : Fˣ) : F) = 1 :=
    mul_right_cancel₀ hcne (by rw [h3, one_mul])
  exact Units.ext h4

theorem rootDiagUnit_mem_subsystemGroup_e8 (hsq : ∀ c : Fˣ, c * c = 1) {a : Fin 8 → Fˣ}
    (ha : rootChar (τ := .E8) a thetaE8 = 1) :
    rootDiagUnit .E8 a ∈ subsystemGroup .E8 F JE8 := by
  have e2 : ∀ c : Fˣ, c ^ 2 = 1 := fun c => by rw [sq]; exact hsq c
  have e3 : ∀ c : Fˣ, c ^ 3 = c := fun c => by rw [pow_succ, e2, one_mul]
  have e4 : ∀ c : Fˣ, c ^ 4 = 1 := fun c => by rw [pow_succ, e3, hsq]
  have e5 : ∀ c : Fˣ, c ^ 5 = c := fun c => by rw [pow_succ, e4, one_mul]
  have e6 : ∀ c : Fˣ, c ^ 6 = 1 := fun c => by rw [pow_succ, e5, hsq]
  have hrel : a 1 * a 4 * a 6 = 1 := by
    rw [thetaE8_eq] at ha
    change ∏ i : Fin 8, a i ^ (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) i = 1 at ha
    rw [Fin.prod_univ_eight] at ha
    simp [e2, e3, e4, e5, e6] at ha
    exact ha
  have hinv : ∀ x : Fˣ, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  set c : Fin 8 → Fˣ := ![a 1 * a 2, a 0 * a 3 * a 5 * a 7, a 0, a 1, a 5 * a 7, a 6, a 7, 1]
    with hc
  have hsq' : ∀ x y : Fˣ, x * (x * y) = y := fun x y => by rw [← mul_assoc, hsq, one_mul]
  have hrel' : a 1 * a 6 = a 4 :=
    calc a 1 * a 6 = a 4 * (a 1 * a 4 * a 6) := by
          simp [mul_assoc, mul_left_comm, mul_comm, hsq, hsq']
      _ = a 4 := by rw [hrel, mul_one]
  have key : ∀ l : Fin 8, ∏ j : Fin 8, c j ^ Tag.cartanE 8 j l = a l := by
    intro l
    rw [Fin.prod_univ_eight]
    fin_cases l
    all_goals
      simp [hc, Tag.cartanE, e2, hinv, mul_assoc, mul_left_comm, mul_comm, hsq, hsq', hrel']
  have hcart : cartanChar (τ := .E8) c = a := funext key
  rw [← hcart, ← list_prod_torusElt_eq_rootDiagUnit (τ := .E8) (K := F) c]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j ∈ JE8
  · exact subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hj _)
  · have hj7 : j = ⟨7, by decide⟩ := by
      apply Fin.ext
      have h1 : ¬ j.val ≤ 6 := hj
      have h2 : j.val < 8 := j.2
      show j.val = 7
      omega
    subst hj7
    have hc7 : c (⟨7, by decide⟩ : Fin (Tag.rank .E8)) = 1 := rfl
    rw [hc7, torusElt_one]
    exact one_mem _

theorem centralizer_stdRankOne_le_layer (hF : ringChar F ≠ 2) (hsq : ∀ u : Fˣ, u * u = 1)
    (hcomm : ∀ x ∈ layerE7 F, ∀ r ∈ stdRankOne (e8Datum F) thetaE8, x * r = r * x)
    {c : ↥(adjointGroup .E8 F)} (hc : ∀ r ∈ stdRankOne (e8Datum F) thetaE8, c * r = r * c) :
    c ∈ layerE7 F := by
  have hρ : ∀ A : SL2 F, (⟨rootSL2 .E8 F thetaE8 A, rootSL2_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .E8 F)) ∈ stdRankOne (e8Datum F) thetaE8 :=
    fun A => (mem_stdRankOne_e8_iff _).2 ⟨A, rfl⟩
  have hcL : (c : ModGL .E8 F) ∈ parabolicLevi .E8 F JE8 :=
    mem_parabolicLevi_of_commute_rootSL2_E8 hF c.2 fun A =>
      congrArg Subtype.val (hc _ (hρ A))
  obtain ⟨t, ht, η, hη, hcη⟩ := exists_mul_of_mem_levi_e8 hcL
  obtain ⟨η', hη'L, hη'⟩ := Subgroup.mem_map.1 (subsystemGroup_le_map_layerE7 hη)
  have hηc : ∀ A : SL2 F, η * rootSL2 .E8 F thetaE8 A = rootSL2 .E8 F thetaE8 A * η := by
    intro A
    rw [← hη']
    exact congrArg Subtype.val (hcomm η' hη'L _ (hρ A))
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hta : rootDiagUnit .E8 a * rootSL2 .E8 F thetaE8 (uSL 1) =
      rootSL2 .E8 F thetaE8 (uSL 1) * rootDiagUnit .E8 a := by
    have h1 := congrArg Subtype.val (hc _ (hρ (uSL 1)))
    have h2 := hηc (uSL 1)
    simp only [Subgroup.coe_mul] at h1
    rw [hcη] at h1
    have h3 : (rootDiagUnit .E8 a * rootSL2 .E8 F thetaE8 (uSL 1)) * η =
        (rootSL2 .E8 F thetaE8 (uSL 1) * rootDiagUnit .E8 a) * η :=
      calc (rootDiagUnit .E8 a * rootSL2 .E8 F thetaE8 (uSL 1)) * η
          = rootDiagUnit .E8 a * (rootSL2 .E8 F thetaE8 (uSL 1) * η) := mul_assoc _ _ _
        _ = rootDiagUnit .E8 a * (η * rootSL2 .E8 F thetaE8 (uSL 1)) := by rw [h2]
        _ = (rootDiagUnit .E8 a * η) * rootSL2 .E8 F thetaE8 (uSL 1) := (mul_assoc _ _ _).symm
        _ = rootSL2 .E8 F thetaE8 (uSL 1) * (rootDiagUnit .E8 a * η) := h1
        _ = (rootSL2 .E8 F thetaE8 (uSL 1) * rootDiagUnit .E8 a) * η := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  have hχ := rootChar_thetaE8_eq_one_of_commute hta
  have hN := rootDiagUnit_mem_subsystemGroup_e8 hsq hχ
  have hmem : (c : ModGL .E8 F) ∈ (layerE7 F).map (adjointGroup .E8 F).subtype := by
    rw [hcη]
    exact mul_mem (subsystemGroup_le_map_layerE7 hN) (subsystemGroup_le_map_layerE7 hη)
  obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hmem
  have : y = c := Subtype.ext hyc
  rwa [this] at hy

theorem normal_layerE7_centralizer_dTheta {F : Type} [Field F] (hF : ringChar F ≠ 2)
    (hsq : ∀ u : Fˣ, u * u = 1)
    (hcomm : ∀ x ∈ layerE7 F, ∀ r ∈ stdRankOne (e8Datum F) thetaE8, x * r = r * x) :
    ((layerE7 F).subgroupOf
      (Subgroup.centralizer ({dTheta F} : Set ↥(adjointGroup .E8 F)))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hg : (g : ↥(adjointGroup .E8 F)) * dTheta F = dTheta F * (g : ↥(adjointGroup .E8 F)) :=
    Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hgi : (g : ↥(adjointGroup .E8 F))⁻¹ * dTheta F =
      dTheta F * (g : ↥(adjointGroup .E8 F))⁻¹ := by
    calc (g : ↥(adjointGroup .E8 F))⁻¹ * dTheta F
        = (g : ↥(adjointGroup .E8 F))⁻¹ * (dTheta F * g) * (g : ↥(adjointGroup .E8 F))⁻¹ := by
          group
      _ = (g : ↥(adjointGroup .E8 F))⁻¹ * (g * dTheta F) * (g : ↥(adjointGroup .E8 F))⁻¹ := by
          rw [hg]
      _ = dTheta F * (g : ↥(adjointGroup .E8 F))⁻¹ := by group
  show (g : ↥(adjointGroup .E8 F)) * (x : ↥(adjointGroup .E8 F)) *
    (g : ↥(adjointGroup .E8 F))⁻¹ ∈ layerE7 F
  refine centralizer_stdRankOne_le_layer hF hsq hcomm fun r hr => ?_
  have hr' := conj_stdRankOne_of_commute_dTheta hF (x := (g : ↥(adjointGroup .E8 F))⁻¹) hgi hr
  rw [inv_inv] at hr'
  have hxr := hcomm (x : ↥(adjointGroup .E8 F)) hx _ hr'
  calc (g : ↥(adjointGroup .E8 F)) * x * (g : ↥(adjointGroup .E8 F))⁻¹ * r
      = g * ((x : ↥(adjointGroup .E8 F)) * ((g : ↥(adjointGroup .E8 F))⁻¹ * r * g)) *
          (g : ↥(adjointGroup .E8 F))⁻¹ := by group
    _ = g * (((g : ↥(adjointGroup .E8 F))⁻¹ * r * g) * (x : ↥(adjointGroup .E8 F))) *
          (g : ↥(adjointGroup .E8 F))⁻¹ := by rw [hxr]
    _ = r * ((g : ↥(adjointGroup .E8 F)) * x * (g : ↥(adjointGroup .E8 F))⁻¹) := by group

end CFSG.OddStandard.HigherRank.F3
