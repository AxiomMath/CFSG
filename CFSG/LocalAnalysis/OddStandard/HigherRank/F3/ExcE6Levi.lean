module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Theta
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Adj
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.RouteD (path6 path6_ne theta6)
open scoped MatrixGroups

section Theta

theorem thetaE6_eq_theta6 : thetaE6 = theta6 := by
  have hsum : ∀ θ v : Fin (Tag.rank .E6) → ℤ,
      iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
    intro θ v
    simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  suffices h : ∀ t : Fin (Tag.rank .E6) → ℤ,
      (∀ j : Fin (Tag.rank .E6), iform t (Pi.single j 1) = if j.val = 1 then 1 else 0) →
        thetaE6 = t from h theta6 (by decide +kernel)
  intro t ht
  by_contra hne
  have hpos := iform_self_pos (sub_ne_zero.2 hne)
  rw [iform_sub_left, hsum thetaE6 (thetaE6 - t), hsum t (thetaE6 - t)] at hpos
  simp only [iform_thetaE6_single, ht, sub_self] at hpos
  exact lt_irrefl _ hpos

end Theta

section Normalizer

variable {K : Type} [Field K]

theorem conj_mem_subsystemGroup_e6 {J : Set (Fin (Tag.rank .E6))} {t : ModGL .E6 K}
    (ht : t ∈ torusGroup .E6 K) {η : ModGL .E6 K} (hη : η ∈ subsystemGroup .E6 K J) :
    t * η * t⁻¹ ∈ subsystemGroup .E6 K J := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E6 K b
  induction hη using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hg
    · rw [hx]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩
    · rw [hy]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩
  | one => simp
  | mul g₁ g₂ _ _ h₁ h₂ =>
    have : rootDiagUnit .E6 b * (g₁ * g₂) * (rootDiagUnit .E6 b)⁻¹ =
        (rootDiagUnit .E6 b * g₁ * (rootDiagUnit .E6 b)⁻¹) *
          (rootDiagUnit .E6 b * g₂ * (rootDiagUnit .E6 b)⁻¹) := by group
    rw [this]
    exact mul_mem h₁ h₂
  | inv g _ h =>
    have : rootDiagUnit .E6 b * g⁻¹ * (rootDiagUnit .E6 b)⁻¹ =
        (rootDiagUnit .E6 b * g * (rootDiagUnit .E6 b)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem h

theorem parabolicLevi_le_normalizer_subsystemGroup_e6 (J : Set (Fin (Tag.rank .E6))) :
    parabolicLevi .E6 K J ≤
      Subgroup.normalizer (subsystemGroup .E6 K J : Set (ModGL .E6 K)) := by
  refine sup_le (fun t ht => ?_) Subgroup.le_normalizer
  refine Subgroup.mem_normalizer_iff.2 fun η => ⟨fun hη => conj_mem_subsystemGroup_e6 ht hη,
    fun hη => ?_⟩
  have := conj_mem_subsystemGroup_e6 (inv_mem ht) hη
  simpa [mul_assoc] using this

end Normalizer

section LeviForm

variable {F : Type} [Field F]

theorem exists_levi_form_e6 (hF : ringChar F ≠ 2) {c : ModGL .E6 F}
    (hcG : c ∈ adjointGroup .E6 F)
    (hc : rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : Fˣ)) * c =
      c * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : Fˣ))) :
    ∃ n ∈ parabolicLevi .E6 F JE6, ∃ A : SL2 F, c = n * rootSL2 .E6 F thetaE6 A := by
  have hcT : c ∈ toralCentralizer .E6 F (thetaDiag thetaE6 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    exact ⟨hcG, mul_inv_eq_iff_eq_mul.2 hc⟩
  have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inl rfl))) hF
    (thetaDiag_neg_one_sign_E6 thetaE6) hcT
  exact toralRootGroup_le_h1E6 hF hM

end LeviForm

section Image

@[expose] noncomputable def e6Eps :
    ↥(e6Data_valid.minGroup (GaloisField 3 1)) →* ModGL .E6 (GaloisField 3 1) :=
  (adjointGroup .E6 (GaloisField 3 1)).subtype.comp (e6Isogeny (GaloisField 3 1))

theorem e6Eps_injective : Function.Injective e6Eps :=
  fun _ _ h => e6Isogeny_injective_three (Subtype.ext h)

variable {K : Type} [Field K]

theorem mem_adjRootGroup_single (j : Fin (Tag.rank .E6)) (g : ↥(adjointGroup .E6 K)) :
    g ∈ rootGroup (rootOperatorFamily .E6) K (Pi.single j 1) ↔
      ∃ c : K, (g : ModGL .E6 K) = xUnit .E6 K j c := by
  rw [rootGroup_of_isRoot (isRoot_single .E6 j)]
  exact (rootOperatorFamily .E6).mem_rootSubgroup_simple j g

theorem mem_adjRootGroup_neg_single (j : Fin (Tag.rank .E6)) (g : ↥(adjointGroup .E6 K)) :
    g ∈ rootGroup (rootOperatorFamily .E6) K (-Pi.single j 1) ↔
      ∃ c : K, (g : ModGL .E6 K) = yUnit .E6 K j c := by
  rw [rootGroup_of_isRoot (IsRoot.neg (isRoot_single .E6 j))]
  exact (rootOperatorFamily .E6).mem_rootSubgroup_neg_simple j g

theorem exists_path6_eq : ∀ j : Fin 6, j.val ≠ 1 → ∃ i : Fin 5, path6 i = j := by decide

theorem exists_xUnit_of_mem_rootGroup (j : Fin (Tag.rank .E6))
    {x : ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hx : x ∈ (e6Datum (GaloisField 3 1)).rootGroup (Pi.single j 1)) :
    ∃ c : GaloisField 3 1, e6Eps x = xUnit .E6 (GaloisField 3 1) j c := by
  have h1 : e6Isogeny (GaloisField 3 1) x ∈
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (Pi.single j 1) := by
    rw [← map_e6Isogeny_rootGroup (GaloisField 3 1) (isRoot_single .E6 j)]
    exact Subgroup.mem_map_of_mem _ hx
  exact (mem_adjRootGroup_single _ _).1 h1

theorem exists_yUnit_of_mem_rootGroup (j : Fin (Tag.rank .E6))
    {x : ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hx : x ∈ (e6Datum (GaloisField 3 1)).rootGroup (-Pi.single j 1)) :
    ∃ c : GaloisField 3 1, e6Eps x = yUnit .E6 (GaloisField 3 1) j c := by
  have h1 : e6Isogeny (GaloisField 3 1) x ∈
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-Pi.single j 1) := by
    rw [← map_e6Isogeny_rootGroup (GaloisField 3 1) (IsRoot.neg (isRoot_single .E6 j))]
    exact Subgroup.mem_map_of_mem _ hx
  exact (mem_adjRootGroup_neg_single _ _).1 h1

theorem exists_mem_rootGroup_of_xUnit (j : Fin (Tag.rank .E6)) (c : GaloisField 3 1) :
    ∃ x ∈ (e6Datum (GaloisField 3 1)).rootGroup (Pi.single j 1),
      e6Eps x = xUnit .E6 (GaloisField 3 1) j c := by
  have hmem : (⟨xUnit .E6 (GaloisField 3 1) j c, xUnit_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .E6 (GaloisField 3 1))) ∈
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (Pi.single j 1) :=
    (mem_adjRootGroup_single _ _).2 ⟨c, rfl⟩
  rw [← map_e6Isogeny_rootGroup (GaloisField 3 1) (isRoot_single .E6 j)] at hmem
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  exact ⟨x, hx, congrArg Subtype.val hxe⟩

theorem exists_mem_rootGroup_of_yUnit (j : Fin (Tag.rank .E6)) (c : GaloisField 3 1) :
    ∃ x ∈ (e6Datum (GaloisField 3 1)).rootGroup (-Pi.single j 1),
      e6Eps x = yUnit .E6 (GaloisField 3 1) j c := by
  have hmem : (⟨yUnit .E6 (GaloisField 3 1) j c, yUnit_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .E6 (GaloisField 3 1))) ∈
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-Pi.single j 1) :=
    (mem_adjRootGroup_neg_single _ _).2 ⟨c, rfl⟩
  rw [← map_e6Isogeny_rootGroup (GaloisField 3 1) (IsRoot.neg (isRoot_single .E6 j))] at hmem
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  exact ⟨x, hx, congrArg Subtype.val hxe⟩

theorem map_iSup_rankOne_e6 :
    (⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne
      (e6Datum (GaloisField 3 1)).rootGroup (path6 i)).map e6Eps =
    subsystemGroup .E6 (GaloisField 3 1) JE6 := by
  refine (Subgroup.map_iSup _ _).trans (le_antisymm (iSup_le fun i => ?_) ?_)
  · have hj : path6 i ∈ JE6 := fun h => path6_ne i (Fin.ext h)
    refine (Subgroup.map_sup _ _ _).le.trans (sup_le ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := exists_xUnit_of_mem_rootGroup (path6 i) hx
      rw [hc]
      exact xUnit_mem_subsystemGroup hj c
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := exists_yUnit_of_mem_rootGroup (path6 i) hx
      rw [hc]
      exact yUnit_mem_subsystemGroup hj c
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · obtain ⟨i, rfl⟩ := exists_path6_eq j hj
      obtain ⟨x, hx, hxe⟩ := exists_mem_rootGroup_of_xUnit (path6 i) c
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_left hx, hxe⟩)
    · obtain ⟨i, rfl⟩ := exists_path6_eq j hj
      obtain ⟨x, hx, hxe⟩ := exists_mem_rootGroup_of_yUnit (path6 i) c
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_right hx, hxe⟩)

end Image

section Normal

theorem normal_range_theta_e6
    {Θ : SL(6, GaloisField 3 1) →* ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hrange : Θ.range = ⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne
      (e6Datum (GaloisField 3 1)).rootGroup (path6 i))
    {u : ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hu : e6Eps u = rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (GaloisField 3 1)ˣ))) :
    (Θ.range.subgroupOf (Subgroup.centralizer
      ({u} : Set ↥(e6Data_valid.minGroup (GaloisField 3 1))))).Normal := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hmap : Θ.range.map e6Eps = subsystemGroup .E6 (GaloisField 3 1) JE6 := by
    rw [hrange]
    exact map_iSup_rankOne_e6
  have hcomm : ∀ y ∈ ⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne
      (e6Datum (GaloisField 3 1)).rootGroup (path6 i),
      ∀ r ∈ (e6Datum (GaloisField 3 1)).rootGroup theta6 ⊔
        (e6Datum (GaloisField 3 1)).rootGroup (-theta6), y * r = r * y :=
    commutes_iSup_rankOne_theta_e6
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hgu := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hcg : rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (GaloisField 3 1)ˣ)) * e6Eps ↑g =
      e6Eps ↑g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (GaloisField 3 1)ˣ)) := by
    rw [← hu, ← map_mul, ← map_mul, hgu]
  obtain ⟨n, hn, A, hA⟩ := exists_levi_form_e6 hF (e6Isogeny (GaloisField 3 1) ↑g).2 hcg
  replace hA : e6Eps ↑g = n * rootSL2 .E6 (GaloisField 3 1) thetaE6 A := hA
  have hρ : (⟨rootSL2 .E6 (GaloisField 3 1) thetaE6 A,
      CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup thetaE6 A⟩ :
      ↥(adjointGroup .E6 (GaloisField 3 1))) ∈
        stdRankOne (e6AdjDatum (GaloisField 3 1)) thetaE6 :=
    (mem_stdRankOne_e6_iff_gen isRoot_thetaE6 _).2 ⟨A, rfl⟩
  rw [← map_stdRankOne_e6_gen isRoot_thetaE6] at hρ
  obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.1 hρ
  have hr' : r ∈ (e6Datum (GaloisField 3 1)).rootGroup theta6 ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-theta6) :=
    Eq.mp (congrArg (fun t : Fin (Tag.rank .E6) → ℤ => r ∈ (e6Datum (GaloisField 3 1)).rootGroup t ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-t)) thetaE6_eq_theta6) hr
  have hρe : e6Eps r = rootSL2 .E6 (GaloisField 3 1) thetaE6 A := congrArg Subtype.val hre
  have hcρ : e6Eps r * e6Eps ↑x = e6Eps ↑x * e6Eps r := by
    rw [← map_mul, ← map_mul, (hcomm ↑x (by rw [← hrange]; exact hx) r hr').symm]
  have hxN : e6Eps ↑x ∈ subsystemGroup .E6 (GaloisField 3 1) JE6 := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hnN : n * e6Eps ↑x * n⁻¹ ∈ subsystemGroup .E6 (GaloisField 3 1) JE6 :=
    (Subgroup.mem_normalizer_iff.1 (parabolicLevi_le_normalizer_subsystemGroup_e6 JE6 hn)
      _).1 hxN
  rw [← hmap] at hnN
  obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.1 hnN
  have hzeq : z = ↑g * ↑x * (↑g)⁻¹ := by
    refine e6Eps_injective ?_
    rw [hze, map_mul, map_mul, map_inv, hA, ← hρe]
    calc n * e6Eps ↑x * n⁻¹ =
        n * (e6Eps r * e6Eps ↑x) * (e6Eps r)⁻¹ * n⁻¹ := by
          rw [hcρ]; group
      _ = _ := by group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hzeq]
  exact hz

end Normal

end CFSG.OddStandard.HigherRank.F3
