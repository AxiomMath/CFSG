module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

private def rootSplitTable : Tag → List ℕ
  | .D4 =>
    [1288, 1800, 1029, 2057, 523, 2, 526, 258, 11, 515,
    528, 273, 7, 9, 17, 265, 18, 789, 277, 15,
    21, 535, 531, 2069]
  | .E6 =>
    [1802, 2316, 1543, 2057, 3085, 3599, 529, 2, 787, 259,
    17, 515, 275, 772, 792, 1029, 1050, 795, 11, 542,
    267, 269, 27, 525, 287, 783, 804, 293, 20, 23,
    37, 553, 279, 281, 38, 537, 298, 1070, 302, 32,
    35, 46, 563, 800, 291, 47, 821, 310, 43, 44,
    53, 54, 812, 571, 828, 560, 52, 60, 1076, 1344,
    576, 568, 58, 65, 1091, 579, 574, 837, 834, 327,
    324, 2117]
  | .E7 =>
    [2059, 2573, 1800, 2314, 3342, 3856, 4370, 532, 2, 790,
    259, 20, 515, 278, 772, 795, 1029, 1053, 1286, 1311,
    800, 12, 547, 268, 270, 32, 526, 292, 784, 809,
    1042, 1067, 300, 23, 26, 44, 560, 282, 284, 45,
    540, 305, 798, 823, 1080, 312, 37, 40, 56, 574,
    805, 296, 298, 57, 554, 319, 835, 324, 50, 51,
    54, 67, 68, 586, 819, 310, 69, 589, 846, 335,
    570, 64, 65, 78, 79, 1088, 833, 1366, 598, 856,
    583, 75, 76, 87, 88, 1100, 1118, 606, 607, 593,
    594, 85, 96, 1365, 869, 1126, 614, 857, 603, 93,
    103, 363, 876, 621, 353, 866, 611, 1648, 368, 881,
    361, 874, 1396, 372, 367, 1135, 1143, 375, 371, 889,
    886, 635, 632, 125, 122, 1915]
  | .E8 =>
    [2316, 2830, 2057, 2571, 3599, 4113, 4627, 5141, 535, 2,
    793, 259, 23, 515, 281, 772, 798, 1029, 1056, 1286,
    1314, 1543, 1572, 805, 13, 552, 269, 271, 37, 527,
    297, 785, 814, 1043, 1072, 1301, 1330, 307, 26, 29,
    51, 567, 285, 287, 52, 543, 312, 801, 830, 1059,
    1088, 1089, 321, 42, 45, 65, 583, 810, 301, 303,
    66, 559, 328, 817, 846, 847, 336, 57, 58, 61,
    79, 80, 599, 826, 317, 319, 81, 575, 344, 605,
    862, 351, 579, 73, 74, 77, 94, 95, 615, 1097,
    842, 333, 96, 1386, 618, 876, 365, 595, 89, 90,
    91, 107, 108, 109, 1114, 859, 1142, 630, 631, 889,
    610, 611, 104, 105, 120, 121, 1384, 1129, 898, 1155,
    643, 644, 878, 624, 625, 116, 117, 133, 134, 1397,
    398, 911, 1169, 656, 657, 378, 891, 637, 638, 129,
    146, 1665, 1689, 409, 922, 923, 668, 392, 905, 906,
    651, 141, 157, 1443, 419, 420, 934, 679, 404, 405,
    1172, 918, 663, 1196, 1453, 428, 429, 943, 416, 417,
    1185, 930, 948, 1205, 437, 438, 936, 426, 427, 1195,
    700, 957, 1214, 446, 688, 945, 435, 1459, 196, 709,
    966, 455, 184, 697, 954, 443, 1995, 203, 716, 973,
    193, 706, 963, 1745, 209, 722, 201, 714, 1226, 1494,
    214, 727, 207, 720, 1242, 218, 213, 981, 990, 222,
    217, 473, 482, 226, 221, 732, 741, 485, 481, 999,
    996, 1257, 1254, 1515, 1512, 1773, 1770, 2031, 2028, 5869]
  | .F4 =>
    [1286, 1029, 2571, 2314, 268, 1, 12, 1037, 2833, 787,
    515, 531, 1030, 7, 20, 1046, 2840, 776, 795, 2081,
    284, 269, 15, 29, 784, 529, 800, 545, 1556, 290,
    278, 536, 549, 2331, 1565, 1575, 2072, 2093, 298, 291,
    548, 557, 46, 39, 808, 815, 1066, 2861]
  | .G2 => []

private def rootSplitFst (τ : Tag) (n : ℕ) : ℕ :=
  (rootSplitTable τ).getD n 0 / 256

private def rootSplitSnd (τ : Tag) (n : ℕ) : ℕ :=
  (rootSplitTable τ).getD n 0 % 256

private def SplitOK (τ : Tag) (n : ℕ) : Prop :=
  let k := rootSplitFst τ n
  let l := rootSplitSnd τ n
  k < τ.rootCertificate.roots.length ∧
  l < τ.rootCertificate.roots.length ∧
  τ.rootCertificate.root n = τ.rootCertificate.root k + τ.rootCertificate.root l ∧
  RootOps.isRootB τ (τ.rootCertificate.root k) = true ∧
  RootOps.isRootB τ (τ.rootCertificate.root l) = true ∧
  τ.rootCertificate.root k ≠ τ.rootCertificate.root n ∧
  τ.rootCertificate.root k ≠ -τ.rootCertificate.root n ∧
  τ.rootCertificate.root l ≠ τ.rootCertificate.root n ∧
  τ.rootCertificate.root l ≠ -τ.rootCertificate.root n ∧
  τ.rootCertificate.root k ≠ τ.rootCertificate.root l ∧
  τ.rootCertificate.root k ≠ -τ.rootCertificate.root l ∧
  RootOps.commPairsAt τ k l = [(1, 1)] ∧
  (τ = .F4 →
    RootOps.isRootB τ (τ.rootCertificate.root l - τ.rootCertificate.root k) = false)

private instance splitOKDecidable (τ : Tag) (n : ℕ) : Decidable (SplitOK τ n) := by
  unfold SplitOK
  infer_instance

private theorem splitOK_D4 :
    ∀ n : Fin Tag.D4.rootCertificate.roots.length, SplitOK .D4 n.1 := by
  decide +kernel

private theorem splitOK_E6 :
    ∀ n : Fin Tag.E6.rootCertificate.roots.length, SplitOK .E6 n.1 := by
  decide +kernel

private theorem splitOK_E7 :
    ∀ n : Fin Tag.E7.rootCertificate.roots.length, SplitOK .E7 n.1 := by
  decide +kernel

private theorem splitOK_E8 :
    ∀ n : Fin Tag.E8.rootCertificate.roots.length, SplitOK .E8 n.1 := by
  decide +kernel

private theorem splitOK_F4 :
    ∀ n : Fin Tag.F4.rootCertificate.roots.length, SplitOK .F4 n.1 := by
  decide +kernel

private theorem splitOK_check (τ : Tag)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    ∀ n : Fin τ.rootCertificate.roots.length, SplitOK τ n.1 := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  exacts [splitOK_D4, splitOK_E6, splitOK_E7, splitOK_E8, splitOK_F4]

private theorem split_spec
    (τ : Tag) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {n : ℕ} (hn : n < τ.rootCertificate.roots.length) :
    let k := rootSplitFst τ n
    let l := rootSplitSnd τ n
    k < τ.rootCertificate.roots.length ∧
    l < τ.rootCertificate.roots.length ∧
    IsRoot τ (τ.rootCertificate.root k) ∧
    IsRoot τ (τ.rootCertificate.root l) ∧
    τ.rootCertificate.root n = τ.rootCertificate.root k + τ.rootCertificate.root l ∧
    τ.rootCertificate.root k ≠ τ.rootCertificate.root n ∧
    τ.rootCertificate.root k ≠ -τ.rootCertificate.root n ∧
    τ.rootCertificate.root l ≠ τ.rootCertificate.root n ∧
    τ.rootCertificate.root l ≠ -τ.rootCertificate.root n ∧
    τ.rootCertificate.root k ≠ τ.rootCertificate.root l ∧
    τ.rootCertificate.root k ≠ -τ.rootCertificate.root l ∧
    commPairs τ (τ.rootCertificate.root k) (τ.rootCertificate.root l) = [(1, 1)] ∧
    (τ = .F4 → ¬ IsRoot τ (τ.rootCertificate.root l - τ.rootCertificate.root k)) := by
  have h := splitOK_check τ hτ ⟨n, hn⟩
  unfold SplitOK at h
  dsimp only at h
  rcases h with ⟨hk, hl, hsum, hrootk, hrootl, hk1, hk2, hl1, hl2, hkl1, hkl2, hcp, hdiff⟩
  refine ⟨hk, hl, RootOps.isRootB_iff.1 hrootk, RootOps.isRootB_iff.1 hrootl, hsum,
    hk1, hk2, hl1, hl2, hkl1, hkl2, ?_, ?_⟩
  · rw [← RootOps.commPairsAt_eq]
    exact hcp
  · intro hF hroot
    have hb : RootOps.isRootB τ (τ.rootCertificate.root (rootSplitSnd τ n) -
        τ.rootCertificate.root (rootSplitFst τ n)) = true := RootOps.isRootB_iff.2 hroot
    have hf := hdiff hF
    rw [hb] at hf
    exact Bool.noConfusion hf

private theorem root_split
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ β γ : Fin τ.rank → ℤ,
      IsRoot τ β ∧ IsRoot τ γ ∧ α = β + γ ∧
      β ≠ α ∧ β ≠ -α ∧ γ ≠ α ∧ γ ≠ -α ∧
      β ≠ γ ∧ β ≠ -γ ∧
      commPairs τ β γ = [(1, 1)] ∧
      (τ = .F4 → ¬ IsRoot τ (γ - β)) := by
  obtain ⟨n, hn, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  obtain ⟨hk, hl, hβ, hγ, hsum, hβ1, hβ2, hγ1, hγ2, hβγ1, hβγ2, hcp, hdiff⟩ :=
    split_spec τ hτ hn
  exact ⟨_, _, hβ, hγ, hsum, hβ1, hβ2, hγ1, hγ2, hβγ1, hβγ2, hcp, hdiff⟩

private theorem commutator_unit_of_simplyLaced
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hβγ1 : β ≠ γ) (hβγ2 : β ≠ -γ) (hsum : α = β + γ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        ⁅pinnedX τ R β c, pinnedX τ R γ d⁆ = pinnedX τ R α ((ε : R) * c * d) := by
  obtain ⟨hε, hform⟩ :=
    (simply_laced_root_commutator_unit τ hτ hβ hγ hβγ1 hβγ2).1 (hsum ▸ hα)
  refine ⟨commConst τ β γ (1, 1), hε, ?_⟩
  intro R _ c d
  simpa [← hsum] using hform R c d

private theorem commutator_unit_of_F4
    {α β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (hγ : IsRoot .F4 γ) (hβγ1 : β ≠ γ) (hβγ2 : β ≠ -γ) (hsum : α = β + γ)
    (hcp : commPairs .F4 β γ = [(1, 1)]) (hdiff : ¬ IsRoot .F4 (γ - β)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        ⁅pinnedX .F4 R β c, pinnedX .F4 R γ d⁆ =
          pinnedX .F4 R α ((ε : R) * c * d) := by
  obtain ⟨C, hC, hform⟩ := exists_pinnedX_commFormula_F4_exact hβ hγ hβγ1 hβγ2
  have hC11 : |C (1, 1)| = 1 := by
    have h := hC (1, 1) (by rw [hcp]; exact List.mem_singleton_self _)
    simpa [hdiff] using h
  have hCcases : C (1, 1) = 1 ∨ C (1, 1) = -1 := by
    rcases abs_cases (C (1, 1)) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  refine ⟨C (1, 1), hCcases, ?_⟩
  intro R _ c d
  have h := hform R c d
  rw [hcp] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    one_smul, pow_one] at h
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, h, ← hsum]

private theorem commutator_unit_of_split
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {α β γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hβγ1 : β ≠ γ) (hβγ2 : β ≠ -γ) (hsum : α = β + γ)
    (hcp : commPairs τ β γ = [(1, 1)])
    (hdiff : τ = .F4 → ¬ IsRoot τ (γ - β)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        ⁅pinnedX τ R β c, pinnedX τ R γ d⁆ = pinnedX τ R α ((ε : R) * c * d) := by
  rcases hτ with hτ | hτ | hτ | hτ | hτ
  · exact commutator_unit_of_simplyLaced (Or.inl hτ) hα hβ hγ hβγ1 hβγ2 hsum
  · exact commutator_unit_of_simplyLaced (Or.inr (Or.inl hτ)) hα hβ hγ hβγ1 hβγ2 hsum
  · exact commutator_unit_of_simplyLaced (Or.inr (Or.inr (Or.inl hτ))) hα hβ hγ hβγ1 hβγ2 hsum
  · exact commutator_unit_of_simplyLaced (Or.inr (Or.inr (Or.inr hτ))) hα hβ hγ hβγ1 hβγ2 hsum
  · subst hτ
    exact commutator_unit_of_F4 hβ hγ hβγ1 hβγ2 hsum hcp (hdiff rfl)

private theorem pinnedX_mem_rootSpan_of_split
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    pinnedX τ K α c ∈ rootSpan τ K {β | IsRoot τ β ∧ β ≠ α ∧ β ≠ -α} := by
  obtain ⟨β, γ, hβ, hγ, hsum, hβ1, hβ2, hγ1, hγ2, hβγ1, hβγ2, hcp, hdiff⟩ :=
    root_split hτ hα
  obtain ⟨ε, hε, hform⟩ :=
    commutator_unit_of_split hτ hα hβ hγ hβγ1 hβγ2 hsum hcp hdiff
  set S : Set (Fin τ.rank → ℤ) := {β | IsRoot τ β ∧ β ≠ α ∧ β ≠ -α} with hS
  have hβS : β ∈ S := ⟨hβ, hβ1, hβ2⟩
  have hγS : γ ∈ S := ⟨hγ, hγ1, hγ2⟩
  have hmemX : ∀ δ ∈ S, ∀ x : K, pinnedX τ K δ x ∈ rootSpan τ K S := fun δ hδ x =>
    (le_iSup₂_of_le δ hδ le_rfl : rootSubgroup τ K δ ≤ rootSpan τ K S)
      (Subgroup.subset_closure ⟨x, rfl⟩)
  have hmem : ⁅pinnedX τ K β 1, pinnedX τ K γ ((ε : K) * c)⁆ ∈ rootSpan τ K S := by
    have hle : ⁅rootSpan τ K S, rootSpan τ K S⁆ ≤ rootSpan τ K S :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact hle (Subgroup.commutator_mem_commutator (hmemX β hβS 1)
      (hmemX γ hγS ((ε : K) * c)))
  have heq : ⁅pinnedX τ K β 1, pinnedX τ K γ ((ε : K) * c)⁆ = pinnedX τ K α c := by
    rw [hform K 1 ((ε : K) * c)]
    congr 1
    rcases hε with rfl | rfl <;> push_cast <;> ring
  rwa [heq] at hmem

theorem adjointGroup_eq_rootSpan_ne_pm
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {α₀ : Fin τ.rank → ℤ}
    (hα₀ : IsRoot τ α₀) :
    adjointGroup τ K = rootSpan τ K {β | IsRoot τ β ∧ β ≠ α₀ ∧ β ≠ -α₀} := by
  refine le_antisymm ?_ (iSup₂_le fun β _ => rootSubgroup_le_adjointGroup β)
  rw [adjointGroup_eq_rootSpan]
  refine iSup₂_le fun β hβ => ?_
  by_cases hβ0 : β = α₀
  · subst hβ0
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_rootSpan_of_split hτ hα₀ c
  · by_cases hβ1 : β = -α₀
    · subst hβ1
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      have h := pinnedX_mem_rootSpan_of_split hτ (IsRoot.neg hα₀) c
      have hset : {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ γ ≠ -α₀ ∧ γ ≠ -(-α₀)} =
          {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ γ ≠ α₀ ∧ γ ≠ -α₀} := by
        ext γ
        simp [neg_neg, and_comm, and_left_comm, and_assoc]
      rw [hset] at h
      exact h
    · exact le_iSup₂_of_le β ⟨hβ, hβ0, hβ1⟩ le_rfl

theorem iSup_subgroupOf_rootSubgroup_ne_pm
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {α₀ : Fin τ.rank → ℤ}
    (hα₀ : IsRoot τ α₀) :
    (⨆ (β : Fin τ.rank → ℤ) (_ : IsRoot τ β ∧ β ≠ α₀ ∧ β ≠ -α₀),
      (rootSubgroup τ K β).subgroupOf (adjointGroup τ K)) = ⊤ := by
  let S : Set (Fin τ.rank → ℤ) := {β | IsRoot τ β ∧ β ≠ α₀ ∧ β ≠ -α₀}
  let A : Subgroup (adjointGroup τ K) :=
    ⨆ (β : Fin τ.rank → ℤ) (_ : IsRoot τ β ∧ β ≠ α₀ ∧ β ≠ -α₀),
      (rootSubgroup τ K β).subgroupOf (adjointGroup τ K)
  have hmap : A.map (adjointGroup τ K).subtype = rootSpan τ K S := by
    dsimp [A, S, rootSpan]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun β => iSup_congr fun hβ =>
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup β)
  have htop : A = ⊤ := by
    apply Subgroup.map_injective (f := (adjointGroup τ K).subtype) Subtype.val_injective
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
    exact (adjointGroup_eq_rootSpan_ne_pm (K := K) hτ hα₀).symm
  simpa [A] using htop

end CFSG.LieType.Chevalley
