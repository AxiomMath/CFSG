module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance f4PilotAlignToriNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def leviTorus (J : Finset (Fin (Tag.rank .F4))) : Subgroup (ModGL .F4 K) :=
  (Subgroup.pi (J : Set (Fin (Tag.rank .F4))) fun _ => (⊥ : Subgroup Kˣ)).map
    (rootDiagUnitHom .F4 K)

theorem mem_leviTorus {J : Finset (Fin (Tag.rank .F4))} {g : ModGL .F4 K} :
    g ∈ leviTorus K J ↔ ∃ b : Fin (Tag.rank .F4) → Kˣ, (∀ j ∈ J, b j = 1) ∧
      rootDiagUnit .F4 b = g := by
  simp only [leviTorus, mem_map, mem_pi, Finset.mem_coe, mem_bot]
  rfl

theorem rootDiagUnit_mem_leviTorus {J : Finset (Fin (Tag.rank .F4))}
    {b : Fin (Tag.rank .F4) → Kˣ} (hb : ∀ j ∈ J, b j = 1) : rootDiagUnit .F4 b ∈ leviTorus K J :=
  mem_leviTorus.2 ⟨b, hb, rfl⟩

theorem leviTorus_anti {J J' : Finset (Fin (Tag.rank .F4))} (h : J ⊆ J') :
    leviTorus K J' ≤ leviTorus K J := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hg
  exact rootDiagUnit_mem_leviTorus fun j hj => hb j (h hj)

variable (K) in
theorem antitone_leviTorus : Antitone (leviTorus K) := fun _ _ h => leviTorus_anti h

private theorem eq_vec_four (b : Fin (Tag.rank .F4) → Kˣ) : b = ![b 0, b 1, b 2, b 3] := by
  funext i
  fin_cases i <;> rfl

variable (K) in
theorem torusLineR_eq_leviTorus : torusLineR K = leviTorus K {1, 2, 3} := by
  ext g
  rw [mem_torusLineR, mem_leviTorus]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨rDiag c, fun j hj => ?_, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> rfl
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b 0, congrArg _ ?_⟩
    rw [rDiag_eq, eq_vec_four b, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)]
    rfl

variable (K) in
@[expose] noncomputable def torusLineS : Subgroup (ModGL .F4 K) := leviTorus K {0, 1, 2}

theorem mem_torusLineS {g : ModGL .F4 K} :
    g ∈ torusLineS K ↔ ∃ c : Kˣ, rootDiagUnit .F4 ![1, 1, 1, c] = g := by
  rw [torusLineS, mem_leviTorus]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b 3, congrArg _ ?_⟩
    rw [eq_vec_four b, hb 0 (by decide), hb 1 (by decide), hb 2 (by decide)]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨_, fun j hj => ?_, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> rfl

theorem torusLineS_le_leviTorus {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ {0, 1, 2}) :
    torusLineS K ≤ leviTorus K J :=
  leviTorus_anti hJ

section Weyl


private theorem weylElt_one_conj_rootDiagUnit (a : Fin (Tag.rank .F4) → Kˣ)
    (i : Fin (Tag.rank .F4)) :
    weylElt .F4 K i 1 * rootDiagUnit .F4 a * (weylElt .F4 K i 1)⁻¹ =
      rootDiagUnit .F4 (fun j => a j * a i ^ (-Tag.cartan .F4 i j)) := by
  have h := rootDiagUnit_conj_weylElt_one (K := K) a i
  have h2 : weylElt .F4 K i 1 * rootDiagUnit .F4 a * (weylElt .F4 K i 1)⁻¹ =
      (torusElt .F4 K i (a i))⁻¹ * rootDiagUnit .F4 a := by
    rw [eq_inv_mul_iff_mul_eq]
    calc torusElt .F4 K i (a i) * (weylElt .F4 K i 1 * rootDiagUnit .F4 a *
          (weylElt .F4 K i 1)⁻¹) =
        (rootDiagUnit .F4 a * weylElt .F4 K i 1 * (rootDiagUnit .F4 a)⁻¹) *
          rootDiagUnit .F4 a * (weylElt .F4 K i 1)⁻¹ := by rw [h]; group
      _ = rootDiagUnit .F4 a := by group
  rw [h2, torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  rw [mul_comm]

private theorem coe_n1242_eq : (n1242 K : ModGL .F4 K) = weylElt .F4 K 1 1 * weylElt .F4 K 0 1 := by
  rw [coe_n1242]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem n1242_conj_rDiag (c : Kˣ) :
    (n1242 K : ModGL .F4 K) * rootDiagUnit .F4 (rDiag c) * (n1242 K : ModGL .F4 K)⁻¹ =
      rootDiagUnit .F4 ![1, c⁻¹, c, 1] := by
  rw [coe_n1242_eq]
  calc weylElt .F4 K 1 1 * weylElt .F4 K 0 1 * rootDiagUnit .F4 (rDiag c) *
        (weylElt .F4 K 1 1 * weylElt .F4 K 0 1)⁻¹ =
      weylElt .F4 K 1 1 * (weylElt .F4 K 0 1 * rootDiagUnit .F4 (rDiag c) *
        (weylElt .F4 K 0 1)⁻¹) * (weylElt .F4 K 1 1)⁻¹ := by group
    _ = _ := by
      rw [weylElt_one_conj_rootDiagUnit, weylElt_one_conj_rootDiagUnit]
      congr 1
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> decide
      rcases hj with rfl | rfl | rfl | rfl
      · show c * c ^ (-2 : ℤ) * (1 * c ^ (1 : ℤ)) ^ (1 : ℤ) = 1
        group
      · show 1 * c ^ (1 : ℤ) * (1 * c ^ (1 : ℤ)) ^ (-2 : ℤ) = c⁻¹
        group
      · show 1 * c ^ (0 : ℤ) * (1 * c ^ (1 : ℤ)) ^ (1 : ℤ) = c
        group
      · show 1 * c ^ (0 : ℤ) * (1 * c ^ (1 : ℤ)) ^ (0 : ℤ) = 1
        group

variable (K) in
@[expose] noncomputable def torusLine1242 : Subgroup (ModGL .F4 K) :=
  (torusLineR K).map (MulAut.conj (n1242 K : ModGL .F4 K)).toMonoidHom

theorem mem_torusLine1242_iff {g : ModGL .F4 K} :
    g ∈ torusLine1242 K ↔ ∃ c : Kˣ, rootDiagUnit .F4 ![1, c⁻¹, c, 1] = g := by
  simp only [torusLine1242, mem_map, mem_torusLineR, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (n1242_conj_rDiag c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, n1242_conj_rDiag c⟩

theorem torusLine1242_le_leviTorus {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ {0, 3}) :
    torusLine1242 K ≤ leviTorus K J := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_torusLine1242_iff.1 hg
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  have h := hJ hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl <;> rfl

end Weyl

namespace AmalgamNeighbour


variable (K) in
@[expose] noncomputable def torus : AmalgamNeighbour → Subgroup (ModGL .F4 K)
  | X => torusLineR K
  | Y => torusLineS K
  | X' => torusLine1242 K

theorem torus_le_leviTorus (N : AmalgamNeighbour) {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ N.nodes) : N.torus K ≤ leviTorus K J := by
  cases N
  · rw [torus, torusLineR_eq_leviTorus]
    exact leviTorus_anti hJ
  · exact torusLineS_le_leviTorus hJ
  · exact torusLine1242_le_leviTorus hJ

end AmalgamNeighbour

section Adjoint


theorem leviTorus_le_adjointGroup (J : Finset (Fin (Tag.rank .F4))) :
    leviTorus K J ≤ adjointGroup .F4 K := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hg
  exact f4RootDiagUnit_mem_adjointGroup b

theorem AmalgamNeighbour.torus_le_adjointGroup (N : AmalgamNeighbour) :
    N.torus K ≤ adjointGroup .F4 K :=
  (N.torus_le_leviTorus (Finset.empty_subset _)).trans (leviTorus_le_adjointGroup ∅)

end Adjoint

private theorem rootChar_mulSingle_eq (i : Fin (Tag.rank .F4)) (c : Kˣ)
    (v : Fin (Tag.rank .F4) → ℤ) : rootChar (Pi.mulSingle i c) v = c ^ v i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by
      rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]

theorem leviTorus_kill_check : ∀ γ ∈ rootFinset .F4, (∀ i : Fin (Tag.rank .F4), |γ i| ≤ 4) ∧
    ∀ m ∈ ([3, 4] : List ℤ),
      (Finset.univ.filter fun i : Fin (Tag.rank .F4) => ¬m ∣ γ i).card ≤ 2 →
        ∀ i : Fin (Tag.rank .F4), m ∣ γ i → γ i = 0 := by
  decide +kernel

@[expose] def root1342 : Fin (Tag.rank .F4) → ℤ := ![1, 3, 4, 2]

theorem root1342_mem_rootFinset : root1342 ∈ rootFinset .F4 := by decide +kernel

theorem isRoot_root1342 : IsRoot .F4 root1342 :=
  mem_rootFinset.1 root1342_mem_rootFinset

theorem root1342_coeff_check : ∀ i ∉ ({0, 2, 3} : Finset (Fin (Tag.rank .F4))),
    ((4 - 1 : ℕ) : ℤ) ∣ root1342 i := by
  decide +kernel

section Kill


theorem rootSubgroup_le_centralizer_leviTorus_of_rootChar {J : Finset (Fin (Tag.rank .F4))}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h : ∀ b : Fin (Tag.rank .F4) → Kˣ, (∀ j ∈ J, b j = 1) → rootChar b γ = 1) :
    rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro t ht
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 ht
  have hconj := rootDiagUnit_conj_pinnedX b hγ c
  rw [h b hb, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem rootSubgroup_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .F4))}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (h : ∀ i ∉ J, γ i = 0) :
    rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) :=
  rootSubgroup_le_centralizer_leviTorus_of_rootChar hγ fun b hb =>
    Finset.prod_eq_one fun i _ => by
      by_cases hi : i ∈ J
      · rw [hb i hi, one_zpow]
      · rw [h i hi, zpow_zero]

theorem rootSpan_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .F4))}
    {S : Set (Fin (Tag.rank .F4) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .F4 γ ∧ ∀ i ∉ J, γ i = 0) :
    rootSpan .F4 K S ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) :=
  iSup₂_le fun γ hγ => rootSubgroup_le_centralizer_leviTorus (hS γ hγ).1 (hS γ hγ).2

theorem rootSpan_amalgamRoots_le_centralizer_leviTorus (J : Finset (Fin (Tag.rank .F4))) :
    rootSpan .F4 K (amalgamRoots J) ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) := by
  refine rootSpan_le_centralizer_leviTorus fun γ hγ => ⟨isRoot_of_mem_amalgamRoots hγ, ?_⟩
  obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> intro i hi <;> have hij : i ≠ j := fun h => hi (h ▸ hj)
  · exact Pi.single_eq_of_ne hij _
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hij, neg_zero]

theorem dvd_coeff_of_rootSubgroup_le_centralizer_leviTorus [Finite K]
    {J : Finset (Fin (Tag.rank .F4))} {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h : rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K))) :
    ∀ i ∉ J, ((Nat.card K - 1 : ℕ) : ℤ) ∣ γ i := by
  intro i hi
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hT : rootDiagUnit .F4 (Pi.mulSingle i c) ∈ leviTorus K J :=
    rootDiagUnit_mem_leviTorus fun j hj => by
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact Pi.mulSingle_eq_of_ne (M := fun _ => Kˣ) hji c
  have hcomm := mem_centralizer_iff.1 (h (mem_rootSubgroup.2 ⟨1, rfl⟩)) _ hT
  have hconj := rootDiagUnit_conj_pinnedX (Pi.mulSingle i c) hγ (1 : K)
  rw [hcomm, mul_inv_cancel_right, mul_one] at hconj
  have h1 : ((rootChar (Pi.mulSingle i c) γ : Kˣ) : K) = 1 :=
    (pinnedX_injective .F4 K γ hconj).symm
  rw [rootChar_mulSingle_eq] at h1
  have h2 : c ^ γ i = 1 := Units.ext h1
  rw [← orderOf_dvd_iff_zpow_eq_one, hc, Nat.card_units] at h2
  exact h2

theorem rootSubgroup_le_centralizer_leviTorus_iff_dvd [Finite K]
    {J : Finset (Fin (Tag.rank .F4))} {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) ↔
      ∀ i ∉ J, ((Nat.card K - 1 : ℕ) : ℤ) ∣ γ i := by
  refine ⟨dvd_coeff_of_rootSubgroup_le_centralizer_leviTorus hγ, fun h => ?_⟩
  refine rootSubgroup_le_centralizer_leviTorus_of_rootChar hγ fun b hb =>
    Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i ∈ J
  · rw [hb i hi, one_zpow]
  · have hord : (orderOf (b i) : ℤ) ∣ γ i := by
      refine (Int.natCast_dvd_natCast.2 ?_).trans (h i hi)
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard (b i)
    exact orderOf_dvd_iff_zpow_eq_one.1 hord

theorem rootSubgroup_root1342_le_centralizer_leviTorus_of_card_eq_four [Finite K]
    (hq : Nat.card K = 4) :
    rootSubgroup .F4 K root1342 ≤ centralizer (leviTorus K {0, 2, 3} : Set (ModGL .F4 K)) ∧
      root1342 1 ≠ 0 := by
  refine ⟨(rootSubgroup_le_centralizer_leviTorus_iff_dvd isRoot_root1342).2 ?_, by decide⟩
  rw [hq]
  exact root1342_coeff_check

theorem coeff_eq_zero_of_rootSubgroup_le_centralizer_leviTorus_of_six_le [Finite K]
    (hq : 6 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ)
    (h : rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K))) :
    ∀ i ∉ J, γ i = 0 := by
  intro i hi
  have hd := dvd_coeff_of_rootSubgroup_le_centralizer_leviTorus hγ h i hi
  have hb := (leviTorus_kill_check γ (mem_rootFinset.2 hγ)).1 i
  refine Int.eq_zero_of_abs_lt_dvd hd ?_
  have : (5 : ℤ) ≤ ((Nat.card K - 1 : ℕ) : ℤ) := by omega
  omega

theorem coeff_eq_zero_of_rootSubgroup_le_centralizer_leviTorus [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ)
    (h : rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K))) :
    ∀ i ∉ J, γ i = 0 := by
  have hd := dvd_coeff_of_rootSubgroup_le_centralizer_leviTorus hγ h
  obtain ⟨hb, hcheck⟩ := leviTorus_kill_check γ (mem_rootFinset.2 hγ)
  set m : ℤ := ((Nat.card K - 1 : ℕ) : ℤ) with hm
  have hm3 : 3 ≤ m := by omega
  by_cases hm5 : 5 ≤ m
  · intro i hi
    refine Int.eq_zero_of_abs_lt_dvd (hd i hi) ?_
    have := hb i
    omega
  · have hmem : m ∈ ([3, 4] : List ℤ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hsub : (Finset.univ.filter fun i : Fin (Tag.rank .F4) => ¬m ∣ γ i) ⊆ J := by
      intro i hi
      by_contra hiJ
      exact (Finset.mem_filter.1 hi).2 (hd i hiJ)
    have hcard := (Finset.card_le_card hsub).trans hJ
    exact fun i hi => hcheck m hmem hcard i (hd i hi)

theorem rootSubgroup_le_centralizer_leviTorus_iff [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) ↔ ∀ i ∉ J, γ i = 0 :=
  ⟨coeff_eq_zero_of_rootSubgroup_le_centralizer_leviTorus hq hJ hγ,
    rootSubgroup_le_centralizer_leviTorus hγ⟩

theorem rootSubgroup_le_centralizer_leviTorus_iff_of_six_le [Finite K] (hq : 6 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    rootSubgroup .F4 K γ ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)) ↔ ∀ i ∉ J, γ i = 0 :=
  ⟨coeff_eq_zero_of_rootSubgroup_le_centralizer_leviTorus_of_six_le hq hγ,
    rootSubgroup_le_centralizer_leviTorus hγ⟩

end Kill

end CFSG.SeitzReduction.F4Pilot
