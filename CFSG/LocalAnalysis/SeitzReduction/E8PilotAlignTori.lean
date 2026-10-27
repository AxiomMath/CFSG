module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAmalgamWeyl
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e8PilotAlignToriNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem symmetrizedCartan_E8 : Tag.symmetrizedCartan .E8 = Tag.cartan .E8 := by
  decide +kernel

theorem cartan_E8_transpose : (Tag.cartan .E8).transpose = Tag.cartan .E8 := by
  decide +kernel

theorem cartan_E8_symm (i j : Fin (Tag.rank .E8)) : Tag.cartan .E8 i j = Tag.cartan .E8 j i := by
  conv_lhs => rw [← cartan_E8_transpose]
  rfl

theorem iform_single_right_E8 (δ : Fin (Tag.rank .E8) → ℤ) (l : Fin (Tag.rank .E8)) :
    iform δ (Pi.single l 1) = ∑ j, δ j * Tag.cartan .E8 j l := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, symmetrizedCartan_E8]

theorem iform_single_single_E8 (i j : Fin (Tag.rank .E8)) :
    iform (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single j 1) = Tag.cartan .E8 i j := by
  rw [iform_single_right_E8, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, one_mul]

section Sum

theorem iform_sum_right_E8 {ι : Type*} (s : Finset ι) (γ : Fin (Tag.rank .E8) → ℤ)
    (f : ι → Fin (Tag.rank .E8) → ℤ) : iform γ (∑ k ∈ s, f k) = ∑ k ∈ s, iform γ (f k) :=
  map_sum (AddMonoidHom.mk' (iform γ) (iform_add_right γ)) f s

theorem iform_reflect_single_E8 (i j : Fin (Tag.rank .E8)) (δ : Fin (Tag.rank .E8) → ℤ) :
    iform (reflect .E8 i δ) (Pi.single j 1) =
      iform δ (Pi.single j 1) - iform δ (Pi.single i 1) * Tag.cartan .E8 i j := by
  have hc : ∑ k, Tag.cartan .E8 i k * δ k = iform δ (Pi.single i 1) := by
    rw [iform_single_right_E8]
    exact Finset.sum_congr rfl fun k _ => by rw [cartan_E8_symm, mul_comm]
  rw [reflect, sub_eq_add_neg, ← neg_smul, iform_add_left, iform_smul_left,
    iform_single_single_E8, hc]
  ring

theorem abs_iform_le_two {δ γ : Fin (Tag.rank .E8) → ℤ} (hδ : IsRoot .E8 δ) (hγ : IsRoot .E8 γ) :
    |iform δ γ| ≤ 2 := by
  have h1 := EPilot.iform_self_nonneg (δ + γ)
  have h2 := EPilot.iform_self_nonneg (δ - γ)
  have hδδ := EPilot.iform_self_eq_two (Or.inr (Or.inr rfl)) hδ
  have hγγ := EPilot.iform_self_eq_two (Or.inr (Or.inr rfl)) hγ
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm γ δ] at h1
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm γ δ] at h2
  rw [abs_le]
  constructor <;> linarith

end Sum

@[expose] def invCartan : Matrix (Fin (Tag.rank .E8)) (Fin (Tag.rank .E8)) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem cartan_mul_invCartan_transpose : Tag.cartan .E8 * invCartan.transpose = 1 := by
  decide +kernel

theorem invCartan_mul_cartan : invCartan * Tag.cartan .E8 = 1 := by
  decide +kernel

@[expose] def fundWeight (i : Fin (Tag.rank .E8)) : Fin (Tag.rank .E8) → ℤ :=
  fun l => invCartan i l

theorem iform_fundWeight (v : Fin (Tag.rank .E8) → ℤ) (i : Fin (Tag.rank .E8)) :
    iform v (fundWeight i) = v i := by
  have hA : ∀ k, ∑ j, Tag.cartan .E8 k j * invCartan i j = if k = i then 1 else 0 := by
    intro k
    have h := congrFun (congrFun cartan_mul_invCartan_transpose k) i
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa only [Matrix.transpose_apply] using h
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_single_right_E8, fundWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ k, ∑ j, invCartan i j * (v k * Tag.cartan .E8 k j) =
      ∑ k, v k * ∑ j, Tag.cartan .E8 k j * invCartan i j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = v i := by simp only [hA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]

theorem dvd_apply_of_forall_dvd_iform_single {m : ℤ} {v : Fin (Tag.rank .E8) → ℤ}
    (h : ∀ l, m ∣ iform v (Pi.single l 1)) (i : Fin (Tag.rank .E8)) : m ∣ v i := by
  rw [← iform_fundWeight v i, F4Pilot.iform_eq_sum_mul_iform_single]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l) _

section Adjoint

theorem rootDiagUnit_mem_torusGroup_E8 (b : Fin (Tag.rank .E8) → Kˣ) :
    rootDiagUnit .E8 b ∈ torusGroup .E8 K := by
  set t : Fin (Tag.rank .E8) → Kˣ := fun j => ∏ l, b l ^ invCartan l j with ht
  have hchar : cartanChar t = b := by
    funext l'
    have hB : ∀ l, ∑ j, invCartan l j * Tag.cartan .E8 j l' = if l = l' then 1 else 0 := by
      intro l
      have h := congrFun (congrFun invCartan_mul_cartan l) l'
      rwa [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [cartanChar, ht, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow_eq_zpow_sum, hB]
    rw [Finset.prod_eq_single l' (fun x _ hx => by rw [ite_eq_right hx, zpow_zero])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left (rfl : l' = l'), zpow_one]
  rw [← hchar, ← list_prod_torusElt_eq_rootDiagUnit]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨(j, t j), rfl⟩

theorem rootDiagUnit_mem_adjointGroup_E8 (b : Fin (Tag.rank .E8) → Kˣ) :
    rootDiagUnit .E8 b ∈ adjointGroup .E8 K := by
  have hle : torusGroup .E8 K ≤ adjointGroup .E8 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, rfl⟩
    exact torusElt_mem_adjointGroup q.1 q.2
  exact hle (rootDiagUnit_mem_torusGroup_E8 b)

end Adjoint

variable (K) in
@[expose] noncomputable def leviTorus (J : Finset (Fin (Tag.rank .E8))) :
    Subgroup (ModGL .E8 K) :=
  (Subgroup.pi (J : Set (Fin (Tag.rank .E8))) fun _ => (⊥ : Subgroup Kˣ)).map
    (rootDiagUnitHom .E8 K)

theorem mem_leviTorus {J : Finset (Fin (Tag.rank .E8))} {g : ModGL .E8 K} :
    g ∈ leviTorus K J ↔ ∃ b : Fin (Tag.rank .E8) → Kˣ, (∀ j ∈ J, b j = 1) ∧
      rootDiagUnit .E8 b = g := by
  simp only [leviTorus, mem_map, mem_pi, Finset.mem_coe, mem_bot]
  rfl

theorem rootDiagUnit_mem_leviTorus {J : Finset (Fin (Tag.rank .E8))}
    {b : Fin (Tag.rank .E8) → Kˣ} (hb : ∀ j ∈ J, b j = 1) : rootDiagUnit .E8 b ∈ leviTorus K J :=
  mem_leviTorus.2 ⟨b, hb, rfl⟩

section Adjoint

theorem leviTorus_le_adjointGroup (J : Finset (Fin (Tag.rank .E8))) :
    leviTorus K J ≤ adjointGroup .E8 K := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hg
  exact rootDiagUnit_mem_adjointGroup_E8 b

theorem leviTorus_le_torusGroup (J : Finset (Fin (Tag.rank .E8))) :
    leviTorus K J ≤ torusGroup .E8 K := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hg
  exact rootDiagUnit_mem_torusGroup_E8 b

end Adjoint

@[expose] def corootTuple (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ) : Fin (Tag.rank .E8) → Kˣ :=
  fun i => c ^ iform δ (Pi.single i 1)

theorem rootChar_corootTuple (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ) (v : Fin (Tag.rank .E8) → ℤ) :
    rootChar (corootTuple δ c) v = c ^ iform δ v := by
  rw [rootChar, F4Pilot.iform_eq_sum_mul_iform_single δ v, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [corootTuple, ← zpow_mul, mul_comm]

theorem corootTuple_one (δ : Fin (Tag.rank .E8) → ℤ) : corootTuple δ (1 : Kˣ) = 1 := by
  funext i
  simp [corootTuple]

theorem corootTuple_mul (δ : Fin (Tag.rank .E8) → ℤ) (c d : Kˣ) :
    corootTuple δ (c * d) = corootTuple δ c * corootTuple δ d := by
  funext i
  simp only [corootTuple, Pi.mul_apply, mul_zpow]

theorem rootDiagUnit_corootTuple_mem_leviTorus {J : Finset (Fin (Tag.rank .E8))}
    {δ : Fin (Tag.rank .E8) → ℤ} (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) (c : Kˣ) :
    rootDiagUnit .E8 (corootTuple δ c) ∈ leviTorus K J :=
  rootDiagUnit_mem_leviTorus fun j hj => by rw [corootTuple, h j hj, zpow_zero]

section Adjoint

theorem rootDiagUnit_corootTuple_mem_adjointGroup (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ) :
    rootDiagUnit .E8 (corootTuple δ c) ∈ adjointGroup .E8 K :=
  rootDiagUnit_mem_adjointGroup_E8 _

end Adjoint

theorem corootTuple_highRoot (c : Kˣ) : corootTuple (highRoot .E8) c = EPilot.highDiag .E8 c := by
  funext i
  rw [corootTuple, EPilot.iform_highRoot_single (Or.inr (Or.inr rfl)), EPilot.highDiag_apply]

variable (K) in
@[expose] def corootTupleHom (δ : Fin (Tag.rank .E8) → ℤ) : Kˣ →* (Fin (Tag.rank .E8) → Kˣ) where
  toFun := corootTuple δ
  map_one' := corootTuple_one δ
  map_mul' := corootTuple_mul δ

variable (K) in
@[expose] noncomputable def corootLine (δ : Fin (Tag.rank .E8) → ℤ) : Subgroup (ModGL .E8 K) :=
  ((rootDiagUnitHom .E8 K).comp (corootTupleHom K δ)).range

theorem mem_corootLine {δ : Fin (Tag.rank .E8) → ℤ} {g : ModGL .E8 K} :
    g ∈ corootLine K δ ↔ ∃ c : Kˣ, rootDiagUnit .E8 (corootTuple δ c) = g :=
  MonoidHom.mem_range

theorem rootDiagUnit_corootTuple_mem_corootLine (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ) :
    rootDiagUnit .E8 (corootTuple δ c) ∈ corootLine K δ :=
  mem_corootLine.2 ⟨c, rfl⟩

theorem corootLine_le_leviTorus {J : Finset (Fin (Tag.rank .E8))} {δ : Fin (Tag.rank .E8) → ℤ}
    (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) : corootLine K δ ≤ leviTorus K J := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_leviTorus h c

theorem corootLine_le_adjointGroup
    (δ : Fin (Tag.rank .E8) → ℤ) : corootLine K δ ≤ adjointGroup .E8 K := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_adjointGroup δ c

theorem corootLine_highRoot : corootLine K (highRoot .E8) = EPilot.highTorusLine .E8 K := by
  ext g
  rw [mem_corootLine, EPilot.mem_highTorusLine]
  simp only [corootTuple_highRoot]

section Weyl

theorem weylElt_one_conj_corootTuple (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ)
    (i : Fin (Tag.rank .E8)) :
    weylElt .E8 K i 1 * rootDiagUnit .E8 (corootTuple δ c) * (weylElt .E8 K i 1)⁻¹ =
      rootDiagUnit .E8 (corootTuple (reflect .E8 i δ) c) := by
  rw [E6Pilot.weylElt_one_conj_rootDiagUnit_eq]
  congr 1
  funext j
  rw [corootTuple, corootTuple, corootTuple, iform_reflect_single_E8, ← zpow_mul, ← zpow_add]
  congr 1
  ring

theorem list_prod_weylElt_conj_corootTuple (ω : List (Fin (Tag.rank .E8)))
    (δ : Fin (Tag.rank .E8) → ℤ) (c : Kˣ) :
    (ω.map fun i => weylElt .E8 K i 1).prod * rootDiagUnit .E8 (corootTuple δ c) *
        ((ω.map fun i => weylElt .E8 K i 1).prod)⁻¹ =
      rootDiagUnit .E8 (corootTuple ((coxeterSystem .E8).wordProd ω • δ) c) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, (coxeterSystem .E8).wordProd_cons, mul_smul,
      simple_smul]
    calc weylElt .E8 K i 1 * (ω.map fun i => weylElt .E8 K i 1).prod *
          rootDiagUnit .E8 (corootTuple δ c) *
          (weylElt .E8 K i 1 * (ω.map fun i => weylElt .E8 K i 1).prod)⁻¹ =
        weylElt .E8 K i 1 * ((ω.map fun i => weylElt .E8 K i 1).prod *
          rootDiagUnit .E8 (corootTuple δ c) * ((ω.map fun i => weylElt .E8 K i 1).prod)⁻¹) *
          (weylElt .E8 K i 1)⁻¹ := by group
      _ = _ := by rw [ih, weylElt_one_conj_corootTuple]

theorem map_conj_rep_corootLine (N : E8Neighbour) (δ : Fin (Tag.rank .E8) → ℤ) :
    (corootLine K δ).map (MulAut.conj (N.rep K : ModGL .E8 K)).toMonoidHom =
      corootLine K (N.weyl • δ) := by
  ext g
  simp only [mem_map, mem_corootLine, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    E8Neighbour.coe_rep]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (list_prod_weylElt_conj_corootTuple N.word δ c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, list_prod_weylElt_conj_corootTuple N.word δ c⟩

end Weyl

namespace E8Neighbour

variable (K) in
@[expose] noncomputable def torus (N : E8Neighbour) : Subgroup (ModGL .E8 K) :=
  corootLine K N.root

theorem torus_high : high.torus K = EPilot.highTorusLine .E8 K :=
  corootLine_highRoot

theorem torus_le_leviTorus (N : E8Neighbour) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) : N.torus K ≤ leviTorus K J :=
  corootLine_le_leviTorus fun j hj => (N.iform_root_single_eq_zero_iff j).2 (hJ hj)

theorem torus_le_adjointGroup
    (N : E8Neighbour) : N.torus K ≤ adjointGroup .E8 K :=
  corootLine_le_adjointGroup _

theorem map_conj_rep_torus_high
    (N : E8Neighbour) :
    (high.torus K).map (MulAut.conj (N.rep K : ModGL .E8 K)).toMonoidHom = N.torus K := by
  rw [torus, map_conj_rep_corootLine]
  exact congrArg (corootLine K) (weyl_smul_highRoot N)

end E8Neighbour

@[expose] def perpPositions (J : Finset (Fin (Tag.rank .E8))) : Finset ℕ :=
  (Finset.range Tag.E8.rootCertificate.roots.length).filter fun k =>
    0 < height (Tag.E8.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E8.rootCertificate.root k) (Pi.single j 1) = 0

@[expose] def casimirVec (J : Finset (Fin (Tag.rank .E8))) (i : Fin (Tag.rank .E8)) :
    Fin (Tag.rank .E8) → ℤ :=
  ∑ k ∈ perpPositions J, Tag.E8.rootCertificate.root k i • Tag.E8.rootCertificate.root k

@[expose] def perpCoxeter (J : Finset (Fin (Tag.rank .E8))) : ℤ :=
  2 * (perpPositions J).card / (8 - J.card)

set_option maxRecDepth 100000 in
theorem casimir_check : ∀ J : Finset (Fin (Tag.rank .E8)), J.card ≤ 2 → perpCoxeter J ≠ 0 ∧
    ∀ i ∉ J, casimirVec J i = perpCoxeter J • fundWeight i := by
  decide +kernel

section Roots

theorem isRoot_of_mem_perpPositions {J : Finset (Fin (Tag.rank .E8))} {k : ℕ}
    (hk : k ∈ perpPositions J) :
    IsRoot .E8 (Tag.E8.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E8.rootCertificate.root k) (Pi.single j 1) = 0 := by
  rw [perpPositions, Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨RootCertificate.isRoot_root Tag.E8.rootCertificate_check k hk.1, hk.2.2⟩

theorem iform_casimirVec (v : Fin (Tag.rank .E8) → ℤ) (J : Finset (Fin (Tag.rank .E8)))
    (i : Fin (Tag.rank .E8)) :
    iform v (casimirVec J i) = ∑ k ∈ perpPositions J,
      Tag.E8.rootCertificate.root k i * iform v (Tag.E8.rootCertificate.root k) := by
  rw [casimirVec, iform_sum_right_E8]
  simp only [iform_smul_right]

theorem coeff_eq_zero_of_forall_iform_eq_zero {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J.card ≤ 2) {v : Fin (Tag.rank .E8) → ℤ}
    (h : ∀ δ, IsRoot .E8 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → iform v δ = 0) :
    ∀ i ∉ J, v i = 0 := by
  intro i hi
  obtain ⟨hne, hcas⟩ := casimir_check J hJ
  have h0 : iform v (casimirVec J i) = 0 := by
    rw [iform_casimirVec]
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hδ, hδJ⟩ := isRoot_of_mem_perpPositions hk
    rw [h _ hδ hδJ, mul_zero]
  rw [hcas i hi, iform_smul_right, iform_fundWeight] at h0
  exact (mul_eq_zero.1 h0).resolve_left hne

end Roots

section Kill

theorem rootSubgroup_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E8))}
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) (h : ∀ i ∉ J, γ i = 0) :
    rootSubgroup .E8 K γ ≤ centralizer (leviTorus K J : Set (ModGL .E8 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro t ht
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 ht
  have hconj := rootDiagUnit_conj_pinnedX b hγ c
  have h1 : rootChar b γ = 1 := Finset.prod_eq_one fun i _ => by
    by_cases hi : i ∈ J
    · rw [hb i hi, one_zpow]
    · rw [h i hi, zpow_zero]
  rw [h1, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem rootSpan_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E8))}
    {S : Set (Fin (Tag.rank .E8) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E8 γ ∧ ∀ i ∉ J, γ i = 0) :
    rootSpan .E8 K S ≤ centralizer (leviTorus K J : Set (ModGL .E8 K)) :=
  iSup₂_le fun γ hγ => rootSubgroup_le_centralizer_leviTorus (hS γ hγ).1 (hS γ hγ).2

theorem rootSpan_amalgamRoots_le_centralizer_leviTorus (J : Finset (Fin (Tag.rank .E8))) :
    rootSpan .E8 K (amalgamRoots J) ≤ centralizer (leviTorus K J : Set (ModGL .E8 K)) :=
  rootSpan_le_centralizer_leviTorus fun _ hγ =>
    ⟨isRoot_of_mem_amalgamRoots hγ, fun _ hi => apply_eq_zero_of_mem_amalgamRoots hγ hi⟩

end Kill

end CFSG.SeitzReduction.E8Pilot
