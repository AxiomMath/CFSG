module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAmalgamWeyl
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e6PilotAlignToriNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem symmetrizedCartan_E6 : Tag.symmetrizedCartan .E6 = Tag.cartan .E6 := by
  decide +kernel

theorem cartan_E6_transpose : (Tag.cartan .E6).transpose = Tag.cartan .E6 := by
  decide +kernel

theorem cartan_E6_symm (i j : Fin (Tag.rank .E6)) : Tag.cartan .E6 i j = Tag.cartan .E6 j i := by
  conv_lhs => rw [← cartan_E6_transpose]
  rfl

theorem iform_single_right_E6 (δ : Fin (Tag.rank .E6) → ℤ) (l : Fin (Tag.rank .E6)) :
    iform δ (Pi.single l 1) = ∑ j, δ j * Tag.cartan .E6 j l := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, symmetrizedCartan_E6]

theorem iform_single_single_E6 (i j : Fin (Tag.rank .E6)) :
    iform (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) (Pi.single j 1) = Tag.cartan .E6 i j := by
  rw [iform_single_right_E6, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, one_mul]

section Sum


theorem iform_reflect_single_E6 (i j : Fin (Tag.rank .E6)) (δ : Fin (Tag.rank .E6) → ℤ) :
    iform (reflect .E6 i δ) (Pi.single j 1) =
      iform δ (Pi.single j 1) - iform δ (Pi.single i 1) * Tag.cartan .E6 i j := by
  have hc : ∑ k, Tag.cartan .E6 i k * δ k = iform δ (Pi.single i 1) := by
    rw [iform_single_right_E6]
    exact Finset.sum_congr rfl fun k _ => by rw [cartan_E6_symm, mul_comm]
  rw [reflect, sub_eq_add_neg, ← neg_smul, iform_add_left, iform_smul_left,
    iform_single_single_E6, hc]
  ring


theorem iform_sum_right_E6 {ι : Type*} (s : Finset ι) (γ : Fin (Tag.rank .E6) → ℤ)
    (f : ι → Fin (Tag.rank .E6) → ℤ) : iform γ (∑ k ∈ s, f k) = ∑ k ∈ s, iform γ (f k) :=
  map_sum (AddMonoidHom.mk' (iform γ) (iform_add_right γ)) f s

end Sum

variable (K) in
@[expose] noncomputable def leviTorus (J : Finset (Fin (Tag.rank .E6))) :
    Subgroup (ModGL .E6 K) :=
  (Subgroup.pi (J : Set (Fin (Tag.rank .E6))) fun _ => (⊥ : Subgroup Kˣ)).map
    (rootDiagUnitHom .E6 K)

theorem mem_leviTorus {J : Finset (Fin (Tag.rank .E6))} {g : ModGL .E6 K} :
    g ∈ leviTorus K J ↔ ∃ b : Fin (Tag.rank .E6) → Kˣ, (∀ j ∈ J, b j = 1) ∧
      rootDiagUnit .E6 b = g := by
  simp only [leviTorus, mem_map, mem_pi, Finset.mem_coe, mem_bot]
  rfl

theorem rootDiagUnit_mem_leviTorus {J : Finset (Fin (Tag.rank .E6))}
    {b : Fin (Tag.rank .E6) → Kˣ} (hb : ∀ j ∈ J, b j = 1) : rootDiagUnit .E6 b ∈ leviTorus K J :=
  mem_leviTorus.2 ⟨b, hb, rfl⟩

theorem leviTorus_anti {J J' : Finset (Fin (Tag.rank .E6))} (h : J ⊆ J') :
    leviTorus K J' ≤ leviTorus K J := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hg
  exact rootDiagUnit_mem_leviTorus fun j hj => hb j (h hj)

variable (K) in
theorem antitone_leviTorus : Antitone (leviTorus K) := fun _ _ h => leviTorus_anti h

@[expose] def corootTuple (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) : Fin (Tag.rank .E6) → Kˣ :=
  fun i => c ^ iform δ (Pi.single i 1)

theorem rootChar_corootTuple (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    rootChar (corootTuple δ c) v = c ^ iform δ v := by
  rw [rootChar, F4Pilot.iform_eq_sum_mul_iform_single δ v, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [corootTuple, ← zpow_mul, mul_comm]

theorem corootTuple_one (δ : Fin (Tag.rank .E6) → ℤ) : corootTuple δ (1 : Kˣ) = 1 := by
  funext i
  simp [corootTuple]

theorem corootTuple_mul (δ : Fin (Tag.rank .E6) → ℤ) (c d : Kˣ) :
    corootTuple δ (c * d) = corootTuple δ c * corootTuple δ d := by
  funext i
  simp only [corootTuple, Pi.mul_apply, mul_zpow]

theorem rootDiagUnit_corootTuple_mem_leviTorus {J : Finset (Fin (Tag.rank .E6))}
    {δ : Fin (Tag.rank .E6) → ℤ} (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) (c : Kˣ) :
    rootDiagUnit .E6 (corootTuple δ c) ∈ leviTorus K J :=
  rootDiagUnit_mem_leviTorus fun j hj => by rw [corootTuple, h j hj, zpow_zero]

section Adjoint


theorem rootDiagUnit_corootTuple_eq_prod (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) :
    rootDiagUnit .E6 (corootTuple δ c) =
      ((List.finRange (Tag.rank .E6)).map fun j => torusElt .E6 K j (c ^ δ j)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, EPilot.cartanChar_zpow]
  congr 1
  funext l
  rw [corootTuple, iform_single_right_E6]

theorem rootDiagUnit_corootTuple_mem_adjointGroup (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) :
    rootDiagUnit .E6 (corootTuple δ c) ∈ adjointGroup .E6 K := by
  rw [rootDiagUnit_corootTuple_eq_prod]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_adjointGroup j _

end Adjoint

theorem corootTuple_highRoot (c : Kˣ) : corootTuple (highRoot .E6) c = EPilot.highDiag .E6 c := by
  funext i
  rw [corootTuple, EPilot.iform_highRoot_single (Or.inl rfl), EPilot.highDiag_apply]

variable (K) in
@[expose] def corootTupleHom (δ : Fin (Tag.rank .E6) → ℤ) : Kˣ →* (Fin (Tag.rank .E6) → Kˣ) where
  toFun := corootTuple δ
  map_one' := corootTuple_one δ
  map_mul' := corootTuple_mul δ

variable (K) in
@[expose] noncomputable def corootLine (δ : Fin (Tag.rank .E6) → ℤ) : Subgroup (ModGL .E6 K) :=
  ((rootDiagUnitHom .E6 K).comp (corootTupleHom K δ)).range

theorem mem_corootLine {δ : Fin (Tag.rank .E6) → ℤ} {g : ModGL .E6 K} :
    g ∈ corootLine K δ ↔ ∃ c : Kˣ, rootDiagUnit .E6 (corootTuple δ c) = g :=
  MonoidHom.mem_range

theorem rootDiagUnit_corootTuple_mem_corootLine (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) :
    rootDiagUnit .E6 (corootTuple δ c) ∈ corootLine K δ :=
  mem_corootLine.2 ⟨c, rfl⟩

theorem corootLine_le_leviTorus {J : Finset (Fin (Tag.rank .E6))} {δ : Fin (Tag.rank .E6) → ℤ}
    (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) : corootLine K δ ≤ leviTorus K J := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_leviTorus h c

theorem corootLine_le_adjointGroup
    (δ : Fin (Tag.rank .E6) → ℤ) : corootLine K δ ≤ adjointGroup .E6 K := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_adjointGroup δ c

theorem corootLine_highRoot : corootLine K (highRoot .E6) = EPilot.highTorusLine .E6 K := by
  ext g
  rw [mem_corootLine, EPilot.mem_highTorusLine]
  simp only [corootTuple_highRoot]

section Weyl


theorem weylElt_one_conj_rootDiagUnit_eq {τ : Tag} (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      rootDiagUnit τ (fun j => a j * a i ^ (-Tag.cartan τ i j)) := by
  have h := rootDiagUnit_conj_weylElt_one (K := K) a i
  have h2 : weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      (torusElt τ K i (a i))⁻¹ * rootDiagUnit τ a := by
    rw [eq_inv_mul_iff_mul_eq]
    calc torusElt τ K i (a i) * (weylElt τ K i 1 * rootDiagUnit τ a *
          (weylElt τ K i 1)⁻¹) =
        (rootDiagUnit τ a * weylElt τ K i 1 * (rootDiagUnit τ a)⁻¹) *
          rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ := by rw [h]; group
      _ = rootDiagUnit τ a := by group
  rw [h2, torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  rw [mul_comm]

theorem weylElt_one_conj_corootTuple (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ)
    (i : Fin (Tag.rank .E6)) :
    weylElt .E6 K i 1 * rootDiagUnit .E6 (corootTuple δ c) * (weylElt .E6 K i 1)⁻¹ =
      rootDiagUnit .E6 (corootTuple (reflect .E6 i δ) c) := by
  rw [weylElt_one_conj_rootDiagUnit_eq]
  congr 1
  funext j
  rw [corootTuple, corootTuple, corootTuple, iform_reflect_single_E6, ← zpow_mul, ← zpow_add]
  congr 1
  ring

theorem list_prod_weylElt_conj_corootTuple (ω : List (Fin (Tag.rank .E6)))
    (δ : Fin (Tag.rank .E6) → ℤ) (c : Kˣ) :
    (ω.map fun i => weylElt .E6 K i 1).prod * rootDiagUnit .E6 (corootTuple δ c) *
        ((ω.map fun i => weylElt .E6 K i 1).prod)⁻¹ =
      rootDiagUnit .E6 (corootTuple ((coxeterSystem .E6).wordProd ω • δ) c) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, (coxeterSystem .E6).wordProd_cons, mul_smul,
      simple_smul]
    calc weylElt .E6 K i 1 * (ω.map fun i => weylElt .E6 K i 1).prod *
          rootDiagUnit .E6 (corootTuple δ c) *
          (weylElt .E6 K i 1 * (ω.map fun i => weylElt .E6 K i 1).prod)⁻¹ =
        weylElt .E6 K i 1 * ((ω.map fun i => weylElt .E6 K i 1).prod *
          rootDiagUnit .E6 (corootTuple δ c) * ((ω.map fun i => weylElt .E6 K i 1).prod)⁻¹) *
          (weylElt .E6 K i 1)⁻¹ := by group
      _ = _ := by rw [ih, weylElt_one_conj_corootTuple]

theorem map_conj_rep_corootLine (N : E6Neighbour) (δ : Fin (Tag.rank .E6) → ℤ) :
    (corootLine K δ).map (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom =
      corootLine K (N.weyl • δ) := by
  ext g
  simp only [mem_map, mem_corootLine, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    E6Neighbour.coe_rep]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (list_prod_weylElt_conj_corootTuple N.word δ c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, list_prod_weylElt_conj_corootTuple N.word δ c⟩

end Weyl

namespace E6Neighbour

variable (K) in
@[expose] noncomputable def torus (N : E6Neighbour) : Subgroup (ModGL .E6 K) :=
  corootLine K N.root

theorem torus_high : high.torus K = EPilot.highTorusLine .E6 K :=
  corootLine_highRoot

theorem torus_le_leviTorus (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) : N.torus K ≤ leviTorus K J :=
  corootLine_le_leviTorus fun j hj => (N.iform_root_single_eq_zero_iff j).2 (hJ hj)

theorem torus_le_adjointGroup
    (N : E6Neighbour) : N.torus K ≤ adjointGroup .E6 K :=
  corootLine_le_adjointGroup _

theorem torus_le_leviTorus_inf
    (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    N.torus K ≤ leviTorus K J ⊓ adjointGroup .E6 K :=
  le_inf (N.torus_le_leviTorus hJ) N.torus_le_adjointGroup

theorem map_conj_rep_torus_high
    (N : E6Neighbour) :
    (high.torus K).map (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom = N.torus K := by
  rw [torus, map_conj_rep_corootLine]
  exact congrArg (corootLine K) (weyl_smul_highRoot N)

end E6Neighbour

theorem iform_root_check : ∀ δ ∈ rootFinset .E6, ∀ γ ∈ rootFinset .E6, |iform δ γ| ≤ 2 := by
  decide +kernel

@[expose] def perpPositions (J : Finset (Fin (Tag.rank .E6))) : Finset ℕ :=
  (Finset.range Tag.E6.rootCertificate.roots.length).filter fun k =>
    0 < height (Tag.E6.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E6.rootCertificate.root k) (Pi.single j 1) = 0

@[expose] def perpVec (J : Finset (Fin (Tag.rank .E6))) : Fin (Tag.rank .E6) → ℤ :=
  ∑ k ∈ perpPositions J, (5 : ℤ) ^ k • Tag.E6.rootCertificate.root k

set_option maxRecDepth 100000 in
theorem perpVec_check : ∀ J : Finset (Fin (Tag.rank .E6)), J.card ≤ 2 →
    ∀ α ∈ rootFinset .E6, iform α (perpVec J) = 0 → ∀ i ∉ J, α i = 0 := by
  decide +kernel

section Roots


theorem abs_iform_le_two {δ γ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ) (hγ : IsRoot .E6 γ) :
    |iform δ γ| ≤ 2 :=
  iform_root_check δ (mem_rootFinset.2 hδ) γ (mem_rootFinset.2 hγ)

theorem isRoot_of_mem_perpPositions {J : Finset (Fin (Tag.rank .E6))} {k : ℕ}
    (hk : k ∈ perpPositions J) :
    IsRoot .E6 (Tag.E6.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E6.rootCertificate.root k) (Pi.single j 1) = 0 := by
  rw [perpPositions, Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨RootCertificate.isRoot_root Tag.E6.rootCertificate_check k hk.1, hk.2.2⟩


theorem iform_perpVec_eq_zero {J : Finset (Fin (Tag.rank .E6))} {γ : Fin (Tag.rank .E6) → ℤ}
    (h : ∀ δ, IsRoot .E6 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → iform γ δ = 0) :
    iform γ (perpVec J) = 0 := by
  rw [perpVec, iform_sum_right_E6]
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hδ, hδJ⟩ := isRoot_of_mem_perpPositions hk
  rw [iform_smul_right, h _ hδ hδJ, mul_zero]

theorem coeff_eq_zero_of_forall_iform_eq_zero {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J.card ≤ 2) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (h : ∀ δ, IsRoot .E6 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → iform γ δ = 0) :
    ∀ i ∉ J, γ i = 0 :=
  perpVec_check J hJ γ (mem_rootFinset.2 hγ) (iform_perpVec_eq_zero h)

end Roots

section Kill


theorem rootSubgroup_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E6))}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (h : ∀ i ∉ J, γ i = 0) :
    rootSubgroup .E6 K γ ≤ centralizer (leviTorus K J : Set (ModGL .E6 K)) := by
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

theorem rootSpan_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E6))}
    {S : Set (Fin (Tag.rank .E6) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E6 γ ∧ ∀ i ∉ J, γ i = 0) :
    rootSpan .E6 K S ≤ centralizer (leviTorus K J : Set (ModGL .E6 K)) :=
  iSup₂_le fun γ hγ => rootSubgroup_le_centralizer_leviTorus (hS γ hγ).1 (hS γ hγ).2

theorem rootSpan_amalgamRoots_le_centralizer_leviTorus (J : Finset (Fin (Tag.rank .E6))) :
    rootSpan .E6 K (amalgamRoots J) ≤ centralizer (leviTorus K J : Set (ModGL .E6 K)) :=
  rootSpan_le_centralizer_leviTorus fun _ hγ =>
    ⟨isRoot_of_mem_amalgamRoots hγ, fun _ hi => apply_eq_zero_of_mem_amalgamRoots hγ hi⟩

theorem iform_eq_zero_of_commute_corootTuple {δ γ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ)
    (hγ : IsRoot .E6 γ) {c : Kˣ} (hc : 3 ≤ orderOf c)
    (h : rootDiagUnit .E6 (corootTuple δ c) * pinnedX .E6 K γ 1 *
      (rootDiagUnit .E6 (corootTuple δ c))⁻¹ = pinnedX .E6 K γ 1) :
    iform δ γ = 0 := by
  rw [rootDiagUnit_conj_pinnedX _ hγ, mul_one] at h
  have h1 : ((rootChar (corootTuple δ c) γ : Kˣ) : K) = 1 := pinnedX_injective .E6 K γ h
  rw [rootChar_corootTuple] at h1
  have h2 : c ^ iform δ γ = 1 := Units.ext h1
  rw [← orderOf_dvd_iff_zpow_eq_one] at h2
  refine Int.eq_zero_of_abs_lt_dvd h2 ?_
  have := abs_iform_le_two hδ hγ
  omega

theorem iform_eq_zero_of_rootSubgroup_le_centralizer_leviTorus_inf [Finite K]
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E6))} {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ)
    (h : rootSubgroup .E6 K γ ≤
      centralizer ((leviTorus K J ⊓ adjointGroup .E6 K : Subgroup (ModGL .E6 K)) :
        Set (ModGL .E6 K)))
    {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ)
    (hδJ : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) : iform δ γ = 0 := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  have hT : rootDiagUnit .E6 (corootTuple δ c) ∈ leviTorus K J ⊓ adjointGroup .E6 K :=
    ⟨rootDiagUnit_corootTuple_mem_leviTorus hδJ c, rootDiagUnit_corootTuple_mem_adjointGroup δ c⟩
  have hcomm := mem_centralizer_iff.1 (h (mem_rootSubgroup.2 ⟨1, rfl⟩)) _ hT
  refine iform_eq_zero_of_commute_corootTuple hδ hγ hc ?_
  rw [hcomm, mul_inv_cancel_right]

theorem rootSubgroup_le_centralizer_leviTorus_inf_iff [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) :
    rootSubgroup .E6 K γ ≤
        centralizer ((leviTorus K J ⊓ adjointGroup .E6 K : Subgroup (ModGL .E6 K)) :
          Set (ModGL .E6 K)) ↔
      ∀ i ∉ J, γ i = 0 := by
  refine ⟨fun h => coeff_eq_zero_of_forall_iform_eq_zero hJ hγ fun δ hδ hδJ => ?_,
    fun h => (rootSubgroup_le_centralizer_leviTorus hγ h).trans
      (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))⟩
  rw [iform_comm]
  exact iform_eq_zero_of_rootSubgroup_le_centralizer_leviTorus_inf hq hγ h hδ hδJ

theorem rootSubgroup_le_centralizer_leviTorus_iff [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) :
    rootSubgroup .E6 K γ ≤ centralizer (leviTorus K J : Set (ModGL .E6 K)) ↔
      ∀ i ∉ J, γ i = 0 :=
  ⟨fun h => (rootSubgroup_le_centralizer_leviTorus_inf_iff hq hJ hγ).1
      (h.trans (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))),
    rootSubgroup_le_centralizer_leviTorus hγ⟩

end Kill

end CFSG.SeitzReduction.E6Pilot
