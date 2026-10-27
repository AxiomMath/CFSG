module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAmalgamWeyl
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e7PilotAlignToriNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem symmetrizedCartan_E7 : Tag.symmetrizedCartan .E7 = Tag.cartan .E7 := by
  decide +kernel

theorem cartan_E7_transpose : (Tag.cartan .E7).transpose = Tag.cartan .E7 := by
  decide +kernel

theorem cartan_E7_symm (i j : Fin (Tag.rank .E7)) : Tag.cartan .E7 i j = Tag.cartan .E7 j i := by
  conv_lhs => rw [← cartan_E7_transpose]
  rfl

theorem iform_single_right_E7 (δ : Fin (Tag.rank .E7) → ℤ) (l : Fin (Tag.rank .E7)) :
    iform δ (Pi.single l 1) = ∑ j, δ j * Tag.cartan .E7 j l := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, symmetrizedCartan_E7]

theorem iform_single_single_E7 (i j : Fin (Tag.rank .E7)) :
    iform (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) = Tag.cartan .E7 i j := by
  rw [iform_single_right_E7, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, one_mul]

section Sum

theorem iform_sum_right_E7 {ι : Type*} (s : Finset ι) (γ : Fin (Tag.rank .E7) → ℤ)
    (f : ι → Fin (Tag.rank .E7) → ℤ) : iform γ (∑ k ∈ s, f k) = ∑ k ∈ s, iform γ (f k) :=
  map_sum (AddMonoidHom.mk' (iform γ) (iform_add_right γ)) f s

theorem iform_reflect_single_E7 (i j : Fin (Tag.rank .E7)) (δ : Fin (Tag.rank .E7) → ℤ) :
    iform (reflect .E7 i δ) (Pi.single j 1) =
      iform δ (Pi.single j 1) - iform δ (Pi.single i 1) * Tag.cartan .E7 i j := by
  have hc : ∑ k, Tag.cartan .E7 i k * δ k = iform δ (Pi.single i 1) := by
    rw [iform_single_right_E7]
    exact Finset.sum_congr rfl fun k _ => by rw [cartan_E7_symm, mul_comm]
  rw [reflect, sub_eq_add_neg, ← neg_smul, iform_add_left, iform_smul_left,
    iform_single_single_E7, hc]
  ring

theorem abs_iform_le_two {δ γ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hγ : IsRoot .E7 γ) :
    |iform δ γ| ≤ 2 := by
  have h1 := EPilot.iform_self_nonneg (δ + γ)
  have h2 := EPilot.iform_self_nonneg (δ - γ)
  have hδδ := EPilot.iform_self_eq_two (Or.inr (Or.inl rfl)) hδ
  have hγγ := EPilot.iform_self_eq_two (Or.inr (Or.inl rfl)) hγ
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm γ δ] at h1
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm γ δ] at h2
  rw [abs_le]
  constructor <;> linarith

end Sum

@[expose] def invCartan2 : Matrix (Fin (Tag.rank .E7)) (Fin (Tag.rank .E7)) ℤ :=
  !![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3]

theorem cartan_mul_invCartan2_transpose :
    Tag.cartan .E7 * invCartan2.transpose = (2 : ℤ) • 1 := by
  decide +kernel

theorem invCartan2_mul_cartan : invCartan2 * Tag.cartan .E7 = (2 : ℤ) • 1 := by
  decide +kernel

@[expose] def fundWeight2 (i : Fin (Tag.rank .E7)) : Fin (Tag.rank .E7) → ℤ :=
  fun l => invCartan2 i l

theorem iform_fundWeight2 (v : Fin (Tag.rank .E7) → ℤ) (i : Fin (Tag.rank .E7)) :
    iform v (fundWeight2 i) = 2 * v i := by
  have hA : ∀ k, ∑ j, Tag.cartan .E7 k j * invCartan2 i j = if k = i then 2 else 0 := by
    intro k
    have h := congrFun (congrFun cartan_mul_invCartan2_transpose k) i
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    exact h
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_single_right_E7, fundWeight2, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ k, ∑ j, invCartan2 i j * (v k * Tag.cartan .E7 k j) =
      ∑ k, v k * ∑ j, Tag.cartan .E7 k j * invCartan2 i j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 2 * v i := by
        simp only [hA, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring

theorem dvd_two_mul_apply_of_forall_dvd_iform_single {m : ℤ} {v : Fin (Tag.rank .E7) → ℤ}
    (h : ∀ l, m ∣ iform v (Pi.single l 1)) (i : Fin (Tag.rank .E7)) : m ∣ 2 * v i := by
  rw [← iform_fundWeight2 v i, F4Pilot.iform_eq_sum_mul_iform_single]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l) _

section Adjoint

theorem rootDiagUnit_mem_torusGroup_E7_of_sq (s : Fin (Tag.rank .E7) → Kˣ) :
    rootDiagUnit .E7 (fun l => s l ^ 2) ∈ torusGroup .E7 K := by
  set t : Fin (Tag.rank .E7) → Kˣ := fun j => ∏ l, s l ^ invCartan2 l j with ht
  have hchar : cartanChar t = fun l => s l ^ 2 := by
    funext l'
    have hB : ∀ l, ∑ j, invCartan2 l j * Tag.cartan .E7 j l' = if l = l' then 2 else 0 := by
      intro l
      have h := congrFun (congrFun invCartan2_mul_cartan l) l'
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at h
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero] at h
      exact h
    simp only [cartanChar, ht, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow_eq_zpow_sum, hB]
    rw [Finset.prod_eq_single l' (fun x _ hx => by rw [ite_eq_right hx, zpow_zero])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left (rfl : l' = l')]
    exact zpow_natCast (s l') 2
  rw [← hchar, ← list_prod_torusElt_eq_rootDiagUnit]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨(j, t j), rfl⟩

theorem rootDiagUnit_mem_torusGroup_of_isSquare {b : Fin (Tag.rank .E7) → Kˣ}
    (hb : ∀ l, IsSquare (b l)) : rootDiagUnit .E7 b ∈ torusGroup .E7 K := by
  choose s hs using hb
  have hbs : b = fun l => s l ^ 2 := funext fun l => by rw [hs l, sq]
  rw [hbs]
  exact rootDiagUnit_mem_torusGroup_E7_of_sq s

theorem torusGroup_le_adjointGroup_E7 : torusGroup .E7 K ≤ adjointGroup .E7 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨q, rfl⟩
  exact torusElt_mem_adjointGroup q.1 q.2

theorem rootDiagUnit_mem_adjointGroup_of_isSquare {b : Fin (Tag.rank .E7) → Kˣ}
    (hb : ∀ l, IsSquare (b l)) : rootDiagUnit .E7 b ∈ adjointGroup .E7 K :=
  torusGroup_le_adjointGroup_E7 (rootDiagUnit_mem_torusGroup_of_isSquare hb)

end Adjoint

omit [Field K] in
theorem isSquare_units_of_ringChar_eq_two {F : Type} [Field F] [Finite F] (hF : ringChar F = 2)
    (x : Fˣ) : IsSquare x := by
  have := Fintype.ofFinite F
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hF (x : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact x.ne_zero hr
  exact ⟨Units.mk0 r hr0, Units.ext (by rw [Units.val_mul, Units.val_mk0]; exact hr)⟩

section Adjoint

theorem rootDiagUnit_mem_torusGroup_of_ringChar_eq_two [Finite K] (hK : ringChar K = 2)
    (b : Fin (Tag.rank .E7) → Kˣ) : rootDiagUnit .E7 b ∈ torusGroup .E7 K :=
  rootDiagUnit_mem_torusGroup_of_isSquare fun l => isSquare_units_of_ringChar_eq_two hK (b l)

theorem rootDiagUnit_mem_adjointGroup_of_ringChar_eq_two [Finite K] (hK : ringChar K = 2)
    (b : Fin (Tag.rank .E7) → Kˣ) : rootDiagUnit .E7 b ∈ adjointGroup .E7 K :=
  torusGroup_le_adjointGroup_E7 (rootDiagUnit_mem_torusGroup_of_ringChar_eq_two hK b)

end Adjoint

variable (K) in
@[expose] noncomputable def leviTorus (J : Finset (Fin (Tag.rank .E7))) :
    Subgroup (ModGL .E7 K) :=
  (Subgroup.pi (J : Set (Fin (Tag.rank .E7))) fun _ => (⊥ : Subgroup Kˣ)).map
    (rootDiagUnitHom .E7 K)

theorem mem_leviTorus {J : Finset (Fin (Tag.rank .E7))} {g : ModGL .E7 K} :
    g ∈ leviTorus K J ↔ ∃ b : Fin (Tag.rank .E7) → Kˣ, (∀ j ∈ J, b j = 1) ∧
      rootDiagUnit .E7 b = g := by
  simp only [leviTorus, mem_map, mem_pi, Finset.mem_coe, mem_bot]
  rfl

theorem rootDiagUnit_mem_leviTorus {J : Finset (Fin (Tag.rank .E7))}
    {b : Fin (Tag.rank .E7) → Kˣ} (hb : ∀ j ∈ J, b j = 1) : rootDiagUnit .E7 b ∈ leviTorus K J :=
  mem_leviTorus.2 ⟨b, hb, rfl⟩

section Adjoint

theorem leviTorus_le_torusGroup_of_isSquare (hK : ∀ x : Kˣ, IsSquare x)
    (J : Finset (Fin (Tag.rank .E7))) : leviTorus K J ≤ torusGroup .E7 K := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hg
  exact rootDiagUnit_mem_torusGroup_of_isSquare fun l => hK (b l)

theorem leviTorus_le_adjointGroup_of_isSquare (hK : ∀ x : Kˣ, IsSquare x)
    (J : Finset (Fin (Tag.rank .E7))) : leviTorus K J ≤ adjointGroup .E7 K :=
  (leviTorus_le_torusGroup_of_isSquare hK J).trans torusGroup_le_adjointGroup_E7

theorem leviTorus_le_torusGroup_of_ringChar_eq_two [Finite K] (hK : ringChar K = 2)
    (J : Finset (Fin (Tag.rank .E7))) : leviTorus K J ≤ torusGroup .E7 K :=
  leviTorus_le_torusGroup_of_isSquare (isSquare_units_of_ringChar_eq_two hK) J

theorem leviTorus_le_adjointGroup_of_ringChar_eq_two [Finite K] (hK : ringChar K = 2)
    (J : Finset (Fin (Tag.rank .E7))) : leviTorus K J ≤ adjointGroup .E7 K :=
  leviTorus_le_adjointGroup_of_isSquare (isSquare_units_of_ringChar_eq_two hK) J

end Adjoint

@[expose] def corootTuple (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) : Fin (Tag.rank .E7) → Kˣ :=
  fun i => c ^ iform δ (Pi.single i 1)

theorem rootChar_corootTuple (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) (v : Fin (Tag.rank .E7) → ℤ) :
    rootChar (corootTuple δ c) v = c ^ iform δ v := by
  rw [rootChar, F4Pilot.iform_eq_sum_mul_iform_single δ v, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [corootTuple, ← zpow_mul, mul_comm]

theorem corootTuple_one (δ : Fin (Tag.rank .E7) → ℤ) : corootTuple δ (1 : Kˣ) = 1 := by
  funext i
  simp [corootTuple]

theorem corootTuple_mul (δ : Fin (Tag.rank .E7) → ℤ) (c d : Kˣ) :
    corootTuple δ (c * d) = corootTuple δ c * corootTuple δ d := by
  funext i
  simp only [corootTuple, Pi.mul_apply, mul_zpow]

theorem rootDiagUnit_corootTuple_mem_leviTorus {J : Finset (Fin (Tag.rank .E7))}
    {δ : Fin (Tag.rank .E7) → ℤ} (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) (c : Kˣ) :
    rootDiagUnit .E7 (corootTuple δ c) ∈ leviTorus K J :=
  rootDiagUnit_mem_leviTorus fun j hj => by rw [corootTuple, h j hj, zpow_zero]

section Adjoint

theorem rootDiagUnit_corootTuple_eq_prod (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) :
    rootDiagUnit .E7 (corootTuple δ c) =
      ((List.finRange (Tag.rank .E7)).map fun j => torusElt .E7 K j (c ^ δ j)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, EPilot.cartanChar_zpow]
  congr 1
  funext l
  rw [corootTuple, iform_single_right_E7]

theorem rootDiagUnit_corootTuple_mem_adjointGroup (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) :
    rootDiagUnit .E7 (corootTuple δ c) ∈ adjointGroup .E7 K := by
  rw [rootDiagUnit_corootTuple_eq_prod]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_adjointGroup j _

end Adjoint

theorem corootTuple_highRoot (c : Kˣ) : corootTuple (highRoot .E7) c = EPilot.highDiag .E7 c := by
  funext i
  rw [corootTuple, EPilot.iform_highRoot_single (Or.inr (Or.inl rfl)), EPilot.highDiag_apply]

variable (K) in
@[expose] def corootTupleHom (δ : Fin (Tag.rank .E7) → ℤ) : Kˣ →* (Fin (Tag.rank .E7) → Kˣ) where
  toFun := corootTuple δ
  map_one' := corootTuple_one δ
  map_mul' := corootTuple_mul δ

variable (K) in
@[expose] noncomputable def corootLine (δ : Fin (Tag.rank .E7) → ℤ) : Subgroup (ModGL .E7 K) :=
  ((rootDiagUnitHom .E7 K).comp (corootTupleHom K δ)).range

theorem mem_corootLine {δ : Fin (Tag.rank .E7) → ℤ} {g : ModGL .E7 K} :
    g ∈ corootLine K δ ↔ ∃ c : Kˣ, rootDiagUnit .E7 (corootTuple δ c) = g :=
  MonoidHom.mem_range

theorem rootDiagUnit_corootTuple_mem_corootLine (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) :
    rootDiagUnit .E7 (corootTuple δ c) ∈ corootLine K δ :=
  mem_corootLine.2 ⟨c, rfl⟩

theorem corootLine_le_leviTorus {J : Finset (Fin (Tag.rank .E7))} {δ : Fin (Tag.rank .E7) → ℤ}
    (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) : corootLine K δ ≤ leviTorus K J := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_leviTorus h c

theorem corootLine_le_adjointGroup
    (δ : Fin (Tag.rank .E7) → ℤ) : corootLine K δ ≤ adjointGroup .E7 K := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_adjointGroup δ c

theorem corootLine_highRoot : corootLine K (highRoot .E7) = EPilot.highTorusLine .E7 K := by
  ext g
  rw [mem_corootLine, EPilot.mem_highTorusLine]
  simp only [corootTuple_highRoot]

section Weyl

theorem weylElt_one_conj_corootTuple (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ)
    (i : Fin (Tag.rank .E7)) :
    weylElt .E7 K i 1 * rootDiagUnit .E7 (corootTuple δ c) * (weylElt .E7 K i 1)⁻¹ =
      rootDiagUnit .E7 (corootTuple (reflect .E7 i δ) c) := by
  rw [E6Pilot.weylElt_one_conj_rootDiagUnit_eq]
  congr 1
  funext j
  rw [corootTuple, corootTuple, corootTuple, iform_reflect_single_E7, ← zpow_mul, ← zpow_add]
  congr 1
  ring

theorem list_prod_weylElt_conj_corootTuple (ω : List (Fin (Tag.rank .E7)))
    (δ : Fin (Tag.rank .E7) → ℤ) (c : Kˣ) :
    (ω.map fun i => weylElt .E7 K i 1).prod * rootDiagUnit .E7 (corootTuple δ c) *
        ((ω.map fun i => weylElt .E7 K i 1).prod)⁻¹ =
      rootDiagUnit .E7 (corootTuple ((coxeterSystem .E7).wordProd ω • δ) c) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, (coxeterSystem .E7).wordProd_cons, mul_smul,
      simple_smul]
    calc weylElt .E7 K i 1 * (ω.map fun i => weylElt .E7 K i 1).prod *
          rootDiagUnit .E7 (corootTuple δ c) *
          (weylElt .E7 K i 1 * (ω.map fun i => weylElt .E7 K i 1).prod)⁻¹ =
        weylElt .E7 K i 1 * ((ω.map fun i => weylElt .E7 K i 1).prod *
          rootDiagUnit .E7 (corootTuple δ c) * ((ω.map fun i => weylElt .E7 K i 1).prod)⁻¹) *
          (weylElt .E7 K i 1)⁻¹ := by group
      _ = _ := by rw [ih, weylElt_one_conj_corootTuple]

theorem map_conj_rep_corootLine (N : E7Neighbour) (δ : Fin (Tag.rank .E7) → ℤ) :
    (corootLine K δ).map (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom =
      corootLine K (N.weyl • δ) := by
  ext g
  simp only [mem_map, mem_corootLine, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    E7Neighbour.coe_rep]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (list_prod_weylElt_conj_corootTuple N.word δ c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, list_prod_weylElt_conj_corootTuple N.word δ c⟩

end Weyl

namespace E7Neighbour

variable (K) in
@[expose] noncomputable def torus (N : E7Neighbour) : Subgroup (ModGL .E7 K) :=
  corootLine K N.root

theorem torus_high : high.torus K = EPilot.highTorusLine .E7 K :=
  corootLine_highRoot

theorem torus_le_leviTorus (N : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J ⊆ N.nodes) : N.torus K ≤ leviTorus K J :=
  corootLine_le_leviTorus fun j hj => (N.iform_root_single_eq_zero_iff j).2 (hJ hj)

theorem torus_le_adjointGroup
    (N : E7Neighbour) : N.torus K ≤ adjointGroup .E7 K :=
  corootLine_le_adjointGroup _

theorem map_conj_rep_torus_high
    (N : E7Neighbour) :
    (high.torus K).map (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom = N.torus K := by
  rw [torus, map_conj_rep_corootLine]
  exact congrArg (corootLine K) (weyl_smul_highRoot N)

end E7Neighbour

@[expose] def perpPositions (J : Finset (Fin (Tag.rank .E7))) : Finset ℕ :=
  (Finset.range Tag.E7.rootCertificate.roots.length).filter fun k =>
    0 < height (Tag.E7.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E7.rootCertificate.root k) (Pi.single j 1) = 0

@[expose] def isolatedPositions (J : Finset (Fin (Tag.rank .E7))) : Finset ℕ :=
  if J.card = 2 then
    (perpPositions J).filter fun k => ∀ k' ∈ perpPositions J,
      k' = k ∨ iform (Tag.E7.rootCertificate.root k) (Tag.E7.rootCertificate.root k') = 0
  else ∅

@[expose] def casimirVec (J : Finset (Fin (Tag.rank .E7))) (i : Fin (Tag.rank .E7)) :
    Fin (Tag.rank .E7) → ℤ :=
  ∑ k ∈ perpPositions J, Tag.E7.rootCertificate.root k i • Tag.E7.rootCertificate.root k +
    ∑ k ∈ isolatedPositions J, (2 * Tag.E7.rootCertificate.root k i) • Tag.E7.rootCertificate.root k

@[expose] def perpCasimir (J : Finset (Fin (Tag.rank .E7))) : ℤ :=
  if J.card = 0 then 9 else if J.card = 1 then 5 else 3

theorem perpCasimir_ne_zero (J : Finset (Fin (Tag.rank .E7))) : perpCasimir J ≠ 0 := by
  unfold perpCasimir
  split_ifs <;> decide

set_option maxRecDepth 100000 in
theorem casimir_check : ∀ J : Finset (Fin (Tag.rank .E7)), J.card ≤ 2 →
    ∀ i ∉ J, casimirVec J i = perpCasimir J • fundWeight2 i := by
  decide +kernel

section Roots

theorem isRoot_of_mem_perpPositions {J : Finset (Fin (Tag.rank .E7))} {k : ℕ}
    (hk : k ∈ perpPositions J) :
    IsRoot .E7 (Tag.E7.rootCertificate.root k) ∧
      ∀ j ∈ J, iform (Tag.E7.rootCertificate.root k) (Pi.single j 1) = 0 := by
  rw [perpPositions, Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨RootCertificate.isRoot_root Tag.E7.rootCertificate_check k hk.1, hk.2.2⟩

theorem mem_perpPositions_of_mem_isolatedPositions {J : Finset (Fin (Tag.rank .E7))} {k : ℕ}
    (hk : k ∈ isolatedPositions J) : k ∈ perpPositions J := by
  unfold isolatedPositions at hk
  split_ifs at hk
  · exact (Finset.mem_filter.1 hk).1
  · exact absurd hk (Finset.notMem_empty k)

theorem iform_casimirVec (v : Fin (Tag.rank .E7) → ℤ) (J : Finset (Fin (Tag.rank .E7)))
    (i : Fin (Tag.rank .E7)) :
    iform v (casimirVec J i) = ∑ k ∈ perpPositions J,
        Tag.E7.rootCertificate.root k i * iform v (Tag.E7.rootCertificate.root k) +
      ∑ k ∈ isolatedPositions J,
        2 * Tag.E7.rootCertificate.root k i * iform v (Tag.E7.rootCertificate.root k) := by
  rw [casimirVec, iform_add_right, iform_sum_right_E7, iform_sum_right_E7]
  simp only [iform_smul_right]

theorem coeff_eq_zero_of_forall_iform_eq_zero {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J.card ≤ 2) {v : Fin (Tag.rank .E7) → ℤ}
    (h : ∀ δ, IsRoot .E7 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → iform v δ = 0) :
    ∀ i ∉ J, v i = 0 := by
  intro i hi
  have h0 : iform v (casimirVec J i) = 0 := by
    rw [iform_casimirVec]
    have h1 : ∀ k ∈ perpPositions J, iform v (Tag.E7.rootCertificate.root k) = 0 := fun k hk =>
      h _ (isRoot_of_mem_perpPositions hk).1 (isRoot_of_mem_perpPositions hk).2
    rw [Finset.sum_eq_zero fun k hk => by rw [h1 k hk, mul_zero],
      Finset.sum_eq_zero fun k hk => by
        rw [h1 k (mem_perpPositions_of_mem_isolatedPositions hk), mul_zero], add_zero]
  rw [casimir_check J hJ i hi, iform_smul_right, iform_fundWeight2] at h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (perpCasimir_ne_zero J)
  · omega

end Roots

section Kill

theorem rootSubgroup_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E7))}
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h : ∀ i ∉ J, γ i = 0) :
    rootSubgroup .E7 K γ ≤ centralizer (leviTorus K J : Set (ModGL .E7 K)) := by
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

theorem rootSpan_le_centralizer_leviTorus {J : Finset (Fin (Tag.rank .E7))}
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E7 γ ∧ ∀ i ∉ J, γ i = 0) :
    rootSpan .E7 K S ≤ centralizer (leviTorus K J : Set (ModGL .E7 K)) :=
  iSup₂_le fun γ hγ => rootSubgroup_le_centralizer_leviTorus (hS γ hγ).1 (hS γ hγ).2

theorem rootSpan_amalgamRoots_le_centralizer_leviTorus (J : Finset (Fin (Tag.rank .E7))) :
    rootSpan .E7 K (amalgamRoots J) ≤ centralizer (leviTorus K J : Set (ModGL .E7 K)) :=
  rootSpan_le_centralizer_leviTorus fun _ hγ =>
    ⟨isRoot_of_mem_amalgamRoots hγ, fun _ hi => apply_eq_zero_of_mem_amalgamRoots hγ hi⟩

end Kill

end CFSG.SeitzReduction.E7Pilot
