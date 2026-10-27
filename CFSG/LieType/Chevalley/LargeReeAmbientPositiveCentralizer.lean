module

public import CFSG.LieType.Chevalley.EvenRootCommutatorF4

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

section Coordinate

variable {τ : Tag}

@[expose] def coordKerRoots (α : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {β | IsRoot τ β ∧ 0 < height β ∧ height α ≤ height β ∧ β ≠ α}

theorem heightSeriesSet_closed {h : ℤ} :
    ∀ α ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ},
      ∀ β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ},
        ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ} := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.2.1, hα.2.2, hβ.2.1]

theorem coordKerRoots_closed (α : Fin τ.rank → ℤ) :
    ∀ β ∈ coordKerRoots α, ∀ γ ∈ coordKerRoots α, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • β + b • γ) → a • β + b • γ ∈ coordKerRoots α := by
  intro β hβ γ hγ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hht : height α < height (a • β + b • γ) := by
    rw [height_nsmul_add_nsmul]
    nlinarith [hβ.2.1, hβ.2.2.1, hγ.2.1]
  have hpos : 0 < height (a • β + b • γ) := by
    rw [height_nsmul_add_nsmul]
    nlinarith [hβ.2.1, hγ.2.1]
  exact ⟨hr, hpos, hht.le, fun h => by rw [h] at hht; exact lt_irrefl _ hht⟩

theorem coordKerRoots_ideal (α : Fin τ.rank → ℤ) :
    ∀ β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ}, ∀ γ ∈ coordKerRoots α,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) → a • β + b • γ ∈ coordKerRoots α := by
  intro β hβ γ hγ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hht : height α < height (a • β + b • γ) := by
    rw [height_nsmul_add_nsmul]
    nlinarith [hβ.2, hγ.2.2.1, hγ.2.1]
  have hpos : 0 < height (a • β + b • γ) := by
    rw [height_nsmul_add_nsmul]
    nlinarith [hβ.2, hγ.2.1]
  exact ⟨hr, hpos, hht.le, fun h => by rw [h] at hht; exact lt_irrefl _ hht⟩

variable {K : Type} [Field K]

theorem coordKer_le_heightSeries
    (α : Fin τ.rank → ℤ) :
    rootSpan τ K (coordKerRoots α) ≤ heightSeries τ K (height α) :=
  rootSpan_mono fun _ hβ => ⟨hβ.1, hβ.2.1, hβ.2.2.1⟩

theorem heightSeries_succ_le_coordKer
    (α : Fin τ.rank → ℤ) :
    heightSeries τ K (height α + 1) ≤ rootSpan τ K (coordKerRoots α) :=
  rootSpan_mono fun β hβ => ⟨hβ.1, hβ.2.1, by linarith [hβ.2.2], by
    rintro rfl
    linarith [hβ.2.2]⟩

theorem posUnipotent_le_normalizer_coordKer
    (α : Fin τ.rank → ℤ) :
    posUnipotent τ K ≤
      Subgroup.normalizer (rootSpan τ K (coordKerRoots α) : Set (ModGL τ K)) := by
  obtain ⟨hle, hn⟩ := positive_root_ideal_normality τ K (J := coordKerRoots α)
    (S := {γ | IsRoot τ γ ∧ 0 < height γ}) (fun β hβ => ⟨hβ.1, hβ.2.1⟩) (fun _ h => h)
    (coordKerRoots_ideal α)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hn

instance coordKer_normal
    (α : Fin τ.rank → ℤ) :
    ((rootSpan τ K (coordKerRoots α)).subgroupOf (heightSeries τ K (height α))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((heightSeries_le_posUnipotent _).trans (posUnipotent_le_normalizer_coordKer α))

theorem commutator_posUnipotent_heightSeries_le
    (h : ℤ) :
    ⁅posUnipotent τ K, heightSeries τ K h⁆ ≤ heightSeries τ K (h + 1) := by
  have e := commutator_heightSeries_le (τ := τ) K 1 h
  rw [heightSeries_one, add_comm] at e
  exact e

theorem pinnedX_mem_heightSeries_height
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (c : K) :
    pinnedX τ K α c ∈ heightSeries τ K (height α) :=
  pinnedX_mem_rootSpan (S := {γ | IsRoot τ γ ∧ 0 < height γ ∧ height α ≤ height γ})
    ⟨hα.1, hα.2, le_rfl⟩ c

@[expose] def rootCoordHom
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    Multiplicative K →* heightSeries τ K (height α) ⧸
      (rootSpan τ K (coordKerRoots α)).subgroupOf (heightSeries τ K (height α)) where
  toFun c := QuotientGroup.mk ⟨pinnedX τ K α c.toAdd, pinnedX_mem_heightSeries_height hα _⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    exact congrArg QuotientGroup.mk (Subtype.ext (pinnedX_zero τ K α))
  map_mul' c d := by
    rw [← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (pinnedX_add τ K α c.toAdd d.toAdd))

theorem rootCoordHom_apply
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) (c : K) :
    rootCoordHom hα (Multiplicative.ofAdd c) =
      QuotientGroup.mk ⟨pinnedX τ K α c, pinnedX_mem_heightSeries_height hα _⟩ :=
  rfl

theorem rootCoordHom_surjective
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    Function.Surjective (rootCoordHom (K := K) hα) := by
  set M := heightSeries τ K (height α)
  have hM : M = Subgroup.closure {g | ∃ β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧
      height α ≤ height γ}, ∃ c : K, pinnedX τ K β c = g} := rootSpan_eq_closure K _
  have key : ∀ g (hg : g ∈ Subgroup.closure {g | ∃ β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧
      0 < height γ ∧ height α ≤ height γ}, ∃ c : K, pinnedX τ K β c = g}),
      (QuotientGroup.mk (⟨g, hM ▸ hg⟩ : M) : M ⧸
        (rootSpan τ K (coordKerRoots α)).subgroupOf M) ∈ (rootCoordHom hα).range := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨β, hβ, c, rfl⟩ := hg
      by_cases hβα : β = α
      · subst hβα
        exact ⟨Multiplicative.ofAdd c, rfl⟩
      · refine ⟨1, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan (S := coordKerRoots α)
          ⟨hβ.1, hβ.2.1, hβ.2.2, hβα⟩ c)
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨v, hv⟩ := ihy
      refine ⟨u * v, ?_⟩
      rw [map_mul, hu, hv, ← QuotientGroup.mk_mul]
      rfl
    | inv x hx ihx =>
      obtain ⟨u, hu⟩ := ihx
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, hu, ← QuotientGroup.mk_inv]
      rfl
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact key x (hM ▸ x.2)

section Finite

variable [Finite K]

omit [Finite K] in
theorem card_heightSeries_eq_mul
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    Nat.card (heightSeries τ K (height α)) =
      Nat.card K * Nat.card (rootSpan τ K (coordKerRoots α)) := by
  have hfin : (coordKerRoots α).Finite :=
    finite_of_forall_isRoot_pos fun β hβ => ⟨hβ.1, hβ.2.1⟩
  have hset : {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ height α ≤ height γ} =
      insert α (coordKerRoots α) := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, coordKerRoots]
    constructor
    · intro h
      by_cases hb : β = α
      · exact Or.inl hb
      · exact Or.inr ⟨h.1, h.2.1, h.2.2, hb⟩
    · rintro (rfl | h)
      · exact ⟨hα.1, hα.2, le_rfl⟩
      · exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hnot : α ∉ coordKerRoots α := fun h => h.2.2.2 rfl
  rw [heightSeries, card_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) heightSeriesSet_closed,
    card_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) (coordKerRoots_closed α), hset,
    Set.ncard_insert_of_notMem hnot hfin, pow_succ']

theorem card_rootCoordQuot
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    Nat.card (heightSeries τ K (height α) ⧸
      (rootSpan τ K (coordKerRoots α)).subgroupOf (heightSeries τ K (height α))) =
      Nat.card K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((rootSpan τ K (coordKerRoots α)).subgroupOf (heightSeries τ K (height α)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (coordKer_le_heightSeries α)).toEquiv,
    card_heightSeries_eq_mul hα] at h1
  have hpos : 0 < Nat.card (rootSpan τ K (coordKerRoots α)) := by
    rw [card_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) (coordKerRoots_closed α)]
    exact pow_pos Nat.card_pos _
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

theorem rootCoordHom_bijective
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    Function.Bijective (rootCoordHom (K := K) hα) :=
  (rootCoordHom_surjective hα).bijective_of_nat_card_le
    ((Nat.card_congr Multiplicative.toAdd).trans (card_rootCoordQuot hα).symm).le

open scoped _root_.Classical in
@[expose] def rootCoord
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (g : ModGL τ K) : K :=
  if hg : g ∈ heightSeries τ K (height α) then
    ((MulEquiv.ofBijective _ (rootCoordHom_bijective hα)).symm (QuotientGroup.mk ⟨g, hg⟩)).toAdd
  else 0

theorem rootCoordHom_rootCoord
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    {g : ModGL τ K} (hg : g ∈ heightSeries τ K (height α)) :
    rootCoordHom hα (Multiplicative.ofAdd (rootCoord hα g)) = QuotientGroup.mk ⟨g, hg⟩ := by
  rw [rootCoord, dite_eq_left hg, ofAdd_toAdd]
  exact (MulEquiv.ofBijective _ (rootCoordHom_bijective hα)).apply_symm_apply _

theorem rootCoord_eq
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    {g : ModGL τ K} (hg : g ∈ heightSeries τ K (height α)) {c : K}
    (h : QuotientGroup.mk ⟨g, hg⟩ = rootCoordHom hα (Multiplicative.ofAdd c)) :
    rootCoord hα g = c :=
  Multiplicative.ofAdd.injective ((rootCoordHom_bijective hα).1
    ((rootCoordHom_rootCoord hα hg).trans h))

theorem rootCoord_mul
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    {g g' : ModGL τ K} (hg : g ∈ heightSeries τ K (height α))
    (hg' : g' ∈ heightSeries τ K (height α)) :
    rootCoord hα (g * g') = rootCoord hα g + rootCoord hα g' := by
  refine rootCoord_eq hα (mul_mem hg hg') ?_
  rw [ofAdd_add, map_mul, rootCoordHom_rootCoord hα hg, rootCoordHom_rootCoord hα hg',
    ← QuotientGroup.mk_mul]
  rfl

theorem rootCoord_self
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) (c : K) :
    rootCoord hα (pinnedX τ K α c) = c :=
  rootCoord_eq hα (pinnedX_mem_heightSeries_height hα c) rfl

theorem rootCoord_of_mem_coordKer
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    {g : ModGL τ K} (hg : g ∈ rootSpan τ K (coordKerRoots α)) : rootCoord hα g = 0 := by
  refine rootCoord_eq hα (coordKer_le_heightSeries α hg) ?_
  rw [ofAdd_zero, map_one, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 hg

theorem rootCoord_pinnedX_of_ne
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (hβ : IsRoot τ β ∧ 0 < height β) (hh : height α ≤ height β) (hne : β ≠ α) (c : K) :
    rootCoord hα (pinnedX τ K β c) = 0 :=
  rootCoord_of_mem_coordKer hα (pinnedX_mem_rootSpan (S := coordKerRoots α)
    ⟨hβ.1, hβ.2, hh, hne⟩ c)

theorem rootCoord_one
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    rootCoord hα (1 : ModGL τ K) = 0 :=
  rootCoord_of_mem_coordKer hα (Subgroup.one_mem _)

theorem rootCoord_conj
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    {x g : ModGL τ K} (hx : x ∈ posUnipotent τ K) (hg : g ∈ heightSeries τ K (height α)) :
    rootCoord hα (x * g * x⁻¹) = rootCoord hα g := by
  have hxg : x * g * x⁻¹ ∈ heightSeries τ K (height α) :=
    (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hx) g).1 hg
  refine rootCoord_eq hα hxg ?_
  rw [rootCoordHom_rootCoord hα hg, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hc : ⁅x, g⁻¹⁆ ∈ rootSpan τ K (coordKerRoots α) :=
    heightSeries_succ_le_coordKer α (commutator_posUnipotent_heightSeries_le _
      (Subgroup.commutator_mem_commutator hx (inv_mem hg)))
  convert hc using 1

theorem rootCoord_list_prod
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) :
    ∀ L : List (ModGL τ K), (∀ g ∈ L, g ∈ heightSeries τ K (height α)) →
      rootCoord hα L.prod = (L.map (rootCoord hα)).sum
  | [], _ => by simp [rootCoord_one]
  | g :: L, hL => by
    have hg := hL g List.mem_cons_self
    have hL' : ∀ g' ∈ L, g' ∈ heightSeries τ K (height α) := fun g' h =>
      hL g' (List.mem_cons_of_mem _ h)
    rw [List.prod_cons, rootCoord_mul hα hg (list_prod_mem hL'), rootCoord_list_prod hα L hL',
      List.map_cons, List.sum_cons]

end Finite

end Coordinate

theorem commutator_prod_mem_and_coord {G A : Type*} [Group G] [AddCommGroup A]
    {U M : Subgroup G} (hMU : U ≤ Subgroup.normalizer (M : Set G)) (π : G → A)
    (hmul : ∀ x ∈ M, ∀ y ∈ M, π (x * y) = π x + π y)
    (hconj : ∀ g ∈ U, ∀ x ∈ M, π (g * x * g⁻¹) = π x) :
    ∀ zs ws : List G, (∀ z ∈ zs, z ∈ U) → (∀ w ∈ ws, w ∈ U) →
      (∀ z ∈ zs, ∀ w ∈ ws, ⁅z, w⁆ ∈ M) →
      ⁅zs.prod, ws.prod⁆ ∈ M ∧
        π ⁅zs.prod, ws.prod⁆ = (zs.map fun z => (ws.map fun w => π ⁅z, w⁆).sum).sum := by
  have h1 : π 1 = 0 := by
    have h := hmul 1 M.one_mem 1 M.one_mem
    rw [mul_one] at h
    exact (add_eq_left.mp h.symm)
  have conj : ∀ g ∈ U, ∀ x ∈ M, g * x * g⁻¹ ∈ M := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hMU hg) x).1 hx
  have inner : ∀ z ∈ U, ∀ ws : List G, (∀ w ∈ ws, w ∈ U) → (∀ w ∈ ws, ⁅z, w⁆ ∈ M) →
      ⁅z, ws.prod⁆ ∈ M ∧ π ⁅z, ws.prod⁆ = (ws.map fun w => π ⁅z, w⁆).sum := by
    intro z _ ws
    induction ws with
    | nil => intro _ _; simp [h1]
    | cons w ws ih =>
      intro hw hzw
      have hw0 := hw w List.mem_cons_self
      have hzw0 := hzw w List.mem_cons_self
      obtain ⟨hm, hπ⟩ := ih (fun w' h => hw w' (List.mem_cons_of_mem _ h))
        (fun w' h => hzw w' (List.mem_cons_of_mem _ h))
      have e : ⁅z, w * ws.prod⁆ = ⁅z, w⁆ * (w * ⁅z, ws.prod⁆ * w⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hc := conj w hw0 _ hm
      rw [List.prod_cons, e, List.map_cons, List.sum_cons, hmul _ hzw0 _ hc, hconj w hw0 _ hm,
        hπ]
      exact ⟨mul_mem hzw0 hc, rfl⟩
  intro zs ws hz hw hzw
  induction zs with
  | nil => simp [h1]
  | cons z zs ih =>
    have hz0 := hz z List.mem_cons_self
    obtain ⟨hm, hπ⟩ := ih (fun z' h => hz z' (List.mem_cons_of_mem _ h))
      (fun z' h => hzw z' (List.mem_cons_of_mem _ h))
    obtain ⟨hm1, hπ1⟩ := inner z hz0 ws hw (hzw z List.mem_cons_self)
    have e : ⁅z * zs.prod, ws.prod⁆ = (z * ⁅zs.prod, ws.prod⁆ * z⁻¹) * ⁅z, ws.prod⁆ := by
      simp only [commutatorElement_def]
      group
    have hc := conj z hz0 _ hm
    rw [List.prod_cons, e, List.map_cons, List.sum_cons, hmul _ hc _ hm1, hconj z hz0 _ hm, hπ,
      hπ1, add_comm]
    exact ⟨mul_mem hc hm1, rfl⟩

@[expose] def f4x
    (K : Type) [Field K] (i : ℕ) (c : K) : ModGL .F4 K :=
  pinnedX .F4 K (orbitCertRoot .F4 i) c

theorem f4_isRoot_pos
    {i : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) :
    IsRoot .F4 (orbitCertRoot .F4 i) ∧ 0 < height (orbitCertRoot .F4 i) :=
  (f4_even_positive_root_commutator_table.{0}.1 _).2 ⟨i, hi.1, hi.2, rfl⟩

theorem f4_orbitCertRoot_inj : ∀ i j : Fin 48, 24 ≤ (i : ℕ) → 24 ≤ (j : ℕ) →
    orbitCertRoot .F4 i = orbitCertRoot .F4 j → i = j := by
  decide +kernel

theorem f4_orbitCertRoot_inj' {i j : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) (hj : 24 ≤ j ∧ j ≤ 47)
    (h : orbitCertRoot .F4 i = orbitCertRoot .F4 j) : i = j :=
  congrArg Fin.val (f4_orbitCertRoot_inj ⟨i, by omega⟩ ⟨j, by omega⟩ hi.1 hj.1 h)

variable {K : Type} [Field K]

theorem f4x_mem_posUnipotent
    {i : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) (c : K) :
    f4x K i c ∈ posUnipotent .F4 K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α}) (f4_isRoot_pos hi) c

theorem f4x_zero
    (i : ℕ) : f4x K i 0 = 1 :=
  pinnedX_zero _ _ _

theorem f4x_mem_heightSeries
    {k i : ℕ} (hi : 24 ≤ i ∧ i ≤ 47)
    (hh : height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 i)) (c : K) :
    f4x K i c ∈ heightSeries .F4 K (height (orbitCertRoot .F4 k)) :=
  pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧
    height (orbitCertRoot .F4 k) ≤ height α}) ⟨(f4_isRoot_pos hi).1, (f4_isRoot_pos hi).2, hh⟩ c

section Finite

variable [Finite K]

theorem rootCoord_f4x
    {k k' : ℕ} (hk : 24 ≤ k ∧ k ≤ 47) (hk' : 24 ≤ k' ∧ k' ≤ 47)
    (hh : height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 k')) (e : K) :
    rootCoord (f4_isRoot_pos hk) (f4x K k' e) = if k' = k then e else 0 := by
  by_cases h : k' = k
  · subst h
    rw [ite_eq_left rfl]
    exact rootCoord_self _ e
  · rw [ite_eq_right h]
    exact rootCoord_pinnedX_of_ne _ (f4_isRoot_pos hk') hh
      (fun he => h (f4_orbitCertRoot_inj' hk' hk he)) e

theorem f4_commutator_coord
    [CharP K 2] {k i p : ℕ} (hk : 24 ≤ k ∧ k ≤ 47)
    (hi : 24 ≤ i ∧ i ≤ 47) (hp : 24 ≤ p ∧ p ≤ 47)
    (hmin : i ≠ p → ∀ f ∈ (f4OddCommutatorFactors.lookup (i, p)).getD [],
      24 ≤ f.2.2 ∧ f.2.2 ≤ 47 ∧ height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 f.2.2))
    (c v : K) :
    ⁅f4x K i c, f4x K p v⁆ ∈ heightSeries .F4 K (height (orbitCertRoot .F4 k)) ∧
      rootCoord (f4_isRoot_pos hk) ⁅f4x K i c, f4x K p v⁆ =
        if i = p then 0 else
          (((f4OddCommutatorFactors.lookup (i, p)).getD []).map fun f =>
            if f.2.2 = k then c ^ f.1 * v ^ f.2.1 else 0).sum := by
  by_cases hip : i = p
  · subst hip
    have h1 : ⁅f4x K i c, f4x K i v⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm, f4x, f4x, ← pinnedX_add, ← pinnedX_add,
        add_comm]
    rw [h1, rootCoord_one, ite_eq_left rfl]
    exact ⟨Subgroup.one_mem _, rfl⟩
  · rw [ite_eq_right hip]
    have htab : ⁅f4x K i c, f4x K p v⁆ = (((f4OddCommutatorFactors.lookup (i, p)).getD []).map
        fun f => f4x K f.2.2 (c ^ f.1 * v ^ f.2.1)).prod :=
      f4_even_positive_root_commutator_table.2.2.2.2 K i p hi.1 hi.2 hp.1 hp.2 hip c v
    have hmem : ∀ g ∈ ((f4OddCommutatorFactors.lookup (i, p)).getD []).map
        (fun f => f4x K f.2.2 (c ^ f.1 * v ^ f.2.1)),
        g ∈ heightSeries .F4 K (height (orbitCertRoot .F4 k)) := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      obtain ⟨h1, h2, h3⟩ := hmin hip f hf
      exact f4x_mem_heightSeries ⟨h1, h2⟩ h3 _
    rw [htab]
    refine ⟨list_prod_mem hmem, ?_⟩
    rw [rootCoord_list_prod _ _ hmem, List.map_map]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    obtain ⟨h1, h2, h3⟩ := hmin hip f hf
    exact rootCoord_f4x hk ⟨h1, h2⟩ h3 _

end Finite

@[expose] def f4Contribs (k : ℕ) (S wp : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  S.flatMap fun i => wp.flatMap fun p =>
    if i = p then [] else
      ((f4OddCommutatorFactors.lookup (i, p)).getD []).filterMap fun f =>
        if f.2.2 = k then some (i, f.1, p, f.2.1) else none

@[expose] def f4RowOK (k : ℕ) (S wp : List ℕ) : Bool :=
  decide (24 ≤ k ∧ k ≤ 47) && S.all (fun i => decide (24 ≤ i ∧ i ≤ 47)) &&
    wp.all (fun p => decide (24 ≤ p ∧ p ≤ 47)) &&
    S.all fun i => wp.all fun p => decide (i = p) ||
      ((f4OddCommutatorFactors.lookup (i, p)).getD []).all fun f =>
        decide (24 ≤ f.2.2 ∧ f.2.2 ≤ 47 ∧
          height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 f.2.2))

theorem f4RowOK_spec {k : ℕ} {S wp : List ℕ} (h : f4RowOK k S wp = true) :
    (24 ≤ k ∧ k ≤ 47) ∧ (∀ i ∈ S, 24 ≤ i ∧ i ≤ 47) ∧ (∀ p ∈ wp, 24 ≤ p ∧ p ≤ 47) ∧
      ∀ i ∈ S, ∀ p ∈ wp, i ≠ p → ∀ f ∈ (f4OddCommutatorFactors.lookup (i, p)).getD [],
        24 ≤ f.2.2 ∧ f.2.2 ≤ 47 ∧
          height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 f.2.2) := by
  simp only [f4RowOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    at h
  obtain ⟨⟨⟨hk, hS⟩, hwp⟩, hm⟩ := h
  exact ⟨hk, hS, hwp, fun i hi p hp hip f hf => (hm i hi p hp).resolve_left hip f hf⟩

theorem sum_map_filterMap_ite {β γ δ : Type*} [AddCommMonoid δ] (L : List β) (P : β → Prop)
    [DecidablePred P] (g : β → γ) (F : γ → δ) :
    ((L.filterMap fun f => if P f then some (g f) else none).map F).sum =
      (L.map fun f => if P f then F (g f) else 0).sum := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    by_cases hP : P f
    · simp [hP, ih]
    · simp [hP, ih]

theorem f4Contribs_sum (k : ℕ) (S wp : List ℕ) (c v : ℕ → K) :
    ((f4Contribs k S wp).map fun m => c m.1 ^ m.2.1 * v m.2.2.1 ^ m.2.2.2).sum =
      (S.map fun i => (wp.map fun p => if i = p then 0 else
        (((f4OddCommutatorFactors.lookup (i, p)).getD []).map fun f =>
          if f.2.2 = k then c i ^ f.1 * v p ^ f.2.1 else 0).sum).sum).sum := by
  induction S with
  | nil => rfl
  | cons i S ihS =>
    rw [f4Contribs, List.flatMap_cons, List.map_append, List.sum_append, ← f4Contribs, ihS,
      List.map_cons, List.sum_cons]
    congr 1
    clear ihS
    induction wp with
    | nil => rfl
    | cons p wp ihw =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ihw, List.map_cons, List.sum_cons]
      congr 1
      by_cases hip : i = p
      · rw [ite_eq_left hip, ite_eq_left hip]
        rfl
      · rw [ite_eq_right hip, ite_eq_right hip, sum_map_filterMap_ite]

theorem f4_row
    [Finite K] [CharP K 2] {k : ℕ} {S wp : List ℕ} (hok : f4RowOK k S wp = true)
    (c v : ℕ → K)
    (hcomm : ⁅(S.map fun i => f4x K i (c i)).prod, (wp.map fun p => f4x K p (v p)).prod⁆ = 1) :
    ((f4Contribs k S wp).map fun m => c m.1 ^ m.2.1 * v m.2.2.1 ^ m.2.2.2).sum = 0 := by
  obtain ⟨hk, hS, hwp, hmin⟩ := f4RowOK_spec hok
  have hcom := commutator_prod_mem_and_coord (U := posUnipotent .F4 K)
    (M := heightSeries .F4 K (height (orbitCertRoot .F4 k)))
    (heightSeries_le_normalizer K _) (rootCoord (f4_isRoot_pos hk))
    (fun x hx y hy => rootCoord_mul _ hx hy) (fun g hg x hx => rootCoord_conj _ hg hx)
    (S.map fun i => f4x K i (c i)) (wp.map fun p => f4x K p (v p))
    (fun z hz => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      exact f4x_mem_posUnipotent (hS i hi) _)
    (fun w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
      exact f4x_mem_posUnipotent (hwp p hp) _)
    (fun z hz w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
      exact (f4_commutator_coord (K := K) hk (hS i hi) (hwp p hp) (hmin i hi p hp) _ _).1)
  rw [hcomm, rootCoord_one, List.map_map] at hcom
  rw [f4Contribs_sum]
  refine Eq.trans ?_ hcom.2.symm
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp only [Function.comp_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  exact (f4_commutator_coord (K := K) hk (hS i hi) (hwp p hp) (hmin i hi p hp) _ _).2.symm

@[expose] def f4PosList : List ℕ :=
  List.ofFn fun j : Fin 24 => 24 + (j : ℕ)

@[expose] def f4KillOrder : List ℕ :=
  [25, 27, 28, 30, 29, 35, 31, 37, 32, 40, 43, 46, 24, 33, 26, 34, 36, 38, 39, 41, 42, 45]

@[expose] def f4Support (n : ℕ) : List ℕ :=
  f4PosList.filter fun i => decide (i ∉ f4KillOrder.take n)

@[expose] def testVA {K : Type} [Field K] (θ : ℕ) (t : K) (p : ℕ) : K :=
  if p = 33 then t else t ^ θ

@[expose] def largeReeTestA
    (K : Type) [Field K] (θ : ℕ) (t : K) : ModGL .F4 K :=
  f4x K 33 t * f4x K 24 (t ^ θ)

@[expose] def largeReeTestB
    (K : Type) [Field K] (θ : ℕ) (t : K) : ModGL .F4 K :=
  f4x K 25 t * f4x K 27 (t ^ (2 * θ)) * f4x K 30 (t ^ (2 * θ + 2))

theorem largeReeTestA_eq
    (θ : ℕ) (t : K) :
    largeReeTestA K θ t = ([33, 24].map fun p => f4x K p (testVA θ t p)).prod := by
  simp [largeReeTestA, testVA]

theorem largeReeTestA_one (θ : ℕ) :
    largeReeTestA K θ 1 = ([33, 24].map fun p => f4x K p ((fun _ => (1 : K)) p)).prod := by
  simp [largeReeTestA]

theorem largeReeTestB_one (θ : ℕ) :
    largeReeTestB K θ 1 = ([25, 27, 30].map fun p => f4x K p ((fun _ => (1 : K)) p)).prod := by
  simp [largeReeTestB, mul_assoc]

theorem f4_take_succ {c : ℕ → K} {n : ℕ} (hD : ∀ j ∈ f4KillOrder.take n, c j = 0)
    (h : c (f4KillOrder.getD n 0) = 0) : ∀ j ∈ f4KillOrder.take (n + 1), c j = 0 := by
  intro j hj
  rw [List.take_add_one, List.mem_append] at hj
  rcases hj with hj | hj
  · exact hD j hj
  · simp only [Option.mem_toList] at hj
    rw [List.getD_eq_getElem?_getD, hj, Option.getD_some] at h
    exact h

theorem f4_row_n
    [Finite K] [CharP K 2] (c : ℕ → K) {v : ℕ → K} (n : ℕ)
    (hD : ∀ j ∈ f4KillOrder.take n, c j = 0) {k : ℕ} {wp : List ℕ} {E : List (ℕ × ℕ × ℕ × ℕ)}
    (hok : (f4RowOK k (f4Support n) wp && f4Contribs k (f4Support n) wp == E) = true)
    (hcomm : ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      (wp.map fun p => f4x K p (v p)).prod⁆ = 1) :
    (E.map fun m => c m.1 ^ m.2.1 * v m.2.2.1 ^ m.2.2.2).sum = 0 := by
  rw [Bool.and_eq_true, beq_iff_eq] at hok
  rw [← hok.2]
  rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i ∉ f4KillOrder.take n)) _
    (fun i _ hi => by
      simp only [decide_eq_false_iff_not, not_not] at hi
      rw [hD i hi, f4x_zero])] at hcomm
  exact f4_row hok.1 c v hcomm

theorem eq_zero_of_forall_mul_add_mul_pow [Finite K] {θ : ℕ} (hθ : 1 < θ)
    (hθq : θ < Nat.card K) {C D : K} (h : ∀ t : K, C * t + D * t ^ θ = 0) : C = 0 ∧ D = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set P : Polynomial K := Polynomial.C C * Polynomial.X + Polynomial.C D * Polynomial.X ^ θ
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := id)
      Function.injective_id (fun t => by simp [P, h t]) ?_
    have hd1 : (Polynomial.C C * Polynomial.X).natDegree ≤ θ :=
      (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans hθ.le)
    have hd2 : (Polynomial.C D * Polynomial.X ^ θ).natDegree ≤ θ :=
      (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le θ)
    calc P.natDegree ≤ θ := (Polynomial.natDegree_add_le _ _).trans (max_le hd1 hd2)
      _ < Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have h1 := congrArg (fun p => Polynomial.coeff p 1) hP0
  have h2 := congrArg (fun p => Polynomial.coeff p θ) hP0
  simp [P, Polynomial.coeff_X, Polynomial.coeff_X_pow, hθ.ne] at h1 h2
  exact ⟨h1, h2⟩

theorem f4_coords_eq_zero
    [Finite K] [CharP K 2] {θ : ℕ} (hθ : 1 < θ) (hθq : θ < Nat.card K)
    (c : ℕ → K)
    (hA : ∀ t, ⁅(f4PosList.map fun i => f4x K i (c i)).prod, largeReeTestA K θ t⁆ = 1)
    (hB : ⁅(f4PosList.map fun i => f4x K i (c i)).prod, largeReeTestB K θ 1⁆ = 1) :
    ∀ i ∈ f4KillOrder, c i = 0 := by
  have hAw : ∀ t, ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      ([33, 24].map fun p => f4x K p (testVA θ t p)).prod⁆ = 1 := fun t => by
    rw [← largeReeTestA_eq]
    exact hA t
  have hA1 := hA 1
  rw [largeReeTestA_one] at hA1
  have hB1 := hB
  rw [largeReeTestB_one] at hB1
  have hD0 : ∀ j ∈ f4KillOrder.take 0, c j = 0 := by simp
  have k25 : c 25 = 0 := by
    simpa using f4_row_n c 0 hD0 (k := 26) (E := [(25, 1, 24, 1)]) (by decide +kernel) hA1
  have hD1 := f4_take_succ hD0 k25
  have k27 : c 27 = 0 := by
    simpa using f4_row_n c 1 hD1 (k := 34) (E := [(27, 1, 33, 1)]) (by decide +kernel) hA1
  have hD2 := f4_take_succ hD1 k27
  have k28 : c 28 = 0 := by
    simpa using f4_row_n c 2 hD2 (k := 35) (E := [(28, 1, 33, 1)]) (by decide +kernel) hA1
  have hD3 := f4_take_succ hD2 k28
  have k30 : c 30 = 0 := by
    simpa using f4_row_n c 3 hD3 (k := 37) (E := [(30, 1, 33, 1)]) (by decide +kernel) hA1
  have hD4 := f4_take_succ hD3 k30
  obtain ⟨k29, k35⟩ : c 29 = 0 ∧ c 35 = 0 :=
    eq_zero_of_forall_mul_add_mul_pow hθ hθq fun t => by
      simpa [testVA] using f4_row_n c 4 hD4 (k := 36)
        (E := [(29, 1, 33, 1), (35, 1, 24, 1)]) (by decide +kernel) (hAw t)
  have hD5 := f4_take_succ hD4 k29
  have hD6 := f4_take_succ hD5 k35
  obtain ⟨k31, k37⟩ : c 31 = 0 ∧ c 37 = 0 :=
    eq_zero_of_forall_mul_add_mul_pow hθ hθq fun t => by
      simpa [testVA] using f4_row_n c 6 hD6 (k := 38)
        (E := [(31, 1, 33, 1), (37, 1, 24, 1)]) (by decide +kernel) (hAw t)
  have hD7 := f4_take_succ hD6 k31
  have hD8 := f4_take_succ hD7 k37
  have k32 : c 32 = 0 := by
    simpa using f4_row_n c 8 hD8 (k := 39) (E := [(32, 1, 33, 1)]) (by decide +kernel) hA1
  have hD9 := f4_take_succ hD8 k32
  have k40 : c 40 = 0 := by
    simpa using f4_row_n c 9 hD9 (k := 41) (E := [(40, 1, 24, 1)]) (by decide +kernel) hA1
  have hD10 := f4_take_succ hD9 k40
  have k43 : c 43 = 0 := by
    simpa using f4_row_n c 10 hD10 (k := 44) (E := [(43, 1, 24, 1)]) (by decide +kernel) hA1
  have hD11 := f4_take_succ hD10 k43
  have k46 : c 46 = 0 := by
    simpa using f4_row_n c 11 hD11 (k := 47) (E := [(46, 1, 33, 1)]) (by decide +kernel) hA1
  have hD12 := f4_take_succ hD11 k46
  have k24 : c 24 = 0 := by
    simpa using f4_row_n c 12 hD12 (k := 26) (E := [(24, 1, 25, 1)]) (by decide +kernel) hB1
  have hD13 := f4_take_succ hD12 k24
  have k33 : c 33 = 0 := by
    simpa using f4_row_n c 13 hD13 (k := 34) (E := [(33, 1, 27, 1)]) (by decide +kernel) hB1
  have hD14 := f4_take_succ hD13 k33
  have k26 : c 26 = 0 := by
    simpa using f4_row_n c 14 hD14 (k := 29) (E := [(26, 1, 27, 1)]) (by decide +kernel) hB1
  have hD15 := f4_take_succ hD14 k26
  have k34 : c 34 = 0 := by
    simpa using f4_row_n c 15 hD15 (k := 35) (E := [(34, 1, 25, 1)]) (by decide +kernel) hB1
  have hD16 := f4_take_succ hD15 k34
  have k36 : c 36 = 0 := by
    simpa using f4_row_n c 16 hD16 (k := 38) (E := [(36, 1, 25, 1)]) (by decide +kernel) hB1
  have hD17 := f4_take_succ hD16 k36
  have k38 : c 38 = 0 := by
    simpa using f4_row_n c 17 hD17 (k := 41) (E := [(38, 1, 27, 1)]) (by decide +kernel) hB1
  have hD18 := f4_take_succ hD17 k38
  have k39 : c 39 = 0 := by
    simpa using f4_row_n c 18 hD18 (k := 42) (E := [(39, 1, 27, 1)]) (by decide +kernel) hB1
  have hD19 := f4_take_succ hD18 k39
  have k41 : c 41 = 0 := by
    simpa using f4_row_n c 19 hD19 (k := 43) (E := [(41, 1, 25, 1)]) (by decide +kernel) hB1
  have hD20 := f4_take_succ hD19 k41
  have k42 : c 42 = 0 := by
    simpa using f4_row_n c 20 hD20 (k := 44) (E := [(42, 1, 25, 1)]) (by decide +kernel) hB1
  have hD21 := f4_take_succ hD20 k42
  have k45 : c 45 = 0 := by
    simpa using f4_row_n c 21 hD21 (k := 46) (E := [(45, 1, 27, 1)]) (by decide +kernel) hB1
  have hD22 := f4_take_succ hD21 k45
  rw [show f4KillOrder.take 22 = f4KillOrder by decide] at hD22
  exact hD22

theorem exists_f4_coords
    {z : ModGL .F4 K} (hz : z ∈ posUnipotent .F4 K) :
    ∃ c : ℕ → K, z = (f4PosList.map fun i => f4x K i (c i)).prod := by
  let α : Fin 24 → Fin Tag.F4.rank → ℤ := fun j => orbitCertRoot .F4 (24 + j)
  have hα : Function.Injective α := fun i j h => Fin.ext (by
    have := f4_orbitCertRoot_inj' (i := 24 + i) (j := 24 + j) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ h
    omega)
  have hrange : Set.range α = {β | IsRoot .F4 β ∧ 0 < height β} := by
    ext β
    refine ⟨?_, fun hβ => ?_⟩
    · rintro ⟨j, rfl⟩
      exact f4_isRoot_pos ⟨by omega, by omega⟩
    · obtain ⟨i, hi, hi', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 β).1 hβ
      refine ⟨⟨i - 24, by omega⟩, ?_⟩
      simp only [α]
      congr 1
      omega
  obtain ⟨c, -, hc⟩ := ((positive_root_collection .F4 K).2 α hα hrange).2.2 hz
  refine ⟨fun i => c ⟨(i - 24) % 24, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  rw [← hc, f4PosList, List.map_ofFn]
  congr 1
  funext j
  congr 2
  ext
  simp only
  omega

theorem f4_lookup_44_47 : ∀ j : Fin 48, 24 ≤ (j : ℕ) →
    (f4OddCommutatorFactors.lookup (44, (j : ℕ))).getD [] = [] ∧
      (f4OddCommutatorFactors.lookup (47, (j : ℕ))).getD [] = [] := by
  decide +kernel

theorem f4x_central
    [CharP K 2] {k : ℕ} (hk : k = 44 ∨ k = 47) (c : K) {u : ModGL .F4 K}
    (hu : u ∈ posUnipotent .F4 K) : u * f4x K k c = f4x K k c * u := by
  have hk' : 24 ≤ k ∧ k ≤ 47 := by omega
  rw [posUnipotent, rootSpan_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨β, hβ, d, rfl⟩ := hg
    obtain ⟨j, hj, hj', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 β).1 hβ
    by_cases hkj : k = j
    · subst hkj
      rw [f4x, ← pinnedX_add, ← pinnedX_add, add_comm]
    · have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K k j hk'.1 hk'.2 hj hj' hkj c d
      have hl : (f4OddCommutatorFactors.lookup (k, j)).getD [] = [] := by
        rcases hk with rfl | rfl
        · exact (f4_lookup_44_47 ⟨j, by omega⟩ hj).1
        · exact (f4_lookup_44_47 ⟨j, by omega⟩ hj).2
      rw [hl, List.map_nil, List.prod_nil] at h
      exact (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_cancel, mul_one]

theorem f4_mem_of_commute
    [Finite K] [CharP K 2] {θ : ℕ} (hθ : 1 < θ) (hθq : θ < Nat.card K)
    {z : ModGL .F4 K} (hz : z ∈ posUnipotent .F4 K) (hA : ∀ t, ⁅z, largeReeTestA K θ t⁆ = 1)
    (hB : ⁅z, largeReeTestB K θ 1⁆ = 1) : ∃ c d : K, f4x K 44 c * f4x K 47 d = z := by
  obtain ⟨c, rfl⟩ := exists_f4_coords hz
  have h0 := f4_coords_eq_zero hθ hθq c hA hB
  have hcover : ∀ i ∈ f4PosList, decide (i = 44 ∨ i = 47) = false → i ∈ f4KillOrder := by
    decide
  refine ⟨c 44, c 47, ?_⟩
  rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i = 44 ∨ i = 47)) _
    (fun i hi hne => by rw [h0 i (hcover i hi hne), f4x_zero]),
    show f4PosList.filter (fun i => decide (i = 44 ∨ i = 47)) = [44, 47] by decide]
  simp

theorem largeReeTestA_mem
    (θ : ℕ) (t : K) : largeReeTestA K θ t ∈ posUnipotent .F4 K :=
  mul_mem (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
    (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)

theorem largeReeTestB_mem
    (θ : ℕ) (t : K) : largeReeTestB K θ t ∈ posUnipotent .F4 K :=
  mul_mem (mul_mem (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
    (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _))
    (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)

theorem large_Ree_ambient_positive_centralizer
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    posUnipotent .F4 K ⊓ Subgroup.centralizer (Subgroup.closure
        (Set.range (largeReeTestA K (2 ^ a)) ∪ Set.range (largeReeTestB K (2 ^ a))) :
          Set (ModGL .F4 K)) =
      (Subgroup.center (posUnipotent .F4 K)).map (posUnipotent .F4 K).subtype ∧
    (Subgroup.center (posUnipotent .F4 K)).map (posUnipotent .F4 K).subtype =
      rootSubgroup .F4 K (orbitCertRoot .F4 44) ⊔ rootSubgroup .F4 K (orbitCertRoot .F4 47) ∧
    ((rootSubgroup .F4 K (orbitCertRoot .F4 44) ⊔ rootSubgroup .F4 K (orbitCertRoot .F4 47) :
        Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K)) =
      {g | ∃ c d : K, f4x K 44 c * f4x K 47 d = g} := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have hθ : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
  have hθq : 2 ^ a < Nat.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  set U := posUnipotent .F4 K
  set S := Set.range (largeReeTestA K (2 ^ a)) ∪ Set.range (largeReeTestB K (2 ^ a))
  set P : Set (ModGL .F4 K) := {g | ∃ c d : K, f4x K 44 c * f4x K 47 d = g}
  set J := rootSubgroup .F4 K (orbitCertRoot .F4 44) ⊔ rootSubgroup .F4 K (orbitCertRoot .F4 47)
  set Z := (Subgroup.center U).map U.subtype
  have hCP : ∀ g ∈ U ⊓ Subgroup.centralizer (Subgroup.closure S : Set (ModGL .F4 K)), g ∈ P := by
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.centralizer_closure] at hgC
    have hc : ∀ h ∈ S, ⁅g, h⁆ = 1 := fun h hh =>
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hgC h hh).symm
    exact f4_mem_of_commute hθ hθq hgU (fun t => hc _ (Or.inl ⟨t, rfl⟩)) (hc _ (Or.inr ⟨1, rfl⟩))
  have hPZ : ∀ g ∈ P, g ∈ Z := by
    rintro _ ⟨c, d, rfl⟩
    have hgU : f4x K 44 c * f4x K 47 d ∈ U :=
      mul_mem (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
        (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
    refine ⟨⟨_, hgU⟩, Subgroup.mem_center_iff.2 fun u => Subtype.ext ?_, rfl⟩
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, f4x_central (Or.inl rfl) c u.2, mul_assoc, f4x_central (Or.inr rfl) d u.2,
      ← mul_assoc]
  have hZC : ∀ g ∈ Z, g ∈ U ⊓ Subgroup.centralizer (Subgroup.closure S : Set (ModGL .F4 K)) := by
    rintro _ ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.2 ⟨z.2, ?_⟩
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    have hhU : h ∈ U := by
      rcases hh with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact largeReeTestA_mem _ t
      · exact largeReeTestB_mem _ t
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hhU⟩)
  have hJZ : J ≤ Z := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
      exact hPZ _ ⟨c, 0, (congrArg (f4x K 44 c * ·) (f4x_zero 47)).trans (mul_one _)⟩
    · obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hg
      exact hPZ _ ⟨0, d, (congrArg (· * f4x K 47 d) (f4x_zero 44)).trans (one_mul _)⟩
  have hPJ : ∀ g ∈ P, g ∈ J := by
    rintro _ ⟨c, d, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨c, rfl⟩))
      (Subgroup.mem_sup_right (mem_rootSubgroup.2 ⟨d, rfl⟩))
  refine ⟨le_antisymm (fun g hg => hPZ g (hCP g hg)) hZC,
    le_antisymm (fun g hg => hPJ g (hCP g (hZC g hg))) hJZ, ?_⟩
  exact Set.Subset.antisymm (fun g hg => hCP g (hZC g (hJZ hg))) hPJ

end CFSG.LieType.Chevalley
