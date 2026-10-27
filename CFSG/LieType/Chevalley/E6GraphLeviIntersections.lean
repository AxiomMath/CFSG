module

public import CFSG.LieType.Chevalley.E6GraphLeviTheta
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
open scoped commutatorElement

variable {E : Type} [Field E]

theorem map_conj_eq_of_forall {G : Type*} [Group G] {P : G} (hP : P * P = 1) {Y : Subgroup G}
    (h : ∀ y ∈ Y, P * y * P⁻¹ ∈ Y) : Y.map (MulAut.conj P).toMonoidHom = Y := by
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hP).symm
  refine le_antisymm ?_ fun y hy => ⟨P * y * P⁻¹, h y hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · change P * (P * y * P⁻¹) * P⁻¹ = y
    rw [hPinv]
    calc P * (P * y * P) * P = (P * P) * y * (P * P) := by group
      _ = y := by rw [hP, one_mul, mul_one]

@[expose] def foldedSetA : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a.val ≠ 3}

theorem orbitUnion_foldedSetA : TwistTag.E6.orbitUnion foldedSetA = setA := by
  ext i
  rw [TwistTag.mem_orbitUnion]
  simp only [foldedSetA, setA, Set.mem_ofPred_eq]
  revert i
  decide

theorem twistHom_refl_eq :
    twistHom TwistTag.E6 E (RingEquiv.refl E).toRingHom =
      (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom :=
  MonoidHom.ext fun g => twistHom_id_eq TwistTag.E6 E g

theorem diagram_parabolic_maps :
    (parabolicRadical TwistTag.E6.tag E setA).map
        (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom =
      parabolicRadical TwistTag.E6.tag E setA ∧
    (parabolicLevi TwistTag.E6.tag E setA).map
        (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom =
      parabolicLevi TwistTag.E6.tag E setA ∧
    (parabolicSubgroup TwistTag.E6.tag E setA).map
        (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom =
      parabolicSubgroup TwistTag.E6.tag E setA := by
  have h := diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 E (RingEquiv.refl E)
    foldedSetA
  rw [orbitUnion_foldedSetA, twistHom_refl_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.2.1⟩

theorem conj_mem_of_map_eq {G : Type*} [Group G] {P : G} {Y : Subgroup G}
    (hY : Y.map (MulAut.conj P).toMonoidHom = Y) {y : G} (hy : y ∈ Y) : P * y * P⁻¹ ∈ Y := by
  rw [← hY]
  exact ⟨y, hy, rfl⟩

theorem diagramMap_conj_mem_subsystemGroup
    (h2 : (2 : E) = 0) {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag E setA) :
    diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹ ∈
      subsystemGroup TwistTag.E6.tag E setA := by
  rw [← range_realize h2] at hg ⊢
  obtain ⟨B, rfl⟩ := hg
  exact ⟨graphSL E B, (diagramMap_conj_realize h2 B).symm⟩

theorem diagramMap_conj_mem_adjointGroup'
    {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ adjointGroup TwistTag.E6.tag E) :
    diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹ ∈
      adjointGroup TwistTag.E6.tag E := by
  have h := map_twistHom_adjointGroup (t := TwistTag.E6) (K := E) (σ := RingHom.id E)
    Function.surjective_id
  rw [← twistHom_id_eq, ← h]
  exact ⟨g, hg, rfl⟩

theorem map_conj_eq_of_le_range
    (h2 : (2 : E) = 0) {Y : Subgroup (ModGL TwistTag.E6.tag E)}
    (hY : Y ≤ (thetaSL2 E).range) :
    Y.map (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom = Y := by
  refine map_conj_eq_of_forall diagramMap_E6_mul_self fun y hy => ?_
  obtain ⟨B, rfl⟩ := hY hy
  rw [diagramMap_conj_thetaSL2 h2]
  exact hy

theorem subsystemGroup_le_adjointGroup :
    subsystemGroup TwistTag.E6.tag E setA ≤ adjointGroup TwistTag.E6.tag E :=
  (le_sup_right : subsystemGroup TwistTag.E6.tag E setA ≤
    parabolicLevi TwistTag.E6.tag E setA).trans (parabolicLevi_le_adjointGroup _ _ _)

theorem subsystemGroup_le_parabolicLevi'
    :
    subsystemGroup TwistTag.E6.tag E setA ≤ parabolicLevi TwistTag.E6.tag E setA :=
  le_sup_right

theorem rootTorusSL2_conj_pinnedX_map
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E)
    (a : kˣ) (c : k) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom a) *
        pinnedX TwistTag.E6.tag E e6HighestRoot (ι c) *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom a))⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot (ι ((a : k) ^ 2 * c)) := by
  rw [rootTorusSL2_conj_pinnedX h2, map_mul, map_pow]
  rfl

theorem twistHom_pinnedX_theta
    (h2 : (2 : E) = 0) (σ : E →+* E) (t : Bool) (c : E) :
    twistHom TwistTag.E6 E σ
        (pinnedX TwistTag.E6.tag E (if t then e6HighestRoot else -e6HighestRoot) c) =
      pinnedX TwistTag.E6.tag E (if t then e6HighestRoot else -e6HighestRoot) (σ c) := by
  rw [twistHom_apply, units_map_entrywiseHom_pinnedX']
  exact diagramMap_conj_pinnedX_theta h2 t (σ c)

section Twisted

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem two_eq_zero_of_card_sq {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    (2 : K) = 0 :=
  two_eq_zero_of_card (n := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])

theorem fixed_algebraMap [Finite k] {σ : K →+* K} (hσ : ∀ c, σ c = c ^ Nat.card k) (a : k) :
    σ (algebraMap k K a) = algebraMap k K a := by
  have : Fintype k := Fintype.ofFinite k
  rw [hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem thetaRankOneGroup_le_graphFixedRootGroup
    [Finite k] (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ Nat.card k) :
    thetaRankOneGroup (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  have hfix : ∀ (t : Bool) (a : k), pinnedX TwistTag.E6.tag K
      (if t then e6HighestRoot else -e6HighestRoot) (algebraMap k K a) ∈
        twistedFixedGroup TwistTag.E6 K σ := fun t a =>
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).2
      ⟨rootSpan_le_adjointGroup K _ (pinnedX_mem_rootSpan (S := {_}) rfl _), by
        rw [twistHom_pinnedX_theta h2, fixed_algebraMap hσ]⟩
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨a, rfl⟩
    refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact pinnedX_e6HighestRoot_mem_posUnipotent _
    · exact hfix true a
  · rintro _ ⟨a, rfl⟩
    refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ height α < 0})
        ⟨IsRoot.neg isRoot_e6HighestRoot, by decide⟩ _
    · exact hfix false a

theorem mem_thetaTorus_id {g : ModGL TwistTag.E6.tag K} :
    g ∈ thetaTorus (RingHom.id K) ↔ ∃ c : Kˣ, thetaTorusHom K c = g :=
  Iff.rfl

variable [Finite k] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] {f : ℕ} {σ : K →+* K}

theorem subsystemGroup_inf_eq_map_realize
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (h2 : (2 : K) = 0) :
    subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        (unitarySL σ).map (realize h2) ∧
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ =
        (unitarySL σ).map (realize h2) ∧
      (unitarySL σ).map (realize h2) ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hΓ : (unitarySL σ).map (realize h2) ≤
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
    rintro _ ⟨B, hB, rfl⟩
    have hL : realize h2 B ∈ subsystemGroup TwistTag.E6.tag K setA := by
      rw [← range_realize h2]
      exact ⟨B, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hL, (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).2
      ⟨subsystemGroup_le_adjointGroup hL, ?_⟩⟩
    rw [twistHom_realize, mem_unitarySL_iff_unitaryTwist.1 hB]
  have : Group.IsPerfect (unitarySL σ) := isPerfect_unitarySL hK hσ
  have hC : (unitarySL σ).map (realize h2) ≤ graphFixedRootGroup TwistTag.E6 K σ := by
    have hΓ' := hΓ.trans inf_le_right
    calc (unitarySL σ).map (realize h2) = (⁅unitarySL σ, unitarySL σ⁆).map (realize h2) := by
          rw [Subgroup.commutator_eq_self]
      _ = ⁅(unitarySL σ).map (realize h2), (unitarySL σ).map (realize h2)⁆ :=
          Subgroup.map_commutator _ _ _
      _ ≤ ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ :=
          Subgroup.commutator_mono hΓ' hΓ'
      _ ≤ graphFixedRootGroup TwistTag.E6 K σ := commutator_twistedFixedGroup_le hsurj
  have hlift : subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ ≤
      (unitarySL σ).map (realize h2) := by
    intro g hg
    obtain ⟨hgL, hgΓ⟩ := Subgroup.mem_inf.1 hg
    rw [← range_realize h2] at hgL
    obtain ⟨B, rfl⟩ := hgL
    obtain ⟨B', hB', he⟩ := exists_mem_unitarySL_of_twistHom h2 hσσ B
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1 hgΓ).2
    exact ⟨B', hB', he⟩
  refine ⟨le_antisymm ((inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)).trans hlift)
    (le_inf (hΓ.trans inf_le_left) hC), le_antisymm hlift hΓ, hC⟩

theorem parabolicLevi_inf_le
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (h2 : (2 : K) = 0) :
    parabolicLevi TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ ≤
      (unitarySL σ).map (realize h2) ⊔ thetaTorus (algebraMap k K) := by
  have hσk : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
  intro m hm
  obtain ⟨hmM, hmΓ⟩ := Subgroup.mem_inf.1 hm
  rw [parabolicLevi_eq_subsystemGroup_sup (exists_sq_eq_of_two h2)] at hmM
  have huniq := existsUnique_mul_of_commute (subsystemGroup_inf_thetaTorus h2 (RingHom.id K))
    (fun l hl h hh => commute_of_mem_thetaTorus h2 _ hl hh)
  obtain ⟨⟨l, h⟩, ⟨hl, hh, rfl⟩, hu⟩ := huniq m hmM
  obtain ⟨c, rfl⟩ := mem_thetaTorus_id.1 hh
  have hFm := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1 hmΓ).2
  rw [map_mul] at hFm
  have hFl : twistHom TwistTag.E6 K σ l ∈ subsystemGroup TwistTag.E6.tag K setA := by
    rw [← range_realize h2] at hl ⊢
    obtain ⟨B, rfl⟩ := hl
    exact ⟨unitaryTwist σ B, (twistHom_realize σ h2 B).symm⟩
  have hFh : twistHom TwistTag.E6 K σ (thetaTorusHom K c) =
      thetaTorusHom K (Units.map σ.toMonoidHom c) := by
    rw [thetaTorusHom_eq_thetaSL2, twistHom_thetaSL2 h2, map_HSL, thetaTorusHom_eq_thetaSL2]
  have he := hu (twistHom TwistTag.E6 K σ l, twistHom TwistTag.E6 K σ (thetaTorusHom K c))
    ⟨hFl, mem_thetaTorus_id.2 ⟨_, hFh.symm⟩, hFm.symm⟩
  obtain ⟨hl1, hh1⟩ := Prod.ext_iff.1 he
  simp only at hl1 hh1
  rw [hFh] at hh1
  have hc : σ (c : K) = c := by
    have := congrArg (fun u : Kˣ => (u : K)) (thetaTorusHom_injective h2 hh1)
    simpa using this
  obtain ⟨a, ha⟩ := mem_range_algebraMap_of_pow_card_eq (k := k) (by rw [← hσk, hc])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact c.ne_zero ha.symm
  have hcu : Units.map (algebraMap k K).toMonoidHom (Units.mk0 a ha0) = c :=
    Units.ext (by rw [Units.coe_map, Units.val_mk0]; exact ha)
  have hlΓ : l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ :=
    Subgroup.mem_inf.2 ⟨hl, (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).2
      ⟨subsystemGroup_le_adjointGroup hl, hl1⟩⟩
  rw [(subsystemGroup_inf_eq_map_realize hK hσ h2).2.1] at hlΓ
  exact mul_mem (Subgroup.mem_sup_left hlΓ)
    (Subgroup.mem_sup_right ⟨Units.mk0 a ha0, by rw [MonoidHom.comp_apply, hcu]⟩)

end Twisted

theorem sup_eq_of_factorization {G : Type*} [Group G] {Q M P : Subgroup G} (hQ : Q ≤ P)
    (hM : M ≤ P) (h : ∀ g ∈ P, ∃! qm : G × G, qm.1 ∈ Q ∧ qm.2 ∈ M ∧ g = qm.1 * qm.2) :
    Q ⊔ M = P := by
  refine le_antisymm (sup_le hQ hM) fun g hg => ?_
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := h g hg
  exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hm)

theorem ker_realize_comp_subtype
    {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)]
    [CharP K 2] {f : ℕ}
    {σ : K →+* K} (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h2 : (2 : K) = 0) :
    ((realize h2).comp (unitarySL σ).subtype).ker = Subgroup.center (unitarySL σ) := by
  ext B
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker,
    mem_ker_realize, mem_center_unitarySL_iff hK hσ]
  constructor
  · rintro ⟨l, -, hl⟩
    exact ⟨l, hl⟩
  · rintro ⟨l, hl⟩
    refine ⟨l, pow_three_eq_one_of_pow_six h2 ?_, hl⟩
    have hdet := (B : Matrix.SpecialLinearGroup (Fin 6) K).2
    rw [hl, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet

open CFSG.Assembly.LowTwoRank Matrix in
theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_finite_Levi_intersections
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (Function.Injective (thetaSL2 k) ∧
      (thetaSL2 k).range = thetaRankOneGroup (RingHom.id k) ∧
      (∀ c : k, thetaSL2 k (uSL c) = pinnedX TwistTag.E6.tag k e6HighestRoot c) ∧
      (∀ c : k, thetaSL2 k (vSL c) = pinnedX TwistTag.E6.tag k (-e6HighestRoot) c) ∧
      (∀ a : kˣ, thetaSL2 k (HSL a) = rootTorusSL2 TwistTag.E6.tag k e6HighestRoot a) ∧
      (∀ g, g ∈ thetaRootGroup (RingHom.id k) ↔
        ∃ c : k, pinnedX TwistTag.E6.tag k e6HighestRoot c = g) ∧
      (∀ g, g ∈ thetaNegRootGroup (RingHom.id k) ↔
        ∃ c : k, pinnedX TwistTag.E6.tag k (-e6HighestRoot) c = g) ∧
      (∀ g, g ∈ thetaTorus (RingHom.id k) ↔
        ∃ a : kˣ, rootTorusSL2 TwistTag.E6.tag k e6HighestRoot a = g) ∧
      subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
        Subgroup.centralizer (thetaRankOneGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ∧
      (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
          thetaTorus (RingHom.id k) =
        parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
      (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊓
          thetaTorus (RingHom.id k) = ⊥ ∧
      (∀ l ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
        ∀ h ∈ thetaTorus (RingHom.id k), l * h = h * l) ∧
      (∀ m ∈ parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
        ∃! p : ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k,
          p.1 ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          p.2 ∈ thetaTorus (RingHom.id k) ∧ m = p.1 * p.2) ∧
      Function.Injective (rootTorusSL2 TwistTag.E6.tag k e6HighestRoot) ∧
      parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
        parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
      parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
        parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
      ((parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k).subgroupOf
        (parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k)).Normal ∧
      (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊓
          (parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) = ⊥ ∧
      (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
          (parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) =
        parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
      (∀ g ∈ parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
        ∃! qm : ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k,
          qm.1 ∈ parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          qm.2 ∈ parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          g = qm.1 * qm.2) ∧
      subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        subsystemGroup TwistTag.E6.tag k setA ∧
      (realize (two_eq_zero_of_card hf hk)).range = subsystemGroup TwistTag.E6.tag k setA ∧
      (∀ B : Matrix.SpecialLinearGroup (Fin 6) k, B ∈ (realize (two_eq_zero_of_card hf hk)).ker ↔
        ∃ l : k, l ^ 3 = 1 ∧ (B : Matrix (Fin 6) (Fin 6) k) = Matrix.scalar (Fin 6) l) ∧
      (∃ e : Matrix.SpecialLinearGroup (Fin 6) k ⧸ (realize (two_eq_zero_of_card hf hk)).ker ≃*
          ↥(subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k),
        ∀ B : Matrix.SpecialLinearGroup (Fin 6) k,
          (e (QuotientGroup.mk B) : ModGL TwistTag.E6.tag k) =
            realize (two_eq_zero_of_card hf hk) B) ∧
      parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        parabolicRadical TwistTag.E6.tag k setA ∧
      (∀ x ∈ thetaRankOneGroup (RingHom.id k),
        diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹ = x) ∧
      (∀ Y ∈ ({parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          thetaTorus (RingHom.id k), thetaRankOneGroup (RingHom.id k),
          thetaRootGroup (RingHom.id k), thetaNegRootGroup (RingHom.id k),
          parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k} :
            Set (Subgroup (ModGL TwistTag.E6.tag k))),
        Y.map (MulAut.conj (diagramMap TwistTag.E6 k)).toMonoidHom = Y) ∧
      ∀ (a : kˣ) (c : k), rootTorusSL2 TwistTag.E6.tag k e6HighestRoot a *
          pinnedX TwistTag.E6.tag k e6HighestRoot c *
          (rootTorusSL2 TwistTag.E6.tag k e6HighestRoot a)⁻¹ =
        pinnedX TwistTag.E6.tag k e6HighestRoot ((a : k) ^ 2 * c)) ∧
    (Function.Injective ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))) ∧
      ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))).range =
        thetaRankOneGroup (algebraMap k K) ∧
      (∀ c : k, (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (uSL c) =
        pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c)) ∧
      (∀ c : k, (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (vSL c) =
        pinnedX TwistTag.E6.tag K (-e6HighestRoot) (algebraMap k K c)) ∧
      (∀ a : kˣ, (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (HSL a) =
        rootTorusSL2 TwistTag.E6.tag K e6HighestRoot (Units.map (algebraMap k K).toMonoidHom a)) ∧
      (∀ g, g ∈ thetaRootGroup (algebraMap k K) ↔
        ∃ c : k, pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) = g) ∧
      (∀ g, g ∈ thetaNegRootGroup (algebraMap k K) ↔
        ∃ c : k, pinnedX TwistTag.E6.tag K (-e6HighestRoot) (algebraMap k K c) = g) ∧
      (∀ g, g ∈ thetaTorus (algebraMap k K) ↔ ∃ a : kˣ,
        rootTorusSL2 TwistTag.E6.tag K e6HighestRoot (Units.map (algebraMap k K).toMonoidHom a) =
          g) ∧
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
        Subgroup.centralizer
          (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ∧
      (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
          thetaTorus (algebraMap k K) =
        parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊓
          thetaTorus (algebraMap k K) = ⊥ ∧
      (∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∀ h ∈ thetaTorus (algebraMap k K), l * h = h * l) ∧
      (∀ m ∈ parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∃! p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K,
          p.1 ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          p.2 ∈ thetaTorus (algebraMap k K) ∧ m = p.1 * p.2) ∧
      Function.Injective (fun a : kˣ => rootTorusSL2 TwistTag.E6.tag K e6HighestRoot
        (Units.map (algebraMap k K).toMonoidHom a)) ∧
      parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
        parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
        parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      ((parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
        (parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ)).Normal ∧
      (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊓
          (parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) = ⊥ ∧
      (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
          (parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) =
        parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      (∀ g ∈ parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∃! qm : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K,
          qm.1 ∈ parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          qm.2 ∈ parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          g = qm.1 * qm.2) ∧
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ ∧
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        (unitarySL σ).map (realize (two_eq_zero_of_card_sq hf hK)) ∧
      (∀ B : Matrix.SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ ↔
        ((B : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K * (B : Matrix (Fin 6) (Fin 6) K) =
          antiId K) ∧
      ((realize (two_eq_zero_of_card_sq hf hK)).comp (unitarySL σ).subtype).ker =
        Subgroup.center (unitarySL σ) ∧
      (∀ B : unitarySL σ, B ∈ Subgroup.center (unitarySL σ) ↔
        ∃ l : K, ((B : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          Matrix.scalar (Fin 6) l) ∧
      (∃ e : unitarySL σ ⧸ Subgroup.center (unitarySL σ) ≃*
          ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ),
        ∀ B : unitarySL σ, (e (QuotientGroup.mk B) : ModGL TwistTag.E6.tag K) =
          realize (two_eq_zero_of_card_sq hf hK) B) ∧
      StatedClassicalModel
        ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) .PSU 6 2 f ∧
      parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        parabolicLevi TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ ∧
      (∀ B ∈ unitarySL σ, Matrix.SpecialLinearGroup.map σ B ∈ unitarySL σ ∧
        diagramMap TwistTag.E6 K * realize (two_eq_zero_of_card_sq hf hK) B *
            (diagramMap TwistTag.E6 K)⁻¹ =
          realize (two_eq_zero_of_card_sq hf hK) (Matrix.SpecialLinearGroup.map σ B)) ∧
      parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        parabolicRadical TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ ∧
      (∀ x ∈ thetaRankOneGroup (algebraMap k K),
        diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹ = x) ∧
      (∀ Y ∈ ({parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
          parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
          subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
          thetaTorus (algebraMap k K), thetaRankOneGroup (algebraMap k K),
          thetaRootGroup (algebraMap k K), thetaNegRootGroup (algebraMap k K),
          parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ} :
            Set (Subgroup (ModGL TwistTag.E6.tag K))),
        Y.map (MulAut.conj (diagramMap TwistTag.E6 K)).toMonoidHom = Y) ∧
      ∀ (a : kˣ) (c : k),
        rootTorusSL2 TwistTag.E6.tag K e6HighestRoot (Units.map (algebraMap k K).toMonoidHom a) *
            pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) *
            (rootTorusSL2 TwistTag.E6.tag K e6HighestRoot
              (Units.map (algebraMap k K).toMonoidHom a))⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K ((a : k) ^ 2 * c))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  refine ⟨?_, ?_⟩
  ·
    have hLG : subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        subsystemGroup TwistTag.E6.tag k setA := inf_eq_left.2 subsystemGroup_le_adjointGroup
    have hMG : parabolicLevi TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        parabolicLevi TwistTag.E6.tag k setA :=
      inf_eq_left.2 (parabolicLevi_le_adjointGroup _ _ _)
    have hQG : parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        parabolicRadical TwistTag.E6.tag k setA := inf_eq_left.2 (rootSpan_le_adjointGroup k _)
    have hPG : parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
        parabolicSubgroup TwistTag.E6.tag k setA :=
      inf_eq_left.2 (parabolicSubgroup_le_adjointGroup _ _ _)
    rw [hLG, hMG, hQG, hPG]
    have hMsup := parabolicLevi_eq_subsystemGroup_sup (exists_sq_eq_of_two hk2)
    have hinf := subsystemGroup_inf_thetaTorus hk2 (RingHom.id k)
    have hcomm : ∀ l ∈ subsystemGroup TwistTag.E6.tag k setA,
        ∀ h ∈ thetaTorus (RingHom.id k), l * h = h * l :=
      fun l hl h hh => commute_of_mem_thetaTorus hk2 _ hl hh
    have hR := parabolic_root_radical_Levi_factors TwistTag.E6.tag k setA
    have hXr : thetaRankOneGroup (RingHom.id k) ≤ (thetaSL2 k).range :=
      thetaRankOneGroup_le_range hk2 _
    have hP := diagram_parabolic_maps (E := k)
    refine ⟨thetaSL2_injective hk2, ?_, thetaSL2_uSL hk2, thetaSL2_vSL hk2, fun a => rfl,
      fun g => mem_thetaRootGroup _, fun g => mem_thetaNegRootGroup _, fun g => mem_thetaTorus _,
      (subsystemGroup_le_centralizer_thetaSL2 hk2).trans (Subgroup.centralizer_le hXr),
      hMsup.symm, hinf, hcomm, fun m hm => existsUnique_mul_of_commute hinf hcomm m (hMsup ▸ hm),
      fun a b h => thetaTorusHom_injective hk2 (by rwa [thetaTorusHom_apply, thetaTorusHom_apply]),
      hR.1, hR.2.2.2.1, hR.2.1, hR.2.2.2.2.1, hR.2.2.2.2.2.1, hR.2.2.2.2.2.2.1,
      rfl, range_realize hk2, mem_ker_realize hk2, ⟨realizeQuotient hk2, fun B => rfl⟩, rfl,
      fun x hx => ?_, ?_,
      fun a c => rootTorusSL2_conj_pinnedX hk2 a c⟩
    · rw [range_thetaSL2 hk2, thetaRankOneGroup, thetaRootGroup, thetaNegRootGroup,
        ← Subgroup.closure_union]
      rfl
    · obtain ⟨B, rfl⟩ := hXr hx
      exact diagramMap_conj_thetaSL2 hk2 B
    · rintro Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hP.1
      · exact hP.2.1
      · exact map_conj_eq_of_forall diagramMap_E6_mul_self fun y hy =>
          diagramMap_conj_mem_subsystemGroup hk2 hy
      · exact map_conj_eq_of_le_range hk2 (thetaTorus_le_range_thetaSL2 _)
      · exact map_conj_eq_of_le_range hk2 hXr
      · exact map_conj_eq_of_le_range hk2 (le_sup_left.trans hXr)
      · exact map_conj_eq_of_le_range hk2 (le_sup_right.trans hXr)
      · exact hP.2.2
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
    have hσσ : ∀ c, σ (σ c) = c := fun c => by
      rw [hσ, hσ]
      exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
    have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
    set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩ with hσEdef
    have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
    have hσk : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
    obtain ⟨hLC, hLΓ, hUC⟩ := subsystemGroup_inf_eq_map_realize hK hσ hK2
    have hXC := thetaRankOneGroup_le_graphFixedRootGroup (k := k) hK2 hσk
    have hXr : thetaRankOneGroup (algebraMap k K) ≤ (thetaSL2 K).range :=
      thetaRankOneGroup_le_range hK2 _
    have hHC : thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
      (thetaTorus_le_thetaRankOneGroup hK2 _).trans hXC
    have hUL : (unitarySL σ).map (realize hK2) ≤ subsystemGroup TwistTag.E6.tag K setA := by
      rw [← hLC]
      exact inf_le_left
    have hM1 : parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        (unitarySL σ).map (realize hK2) ⊔ thetaTorus (algebraMap k K) :=
      le_antisymm ((inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)).trans
          (parabolicLevi_inf_le hk hK hσ hK2))
        (sup_le (le_inf (hUL.trans subsystemGroup_le_parabolicLevi') hUC)
          (le_inf ((thetaTorus_le_torusGroup _).trans le_sup_left) hHC))
    have hM2 : parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        parabolicLevi TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ :=
      le_antisymm (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _))
        (hM1 ▸ parabolicLevi_inf_le hk hK hσ hK2)
    have hinf : (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊓
        thetaTorus (algebraMap k K) = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans
        (subsystemGroup_inf_thetaTorus hK2 _).le)
    have hcomm : ∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓
        graphFixedRootGroup TwistTag.E6 K σ, ∀ h ∈ thetaTorus (algebraMap k K), l * h = h * l :=
      fun l hl h hh => commute_of_mem_thetaTorus hK2 _ (Subgroup.mem_inf.1 hl).1 hh
    have hLM : (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
        thetaTorus (algebraMap k K) =
          parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      rw [hLC, hM1]
    have hD := diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σE foldedSetA
    rw [hσE] at hD
    have hQ0 : graphFixedParabolicRadical TwistTag.E6 K σ foldedSetA =
        parabolicRadical TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
      rw [graphFixedParabolicRadical, orbitUnion_foldedSetA]
    have hL0 : graphFixedParabolicLevi TwistTag.E6 K σ foldedSetA =
        parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      rw [graphFixedParabolicLevi, orbitUnion_foldedSetA]
    have hP1 : graphFixedParabolic TwistTag.E6 K σ foldedSetA =
        parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      rw [← parabolicSubgroup_inf_graphFixedRootGroup hsurj foldedSetA, orbitUnion_foldedSetA]
    have hQeq : parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        parabolicRadical TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
      refine le_antisymm (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)) (le_inf inf_le_left ?_)
      rw [← hQ0]
      exact graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K _ foldedSetA
    rw [hQ0, hL0, hP1, orbitUnion_foldedSetA, ← hQeq] at hD
    obtain ⟨-, -, -, -, -, -, hD7, -, hD9, hD10, hD11, hD12, -⟩ := hD
    have hE : ∃ e : unitarySL σ ⧸ Subgroup.center (unitarySL σ) ≃*
        ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ),
          ∀ B : unitarySL σ, (e (QuotientGroup.mk B) : ModGL TwistTag.E6.tag K) =
            realize hK2 B := by
      have hrange : ((realize hK2).comp (unitarySL σ).subtype).range =
          subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hLC]
      exact ⟨(QuotientGroup.quotientMulEquivOfEq (ker_realize_comp_subtype hK hσ hK2).symm).trans
        ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange)),
        fun B => rfl⟩
    have hPSU : StatedClassicalModel
        ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ)
          .PSU 6 2 f := by
      obtain ⟨e, -⟩ := hE
      obtain ⟨hadm, F, i1, i2, hF, ⟨iso⟩⟩ :=
        CFSG.LieType.Universal.Unitary.statedClassicalModel_center_quotient (F := K) (p := 2)
          (f := f) (n := 6) ⟨Nat.prime_two, hf, by norm_num, by simp⟩ hK
      exact ⟨hadm, F, i1, i2, hF, ⟨(e.symm.trans (QuotientGroup.congr _ _ (unitarySLEquiv hσ)
        (CFSG.LieType.Universal.Unitary.map_center_mulEquiv _))).trans iso⟩⟩
    have hC0map := map_conj_diagramMap_graphFixedRootGroup σE hσE hσσ
    have hPK := diagram_parabolic_maps (E := K)
    have hinter : ∀ {A : Subgroup (ModGL TwistTag.E6.tag K)},
        A.map (MulAut.conj (diagramMap TwistTag.E6 K)).toMonoidHom = A →
          (A ⊓ graphFixedRootGroup TwistTag.E6 K σ).map
            (MulAut.conj (diagramMap TwistTag.E6 K)).toMonoidHom =
            A ⊓ graphFixedRootGroup TwistTag.E6 K σ := fun hA =>
      map_conj_eq_of_forall diagramMap_E6_mul_self fun y hy =>
        Subgroup.mem_inf.2 ⟨conj_mem_of_map_eq hA hy.1, conj_mem_of_map_eq hC0map hy.2⟩
    refine ⟨injective_thetaSL2_comp_map hK2 _, (thetaRankOneGroup_eq_range hK2 _).symm,
      fun c => ?_, fun c => ?_, thetaSL2_comp_map_HSL _, fun g => mem_thetaRootGroup _,
      fun g => mem_thetaNegRootGroup _, fun g => mem_thetaTorus _,
      (inf_le_left.trans (subsystemGroup_le_centralizer_thetaSL2 hK2)).trans
        (Subgroup.centralizer_le hXr),
      hLM, hinf, hcomm, fun m hm => existsUnique_mul_of_commute hinf hcomm m (hLM ▸ hm),
      fun a b h => ?_, hD9, hD11, hD10,
      eq_bot_iff.2 ((inf_le_inf_left _ (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _))).trans
        hD7.le),
      sup_eq_of_factorization hD9 hD11 hD12, hD12, hLC.trans hLΓ.symm, hLC,
      fun B => mem_unitarySL_iff, ker_realize_comp_subtype hK hσ hK2,
      mem_center_unitarySL_iff hK hσ, hE, hPSU, hM2,
      fun B hB => ⟨map_mem_unitarySL hσσ hB, diagramMap_conj_realize_of_mem_unitarySL hK2 hB⟩,
      hQeq, fun x hx => ?_, ?_, fun a c => rootTorusSL2_conj_pinnedX_map hK2 _ a c⟩
    · rw [MonoidHom.comp_apply, map_uSL, thetaSL2_uSL hK2]
    · rw [MonoidHom.comp_apply, map_vSL, thetaSL2_vSL hK2]
    · have h' : thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom a) =
          thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom b) := by
        rwa [thetaTorusHom_apply, thetaTorusHom_apply]
      have h'' := congrArg (fun u : Kˣ => (u : K)) (thetaTorusHom_injective hK2 h')
      simp only [Units.coe_map] at h''
      exact Units.ext ((algebraMap k K).injective h'')
    · obtain ⟨B, rfl⟩ := hXr hx
      exact diagramMap_conj_thetaSL2 hK2 B
    · rintro Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hinter hPK.1
      · exact hinter hPK.2.1
      · exact hinter (map_conj_eq_of_forall diagramMap_E6_mul_self fun y hy =>
          diagramMap_conj_mem_subsystemGroup hK2 hy)
      · exact map_conj_eq_of_le_range hK2 ((thetaTorus_le_thetaRankOneGroup hK2 _).trans hXr)
      · exact map_conj_eq_of_le_range hK2 hXr
      · exact map_conj_eq_of_le_range hK2 (le_sup_left.trans hXr)
      · exact map_conj_eq_of_le_range hK2 (le_sup_right.trans hXr)
      · exact hinter hPK.2.2

end CFSG.LieType.Chevalley.E6GraphLevi
