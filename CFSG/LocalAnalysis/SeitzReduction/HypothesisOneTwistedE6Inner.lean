module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K]

theorem odd_card_units_of_card {f : ℕ} (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) :
    Odd (Nat.card Kˣ) := by
  rw [Nat.card_units, hK]
  have h2 : (2 ^ f) ^ 2 = 2 * (2 ^ (2 * f - 1)) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  have h1 : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
  rw [h2]
  exact ⟨2 ^ (2 * f - 1) - 1, by omega⟩


theorem pinnedX_mem_graphFixedPosUnipotent [CharP K 2] {t : TwistTag} (σ : K →+* K)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (hαp : 0 < height α)
    (hρ : permLattice t.perm α = α) {c : K} (hc : σ c = c) :
    pinnedX t.tag K α c ∈ graphFixedPosUnipotent t K σ := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem ⟨hα, hαp⟩
    (mem_rootSubgroup.2 ⟨c, rfl⟩)), (mem_twistedFixedGroup_iff_twistHom t K σ).2
    ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  rw [twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ hα, hρ, hc]

theorem pinnedX_e6HighestRoot_mem_graphFixedRootGroup [CharP K 2] (σ : K →+* K) (c : K)
    (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (pinnedX_mem_graphFixedPosUnipotent σ
    isRoot_e6HighestRoot (by rw [height_e6HighestRoot]; norm_num) permLattice_e6HighestRoot hc)

theorem torus_mem_oddCentralizer {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbr : rootChar b e6HighestRoot = 1) :
    (⟨_, hb⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * t = t * ⟨_, hb⟩ ∧
      Odd (orderOf (⟨_, hb⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  refine ⟨Subtype.ext ?_, ?_⟩
  · simp only [Subgroup.coe_mul, ht]
    have e := rootDiagUnit_conj_pinnedX b isRoot_e6HighestRoot (1 : K)
    rw [hbr, Units.val_one, one_mul] at e
    exact mul_inv_eq_iff_eq_mul.1 e
  · rw [← Subgroup.orderOf_coe]
    exact odd_orderOf_rootDiagUnit_of_odd (odd_card_units_of_card hf hK) b

theorem torus_commutator_mem_closure_odd {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbr : rootChar b e6HighestRoot = 1) {v : ModGL TwistTag.E6.tag K}
    (hv : v ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ * v⁻¹) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  set h' : graphFixedRootGroup TwistTag.E6 K σ.toRingHom := ⟨_, hb⟩
  set v' : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨v, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hv⟩
  obtain ⟨hh, hho⟩ := torus_mem_oddCentralizer hf hK ht hb hbr
  have hvt : v' * t = t * v' := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ht, v']
    exact (commute_e6HighestRoot_of_mem_posUnipotent K (Subgroup.mem_inf.1 hv).1 1).eq
  have e : x = h' * (v' * h'⁻¹ * v'⁻¹) := by
    refine Subtype.ext ?_
    rw [hx]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h', v']
    group
  rw [e]
  exact mul_mem (subset_closure ⟨hh, hho⟩) (subset_closure (conj_inv_mem_oddCentralizer hh hho hvt))

theorem orbit_mem_closure_odd [CharP K 2] {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)} (hO : O ∈ TwistTag.E6.diagramRootOrbits)
    (hOpos : ∀ α ∈ O, 0 < height α) (hOr : e6HighestRoot ∉ O)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K (O : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ.toRingHom) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  obtain ⟨α, hα, rfl⟩ := hO
  have hαp := hOpos α (TwistTag.E6.self_mem_diagramOrbit α)
  have hαr : α ≠ e6HighestRoot := fun h => hOr (h ▸ TwistTag.E6.self_mem_diagramOrbit α)
  obtain ⟨b, hbC, hbr, hbα, hbρα⟩ := exists_twistedE6Torus hf hK hσ hα hαp hαr
  have hbO : ∀ β ∈ TwistTag.E6.diagramOrbit α, rootChar b β ≠ 1 := by
    intro β hβ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hβ
    rw [Finset.mem_range, show TwistTag.E6.order = 2 from rfl] at hk
    interval_cases k
    · exact hbα
    · rw [pow_one]
      exact hbρα
  have hOroot : ∀ β ∈ TwistTag.E6.diagramOrbit α, IsRoot TwistTag.E6.tag β ∧ 0 < height β :=
    fun β hβ => ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hβ, hOpos β hβ⟩
  have hOcl : ∀ β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)), ∀ a c : ℕ,
        1 ≤ a → 1 ≤ c → IsRoot TwistTag.E6.tag (a • β + c • γ) →
          a • β + c • γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) :=
    fun β hβ γ hγ a c ha hc hr =>
      absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα hβ hγ ha hc)
  set A := rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
    twistedFixedGroup TwistTag.E6 K σ.toRingHom with hA
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hbΓ : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ hbC
  have hnorm : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈
      A := by
    intro v hv
    obtain ⟨hvO, hvΓ⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hbΓ hvΓ) (inv_mem hbΓ)⟩
    have hmap := map_rootSpan_of_forall
      (f := (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom)
      (S := (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)))
      fun β hβ => map_conj_rootDiagUnit_rootSubgroup b (hOroot β hβ).1
    rw [← hmap]
    exact ⟨v, hvO, rfl⟩
  have hfree : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      v → v = 1 := by
    intro v hv hfix
    have h1 := mem_rootSpan_of_rootDiagUnit_conj_eq (B := {b}) hOroot hOcl
      (Subgroup.mem_inf.1 hv).1 fun b' hb' => by
        rw [Set.mem_singleton_iff.1 hb']
        exact hfix
    have hempty : {β | β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∧
        ∀ b' ∈ ({b} : Set (Fin TwistTag.E6.tag.rank → Kˣ)), rootChar b' β = 1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun β hβ => hbO β hβ.1 (hβ.2 b rfl)
    rw [hempty] at h1
    have hbot : rootSpan TwistTag.E6.tag K (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ :=
      iSup₂_eq_bot.2 fun β hβ => absurd hβ (Set.notMem_empty β)
    rw [hbot] at h1
    exact Subgroup.mem_bot.1 h1
  obtain ⟨v, hvA, hxv⟩ := exists_eq_mul_conj_inv_of_fixedPointFree hnorm hfree hx
  have hvU : v ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨rootSpan_mono (T := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
      (fun β hβ => hOroot β hβ) (Subgroup.mem_inf.1 hvA).1, (Subgroup.mem_inf.1 hvA).2⟩
  exact torus_commutator_mem_closure_odd (by omega) hK ht hbC hbr hvU hxv

@[expose] def e6HighRootSubTwo : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)

@[expose] def e6NodeTwo : Fin TwistTag.E6.tag.rank → ℤ :=
  Pi.single ⟨1, by decide⟩ 1

theorem isRoot_e6HighRootSubTwo : IsRoot TwistTag.E6.tag e6HighRootSubTwo :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨68, by decide, by decide⟩

theorem highRoot_mem_closure_odd [CharP K 2] {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K {e6HighestRoot} ⊓
      twistedFixedGroup TwistTag.E6 K σ.toRingHom) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hxr, hxΓ⟩ := Subgroup.mem_inf.1 hx
  rw [CFSG.LieType.Chevalley.rootSpan_singleton] at hxr
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hxr
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxΓ).2
  rw [← hc, twistHom_pinnedX_eq_of_charTwo h2 _ isRoot_e6HighestRoot,
    permLattice_e6HighestRoot] at hF
  have hσc : σ.toRingHom c = c := pinnedX_injective _ _ _ hF
  set β := e6HighRootSubTwo with hβdef
  set e := e6NodeTwo with hedef
  have hβ : IsRoot TwistTag.E6.tag β := isRoot_e6HighRootSubTwo
  have he : IsRoot TwistTag.E6.tag e := isRoot_single _ _
  have hsum : β + e = e6HighestRoot := by decide
  have hβe : β ≠ e := by decide
  have hβe' : β ≠ -e := by decide
  have hβp : 0 < height β := by decide
  have hep : 0 < height e := by decide
  have hβρ : permLattice TwistTag.E6.perm β = β := by decide
  have heρ : permLattice TwistTag.E6.perm e = e := by decide
  have hβr : β ≠ e6HighestRoot := by decide
  have her : e ≠ e6HighestRoot := by decide
  obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag
    (Or.inr (Or.inl rfl)) hβ he hβe hβe').1 (hsum.symm ▸ isRoot_e6HighestRoot)
  have hε1 : (commConst TwistTag.E6.tag β e (1, 1) : K) = 1 := by
    refine eq_one_of_mul_self_eq_one_of_two_eq_zero h2 ?_
    rcases hε with h | h <;> simp [h]
  have e1 : pinnedX TwistTag.E6.tag K e6HighestRoot c =
      ⁅pinnedX TwistTag.E6.tag K β 1, pinnedX TwistTag.E6.tag K e c⁆ := by
    rw [hcomm K 1 c, hsum, hε1, one_mul, one_mul]
  have hmemβ := pinnedX_mem_graphFixedPosUnipotent σ.toRingHom hβ hβp hβρ (map_one σ.toRingHom)
  have hmeme := pinnedX_mem_graphFixedPosUnipotent σ.toRingHom he hep heρ hσc
  set y₁ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hmemβ⟩
  set y₂ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hmeme⟩
  have hy : ∀ {α : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag α → 0 < height α →
      permLattice TwistTag.E6.perm α = α → α ≠ e6HighestRoot →
      ∀ {y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom} {d : K},
        (y : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K α d →
        (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom →
        y ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
          c * t = t * c ∧ Odd (orderOf c)} := by
    intro α hα hαp hαρ hαr y d hyd hyΓ
    have hO : TwistTag.E6.diagramOrbit α = {α} := diagramOrbit_eq_singleton_of_fixed hαρ
    refine orbit_mem_closure_odd hf hK hσ ht ⟨α, hα, rfl⟩
      (fun β hβ => by rw [hO, Finset.mem_singleton] at hβ; rw [hβ]; exact hαp)
      (by rw [hO, Finset.mem_singleton]; exact fun h => hαr h.symm) (Subgroup.mem_inf.2 ⟨?_, hyΓ⟩)
    rw [hO, Finset.coe_singleton, CFSG.LieType.Chevalley.rootSpan_singleton, hyd]
    exact mem_rootSubgroup.2 ⟨d, rfl⟩
  have hy₁ := hy hβ hβp hβρ hβr (y := y₁) rfl (Subgroup.mem_inf.1 hmemβ).2
  have hy₂ := hy he hep heρ her (y := y₂) rfl (Subgroup.mem_inf.1 hmeme).2
  have e2 : x = ⁅y₁, y₂⁆ := by
    refine Subtype.ext ?_
    rw [← hc, e1, commutatorElement_def, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, y₁, y₂]
  rw [e2, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)

theorem posRoots_twistedE6_facts :
    (∀ α ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∧
    (∀ α ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      permLattice TwistTag.E6.perm α ∈
        {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) ∧
    (∀ α ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      ∀ β ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
        ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
          a • α + b • β ∈
            {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) := by
  refine ⟨fun α hα => hα, fun α hα => ⟨hα.1.permLattice TwistTag.E6.cartan_perm,
    by rw [height_permLattice]; exact hα.2⟩, fun α hα β hβ a b ha hb hr => ⟨hr, ?_⟩⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hα.2, hβ.2]

theorem graphFixedPosUnipotent_le_closure_odd [CharP K 2] {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom) :
    u ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  set S := {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom | c * t = t * c ∧ Odd (orderOf c)}
  obtain ⟨hposS, hposρ, hposcl⟩ := posRoots_twistedE6_facts
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_posOrbits TwistTag.E6
  have hbij := bijOn_prod_graphFixed (K := K) (σ := σ.toRingHom) σ.surjective hposS hposρ hposcl
    O hO hrange
  obtain ⟨w, -, hw⟩ := hbij.surjOn hu
  suffices h : (u : ModGL TwistTag.E6.tag K) ∈
      (closure S).map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype by
    obtain ⟨y, hy, hyu⟩ := h
    rwa [show u = y from Subtype.ext hyu.symm]
  rw [← hw]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ TwistTag.E6.diagramRootOrbits ∧ (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
      {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h
  obtain ⟨hwO, hwΓ⟩ := Subgroup.mem_inf.1 (w j).2
  have hwU : (w j : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨rootSpan_mono hOj.2 hwO, hwΓ⟩
  refine ⟨⟨w j, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hwU⟩, ?_, rfl⟩
  by_cases hr : e6HighestRoot ∈ O j
  ·
    obtain ⟨α, -, hαO⟩ := hOj.1
    have hOr : O j = {e6HighestRoot} := by
      rw [← hαO] at hr ⊢
      rw [← TwistTag.E6.diagramOrbit_eq_of_mem hr,
        diagramOrbit_eq_singleton_of_fixed permLattice_e6HighestRoot]
    refine highRoot_mem_closure_odd hf hK hσ ht (Subgroup.mem_inf.2 ⟨?_, hwΓ⟩)
    have h : ∀ y : ModGL TwistTag.E6.tag K, y ∈ rootSpan TwistTag.E6.tag K (O j : Set _) →
        y ∈ rootSpan TwistTag.E6.tag K {e6HighestRoot} := by
      intro y hy
      rwa [hOr, Finset.coe_singleton] at hy
    exact h _ hwO
  · exact orbit_mem_closure_odd hf hK hσ ht hOj.1 (fun α hα => (hOj.2 hα).2) hr
      (Subgroup.mem_inf.2 ⟨hwO, hwΓ⟩)

theorem sq_eq_one_of_commute_odd [CharP K 2] {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hz : (z : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom)
    (hc : ∀ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, c * t = t * c →
      Odd (orderOf c) → z * c = c * z) :
    z ^ 2 = 1 := by
  set B : Set (Fin TwistTag.E6.tag.rank → Kˣ) := {b | rootDiagUnit TwistTag.E6.tag b ∈
    graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧ rootChar b e6HighestRoot = 1} with hB
  have hfix : ∀ b ∈ B, rootDiagUnit TwistTag.E6.tag b * (z : ModGL TwistTag.E6.tag K) *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ = z := by
    rintro b ⟨hbC, hbr⟩
    obtain ⟨hh, hho⟩ := torus_mem_oddCentralizer (by omega) hK ht hbC hbr
    have h1 := congrArg Subtype.val (hc _ hh hho)
    simp only [Subgroup.coe_mul] at h1
    rw [← h1]
    group
  obtain ⟨hposS, -, hposcl⟩ := posRoots_twistedE6_facts
  have h1 := mem_rootSpan_of_rootDiagUnit_conj_eq hposS hposcl (Subgroup.mem_inf.1 hz).1 hfix
  have hsub : {β | β ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧
      0 < height α} ∧ ∀ b ∈ B, rootChar b β = 1} ⊆ {e6HighestRoot} := by
    rintro β ⟨hβ, hβB⟩
    by_contra hne
    obtain ⟨b, hbC, hbr, hbβ, -⟩ := exists_twistedE6Torus hf hK hσ hβ.1 hβ.2
      fun h => hne (Set.mem_singleton_iff.2 h)
    exact hbβ (hβB b ⟨hbC, hbr⟩)
  have h2 := rootSpan_mono hsub h1
  rw [CFSG.LieType.Chevalley.rootSpan_singleton] at h2
  obtain ⟨c, hcz⟩ := mem_rootSubgroup.1 h2
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hcz, sq, ← pinnedX_add,
    CharTwo.add_self_eq_zero, pinnedX_zero]

theorem mem_map_radicalIn_empty_iff_fixed {t : TwistTag} {σ : K ≃+* K} {hσ : σ ^ t.order = 1}
    {u : (RootWeightDatum.fixed t σ hσ).group} :
    u ∈ ((RootWeightDatum.fixed t σ hσ).radicalIn ∅).map
        (MulAut.conj (1 : (RootWeightDatum.fixed t σ hσ).group)).toMonoidHom ↔
      (u.1 : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ.toRingHom := by
  rw [map_one, show (1 : MulAut (RootWeightDatum.fixed t σ hσ).group).toMonoidHom =
      MonoidHom.id _ from rfl, Subgroup.map_id, RootWeightDatum.radicalIn,
    Subgroup.mem_subgroupOf]
  change (u.1 : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ.toRingHom ∅ ↔ _
  rw [graphFixedParabolicRadical, show t.orbitUnion ∅ = ∅ by simp [TwistTag.orbitUnion],
    parabolicRadical_empty]
  rfl

theorem innerCentralizerCriterion_twistedE6_longRoot [CharP K 2] {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InnerCentralizerCriterion (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1,
      pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1 (map_one _)⟩ :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have hσ2 := twistedE6_sigma_pow_order hK hσ
  have hA : (RootWeightDatum.fixed TwistTag.E6 σ hσ2).actors = ⊤ :=
    EvenExceptionalActorCoverage.fixedDiagonalFieldActors_E6_eq_top (by omega) hK σ hσ
  have hJ : (∅ : Set (Fin (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank)) ≠
      Set.univ := by
    intro h
    have := Set.mem_univ (⟨0, (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank_pos⟩ :
      Fin (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank)
    rw [← h] at this
    exact this
  set t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom := ⟨pinnedX TwistTag.E6.tag K
    e6HighestRoot 1, pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1 (map_one _)⟩
  have ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 := rfl
  refine innerCentralizerCriterion_of_conj_radical_of_actors_eq_top
    (RootWeightDatum.fixed TwistTag.E6 σ hσ2) hA hJ 1 (t := t) ?_ ?_
  · intro u hu
    exact graphFixedPosUnipotent_le_closure_odd hf hK hσ ht
      (mem_map_radicalIn_empty_iff_fixed.1 hu)
  · intro z hz _ hc
    exact sq_eq_one_of_commute_odd hf hK hσ ht (mem_map_radicalIn_empty_iff_fixed.1 hz) hc

theorem innerCentralizerCriterion_of_fixedHeightSeries_twistedE6 {f : ℕ} (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {h : ℤ} (h1 : 1 ≤ h) (h7 : h ≤ 7) {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hodd : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ heightSeries TwistTag.E6.tag K h →
        x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
          c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ u ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom,
      (∀ x ∈ heightSeries TwistTag.E6.tag K h ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom,
        u * x = x * u) →
      ∀ hu : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (∀ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, c * t = t * c →
          Odd (orderOf c) → (⟨u, hu⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * c =
            c * ⟨u, hu⟩) → u ^ 2 = 1) :
    InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.conj_injective
      (exceptional_fixed_center_trivial TwistTag.E6 K σ))
    (V := (heightSeries TwistTag.E6.tag K h).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (fun x hx => hodd x (Subgroup.mem_subgroupOf.1 hx)) fun β hβ => ?_
  obtain ⟨u, huU, hu, rfl, hcomm⟩ := exists_eq_conj_of_fix_fixedHeightSeries_twistedE6 hf hK hσ
    h1 h7 β fun x hx => hβ x (Subgroup.mem_subgroupOf.2 hx)
  refine ⟨⟨u, hu⟩, rfl, fun hc => Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact hcen u huU hcomm hu hc

end CFSG.SeitzReduction
