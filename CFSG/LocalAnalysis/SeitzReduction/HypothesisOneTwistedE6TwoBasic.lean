module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem commutatorElement_mul_mul_of_commute_of_commute {G : Type*} [Group G] {a a' b b' : G}
    (hab' : Commute a b') (ha'b : Commute a' b) (hza : Commute ⁅a', b'⁆ a)
    (hzb : Commute ⁅a', b'⁆ b) : ⁅a * a', b * b'⁆ = ⁅a', b'⁆ * ⁅a, b⁆ := by
  have e1 : b' * a⁻¹ * b'⁻¹ = a⁻¹ := by
    rw [← hab'.inv_left.eq]
    group
  have e2 : a * b * ⁅a', b'⁆ = ⁅a', b'⁆ * (a * b) := ((hza.mul_right hzb).eq).symm
  calc ⁅a * a', b * b'⁆ = a * (a' * b) * b' * a'⁻¹ * a⁻¹ * b'⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = a * b * ⁅a', b'⁆ * (b' * a⁻¹ * b'⁻¹) * b⁻¹ := by
        rw [ha'b.eq, commutatorElement_def]
        group
    _ = ⁅a', b'⁆ * ⁅a, b⁆ := by
        rw [e1, e2, commutatorElement_def a b]
        group

variable {K : Type} [Field K]

@[expose] noncomputable def twistedE6PairX
    (σ : K →+* K) (δ : Fin TwistTag.E6.tag.rank → ℤ) (s : K) :
    ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K δ s * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s)


theorem commute_pinnedX_of_not_isRoot_add_E6 {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ¬IsRoot TwistTag.E6.tag (α + β)) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) :=
  (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag (Or.inr (Or.inl rfl)) hα hβ hne
    hne').2 h K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commutator_pinnedX_of_isRoot_add_E6 [CharP K 2] {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (h : IsRoot TwistTag.E6.tag (α + β)) (c d : K) :
    ⁅pinnedX TwistTag.E6.tag K α c, pinnedX TwistTag.E6.tag K β d⁆ =
      pinnedX TwistTag.E6.tag K (α + β) (c * d) := by
  have hne' : α ≠ -β := fun e => h.ne_zero (by rw [e, neg_add_cancel])
  obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag
    (Or.inr (Or.inl rfl)) hα hβ hne hne').1 h
  have hε1 : (commConst TwistTag.E6.tag α β (1, 1) : K) = 1 := by
    refine eq_one_of_mul_self_eq_one_of_two_eq_zero (CharP.cast_eq_zero K 2) ?_
    rcases hε with h | h <;> simp [h]
  rw [hcomm K c d, hε1, one_mul]

theorem commute_pinnedX_permLattice_twistedE6 {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K δ c)
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) d) := by
  by_cases h : permLattice TwistTag.E6.perm δ = δ
  · rw [h, Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  have hmem := TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit δ)
  have hnr := TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hδ
    (TwistTag.E6.self_mem_diagramOrbit δ) hmem (le_refl 1) (le_refl 1)
  rw [one_smul, one_smul] at hnr
  refine commute_pinnedX_of_not_isRoot_add_E6 hδ (hδ.permLattice TwistTag.E6.cartan_perm)
    (Ne.symm h) (fun e => ?_) hnr c d
  have h1 := congrArg height e
  rw [height_neg, height_permLattice] at h1
  rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg hδ with h2 | h2 <;> omega

theorem twistedE6PairX_mem_twistedFixedGroup [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) (s : K) :
    twistedE6PairX σ δ s ∈ twistedFixedGroup TwistTag.E6 K σ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩
  rw [twistedE6PairX, map_mul, twistHom_pinnedX_eq_of_charTwo h2 σ hδ,
    twistHom_pinnedX_eq_of_charTwo h2 σ (hδ.permLattice TwistTag.E6.cartan_perm),
    permLattice_twistedE6_perm_perm, hσσ]
  exact (commute_pinnedX_permLattice_twistedE6 hδ s (σ s)).eq.symm

theorem twistedE6PairX_mem_graphFixedRootGroup [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (s : K) : twistedE6PairX σ δ s ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hΓ := twistedE6PairX_mem_twistedFixedGroup hσσ hδ s
  have hρδ := hδ.permLattice TwistTag.E6.cartan_perm
  rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg hδ with hp | hn
  · refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (Subgroup.mem_inf.2 ⟨mul_mem ?_ ?_, hΓ⟩)
    · exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, hp⟩
        (mem_rootSubgroup.2 ⟨s, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem
        ⟨hρδ, by rw [height_permLattice]; exact hp⟩ (mem_rootSubgroup.2 ⟨σ s, rfl⟩))
  · refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      (Subgroup.mem_inf.2 ⟨mul_mem ?_ ?_, hΓ⟩)
    · exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, hn⟩
        (mem_rootSubgroup.2 ⟨s, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem
        ⟨hρδ, by rw [height_permLattice]; exact hn⟩ (mem_rootSubgroup.2 ⟨σ s, rfl⟩))

theorem commute_twistedE6PairX_e6HighestRoot (σ : K →+* K) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hρδ : permLattice TwistTag.E6.perm δ ≠ δ)
    (hδr : ¬IsRoot TwistTag.E6.tag (δ + e6HighestRoot)) (s c : K) :
    Commute (twistedE6PairX σ δ s) (pinnedX TwistTag.E6.tag K e6HighestRoot c) := by
  have hr := permLattice_e6HighestRoot
  have hρ : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, permLattice TwistTag.E6.perm (-v) =
      -permLattice TwistTag.E6.perm v := fun v => rfl
  have hδr' : δ ≠ e6HighestRoot := fun e => hρδ (by rw [e, hr])
  have hδr'' : δ ≠ -e6HighestRoot := fun e => hρδ (by rw [e, hρ, hr])
  refine Commute.mul_left (commute_pinnedX_of_not_isRoot_add_E6 hδ isRoot_e6HighestRoot hδr'
    hδr'' hδr s c) (commute_pinnedX_of_not_isRoot_add_E6
      (hδ.permLattice TwistTag.E6.cartan_perm) isRoot_e6HighestRoot (fun e => ?_) (fun e => ?_)
      (fun h => hδr ?_) (σ s) c)
  · apply hδr'
    rw [← permLattice_twistedE6_perm_perm δ, e, hr]
  · apply hδr''
    rw [← permLattice_twistedE6_perm_perm δ, e, hρ, hr]
  · rw [← isRoot_permLattice_twistedE6_iff]
    have e : permLattice TwistTag.E6.perm (δ + e6HighestRoot) =
        permLattice TwistTag.E6.perm δ + permLattice TwistTag.E6.perm e6HighestRoot := rfl
    rw [e, hr]
    exact h

theorem commutator_twistedE6PairX [CharP K 2] (σ : K →+* K)
    {δ ε : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hε : IsRoot TwistTag.E6.tag ε) (hγ : IsRoot TwistTag.E6.tag (δ + ε))
    (hργ : permLattice TwistTag.E6.perm (δ + ε) = δ + ε) (hne : δ ≠ ε)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + permLattice TwistTag.E6.perm ε))
    (h2 : δ + permLattice TwistTag.E6.perm ε ≠ 0) (h3 : δ ≠ permLattice TwistTag.E6.perm ε)
    (h4 : ¬IsRoot TwistTag.E6.tag (δ + ε + δ)) (h5 : ¬IsRoot TwistTag.E6.tag (δ + ε + ε))
    (h6 : δ + ε ≠ -δ) (h7 : δ + ε ≠ -ε) (s u : K) :
    ⁅twistedE6PairX σ δ s, twistedE6PairX σ ε u⁆ =
      pinnedX TwistTag.E6.tag K (δ + ε) (s * u + σ (s * u)) := by
  have hρδ := hδ.permLattice TwistTag.E6.cartan_perm
  have hρε := hε.permLattice TwistTag.E6.cartan_perm
  have hadd : ∀ v w : Fin TwistTag.E6.tag.rank → ℤ, permLattice TwistTag.E6.perm (v + w) =
      permLattice TwistTag.E6.perm v + permLattice TwistTag.E6.perm w := fun v w => rfl
  have hsum : permLattice TwistTag.E6.perm δ + permLattice TwistTag.E6.perm ε = δ + ε := by
    rw [← hadd, hργ]
  have e1 := commutator_pinnedX_of_isRoot_add_E6 hδ hε hne hγ s u
  have e2 : ⁅pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s),
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ε) (σ u)⁆ =
        pinnedX TwistTag.E6.tag K (δ + ε) (σ (s * u)) := by
    rw [commutator_pinnedX_of_isRoot_add_E6 hρδ hρε
      (fun e => hne (permLattice_injective _ e)) (hsum ▸ hγ), hsum, map_mul]
  have c1 := commute_pinnedX_of_not_isRoot_add_E6 (K := K) hδ hρε h3
    (fun e => h2 (by rw [e, neg_add_cancel])) h1 s (σ u)
  have c2 : Commute (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s))
      (pinnedX TwistTag.E6.tag K ε u) := by
    have e : permLattice TwistTag.E6.perm δ + ε =
        permLattice TwistTag.E6.perm (δ + permLattice TwistTag.E6.perm ε) := by
      rw [hadd, permLattice_twistedE6_perm_perm]
    refine commute_pinnedX_of_not_isRoot_add_E6 hρδ hε (fun h => h3 ?_) (fun h => h2 ?_)
      (by rw [e, isRoot_permLattice_twistedE6_iff]; exact h1) _ _
    · rw [← h, permLattice_twistedE6_perm_perm]
    · apply permLattice_injective TwistTag.E6.perm
      rw [← e, h, neg_add_cancel]
      rfl
  have c5 : ∀ c : K, Commute (pinnedX TwistTag.E6.tag K (δ + ε) c)
      (pinnedX TwistTag.E6.tag K δ s) := fun c =>
    commute_pinnedX_of_not_isRoot_add_E6 hγ hδ
      (fun e => hε.ne_zero (by simpa using e)) h6 h4 c s
  have c6 : ∀ c : K, Commute (pinnedX TwistTag.E6.tag K (δ + ε) c)
      (pinnedX TwistTag.E6.tag K ε u) := fun c =>
    commute_pinnedX_of_not_isRoot_add_E6 hγ hε
      (fun e => hδ.ne_zero (by simpa using e)) h7 h5 c u
  have hza : Commute ⁅pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s),
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ε) (σ u)⁆
        (pinnedX TwistTag.E6.tag K δ s) := by
    rw [e2]
    exact c5 _
  have hzb : Commute ⁅pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s),
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ε) (σ u)⁆
        (pinnedX TwistTag.E6.tag K ε u) := by
    rw [e2]
    exact c6 _
  unfold twistedE6PairX
  rw [commutatorElement_mul_mul_of_commute_of_commute c1 c2 hza hzb, e1, e2,
    ← pinnedX_add TwistTag.E6.tag K (δ + ε), add_comm (σ (s * u))]

theorem exists_twistedE6PairX_eq_conj (σ : K →+* K) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hbδ : rootChar b δ ≠ 1)
    (hbρ : rootChar b (permLattice TwistTag.E6.perm δ) = Units.map σ.toMonoidHom (rootChar b δ))
    (s : K) :
    ∃ a : K, twistedE6PairX σ δ s = rootDiagUnit TwistTag.E6.tag b * twistedE6PairX σ δ a *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ * (twistedE6PairX σ δ a)⁻¹ := by
  have hχ : (rootChar b δ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hbδ (Units.ext h)
  have hρδ := hδ.permLattice TwistTag.E6.cartan_perm
  refine ⟨s * ((rootChar b δ : K) - 1)⁻¹, ?_⟩
  generalize ha : s * ((rootChar b δ : K) - 1)⁻¹ = a
  have hsa : (rootChar b δ : K) * a + -a = s := by
    rw [← ha]
    field_simp
    ring
  have hσa : σ ((rootChar b δ : K) * a) + -σ a = σ s := by
    rw [← hsa, map_add, map_neg]
  have hc1 := rootDiagUnit_conj_pinnedX b hδ a
  have hc2 : rootDiagUnit TwistTag.E6.tag b *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a) *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)) := by
    rw [rootDiagUnit_conj_pinnedX b hρδ (σ a), hbρ, Units.coe_map, map_mul]
    rfl
  have hcomm := (commute_pinnedX_permLattice_twistedE6 (K := K) hδ (-a) (σ s)).eq
  unfold twistedE6PairX
  calc pinnedX TwistTag.E6.tag K δ s * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ)
        (σ s)
      = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) * pinnedX TwistTag.E6.tag K δ (-a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s) := by
        rw [← pinnedX_add TwistTag.E6.tag K δ, hsa]
    _ = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s) *
            pinnedX TwistTag.E6.tag K δ (-a) := by
        rw [mul_assoc, hcomm, ← mul_assoc]
    _ = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)) *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (-σ a) *
              pinnedX TwistTag.E6.tag K δ (-a) := by
        rw [mul_assoc (pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a))
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)))
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (-σ a)),
          ← pinnedX_add TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ), hσa]
    _ = (rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag K δ a *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹) *
          (rootDiagUnit TwistTag.E6.tag b *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a) *
              (rootDiagUnit TwistTag.E6.tag b)⁻¹) *
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a))⁻¹ *
            (pinnedX TwistTag.E6.tag K δ a)⁻¹ := by
        rw [hc1, hc2, pinnedX_neg, pinnedX_neg]
    _ = rootDiagUnit TwistTag.E6.tag b * (pinnedX TwistTag.E6.tag K δ a *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a)) *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹ * (pinnedX TwistTag.E6.tag K δ a *
              pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a))⁻¹ := by
        group

theorem rootChar_twistedE6TorusTuple_permLattice {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (i : Fin TwistTag.E6.tag.rank) (u : Kˣ) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (twistedE6TorusTuple σ i u) (permLattice TwistTag.E6.perm γ) =
      Units.map σ.toMonoidHom (rootChar (twistedE6TorusTuple σ i u) γ) := by
  have hu : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u) = u := Units.ext (hσσ u)
  rw [rootChar_twistedE6TorusTuple, rootChar_twistedE6TorusTuple, coPair_permLattice_twistedE6,
    coPair_permLattice_twistedE6, twistedE6_perm_perm, map_mul, map_zpow, map_zpow, hu,
    mul_comm]

theorem exists_twistedE6TorusTwo [Finite K] (hK : Nat.card K = 4) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2) {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hργ : permLattice TwistTag.E6.perm γ ≠ γ) :
    ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
      rootChar b e6HighestRoot = 1 ∧ rootChar b γ ≠ 1 ∧
      rootChar b (permLattice TwistTag.E6.perm γ) ≠ 1 ∧
      rootChar b (permLattice TwistTag.E6.perm γ) =
        Units.map σ.toRingHom.toMonoidHom (rootChar b γ) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hσ2 : σ ^ TwistTag.E6.order = 1 :=
    twistedE6_sigma_pow_order (f := 1) (by rw [hK]; norm_num) (fun c => by rw [hσ]; norm_num)
  have hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x := fun x => by
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    simpa [TwistTag.order, pow_two] using h
  have hσζ : Units.map σ.toRingHom.toMonoidHom ζ = ζ ^ 2 := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ ζ)
  obtain ⟨i, hi, h1, h2⟩ := exists_twistedE6TwoTorusIndex hγ hργ
  have hi' : i = ⟨0, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hchar : ∀ v, rootChar (twistedE6TorusTuple σ.toRingHom i ζ) v =
      ζ ^ twistedE6TwoExp i v := by
    intro v
    rw [rootChar_twistedE6TorusTuple, hσζ, ← zpow_natCast, ← zpow_mul, ← zpow_add,
      twistedE6TwoExp]
    norm_num
  have hne : ∀ m : ℤ, m % 3 ≠ 0 → ζ ^ m ≠ 1 := by
    intro m hm h
    have hd := orderOf_dvd_iff_zpow_eq_one.2 h
    rw [hζ] at hd
    norm_num at hd
    omega
  refine ⟨twistedE6TorusTuple σ.toRingHom i ζ, rootDiagUnit_twistedE6TorusTuple_mem σ hσ2 hi' ζ,
    ?_, ?_, ?_, rootChar_twistedE6TorusTuple_permLattice hσσ i ζ γ⟩
  · obtain ⟨hr1, hr2⟩ := coPair_e6HighestRoot_of_mem hi
    rw [hchar, twistedE6TwoExp, hr1, hr2]
    simp
  · rw [hchar]
    exact hne _ h1
  · rw [hchar]
    exact hne _ h2

end CFSG.SeitzReduction
