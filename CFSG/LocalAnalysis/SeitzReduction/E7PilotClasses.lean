module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e7RepFrames : Fin 5 → List (Fin Tag.E7.rank → ℤ) :=
  ![[![0, 1, 0, 0, 0, 0, 0]],
    [![0, 1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1]],
    [![0, 0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 0]],
    [![0, 1, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0, 0]],
    [![0, 0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0, 0], ![0, 1, 0, 1, 1, 1, 1],
      ![0, 1, 1, 1, 1, 1, 0]]]

@[expose] def e7ASFrame : Fin 5 → List (Fin Tag.E7.rank → ℤ) :=
  ![[highRoot .E7], oddDerivE7YFrame, oddDerivE7ZFrame, oddDerivE7UFrame, oddDerivE7VFrame]

@[expose] def e7RepPos : Fin 5 → List ℕ :=
  ![[1], [52, 54], [54, 50, 51], [51, 52, 50], [54, 50, 52, 51]]

@[expose] def e7ASPos : Fin 5 → List ℕ :=
  ![[124], [115, 114], [104, 106, 105], [91, 90, 93], [104, 93, 90, 91]]

@[expose] def e7RepWord : Fin 5 → List ℕ :=
  ![[0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 2, 6, 5, 4, 3],
    [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0],
    [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0],
    [1, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0],
    [1, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]]

@[expose] def e7RepPreHigh : Fin 5 → Fin Tag.E7.rank → ℤ :=
  ![![0, 1, 1, 2, 2, 2, 1], ![0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0]]

@[expose] def e7RepPreHighPos : Fin 5 → ℕ :=
  ![93, 6, 0, 3, 3]

@[expose] noncomputable def e7RepWeyl (k : Fin 5) : WeylGroup .E7 :=
  weylOfWord .E7 (e7RepWord k)

theorem e7RepPos_map (k : Fin 5) :
    (e7RepPos k).map Tag.E7.rootCertificate.root = e7RepFrames k := by
  apply List.map_injective_iff.2 List.ofFn_injective
  revert k
  decide +kernel

theorem e7ASPos_map (k : Fin 5) :
    (e7ASPos k).map Tag.E7.rootCertificate.root = e7ASFrame k := by
  apply List.map_injective_iff.2 List.ofFn_injective
  revert k
  decide +kernel

theorem e7RepPreHighPos_root (k : Fin 5) :
    Tag.E7.rootCertificate.root (e7RepPreHighPos k) = e7RepPreHigh k ∧
      Tag.E7.rootCertificate.root 124 = highRoot .E7 := by
  refine ⟨List.ofFn_injective ?_, List.ofFn_injective (by decide +kernel)⟩
  revert k
  decide +kernel

theorem e7Pos_lt (k : Fin 5) :
    (∀ i ∈ e7RepPos k, i < Tag.E7.rootCertificate.roots.length) ∧
      (∀ i ∈ e7ASPos k, i < Tag.E7.rootCertificate.roots.length) ∧
      e7RepPreHighPos k < Tag.E7.rootCertificate.roots.length := by
  revert k
  decide +kernel

theorem e7RepWord_wordPos (k : Fin 5) :
    (e7ASPos k).map (wordPos Tag.E7.rootCertificate (e7RepWord k)) = e7RepPos k ∧
      wordPos Tag.E7.rootCertificate (e7RepWord k) (e7RepPreHighPos k) = 124 := by
  revert k
  decide +kernel

theorem e7RepFrames_highNode (k : Fin 5) : ∀ β ∈ e7RepFrames k,
    β (highNode .E7) = 0 ∧ iform β (highRoot .E7) = 0 ∧ iform (highRoot .E7) β = 0 ∧
      iform (-highRoot .E7) β = 0 := by
  revert k
  decide +kernel

theorem e7RepFrames_pairwise (k : Fin 5) :
    (e7RepFrames k).Pairwise fun σ σ' => iform σ σ' = 0 := by
  revert k
  decide +kernel

theorem e7ASFrame_pairwise (k : Fin 5) :
    (e7ASFrame k).Pairwise fun σ σ' => iform σ σ' = 0 := by
  revert k
  decide +kernel

theorem e7RepFrames_ne_nil (k : Fin 5) : e7RepFrames k ≠ [] := by
  revert k
  decide

theorem e7RepFrames_nodup_pos (k : Fin 5) :
    (e7RepFrames k).Nodup ∧ ∀ β ∈ e7RepFrames k, 0 < height β := by
  revert k
  decide +kernel

section Roots

theorem e7RepFrames_isRoot (k : Fin 5) : ∀ σ ∈ e7RepFrames k, IsRoot .E7 σ := by
  intro σ hσ
  rw [← e7RepPos_map] at hσ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hσ
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) i ((e7Pos_lt k).1 i hi)

theorem e7ASFrame_isRoot (k : Fin 5) : ∀ σ ∈ e7ASFrame k, IsRoot .E7 σ := by
  intro σ hσ
  rw [← e7ASPos_map] at hσ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hσ
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) i ((e7Pos_lt k).2.1 i hi)

theorem e7RepPreHigh_isRoot (k : Fin 5) : IsRoot .E7 (e7RepPreHigh k) := by
  rw [← (e7RepPreHighPos_root k).1]
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) _ (e7Pos_lt k).2.2

theorem e7RepFrames_mem_perpRoots (k : Fin 5) : ∀ β ∈ e7RepFrames k, β ∈ EPilot.perpRoots .E7 :=
  fun β hβ => ⟨e7RepFrames_isRoot k β hβ, (e7RepFrames_highNode k β hβ).1⟩

end Roots

section Weyl

theorem e7RepWeyl_smul_e7ASFrame (k : Fin 5) :
    (e7ASFrame k).map (e7RepWeyl k • ·) = e7RepFrames k := by
  rw [← e7ASPos_map, ← e7RepPos_map, ← (e7RepWord_wordPos k).1, List.map_map, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  exact (wordPos_spec (Tag.rootCertificate_check .E7) (e7RepWord k)
    ((e7Pos_lt k).2.1 i hi)).2.symm

theorem e7RepWeyl_smul_e7RepPreHigh (k : Fin 5) :
    e7RepWeyl k • e7RepPreHigh k = highRoot .E7 := by
  obtain ⟨h1, h2⟩ := e7RepPreHighPos_root k
  have h := (wordPos_spec (Tag.rootCertificate_check .E7) (e7RepWord k) (e7Pos_lt k).2.2).2
  rw [(e7RepWord_wordPos k).2, h2, h1] at h
  exact h.symm

theorem e7RepWeyl_smul_neg_e7RepPreHigh (k : Fin 5) :
    e7RepWeyl k • (-e7RepPreHigh k) = -highRoot .E7 := by
  rw [smul_neg, e7RepWeyl_smul_e7RepPreHigh]

end Weyl

variable {K : Type} [Field K]

section Reps

variable (K) in
@[expose] noncomputable def e7Rep (k : Fin 5) : adjointGroup .E7 K :=
  ⟨((e7RepFrames k).map fun σ => pinnedX .E7 K σ 1).prod,
    list_prod_map_pinnedX_mem_adjointGroup _⟩

variable (K) in
@[expose] noncomputable def e7ASRep (k : Fin 5) : adjointGroup .E7 K :=
  ⟨((e7ASFrame k).map fun σ => pinnedX .E7 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup _⟩

variable (K) in
@[expose] noncomputable def e7RepConj (k : Fin 5) : adjointGroup .E7 K :=
  ⟨canonicalRep (coxeterSystem .E7) K (e7RepWeyl k), canonicalRep_mem_adjointGroup _ K _⟩

theorem coe_e7Rep (k : Fin 5) :
    (e7Rep K k : ModGL .E7 K) = ((e7RepFrames k).map fun σ => pinnedX .E7 K σ 1).prod :=
  rfl

theorem coe_e7ASRep (k : Fin 5) :
    (e7ASRep K k : ModGL .E7 K) = ((e7ASFrame k).map fun σ => pinnedX .E7 K σ 1).prod :=
  rfl

theorem coe_e7Rep_zero :
    (e7Rep K 0 : ModGL .E7 K) = pinnedX .E7 K ![0, 1, 0, 0, 0, 0, 0] 1 := by
  rw [coe_e7Rep]
  exact List.prod_singleton

theorem e7Rep_zero_eq_pinnedElt :
    e7Rep K 0 = EPilot.pinnedElt .E7 ![0, 1, 0, 0, 0, 0, 0] (1 : K) :=
  Subtype.ext coe_e7Rep_zero

theorem mem_innerRepsE7_iff {t : adjointGroup .E7 K} :
    t ∈ innerRepsE7 K ↔ ∃ k : Fin 5, t = e7ASRep K k := by
  have e0 : e7ASRep K 0 = ⟨pinnedX .E7 K (highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (by simp [e7ASRep, e7ASFrame])
  simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h | h | h)
    · exact ⟨0, h.trans e0.symm⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl e0
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem coe_e7Rep_mem_rootSpan {S : Set (Fin Tag.E7.rank → ℤ)} {k : Fin 5}
    (hS : ∀ β ∈ e7RepFrames k, β ∈ S) : (e7Rep K k : ModGL .E7 K) ∈ rootSpan .E7 K S :=
  list_prod_mem fun x hx => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan (hS σ hσ) 1

theorem coe_e7Rep_mem_rootSpan_perpRoots (k : Fin 5) :
    (e7Rep K k : ModGL .E7 K) ∈ rootSpan .E7 K (EPilot.perpRoots .E7) :=
  coe_e7Rep_mem_rootSpan (e7RepFrames_mem_perpRoots k)

theorem e7Rep_mem_perpLevi (k : Fin 5) : e7Rep K k ∈ EPilot.perpLevi .E7 K :=
  Subgroup.mem_subgroupOf.2 (coe_e7Rep_mem_rootSpan_perpRoots k)

end Reps

section Conj

theorem e7RepConj_mul_e7ASRep_mul_inv [CharP K 2] (k : Fin 5) :
    e7RepConj K k * e7ASRep K k * (e7RepConj K k)⁻¹ = e7Rep K k := by
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E7) K (e7RepWeyl k) *
      ((e7ASFrame k).map fun σ => pinnedX .E7 K σ ((fun _ => (1 : K)) σ)).prod *
        (canonicalRep (coxeterSystem .E7) K (e7RepWeyl k))⁻¹ =
      ((e7RepFrames k).map fun σ => pinnedX .E7 K σ 1).prod
  rw [E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo (e7RepWeyl k) (e7ASFrame_isRoot k),
    ← e7RepWeyl_smul_e7ASFrame k, List.map_map]
  rfl

theorem map_conj_e7RepConj_rootSubgroup (k : Fin 5) {ρ : Fin Tag.E7.rank → ℤ}
    (hρ : IsRoot .E7 ρ) :
    (rootSubgroup .E7 K ρ).map (MulAut.conj (e7RepConj K k : ModGL .E7 K)).toMonoidHom =
      rootSubgroup .E7 K (e7RepWeyl k • ρ) :=
  (canonical_weyl_root_transport .E7 K).2.1 _ ρ hρ

theorem map_conj_e7RepConj_rootSL2_preHigh (k : Fin 5) :
    (rootSubgroup .E7 K (e7RepPreHigh k) ⊔ rootSubgroup .E7 K (-e7RepPreHigh k)).map
        (MulAut.conj (e7RepConj K k : ModGL .E7 K)).toMonoidHom =
      EPilot.highRootSL2 .E7 K := by
  rw [Subgroup.map_sup, map_conj_e7RepConj_rootSubgroup k (e7RepPreHigh_isRoot k),
    map_conj_e7RepConj_rootSubgroup k (IsRoot.neg (e7RepPreHigh_isRoot k)),
    e7RepWeyl_smul_e7RepPreHigh, e7RepWeyl_smul_neg_e7RepPreHigh]
  rfl

end Conj

section ClassList

theorem exists_conj_eq_e7Rep_of_sq [Finite K] [CharP K 2] {y : adjointGroup .E7 K}
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    ∃ (k : Fin 5) (c : adjointGroup .E7 K), c * y * c⁻¹ = e7Rep K k := by
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE7 hy2 hy1
  obtain ⟨k, hk⟩ := mem_innerRepsE7_iff.1 hg
  refine ⟨k, e7RepConj K k * g, ?_⟩
  rw [← e7RepConj_mul_e7ASRep_mul_inv k, ← hk]
  group

theorem exists_conj_eq_e7Rep [Finite K] [CharP K 2] {y : adjointGroup .E7 K}
    (hy : orderOf y = 2) :
    ∃ (k : Fin 5) (c : adjointGroup .E7 K), c * y * c⁻¹ = e7Rep K k := by
  refine exists_conj_eq_e7Rep_of_sq (hy ▸ pow_orderOf_eq_one y) fun h => ?_
  rw [h, orderOf_one] at hy
  exact absurd hy (by decide)

theorem exists_conj_eq_symm_e7Rep [Finite K] [CharP K 2] {L : Type*} [Group L]
    (e : L ≃* adjointGroup .E7 K) {y : L} (hy : orderOf y = 2) :
    ∃ (k : Fin 5) (l : L), l * y * l⁻¹ = e.symm (e7Rep K k) := by
  obtain ⟨k, c, hc⟩ := exists_conj_eq_e7Rep (K := K) (y := e y) (by rw [MulEquiv.orderOf_eq, hy])
  refine ⟨k, e.symm c, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem exists_mem_conj_eq_symm_e7Rep [Finite K] [CharP K 2] {G : Type*} [Group G]
    {L : Subgroup G} (e : L ≃* adjointGroup .E7 K) {w : G} (hwL : w ∈ L) (hw : orderOf w = 2) :
    ∃ (k : Fin 5) (l : G), l ∈ L ∧ l * w * l⁻¹ = ((e.symm (e7Rep K k) : L) : G) ∧
      ((e.symm (e7Rep K k) : L) : G) ∈
        ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨k, l, hl⟩ := exists_conj_eq_symm_e7Rep e (y := ⟨w, hwL⟩)
    (by rw [Subgroup.orderOf_mk, hw])
  refine ⟨k, l, l.2, ?_, ⟨_, ⟨_, e7Rep_mem_perpLevi k, rfl⟩, rfl⟩⟩
  have h := congrArg Subtype.val hl
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

end ClassList

section Involution

theorem e7Rep_ne_one (k : Fin 5) : e7Rep K k ≠ 1 := by
  intro h
  obtain ⟨hnd, hpos⟩ := e7RepFrames_nodup_pos k
  have h1 : ((e7RepFrames k).map fun σ => pinnedX .E7 K σ ((fun _ => (1 : K)) σ)).prod =
      ((e7RepFrames k).map fun σ => pinnedX .E7 K σ ((fun _ => (0 : K)) σ)).prod := by
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
    exact congrArg Subtype.val h
  obtain ⟨β, hβ⟩ := List.exists_mem_of_ne_nil _ (e7RepFrames_ne_nil k)
  exact one_ne_zero (pinnedX_list_prod_injective (e7RepFrames k) hnd
    (fun α hα => ⟨e7RepFrames_isRoot k α hα, hpos α hα⟩) _ _ h1 β hβ)

end Involution

section HighRoot

theorem coe_e7Rep_mem_centralizer_highRootSL2 (k : Fin 5) :
    (e7Rep K k : ModGL .E7 K) ∈
      Subgroup.centralizer (EPilot.highRootSL2 .E7 K : Set (ModGL .E7 K)) := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have key : ∀ {ρ : Fin Tag.E7.rank → ℤ}, IsRoot .E7 ρ → (∀ β ∈ e7RepFrames k, iform ρ β = 0) →
      rootSubgroup .E7 K ρ ≤
        Subgroup.centralizer ({(e7Rep K k : ModGL .E7 K)} : Set (ModGL .E7 K)) := by
    intro ρ hρ h0
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, coe_e7Rep]
    exact (Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact classD4_commute_pinnedX hτ hρ (e7RepFrames_isRoot k β hβ) (h0 β hβ).ge c 1).eq
  have hle : EPilot.highRootSL2 .E7 K ≤
      Subgroup.centralizer ({(e7Rep K k : ModGL .E7 K)} : Set (ModGL .E7 K)) :=
    sup_le (key (isRoot_highRoot .E7) fun β hβ => (e7RepFrames_highNode k β hβ).2.2.1)
      (key (IsRoot.neg (isRoot_highRoot .E7)) fun β hβ => (e7RepFrames_highNode k β hβ).2.2.2)
  exact Subgroup.mem_centralizer_iff.2 fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem highRootSL2_subgroupOf_le_centralizer_e7Rep (k : Fin 5) :
    (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤
      Subgroup.centralizer ({e7Rep K k} : Set (adjointGroup .E7 K)) := fun h hh => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (coe_e7Rep_mem_centralizer_highRootSL2 k) _
    (Subgroup.mem_subgroupOf.1 hh))

theorem highRootSL2_subgroupOf_le_rootPerpLevi_e7Rep_zero :
    (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤
      EPilot.rootPerpLevi .E7 K ![0, 1, 0, 0, 0, 0, 0] :=
  EPilot.highRootSL2_subgroupOf_le_rootPerpLevi (Or.inr (Or.inl rfl))
    (e7RepFrames_mem_perpRoots 0 _ List.mem_cons_self)

end HighRoot

end CFSG.SeitzReduction.E7Pilot
