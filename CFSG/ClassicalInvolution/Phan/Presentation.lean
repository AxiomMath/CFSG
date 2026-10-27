module

public import CFSG.LieType.CurtisTits.AmalgamRecognition
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.ClassicalInvolution.Generic.TypeA
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanPresentation

open CFSG.LieType.CurtisTits Subgroup

variable {X : Type} [Group X] {ι : Type} (U : ι → Subgroup X)

abbrev PartIndex := {P : Subgroup X // ∃ i j, P = U i ⊔ U j}

abbrev family : PartIndex U → Subgroup X := fun P => P.val

abbrev Completion := PresentedGroup (amalgamRels (family U))

@[expose] def nodeIndex (i : ι) : PartIndex U := ⟨U i, i, i, (sup_idem (U i)).symm⟩

@[expose] def pairIndex (i j : ι) : PartIndex U := ⟨U i ⊔ U j, i, j, rfl⟩

@[expose] def nodeHom (i : ι) : U i →* Completion U :=
  amalgamGenHom (L := family U) (nodeIndex U i)

@[expose] def pairHom (i j : ι) : ↥(U i ⊔ U j) →* Completion U :=
  amalgamGenHom (L := family U) (pairIndex U i j)

@[expose] def nodes (i : ι) : Subgroup (Completion U) := (nodeHom U i).range

@[expose] def pairs (i j : ι) : Subgroup (Completion U) := (pairHom U i j).range

theorem nodeHom_injective (i : ι) : Function.Injective (nodeHom U i) :=
  amalgamGenHom_injective (L := family U) (nodeIndex U i)

theorem pairHom_injective (i j : ι) : Function.Injective (pairHom U i j) :=
  amalgamGenHom_injective (L := family U) (pairIndex U i j)

theorem pairHom_comp_inclusion_left (i j : ι) :
    (pairHom U i j).comp (Subgroup.inclusion (show U i ≤ U i ⊔ U j from le_sup_left)) =
      nodeHom U i := by
  ext x
  exact (isCompatible_amalgamGenHom (L := family U)
    (nodeIndex U i) (pairIndex U i j) (show nodeIndex U i ≤ pairIndex U i j from by
      change U i ≤ U i ⊔ U j
      exact le_sup_left)
    x (Subgroup.inclusion le_sup_left x) rfl).symm

theorem pairHom_comp_inclusion_right (i j : ι) :
    (pairHom U i j).comp (Subgroup.inclusion (show U j ≤ U i ⊔ U j from le_sup_right)) =
      nodeHom U j := by
  ext x
  exact (isCompatible_amalgamGenHom (L := family U)
    (nodeIndex U j) (pairIndex U i j) (show nodeIndex U j ≤ pairIndex U i j from by
      change U j ≤ U i ⊔ U j
      exact le_sup_right)
    x (Subgroup.inclusion le_sup_right x) rfl).symm

theorem subgroupOf_map_pairHom_left (i j : ι) :
    ((U i).subgroupOf (U i ⊔ U j)).map (pairHom U i j) = nodes U i := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨(x : X), hx⟩, ?_⟩
    exact (congrArg (fun f : U i →* Completion U => f ⟨(x : X), hx⟩)
      (pairHom_comp_inclusion_left U i j)).symm
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : X), (show U i ≤ U i ⊔ U j from le_sup_left) x.property⟩, x.property, ?_⟩
    exact congrArg (fun f : U i →* Completion U => f x)
      (pairHom_comp_inclusion_left U i j)

theorem subgroupOf_map_pairHom_right (i j : ι) :
    ((U j).subgroupOf (U i ⊔ U j)).map (pairHom U i j) = nodes U j := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨(x : X), hx⟩, ?_⟩
    exact (congrArg (fun f : U j →* Completion U => f ⟨(x : X), hx⟩)
      (pairHom_comp_inclusion_right U i j)).symm
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : X), (show U j ≤ U i ⊔ U j from le_sup_right) x.property⟩, x.property, ?_⟩
    exact congrArg (fun f : U j →* Completion U => f x)
      (pairHom_comp_inclusion_right U i j)

theorem pairs_eq_sup_nodes (i j : ι) : pairs U i j = nodes U i ⊔ nodes U j := by
  have htop : (U i).subgroupOf (U i ⊔ U j) ⊔ (U j).subgroupOf (U i ⊔ U j) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  unfold pairs
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup,
    subgroupOf_map_pairHom_left, subgroupOf_map_pairHom_right]

theorem iSup_nodes_eq_top : (⨆ i, nodes U i) = ⊤ := by
  apply top_unique
  intro z _
  apply PresentedGroup.generated_by (amalgamRels (family U)) (⨆ i, nodes U i) ?_ z
  rintro ⟨P, x⟩
  obtain ⟨i, j, hP⟩ := P.property
  have hP' : P = pairIndex U i j := Subtype.ext hP
  subst P
  change pairHom U i j x ∈ ⨆ k, nodes U k
  have hx : pairHom U i j x ∈ pairs U i j := ⟨x, rfl⟩
  rw [pairs_eq_sup_nodes] at hx
  exact (sup_le (le_iSup (nodes U) i) (le_iSup (nodes U) j)) hx

theorem iSup_family_eq_top (hgen : (⨆ i, U i) = ⊤) : (⨆ P, family U P) = ⊤ := by
  apply top_unique
  rw [← hgen]
  refine iSup_le fun i => ?_
  exact le_iSup (family U) (nodeIndex U i)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  {M : CoxeterMatrix ι} {W : ι → ι → Subgroup X}

theorem weakPhanSL (h : WeakPhanSL F p f M U W) :
    WeakPhanSL F p f M (nodes U) (pairs U) where
  iso i := by
    obtain ⟨e⟩ := h.iso i
    let e' : U i ≃* nodes U i := MulEquiv.ofBijective (nodeHom U i).rangeRestrict
      ⟨fun x y hxy => nodeHom_injective U i (congrArg Subtype.val hxy), by
        rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩⟩
    exact ⟨e.trans e'⟩
  join i j _ := pairs_eq_sup_nodes U i j
  comm i j hij := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    let a' : ↥(U i ⊔ U j) := Subgroup.inclusion le_sup_left a
    let b' : ↥(U i ⊔ U j) := Subgroup.inclusion le_sup_right b
    have hab : a' * b' = b' * a' := Subtype.ext (h.comm i j hij a a.property b b.property)
    have ha : pairHom U i j a' = nodeHom U i a :=
      congrArg (fun g : U i →* Completion U => g a) (pairHom_comp_inclusion_left U i j)
    have hb : pairHom U i j b' = nodeHom U j b :=
      congrArg (fun g : U j →* Completion U => g b) (pairHom_comp_inclusion_right U i j)
    calc nodeHom U i a * nodeHom U j b = pairHom U i j a' * pairHom U i j b' := by rw [ha, hb]
      _ = pairHom U i j b' * pairHom U i j a' := by rw [← map_mul, hab, map_mul]
      _ = nodeHom U j b * nodeHom U i a := by rw [ha, hb]
  pair i j hij := by
    have hne : i ≠ j := by
      intro heq
      subst j
      simp at hij
    have hpair : UnitaryBlockStandardPair F p f (U i ⊔ U j) (U i) (U j) := by
      rw [← h.join i j hne]
      exact h.pair i j hij
    have hrestrict := CFSG.ClassicalInvolution.Generic.unitaryBlockStandardPair_subgroupOf
      (J := U i ⊔ U j) le_rfl hpair
    have hmap := CFSG.ClassicalInvolution.Models.unitaryBlockStandardPair_map hrestrict
      (pairHom U i j) (pairHom_injective U i j)
    simpa only [pairs, Subgroup.subgroupOf_self, Subgroup.map_top,
      subgroupOf_map_pairHom_left, subgroupOf_map_pairHom_right] using hmap
  gen := iSup_nodes_eq_top U

theorem isUniversalCompletion_of_recognition [Finite X]
    (h : WeakPhanSL F p f M U W)
    (hrecognize : ∀ {Y : Type} [Group Y] (V : ι → Subgroup Y) (Z : ι → ι → Subgroup Y),
      WeakPhanSL F p f M V Z → ∃ θ : X →* Y, Function.Surjective θ) :
    IsUniversalCompletion (family U) := by
  obtain ⟨back, hback⟩ := hrecognize (nodes U) (pairs U) (weakPhanSL U h)
  exact isUniversalCompletion_of_isPresentedByAmalgam
    (isPresentedByAmalgam_of_surjective (iSup_family_eq_top U h.gen) back hback)

theorem recognition_of_unmarked [Finite X] (h : WeakPhanSL F p f M U W)
    (hX : IsQuasisimple X)
    (hrecognize : ∀ {Y : Type} [Group Y] (V : ι → Subgroup Y) (Z : ι → ι → Subgroup Y),
      WeakPhanSL F p f M V Z → ∃ θ : X →* Y, Function.Surjective θ)
    {G : Type} [Group G] (φ : ∀ P, family U P →* G)
    (hφ : IsCompatible (family U) φ) (hgen : (⨆ P, (φ P).range) = ⊤)
    (hnt : ∃ P, ∃ x : family U P, φ P x ≠ 1) :
    ∃ Ψ : X →* G, (∀ P (x : family U P), Ψ x = φ P x) ∧
      Function.Surjective Ψ ∧ Ψ.ker ≤ center X := by
  obtain ⟨Ψ, hΨ, hsurj, hker, _⟩ := recognition_of_isUniversalCompletion
    (iSup_family_eq_top U h.gen) hX (isUniversalCompletion_of_recognition U h hrecognize)
    φ hφ hgen hnt
  exact ⟨Ψ, hΨ, hsurj, hker⟩

end CFSG.ClassicalInvolution.Phan.PhanPresentation
