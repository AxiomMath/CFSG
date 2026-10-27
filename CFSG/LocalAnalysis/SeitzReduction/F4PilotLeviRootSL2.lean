module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2B2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFacts

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open scoped Matrix

section Images

variable {G C : Type*} [Group G] [Group C]

private theorem map_map_conj_eq (E : G →* C) (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map E = (H.map E).map (MulAut.conj (E g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem subgroupOf_map_subtype_self (M : Subgroup C) (H : Subgroup M) :
    (H.map M.subtype).subgroupOf M = H :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective H

end Images

section RootGroups


variable {K : Type} [Field K]

theorem rootGroup_eq_subgroupOf {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    (Adjoint.f4Datum K).rootGroup γ = (rootSubgroup .F4 K γ).subgroupOf (adjointGroup .F4 K) := by
  rw [← map_subtype_rootGroup hγ, subgroupOf_map_subtype_self]

theorem rootSL2_eq_sup {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    rootSL2 K γ = (Adjoint.f4Datum K).rootGroup γ ⊔ (Adjoint.f4Datum K).rootGroup (-γ) := by
  rw [rootSL2, Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup γ)
    (rootSubgroup_le_adjointGroup (-γ)), rootGroup_eq_subgroupOf hγ,
    rootGroup_eq_subgroupOf (IsRoot.neg hγ)]

theorem mem_rootGroup_iff_pinnedX {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {g : adjointGroup .F4 K} :
    g ∈ (Adjoint.f4Datum K).rootGroup γ ↔ ∃ c : K, pinnedX .F4 K γ c = (g : ModGL .F4 K) := by
  rw [rootGroup_eq_subgroupOf hγ, mem_subgroupOf, mem_rootSubgroup]

end RootGroups

section Weyl


variable (K : Type) [Field K]

@[expose] noncomputable def weylRepC (w : WeylGroup .F4) : adjointGroup .F4 K :=
  ⟨canonicalRep (coxeterSystem .F4) K w, canonicalRep_mem_adjointGroup _ K w⟩

variable {K}

theorem map_conj_weylRepC_map_subtype (w : WeylGroup .F4) (H : Subgroup (adjointGroup .F4 K)) :
    (H.map (MulAut.conj (weylRepC K w)).toMonoidHom).map (adjointGroup .F4 K).subtype =
      (H.map (adjointGroup .F4 K).subtype).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl


theorem map_conj_weylRepC_rootSpan (w : WeylGroup .F4) {S : Set (Fin (Tag.rank .F4) → ℤ)}
    (hS : ∀ α ∈ S, IsRoot .F4 α) :
    ((rootSpan .F4 K S).subgroupOf (adjointGroup .F4 K)).map
        (MulAut.conj (weylRepC K w)).toMonoidHom =
      (rootSpan .F4 K ((fun α => w • α) '' S)).subgroupOf (adjointGroup .F4 K) := by
  have hle : ∀ T : Set (Fin (Tag.rank .F4) → ℤ), rootSpan .F4 K T ≤ adjointGroup .F4 K :=
    fun T => iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_conj_weylRepC_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle S), inf_of_le_left (hle _),
    (canonical_weyl_root_transport .F4 K).1 w S hS]

theorem map_conj_weylRepC_rootGroup (w : WeylGroup .F4) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    ((Adjoint.f4Datum K).rootGroup γ).map (MulAut.conj (weylRepC K w)).toMonoidHom =
      (Adjoint.f4Datum K).rootGroup (w • γ) := by
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_conj_weylRepC_map_subtype, map_subtype_rootGroup hγ,
    map_subtype_rootGroup (IsRoot.smul hγ w), (canonical_weyl_root_transport .F4 K).2.1 w γ hγ]

end Weyl

noncomputable abbrev wPos : WeylGroup .F4 := weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0]

theorem eq_image_smul_of_forall (w : WeylGroup .F4) {S T : Set (Fin (Tag.rank .F4) → ℤ)}
    (h : ∀ γ, γ ∈ T ↔ w⁻¹ • γ ∈ S) : T = (fun α => w • α) '' S := by
  ext γ
  constructor
  · intro hγ
    exact ⟨w⁻¹ • γ, (h γ).1 hγ, smul_inv_smul w γ⟩
  · rintro ⟨α, hα, rfl⟩
    rw [h, inv_smul_smul]
    exact hα

section RootSets


theorem wPos_smul_rootR : wPos • rootR = root0122 :=
  weylOfWord_rootR_rootS_mem_C3Roots.1

theorem wPos_smul_rootS : wPos • rootS = root0121 :=
  weylOfWord_rootR_rootS_mem_C3Roots.2


theorem iform_inv_smul (w : WeylGroup .F4) (γ δ : Fin (Tag.rank .F4) → ℤ) :
    iform (w⁻¹ • γ) δ = iform γ (w • δ) := by
  rw [← iform_smul w, smul_inv_smul]

theorem iform_eq_zero_iff_inv_smul (w : WeylGroup .F4) (γ δ : Fin (Tag.rank .F4) → ℤ) :
    iform γ (w • δ) = 0 ↔ iform (w⁻¹ • γ) δ = 0 := by
  rw [iform_inv_smul]

theorem phi0_t_eq : phi0 .t = (fun α => wPos • α) '' c3LeviRoots := by
  refine eq_image_smul_of_forall wPos fun γ => ?_
  simp only [phi0, TwoCentral.support, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, Set.mem_ofPred_eq, mem_c3LeviRoots]
  rw [← wPos_smul_rootR, iform_eq_zero_iff_inv_smul, iform_comm, iform_rootR,
    ← isRoot_smul_iff (w := wPos⁻¹)]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  rfl

theorem phi0_u_eq : phi0 .u = (fun α => wPos • α) '' b3LeviRoots := by
  refine eq_image_smul_of_forall wPos fun γ => ?_
  simp only [phi0, TwoCentral.support, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, Set.mem_ofPred_eq, mem_b3LeviRoots]
  rw [← wPos_smul_rootS, iform_eq_zero_iff_inv_smul, iform_comm, iform_rootS,
    ← isRoot_smul_iff (w := wPos⁻¹)]
  rfl

theorem phi0_tu_eq : phi0 .tu = (fun α => wPos • α) '' b2LeviRoots := by
  refine eq_image_smul_of_forall wPos fun γ => ?_
  simp only [phi0, TwoCentral.support, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq, mem_b2LeviRoots]
  rw [← wPos_smul_rootR, ← wPos_smul_rootS, iform_eq_zero_iff_inv_smul,
    iform_eq_zero_iff_inv_smul, iform_comm, iform_rootR, iform_comm, iform_rootS,
    ← isRoot_smul_iff (w := wPos⁻¹)]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]

end RootSets

section Graph


theorem dualRoot_neg {t : ReeTag} {γ : Fin t.tag.rank → ℤ} (hγ : IsRoot t.tag γ) :
    t.dualRoot (-γ) = -t.dualRoot γ := by
  have hq : t.quadForm (-γ) = t.quadForm γ := by
    change (-γ) ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ (-γ)) = γ ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ γ)
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  funext j
  have hd := (ReeTag.rootDualityCheck_spec hγ).2.1 j
  have hm : t.dualMapInt (-γ) j = -t.dualMapInt γ j :=
    mul_neg _ (γ (t.perm.symm j))
  change 2 * t.dualMapInt (-γ) j / t.quadForm (-γ) = -(2 * t.dualMapInt γ j / t.quadForm γ)
  rw [hm, hq, mul_neg]
  exact Int.neg_ediv_of_dvd (Int.dvd_of_emod_eq_zero hd)

@[expose] def psiF4 (γ : Fin (Tag.rank .F4) → ℤ) : Fin (Tag.rank .F4) → ℤ :=
  ReeTag.F4.dualRoot γ

theorem isRoot_psiF4 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) : IsRoot .F4 (psiF4 γ) :=
  ReeTag.isRoot_dualRoot (t := .F4) hγ

theorem psiF4_psiF4 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) : psiF4 (psiF4 γ) = γ :=
  ReeTag.dualRoot_dualRoot (t := .F4) hγ

theorem psiF4_neg {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) : psiF4 (-γ) = -psiF4 γ :=
  dualRoot_neg (t := .F4) hγ

theorem psiF4_mem_b3LeviRoots_iff {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    psiF4 γ ∈ b3LeviRoots ↔ γ ∈ c3LeviRoots :=
  dualRoot_mem_b3LeviRoots_iff hγ


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem map_graphAutF4_rootGroup {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((Adjoint.f4Datum K).rootGroup γ).map (graphAutF4 K).toMonoidHom =
      (Adjoint.f4Datum K).rootGroup (psiF4 γ) := by
  have : CharP K 2 := ‹_›
  have hΨ : IsRoot .F4 (psiF4 γ) := isRoot_psiF4 hγ
  have hsl : γ ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots := by
    rw [ReeTag.shortRoots_union_longRoots]
    exact hγ
  ext g
  simp only [Subgroup.mem_map, mem_rootGroup_iff_pinnedX hγ, mem_rootGroup_iff_pinnedX hΨ,
    MulEquiv.coe_toMonoidHom]
  rcases hsl with hs | hl
  · constructor
    · rintro ⟨h, ⟨c, hc⟩, rfl⟩
      have hh : h = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hc.symm
      subst hh
      exact ⟨c ^ 2, (congrArg Subtype.val (finiteExceptionalAut_pinnedX_short (K := K) hs c)).symm⟩
    · rintro ⟨d, hd⟩
      obtain ⟨c, rfl⟩ := exists_sq_eq_charTwo d
      refine ⟨⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩, ⟨c, rfl⟩, ?_⟩
      exact (finiteExceptionalAut_pinnedX_short (K := K) hs c).trans (Subtype.ext hd)
  · constructor
    · rintro ⟨h, ⟨c, hc⟩, rfl⟩
      have hh : h = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hc.symm
      subst hh
      exact ⟨c, (congrArg Subtype.val (finiteExceptionalAut_pinnedX_long (K := K) hl c)).symm⟩
    · rintro ⟨d, hd⟩
      refine ⟨⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup γ d⟩, ⟨d, rfl⟩, ?_⟩
      exact (finiteExceptionalAut_pinnedX_long (K := K) hl d).trans (Subtype.ext hd)

end Graph

theorem neg_mem_roots_cartanC {n : ℕ} {v : Fin n → ℤ} (hv : v ∈ roots (isFiniteType_cartanC n) ∅) :
    -v ∈ roots (isFiniteType_cartanC n) ∅ := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hv
  exact SpExtras.mem_roots_of_stdVec (by rw [stdVec_negIdx, hr, SpExtras.toStd_neg'])

section Model

section Set


@[expose] def rootSL2Set (K : Type) [Field K] (M : Subgroup (adjointGroup .F4 K))
    (S : Set (Fin (Tag.rank .F4) → ℤ)) : Set (Subgroup (adjointGroup .F4 K)) :=
  {J | ∃ γ ∈ S, ∃ m ∈ M, J = (rootSL2 K γ).map (MulAut.conj m).toMonoidHom}

theorem leviRootSL2s_eq (K : Type) [Field K] (κ : TwoCentral) :
    leviRootSL2s K κ = rootSL2Set K (levi K κ) (phi0 κ) :=
  rfl

end Set


structure LeviModel (K : Type) [Field K] (n : ℕ) (M : Subgroup (adjointGroup .F4 K))
    (S : Set (Fin (Tag.rank .F4) → ℤ)) where
  E : StatedSp n K →* adjointGroup .F4 K
  injective : Function.Injective E
  range_eq : E.range = M
  θ : (Fin n → ℤ) → (Fin (Tag.rank .F4) → ℤ)
  map_rootGroup : ∀ v ∈ roots (isFiniteType_cartanC n) ∅,
    (Symplectic.rootGroup n K v).map E = (Adjoint.f4Datum K).rootGroup (θ v)
  θ_neg : ∀ v ∈ roots (isFiniteType_cartanC n) ∅, θ (-v) = -θ v
  θ_mem : ∀ v ∈ roots (isFiniteType_cartanC n) ∅, θ v ∈ S
  θ_surj : ∀ γ ∈ S, ∃ v ∈ roots (isFiniteType_cartanC n) ∅, θ v = γ
  isRoot : ∀ γ ∈ S, IsRoot .F4 γ

namespace LeviModel

variable {K : Type} [Field K] {n : ℕ} {M : Subgroup (adjointGroup .F4 K)}
  {S : Set (Fin (Tag.rank .F4) → ℤ)}

@[expose] noncomputable def equiv (L : LeviModel K n M S) : StatedSp n K ≃* M :=
  (MonoidHom.ofInjective L.injective).trans (MulEquiv.subgroupCongr L.range_eq)

theorem coe_equiv (L : LeviModel K n M S) (g : StatedSp n K) :
    (L.equiv g : adjointGroup .F4 K) = L.E g :=
  rfl

theorem map_E_eq (L : LeviModel K n M S) (H : Subgroup (StatedSp n K)) :
    H.map L.E = (H.map L.equiv.toMonoidHom).map M.subtype := by
  rw [Subgroup.map_map]
  rfl

theorem natCard_eq (L : LeviModel K n M S) : Nat.card M = Nat.card (StatedSp n K) :=
  Nat.card_congr L.equiv.toEquiv.symm


theorem map_spRootSL2 (L : LeviModel K n M S) {v : Fin n → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC n) ∅) :
    (spRootSL2 n K v).map L.E = rootSL2 K (L.θ v) := by
  rw [spRootSL2, Subgroup.map_sup, L.map_rootGroup v hv, L.map_rootGroup (-v)
    (neg_mem_roots_cartanC hv), L.θ_neg v hv, rootSL2_eq_sup (L.isRoot _ (L.θ_mem v hv))]

theorem mem_rootSL2Set_iff (L : LeviModel K n M S) (J : Subgroup (adjointGroup .F4 K)) :
    J ∈ rootSL2Set K M S ↔ ∃ H : Subgroup (StatedSp n K), IsSpRootSL2 n K H ∧ J = H.map L.E := by
  constructor
  · rintro ⟨γ, hγ, m, hm, rfl⟩
    obtain ⟨v, hv, rfl⟩ := L.θ_surj γ hγ
    rw [← L.range_eq] at hm
    obtain ⟨g, rfl⟩ := hm
    exact ⟨_, ⟨v, hv, g, rfl⟩, by rw [map_map_conj_eq, L.map_spRootSL2 hv]⟩
  · rintro ⟨H, ⟨v, hv, g, rfl⟩, rfl⟩
    have hm : L.E g ∈ M := by
      have h : L.E g ∈ L.E.range := ⟨g, rfl⟩
      rwa [L.range_eq] at h
    exact ⟨L.θ v, L.θ_mem v hv, L.E g, hm, by rw [map_map_conj_eq, L.map_spRootSL2 hv]⟩

theorem map_mem_rootSL2Set [Finite K] [CharP K 2] (L : LeviModel K n M S) (hn : n = 2 ∨ 3 ≤ n)
    {M' : Subgroup (adjointGroup .F4 K)} {S' : Set (Fin (Tag.rank .F4) → ℤ)}
    (L' : LeviModel K n M' S') (ι : M ≃* M') {J : Subgroup (adjointGroup .F4 K)}
    (hJ : J ∈ rootSL2Set K M S) :
    ((J.subgroupOf M).map ι.toMonoidHom).map M'.subtype ∈ rootSL2Set K M' S' := by
  obtain ⟨H, hH, rfl⟩ := (L.mem_rootSL2Set_iff J).1 hJ
  obtain ⟨H', hH', h⟩ := exists_isSpRootSL2_map_mulEquiv hn L.equiv L'.equiv ι hH
  rw [L.map_E_eq, subgroupOf_map_subtype_self, h, ← L'.map_E_eq]
  exact (L'.mem_rootSL2Set_iff _).2 ⟨H', hH', rfl⟩

end LeviModel

end Model

section Models


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def leviModelT : LeviModel K 3 (levi K .t) (phi0 .t) where
  E := (MulAut.conj (weylRepC K wPos)).toMonoidHom.comp (c3LeviHom K)
  injective := (MulAut.conj (weylRepC K wPos)).injective.comp c3LeviHom_injective
  range_eq := by
    rw [MonoidHom.range_comp, range_c3LeviHom, C3Levi,
      map_conj_weylRepC_rootSpan wPos (fun α hα => hα.1), ← phi0_t_eq]
    rfl
  θ v := wPos • c3ToF4 v
  map_rootGroup v hv := by
    rw [← Subgroup.map_map, map_c3LeviHom_rootGroup hv,
      map_conj_weylRepC_rootGroup wPos (isRoot_c3ToF4 hv)]
  θ_neg v _ := by
    simp only [map_neg, smul_neg]
  θ_mem v hv := by
    rw [phi0_t_eq]
    exact ⟨_, c3ToF4_mem_c3LeviRoots hv, rfl⟩
  θ_surj γ hγ := by
    rw [phi0_t_eq] at hγ
    obtain ⟨γ', hγ', rfl⟩ := hγ
    obtain ⟨v, hv, rfl⟩ := exists_c3ToF4_eq_of_mem_c3LeviRoots hγ'
    exact ⟨v, hv, rfl⟩
  isRoot _ hγ := hγ.1

@[expose] noncomputable def leviModelU : LeviModel K 3 (levi K .u) (phi0 .u) :=
  letI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  { E := (MulAut.conj (weylRepC K wPos)).toMonoidHom.comp
      ((graphAutF4 K).toMonoidHom.comp (c3LeviHom K))
    injective := (MulAut.conj (weylRepC K wPos)).injective.comp
      ((graphAutF4 K).injective.comp c3LeviHom_injective)
    range_eq := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, range_c3LeviHom, map_graphAutF4_C3Levi,
        B3Levi, map_conj_weylRepC_rootSpan wPos (fun α hα => hα.1), ← phi0_u_eq]
      rfl
    θ := fun v => wPos • psiF4 (c3ToF4 v)
    map_rootGroup := fun v hv => by
      rw [← Subgroup.map_map, ← Subgroup.map_map, map_c3LeviHom_rootGroup hv,
        map_graphAutF4_rootGroup (isRoot_c3ToF4 hv),
        map_conj_weylRepC_rootGroup wPos (isRoot_psiF4 (isRoot_c3ToF4 hv))]
    θ_neg := fun v hv => by
      rw [map_neg, psiF4_neg (isRoot_c3ToF4 hv), smul_neg]
    θ_mem := fun v hv => by
      rw [phi0_u_eq]
      exact ⟨_, (psiF4_mem_b3LeviRoots_iff (isRoot_c3ToF4 hv)).2
        (c3ToF4_mem_c3LeviRoots hv), rfl⟩
    θ_surj := fun γ hγ => by
      rw [phi0_u_eq] at hγ
      obtain ⟨γ', hγ', rfl⟩ := hγ
      have hr : IsRoot .F4 (psiF4 γ') := isRoot_psiF4 hγ'.1
      have hc : psiF4 γ' ∈ c3LeviRoots := by
        rw [← psiF4_mem_b3LeviRoots_iff hr, psiF4_psiF4 hγ'.1]
        exact hγ'
      obtain ⟨v, hv, hve⟩ := exists_c3ToF4_eq_of_mem_c3LeviRoots hc
      exact ⟨v, hv, by rw [hve, psiF4_psiF4 hγ'.1]⟩
    isRoot := fun _ hγ => hγ.1 }

@[expose] noncomputable def leviModelTU : LeviModel K 2 (levi K .tu) (phi0 .tu) where
  E := (MulAut.conj (weylRepC K wPos)).toMonoidHom.comp (b2LeviHom K)
  injective := (MulAut.conj (weylRepC K wPos)).injective.comp b2LeviHom_injective
  range_eq := by
    rw [MonoidHom.range_comp, range_b2LeviHom, B2Levi,
      map_conj_weylRepC_rootSpan wPos (fun α hα => hα.1), ← phi0_tu_eq]
    rfl
  θ v := wPos • c2ToF4 v
  map_rootGroup v hv := by
    rw [← Subgroup.map_map, map_b2LeviHom_rootGroup hv,
      map_conj_weylRepC_rootGroup wPos (c2ToF4_mem_b2LeviRoots hv).1]
  θ_neg v _ := by
    simp only [map_neg, smul_neg]
  θ_mem v hv := by
    rw [phi0_tu_eq]
    exact ⟨_, c2ToF4_mem_b2LeviRoots hv, rfl⟩
  θ_surj γ hγ := by
    rw [phi0_tu_eq] at hγ
    obtain ⟨γ', hγ', rfl⟩ := hγ
    obtain ⟨v, hv, rfl⟩ := exists_c2ToF4_eq_of_mem_b2LeviRoots hγ'
    exact ⟨v, hv, rfl⟩
  isRoot _ hγ := hγ.1

end Models

theorem natCard_statedSp_two_lt_three (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp 2 K) < Nat.card (StatedSp 3 K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Finset.prod_Icc_succ_top (show 1 ≤ 2 + 1 by norm_num)]
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  set P := ∏ j ∈ Finset.Icc 1 2, (q ^ (2 * j) - 1)
  have hP : 0 < P := Finset.prod_pos fun j hj => by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have : 1 < q ^ (2 * j) := Nat.one_lt_pow (by omega) (by omega)
    omega
  have h6 : 1 ≤ q ^ (2 * (2 + 1)) - 1 := by
    have : 1 < q ^ (2 * (2 + 1)) := Nat.one_lt_pow (by omega) (by omega)
    omega
  have h49 : q ^ (2 ^ 2) < q ^ (3 ^ 2) := Nat.pow_lt_pow_right (by omega) (by norm_num)
  calc q ^ 2 ^ 2 * P < q ^ 3 ^ 2 * P := Nat.mul_lt_mul_of_pos_right h49 hP
    _ ≤ q ^ 3 ^ 2 * (P * (q ^ (2 * (2 + 1)) - 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h6)

section Main


variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem natCard_levi_tu : Nat.card (levi K .tu) = Nat.card (StatedSp 2 K) :=
  (leviModelTU K).natCard_eq

theorem natCard_levi_of_ne_tu {κ : TwoCentral} (hκ : κ ≠ .tu) :
    Nat.card (levi K κ) = Nat.card (StatedSp 3 K) := by
  cases κ
  · exact (leviModelT K).natCard_eq
  · exact (leviModelU K).natCard_eq
  · exact absurd rfl hκ

theorem not_nonempty_mulEquiv_levi_tu {κ : TwoCentral} (hκ : κ ≠ .tu) :
    ¬ Nonempty (levi K κ ≃* levi K .tu) := by
  rintro ⟨ι⟩
  have h := Nat.card_congr ι.toEquiv
  rw [natCard_levi_of_ne_tu K hκ, natCard_levi_tu] at h
  exact absurd h (natCard_statedSp_two_lt_three K).ne'

theorem factF5 : FactF5 K := by
  intro κ κ' ι J hJ
  rw [leviRootSL2s_eq] at hJ ⊢
  cases κ <;> cases κ'
  · exact (leviModelT K).map_mem_rootSL2Set (Or.inr le_rfl) (leviModelT K) ι hJ
  · exact (leviModelT K).map_mem_rootSL2Set (Or.inr le_rfl) (leviModelU K) ι hJ
  · exact absurd ⟨ι⟩ (not_nonempty_mulEquiv_levi_tu K (by decide))
  · exact (leviModelU K).map_mem_rootSL2Set (Or.inr le_rfl) (leviModelT K) ι hJ
  · exact (leviModelU K).map_mem_rootSL2Set (Or.inr le_rfl) (leviModelU K) ι hJ
  · exact absurd ⟨ι⟩ (not_nonempty_mulEquiv_levi_tu K (by decide))
  · exact absurd ⟨ι.symm⟩ (not_nonempty_mulEquiv_levi_tu K (by decide))
  · exact absurd ⟨ι.symm⟩ (not_nonempty_mulEquiv_levi_tu K (by decide))
  · exact (leviModelTU K).map_mem_rootSL2Set (Or.inl rfl) (leviModelTU K) ι hJ

theorem factLeviSimple (hq : 4 ≤ Nat.card K) : FactLeviSimple K := by
  intro κ
  cases κ
  · have := isSimpleGroup_C3Levi (K := K)
    exact ((leviModelT K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
  · have := isSimpleGroup_C3Levi (K := K)
    exact ((leviModelU K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
  · have := isSimpleGroup_B2Levi (K := K) hq
    exact ((leviModelTU K).equiv.symm.trans (b2LeviEquiv K)).isSimpleGroup

end Main

end CFSG.SeitzReduction.F4Pilot
