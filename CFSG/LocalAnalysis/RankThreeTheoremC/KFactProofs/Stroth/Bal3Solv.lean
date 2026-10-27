module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.AGLEmbedding Subgroup
open scoped Pointwise

section Layer

variable {X : Type*} [Group X]

private theorem layer_normal : (CFSG.layer X).Normal := by
  rw [CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.normal X

theorem layer_le_iff_forall_isComponentOf {H : Subgroup X} :
    CFSG.layer X ≤ H ↔ ∀ K : Subgroup X, IsComponentOf K ⊤ → K ≤ H :=
  ⟨fun h K hK => (le_layer_of_isComponentOf hK).trans h,
    fun h => sSup_le fun K hK => h K ((CFSG.isComponent_iff_open K).1 hK)⟩

theorem mem_centralizer_layer_of_forall_isComponentOf {c : X}
    (h : ∀ K : Subgroup X, IsComponentOf K ⊤ → c ∈ centralizer (K : Set X)) :
    c ∈ centralizer (CFSG.layer X : Set X) := by
  have hle : CFSG.layer X ≤ centralizer ({c} : Set X) := by
    refine layer_le_iff_forall_isComponentOf.2 fun K hK x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 (h K hK) x hx
  rw [mem_centralizer_iff]
  intro l hl
  exact mem_centralizer_singleton_iff.1 (hle hl)

theorem centralizer_layer_le_of_fittingSubgroup_eq_bot [Finite X]
    (hF : CFSG.fittingSubgroup X = ⊥) :
    centralizer (CFSG.layer X : Set X) ≤ CFSG.layer X := by
  have h := CFSG.centralizer_generalizedFitting_le X
  rwa [CFSG.generalizedFitting, hF, bot_sup_eq] at h

theorem centralizer_layer_eq_bot_of_fittingSubgroup_eq_bot [Finite X]
    (hF : CFSG.fittingSubgroup X = ⊥) : centralizer (CFSG.layer X : Set X) = ⊥ := by
  have hle := centralizer_layer_le_of_fittingSubgroup_eq_bot hF
  haveI : (CFSG.layer X).Normal := layer_normal
  haveI : (centralizer (CFSG.layer X : Set X)).Normal := inferInstance
  haveI : IsMulCommutative (centralizer (CFSG.layer X : Set X)) :=
    le_centralizer_iff_isMulCommutative.1 fun x hx =>
      mem_centralizer_iff.2 fun h hh => mem_centralizer_iff.1 hx h (hle hh)
  have hnil : centralizer (CFSG.layer X : Set X) ≤ CFSG.fittingSubgroup X :=
    le_sSup ⟨inferInstance, inferInstance⟩
  rwa [hF, le_bot_iff] at hnil

end Layer

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial

theorem isSolvable_outer_of_isComponentOf (hSch : SchreierFor CFSG.Assembly.InCatalog)
    {X : Type} [Group X] [Finite X] (hcat : CatalogSimpleSections X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : Group.IsSolvable (Outer K) := by
  have hnonab := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  haveI : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  have hcatK : IsCatalogGroup (K ⧸ center K) := hcat K (center K) inferInstance hK.2.2.2 hnonab
  haveI : Group.IsPerfect K := ⟨hK.2.2.1⟩
  haveI : Group.IsSolvable (Outer (K ⧸ center K)) := hSch (K ⧸ center K) hnonab hcatK
  exact solvable_of_centerQuotient K

end Outer

theorem isSolvable_pi_of_finite_index {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have h1 : x i ∈ derivedSeries (G i) (Finset.univ.sup n) :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) _ ⟨x, hx, rfl⟩
  have h2 := derivedSeries_antitone (G i) (Finset.le_sup (Finset.mem_univ i)) h1
  rw [hn i] at h2
  exact Subgroup.mem_bot.1 h2

theorem isSolvable_quotient_of_ker_le {G A B : Type*} [Group G] [Group A] [Group B]
    [Group.IsSolvable A] [Group.IsSolvable B] (π : G →* A) (Ψ : π.ker →* B) (N : Subgroup G)
    [N.Normal] (hN : N ≤ π.ker) (hΨ : ∀ y : π.ker, Ψ y = 1 → (y : G) ∈ N) :
    Group.IsSolvable (G ⧸ N) := by
  let g : G ⧸ N →* A := QuotientGroup.lift N π hN
  let f : π.ker ⧸ Ψ.ker →* G ⧸ N :=
    QuotientGroup.lift Ψ.ker ((QuotientGroup.mk' N).comp π.ker.subtype) fun y hy => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hΨ y hy
  haveI : Group.IsSolvable (π.ker ⧸ Ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective Ψ)
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : x ∈ π.ker := hq
  exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩

section ConjPerm

variable {X : Type*} [Group X]

@[expose] def conjSubgroupPerm (P : Subgroup X → Prop)
    (hP : ∀ (K : Subgroup X) (g : X), P K → P (MulAut.conj g • K)) :
    X →* Equiv.Perm {K : Subgroup X // P K} where
  toFun g :=
    { toFun := fun K => ⟨MulAut.conj g • K.1, hP K.1 g K.2⟩
      invFun := fun K => ⟨MulAut.conj g⁻¹ • K.1, hP K.1 g⁻¹ K.2⟩
      left_inv := fun K => Subtype.ext (by simp [smul_smul, ← map_mul])
      right_inv := fun K => Subtype.ext (by simp [smul_smul, ← map_mul]) }
  map_one' := Equiv.ext fun K => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun K => Subtype.ext (by simp [mul_smul])

theorem mem_ker_conjSubgroupPerm_iff (P : Subgroup X → Prop)
    (hP : ∀ (K : Subgroup X) (g : X), P K → P (MulAut.conj g • K)) {g : X} :
    g ∈ (conjSubgroupPerm P hP).ker ↔ ∀ K : Subgroup X, P K → g ∈ normalizer (K : Set X) := by
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  constructor
  · intro h K hK
    exact (conj_smul_eq_self_iff g K).1 (congrArg Subtype.val (h ⟨K, hK⟩))
  · intro h K
    exact Subtype.ext ((conj_smul_eq_self_iff g K.1).2 (h K.1 K.2))

end ConjPerm

section Inner

variable {X : Type*} [Group X]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem exists_mem_of_normalizerMonoidHom_mem_inner {K : Subgroup X} {y : X}
    (hy : y ∈ normalizer (K : Set X)) (h : K.normalizerMonoidHom ⟨y, hy⟩ ∈ inner K) :
    ∃ k ∈ K, k⁻¹ * y ∈ centralizer (K : Set X) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, k.2, ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  have h1 : (k : X) * x * (k : X)⁻¹ = y * x * y⁻¹ :=
    congrArg (fun φ : MulAut K => (φ ⟨x, hx⟩ : X)) hk
  calc x * ((k : X)⁻¹ * y) = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * y := by group
    _ = (k : X)⁻¹ * (y * x * y⁻¹) * y := by rw [h1]
    _ = (k : X)⁻¹ * y * x := by group

theorem exists_mem_iSup_inv_mul_mem_centralizer (y : X) (S : Finset (Subgroup X))
    (hS : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → K ≤ centralizer (L : Set X))
    (hy : ∀ K ∈ S, ∃ k ∈ K, k⁻¹ * y ∈ centralizer (K : Set X)) :
    ∃ e ∈ ⨆ K ∈ S, K, ∀ K ∈ S, e⁻¹ * y ∈ centralizer (K : Set X) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert K₀ S' hK₀ ih =>
    obtain ⟨e', he', he'C⟩ := ih
      (fun K hK L hL => hS K (Finset.mem_insert_of_mem hK) L (Finset.mem_insert_of_mem hL))
      (fun K hK => hy K (Finset.mem_insert_of_mem hK))
    obtain ⟨k₀, hk₀, hk₀C⟩ := hy K₀ (Finset.mem_insert_self _ _)
    have he'K₀ : e' ∈ centralizer (K₀ : Set X) := by
      have hle : (⨆ K ∈ S', K) ≤ centralizer (K₀ : Set X) := by
        refine iSup₂_le fun K hK => ?_
        have hne : K ≠ K₀ := fun h => hK₀ (h ▸ hK)
        exact hS K (Finset.mem_insert_of_mem hK) K₀ (Finset.mem_insert_self _ _) hne
      exact hle he'
    have hcomm : Commute k₀ e' := mem_centralizer_iff.1 he'K₀ k₀ hk₀
    have hle : (⨆ K ∈ S', K) ≤ ⨆ K ∈ insert K₀ S', K :=
      iSup₂_le fun K hK => le_iSup₂_of_le K (Finset.mem_insert_of_mem hK) le_rfl
    refine ⟨e' * k₀, mul_mem (hle he') ?_, ?_⟩
    · exact (le_iSup₂_of_le K₀ (Finset.mem_insert_self _ _) le_rfl :
        K₀ ≤ ⨆ K ∈ insert K₀ S', K) hk₀
    · intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK'
      ·
        have : (e' * k₀)⁻¹ * y = e'⁻¹ * (k₀⁻¹ * y) := by
          rw [mul_inv_rev, hcomm.inv_inv.eq, mul_assoc]
        rw [this]
        exact mul_mem (inv_mem he'K₀) hk₀C
      ·
        have hne : K₀ ≠ K := fun h => hK₀ (h ▸ hK')
        have hk₀K : k₀ ∈ centralizer (K : Set X) :=
          hS K₀ (Finset.mem_insert_self _ _) K (Finset.mem_insert_of_mem hK') hne hk₀
        have : (e' * k₀)⁻¹ * y = k₀⁻¹ * (e'⁻¹ * y) := by
          rw [mul_inv_rev, mul_assoc]
        rw [this]
        exact mul_mem (inv_mem hk₀K) (he'C K hK')

theorem mem_layer_of_forall_exists_inner [Finite X] (hF : CFSG.fittingSubgroup X = ⊥) {y : X}
    (hy : ∀ K : Subgroup X, IsComponentOf K ⊤ → ∃ k ∈ K, k⁻¹ * y ∈ centralizer (K : Set X)) :
    y ∈ CFSG.layer X := by
  classical
  have hfin : {K : Subgroup X | IsComponentOf K ⊤}.Finite := Set.toFinite _
  have hmem : ∀ K : Subgroup X, K ∈ hfin.toFinset ↔ IsComponentOf K ⊤ := fun K =>
    hfin.mem_toFinset
  obtain ⟨e, he, heC⟩ := exists_mem_iSup_inv_mul_mem_centralizer y hfin.toFinset
    (fun K hK L hL hne => commutator_eq_bot_iff_le_centralizer.1
      (ComponentClassification.LocalComponents.commute_of_ne K L ((hmem K).1 hK) ((hmem L).1 hL)
        hne))
    (fun K hK => hy K ((hmem K).1 hK))
  have hc : e⁻¹ * y ∈ centralizer (CFSG.layer X : Set X) :=
    mem_centralizer_layer_of_forall_isComponentOf fun K hK => heC K ((hmem K).2 hK)
  rw [centralizer_layer_eq_bot_of_fittingSubgroup_eq_bot hF, mem_bot, inv_mul_eq_one] at hc
  have hle : (⨆ K ∈ hfin.toFinset, K) ≤ CFSG.layer X :=
    iSup₂_le fun K hK => le_layer_of_isComponentOf ((hmem K).1 hK)
  rw [← hc]
  exact hle he

end Inner

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem isSolvable_quotient_layer_of_card_components_le
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {X : Type} [Group X] [Finite X] (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hF : CFSG.fittingSubgroup X = ⊥)
    (hn : ∀ S : Finset (Subgroup X), (∀ K ∈ S, CFSG.Open.IsComponentOf K ⊤) → S.card ≤ 4)
    (E : Subgroup X) [E.Normal] (hE : E = CFSG.layer X) :
    Group.IsSolvable (X ⧸ E) := by
  classical
  subst hE
  let π := conjSubgroupPerm (fun K : Subgroup X => IsComponentOf K ⊤)
    (fun K g hK => isComponentOf_conj_smul hK g)
  have hker : ∀ K : Subgroup X, IsComponentOf K ⊤ → π.ker ≤ normalizer (K : Set X) :=
    fun K hK y hy => (mem_ker_conjSubgroupPerm_iff _ _).1 hy K hK
  have hEker : CFSG.layer X ≤ π.ker := by
    refine layer_le_iff_forall_isComponentOf.2 fun L hL y hy => ?_
    refine (mem_ker_conjSubgroupPerm_iff _ _).2 fun K hK => ?_
    by_cases hLK : L = K
    · subst hLK
      exact le_normalizer hy
    · exact centralizer_le_normalizer _ (commutator_eq_bot_iff_le_centralizer.1
        (ComponentClassification.LocalComponents.commute_of_ne L K hL hK hLK) hy)
  have hcard : Nat.card {K : Subgroup X // IsComponentOf K ⊤} ≤ 4 := by
    have hfin : {K : Subgroup X | IsComponentOf K ⊤}.Finite := Set.toFinite _
    calc Nat.card {K : Subgroup X // IsComponentOf K ⊤}
        = Set.ncard {K : Subgroup X | IsComponentOf K ⊤} := Nat.card_coe_set_eq _
      _ = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
      _ ≤ 4 := hn _ fun K hK => hfin.mem_toFinset.1 hK
  haveI : Group.IsSolvable (Equiv.Perm {K : Subgroup X // IsComponentOf K ⊤}) :=
    Equiv.Perm.isSolvable hcard
  haveI : ∀ K : {K : Subgroup X // IsComponentOf K ⊤}, Group.IsSolvable (Outer K.1) :=
    fun K => isSolvable_outer_of_isComponentOf hSch hcat K.2
  haveI : Group.IsSolvable (∀ K : {K : Subgroup X // IsComponentOf K ⊤}, Outer K.1) :=
    isSolvable_pi_of_finite_index
  let Ψ : π.ker →* ∀ K : {K : Subgroup X // IsComponentOf K ⊤}, Outer K.1 :=
    Pi.monoidHom fun K => (QuotientGroup.mk' (inner K.1)).comp
      (K.1.normalizerMonoidHom.comp (Subgroup.inclusion (hker K.1 K.2)))
  haveI : (CFSG.layer X).Normal := layer_normal
  refine isSolvable_quotient_of_ker_le π Ψ (CFSG.layer X) hEker fun y hy => ?_
  refine mem_layer_of_forall_exists_inner hF fun K hK => ?_
  have h1 := (QuotientGroup.eq_one_iff _).1 (congrFun hy ⟨K, hK⟩)
  exact exists_mem_of_normalizerMonoidHom_mem_inner (hker K hK y.2) h1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
