module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalCores

open Subgroup

section Perfect

variable {G : Type*} [Group G]

theorem component_le_layer {K : Subgroup G} (hK : IsComponent K) : K ≤ layer G :=
  le_sSup hK

theorem layer_perfect : ⁅layer G, layer G⁆ = layer G := by
  refine le_antisymm (commutator_le_self _) (sSup_le fun K hK => ?_)
  calc K = ⁅K, K⁆ := (isPerfect_iff.mp hK.1.1).symm
    _ ≤ ⁅layer G, layer G⁆ := commutator_mono (component_le_layer hK) (component_le_layer hK)

theorem layer_isPerfect : Group.IsPerfect (layer G) :=
  isPerfect_iff.mpr layer_perfect

theorem layer_eq_bot_of_forall (h : ∀ K : Subgroup G, ¬ IsComponent K) : layer G = ⊥ :=
  sSup_eq_bot.mpr fun K hK => absurd hK (h K)

end Perfect

section Normal

variable {G : Type*} [Group G] [Finite G]

theorem layer_le_normalizer {K : Subgroup G} (hK : IsComponent K) :
    layer G ≤ normalizer (K : Set G) := by
  refine sSup_le fun L hL => ?_
  rcases distinct_components_commute hL hK with rfl | h
  · exact le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le_normalizer _)

theorem components_normal_in_layer {K : Subgroup G} (hK : IsComponent K) :
    K ≤ layer G ∧ (K.subgroupOf (layer G)).Normal :=
  ⟨component_le_layer hK, normal_subgroupOf_of_le_normalizer (layer_le_normalizer hK)⟩

theorem component_normal_of_layer_eq_top (hE : layer G = ⊤) {K : Subgroup G}
    (hK : IsComponent K) : K.Normal :=
  normalizer_eq_top_iff.mp (top_le_iff.mp (hE ▸ layer_le_normalizer hK))

theorem center_component_le_centralizer_layer {K : Subgroup G} (hK : IsComponent K) :
    (center K).map K.subtype ≤ centralizer (layer G : Set G) := by
  rw [le_centralizer_iff]
  refine sSup_le fun L hL => ?_
  rcases distinct_components_commute hL hK with rfl | h
  · intro y hy
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)).symm
  · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans
      (centralizer_le (map_subtype_le (center K)))

end Normal

section Multiplication

variable (G : Type*) [Group G]

abbrev ComponentIndex : Type _ := {K : Subgroup G // IsComponent K}

noncomputable instance [Finite G] : Fintype (ComponentIndex G) := Fintype.ofFinite _

noncomputable instance : DecidableEq (ComponentIndex G) := Classical.decEq _

variable {G} [Finite G]

theorem componentIndex_commute :
    Pairwise fun K L : ComponentIndex G => ∀ x y : G, x ∈ K.1 → y ∈ L.1 → Commute x y := by
  intro K L hKL x y hx hy
  rcases distinct_components_commute K.2 L.2 with h | h
  · exact absurd (Subtype.ext h) hKL
  · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm

variable (G) in
@[expose] noncomputable def layerMul : (∀ K : ComponentIndex G, K.1) →* G :=
  noncommPiCoprod (componentIndex_commute (G := G))

theorem layerMul_apply (x : ∀ K : ComponentIndex G, K.1) :
    layerMul G x = Finset.univ.noncommProd (fun K => (x K : G))
      (fun K _ L _ h => componentIndex_commute h _ _ (x K).2 (x L).2) :=
  noncommPiCoprod_apply _ x

@[simp]
theorem layerMul_mulSingle (K : ComponentIndex G) (k : K.1) :
    layerMul G (Pi.mulSingle K k) = k :=
  noncommPiCoprod_mulSingle K k

theorem layerMul_range : (layerMul G).range = layer G := by
  refine (noncommPiCoprod_range (H := fun K : ComponentIndex G => K.1)).trans ?_
  refine le_antisymm (iSup_le fun K => component_le_layer K.2) (sSup_le fun K hK => ?_)
  exact le_iSup (fun L : ComponentIndex G => L.1) ⟨K, hK⟩

theorem exists_layerMul_eq {g : G} (hg : g ∈ layer G) : ∃ x, layerMul G x = g := by
  rw [← layerMul_range] at hg
  exact hg

theorem layerMul_eq_prod (x : ∀ K : ComponentIndex G, K.1) {l : List (ComponentIndex G)}
    (hl : l.Nodup) (hall : ∀ K, K ∈ l) : layerMul G x = (l.map fun K => (x K : G)).prod := by
  have hcomm : (l.toFinset : Set (ComponentIndex G)).Pairwise
      (Function.onFun Commute fun K => (x K : G)) :=
    fun K _ L _ h => componentIndex_commute h _ _ (x K).2 (x L).2
  rw [← Finset.noncommProd_toFinset l _ hcomm hl, layerMul_apply]
  exact Finset.noncommProd_congr (by ext K; simp [hall]) (fun _ _ => rfl) _

theorem layerMul_mem {H : Subgroup G} (x : ∀ K : ComponentIndex G, K.1)
    (hx : ∀ K, (x K : G) ∈ H) : layerMul G x ∈ H := by
  rw [layerMul_apply]
  exact noncommProd_mem H _ fun K _ => hx K

theorem layerMul_eq_mul_update (x : ∀ K : ComponentIndex G, K.1) (K : ComponentIndex G) :
    layerMul G x = (x K : G) * layerMul G (Function.update x K 1) := by
  have hx : Pi.mulSingle K (x K) * Function.update x K 1 = x := by
    funext L
    by_cases h : L = K
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
  calc layerMul G x = layerMul G (Pi.mulSingle K (x K) * Function.update x K 1) := by rw [hx]
    _ = _ := by rw [map_mul, layerMul_mulSingle]

theorem commute_layerMul_update (x : ∀ K : ComponentIndex G, K.1) (K : ComponentIndex G)
    {k : G} (hk : k ∈ K.1) : Commute k (layerMul G (Function.update x K 1)) := by
  have h : layerMul G (Function.update x K 1) ∈ centralizer {k} := by
    refine layerMul_mem _ fun L => ?_
    by_cases hL : L = K
    · subst hL
      simp
    · rw [Function.update_of_ne hL, mem_centralizer_singleton_iff]
      exact componentIndex_commute hL _ _ (x L).2 hk
  exact (mem_centralizer_singleton_iff.mp h).symm

theorem commute_layerMul_iff (x : ∀ K : ComponentIndex G, K.1) (K : ComponentIndex G) {k : G}
    (hk : k ∈ K.1) : Commute k (layerMul G x) ↔ Commute k (x K : G) := by
  have hu := commute_layerMul_update x K hk
  rw [layerMul_eq_mul_update x K]
  refine ⟨fun h => ?_, fun h => h.mul_right hu⟩
  have := h.mul_right hu.inv_right
  rwa [mul_inv_cancel_right] at this

theorem layerMul_mem_centralizer_iff (x : ∀ K : ComponentIndex G, K.1) :
    layerMul G x ∈ centralizer (layer G : Set G) ↔ ∀ K, x K ∈ center K.1 := by
  refine ⟨fun h K => mem_center_iff.mpr fun k => Subtype.ext ?_, fun h => ?_⟩
  · have hk : Commute (k : G) (layerMul G x) :=
      mem_centralizer_iff.mp h k (component_le_layer K.2 k.2)
    exact ((commute_layerMul_iff x K k.2).mp hk).eq
  · exact layerMul_mem x fun K =>
      center_component_le_centralizer_layer K.2 (mem_map_of_mem _ (h K))

theorem layerMul_ker_le : (layerMul G).ker ≤ Subgroup.pi Set.univ fun K => center K.1 := by
  intro x hx K _
  have h : layerMul G x ∈ centralizer (layer G : Set G) := by
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  exact (layerMul_mem_centralizer_iff x).mp h K

variable (G) in
@[expose] noncomputable def layerMulOnto : (∀ K : ComponentIndex G, K.1) →* layer G :=
  (layerMul G).codRestrict (layer G) fun x => by
    rw [← layerMul_range]
    exact ⟨x, rfl⟩

@[simp]
theorem layerMulOnto_coe (x : ∀ K : ComponentIndex G, K.1) :
    (layerMulOnto G x : G) = layerMul G x :=
  rfl

theorem layerMulOnto_surjective : Function.Surjective (layerMulOnto G) := fun g => by
  obtain ⟨x, hx⟩ := exists_layerMul_eq g.2
  exact ⟨x, Subtype.ext hx⟩

theorem layerMulOnto_mem_center_iff (x : ∀ K : ComponentIndex G, K.1) :
    layerMulOnto G x ∈ center (layer G) ↔ ∀ K, x K ∈ center K.1 := by
  rw [← layerMul_mem_centralizer_iff, mem_center_iff, mem_centralizer_iff]
  refine ⟨fun h g hg => congrArg Subtype.val (h ⟨g, hg⟩), fun h g => Subtype.ext (h g g.2)⟩

theorem layer_multiplication :
    Function.Surjective (layerMulOnto G) ∧ (layerMul G).range = layer G ∧
      (∀ (x : ∀ K : ComponentIndex G, K.1) (l : List (ComponentIndex G)), l.Nodup →
        (∀ K, K ∈ l) → layerMul G x = (l.map fun K => (x K : G)).prod) ∧
      (∀ x : ∀ K : ComponentIndex G, K.1,
        x ∈ (layerMulOnto G).ker ↔ (∀ K, x K ∈ center K.1) ∧ layerMul G x = 1) ∧
      (IsEmpty (ComponentIndex G) →
        Subsingleton (∀ K : ComponentIndex G, K.1) ∧ layer G = ⊥) := by
  refine ⟨layerMulOnto_surjective, layerMul_range, fun x l hl hall => layerMul_eq_prod x hl hall,
    fun x => ?_, fun h => ⟨inferInstance, layer_eq_bot_of_forall fun K hK => h.elim ⟨K, hK⟩⟩⟩
  have hx : x ∈ (layerMulOnto G).ker ↔ layerMul G x = 1 := by
    rw [MonoidHom.mem_ker, ← layerMulOnto_coe, ← OneMemClass.coe_one (layer G), Subtype.ext_iff]
  rw [hx]
  exact ⟨fun h => ⟨fun K => layerMul_ker_le h K (Set.mem_univ K), h⟩, fun h => h.2⟩

end Multiplication

section Center

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_center_iff (H : Subgroup G) {g : G} :
    g ∈ (center H).map H.subtype ↔ g ∈ H ∧ g ∈ centralizer (H : Set G) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, mem_centralizer_iff.mpr fun h hh =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨h, hh⟩)⟩
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, mem_center_iff.mpr fun h => Subtype.ext (mem_centralizer_iff.mp hc h h.2),
      rfl⟩

theorem center_component_le_center_layer {K : Subgroup G} (hK : IsComponent K) :
    (center K).map K.subtype ≤ (center (layer G)).map (layer G).subtype := fun _ hz =>
  (mem_map_center_iff _).mpr ⟨component_le_layer hK (map_subtype_le _ hz),
    center_component_le_centralizer_layer hK hz⟩

theorem layer_center :
    (center (layer G)).map (layer G).subtype =
        ⨆ K : ComponentIndex G, (center K.1).map K.1.subtype ∧
      ∀ K : Subgroup G, IsComponent K →
        K ⊓ (center (layer G)).map (layer G).subtype = (center K).map K.subtype := by
  refine ⟨le_antisymm ?_ (iSup_le fun K => center_component_le_center_layer K.2), fun K hK => ?_⟩
  · intro g hg
    obtain ⟨hgE, hgc⟩ := (mem_map_center_iff _).mp hg
    obtain ⟨x, rfl⟩ := exists_layerMul_eq hgE
    have hx := (layerMul_mem_centralizer_iff x).mp hgc
    exact layerMul_mem x fun K => mem_iSup_of_mem K (mem_map_of_mem _ (hx K))
  · refine le_antisymm (fun g hg => ?_)
      (le_inf (map_subtype_le _) (center_component_le_center_layer hK))
    have hgc := ((mem_map_center_iff _).mp hg.2).2
    refine (mem_map_center_iff K).mpr ⟨hg.1, ?_⟩
    exact centralizer_le (component_le_layer hK) hgc

end Center

section CentralQuotient

variable (G : Type*) [Group G]

@[expose] noncomputable def componentCenterQuotient :
    (∀ K : ComponentIndex G, K.1) →* ∀ K : ComponentIndex G, K.1 ⧸ center K.1 :=
  MonoidHom.pi fun K => (QuotientGroup.mk' (center K.1)).comp (Pi.evalMonoidHom _ K)

theorem componentCenterQuotient_apply (x : ∀ K : ComponentIndex G, K.1) :
    componentCenterQuotient G x = fun K => (x K : K.1 ⧸ center K.1) :=
  rfl

theorem componentCenterQuotient_surjective : Function.Surjective (componentCenterQuotient G) :=
  fun y => ⟨fun K => (QuotientGroup.mk_surjective (y K)).choose,
    funext fun K => (QuotientGroup.mk_surjective (y K)).choose_spec⟩

theorem componentCenterQuotient_ker :
    (componentCenterQuotient G).ker = Subgroup.pi Set.univ fun K => center K.1 := by
  ext x
  rw [MonoidHom.mem_ker, componentCenterQuotient_apply, mem_pi, funext_iff]
  simp only [Set.mem_univ, true_imp_iff, Pi.one_apply, QuotientGroup.eq_one_iff]

variable [Finite G]

@[expose] noncomputable def layerCenterQuotient :
    (∀ K : ComponentIndex G, K.1) →* layer G ⧸ center (layer G) :=
  (QuotientGroup.mk' (center (layer G))).comp (layerMulOnto G)

theorem layerCenterQuotient_surjective : Function.Surjective (layerCenterQuotient G) :=
  (QuotientGroup.mk'_surjective _).comp layerMulOnto_surjective

theorem layerCenterQuotient_ker :
    (layerCenterQuotient G).ker = Subgroup.pi Set.univ fun K => center K.1 := by
  ext x
  rw [layerCenterQuotient, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', mem_comap,
    layerMulOnto_mem_center_iff, mem_pi]
  simp only [Set.mem_univ, true_imp_iff]

@[expose] noncomputable def layerCentralQuotientEquiv :
    (∀ K : ComponentIndex G, K.1 ⧸ center K.1) ≃* layer G ⧸ center (layer G) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (componentCenterQuotient_surjective G)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((componentCenterQuotient_ker G).trans (layerCenterQuotient_ker G).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (layerCenterQuotient_surjective G)))

variable {G}

theorem layerCentralQuotientEquiv_apply (x : ∀ K : ComponentIndex G, K.1) :
    layerCentralQuotientEquiv G (fun K => (x K : K.1 ⧸ center K.1)) =
      (layerMulOnto G x : layer G ⧸ center (layer G)) := by
  have hA : QuotientGroup.quotientKerEquivOfSurjective _ (componentCenterQuotient_surjective G)
      (x : (∀ K : ComponentIndex G, K.1) ⧸ (componentCenterQuotient G).ker) =
      componentCenterQuotient G x := rfl
  rw [← componentCenterQuotient_apply, layerCentralQuotientEquiv, MulEquiv.trans_apply,
    MulEquiv.trans_apply, ← hA, MulEquiv.symm_apply_apply]
  rfl

theorem layerCentralQuotientEquiv_mulSingle (K : ComponentIndex G) (k : K.1) :
    layerCentralQuotientEquiv G (Pi.mulSingle K (k : K.1 ⧸ center K.1)) =
      ((⟨k, component_le_layer K.2 k.2⟩ : layer G) : layer G ⧸ center (layer G)) := by
  have h : Pi.mulSingle K (k : K.1 ⧸ center K.1) =
      fun L => ((Pi.mulSingle K k : ∀ L : ComponentIndex G, L.1) L : L.1 ⧸ center L.1) := by
    funext L
    by_cases hL : L = K
    · subst hL
      simp
    · simp [Pi.mulSingle_eq_of_ne hL]
  rw [h, layerCentralQuotientEquiv_apply]
  congr 1
  exact Subtype.ext (layerMul_mulSingle K k)

theorem layer_central_quotient :
    (∀ (K : ComponentIndex G) (k : K.1),
        layerCentralQuotientEquiv G (Pi.mulSingle K (k : K.1 ⧸ center K.1)) =
          ((⟨k, component_le_layer K.2 k.2⟩ : layer G) : layer G ⧸ center (layer G))) ∧
      (∀ K : ComponentIndex G,
        IsSimpleGroup (K.1 ⧸ center K.1) ∧ ∃ a b : K.1 ⧸ center K.1, a * b ≠ b * a) ∧
      (IsEmpty (ComponentIndex G) → Subsingleton (∀ K : ComponentIndex G, K.1 ⧸ center K.1) ∧
        Subsingleton (layer G ⧸ center (layer G))) := by
  refine ⟨layerCentralQuotientEquiv_mulSingle, fun K => K.2.1.2, fun h => ?_⟩
  have : Subsingleton (∀ K : ComponentIndex G, K.1 ⧸ center K.1) := inferInstance
  exact ⟨this, (layerCentralQuotientEquiv G).symm.injective.subsingleton⟩

end CentralQuotient

section Semisimple

theorem layer_eq_top_of_mulEquiv_pi {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, Group (S i)]
    [∀ i, IsSimpleGroup (S i)] (hS : ∀ i, ∃ a b : S i, a * b ≠ b * a) {H : Type*} [Group H]
    (e : H ≃* ∀ i, S i) : layer H = ⊤ := by
  classical
  have hn : ∀ i, (MonoidHom.mulSingle S i).range.Normal := fun i => ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    refine ⟨g i * s * (g i)⁻¹, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]⟩
  have hK : ∀ i, IsComponent ((MonoidHom.mulSingle S i).range.map e.symm.toMonoidHom) :=
    fun i => ⟨isQuasisimple_of_mulEquiv ((MonoidHom.ofInjective (Pi.mulSingle_injective i)).trans
      (equivMapOfInjective _ _ e.symm.injective)) (isQuasisimple_of_isSimpleGroup (hS i)).1,
      ((hn i).map _ e.symm.surjective).isSubnormal⟩
  have hsup : ⨆ i, (MonoidHom.mulSingle S i).range = ⊤ :=
    eq_top_iff.mpr fun x _ => pi_mem_of_mulSingle_mem x fun i => mem_iSup_of_mem i ⟨x i, rfl⟩
  refine eq_top_iff.mpr ?_
  calc (⊤ : Subgroup H) = (⊤ : Subgroup (∀ i, S i)).map e.symm.toMonoidHom :=
        (map_top_of_surjective _ e.symm.surjective).symm
    _ = ⨆ i, (MonoidHom.mulSingle S i).range.map e.symm.toMonoidHom := by
        rw [← hsup, Subgroup.map_iSup]
    _ ≤ layer H := iSup_le fun i => component_le_layer (hK i)

theorem layer_eq_top_of_surjective {S T : Type*} [Group S] [Group T] [Finite S]
    (hS : layer S = ⊤) (f : S →* T) (hf : Function.Surjective f) : layer T = ⊤ := by
  have hle : layer S ≤ (layer T).comap f := sSup_le fun K hK => by
    refine map_le_iff_le_comap.mp ?_
    by_cases hKf : K ≤ f.ker
    · rw [(map_eq_bot_iff K).mpr hKf]
      exact bot_le
    · exact component_le_layer ⟨isQuasisimple_map hK.1 f hKf,
        ((component_normal_of_layer_eq_top hS hK).map f hf).isSubnormal⟩
  refine eq_top_iff.mpr fun t _ => ?_
  obtain ⟨s, rfl⟩ := hf t
  exact hle (hS ▸ mem_top s)

end Semisimple

end CFSG.LocalCores
