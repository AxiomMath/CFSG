module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitComponentLayer
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

@[expose] def ComponentsLift (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ K : Subgroup G, K ≤ centralizer ({x} : Set G) ⊓ H →
    IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G) ⊓ H)) →
      IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G)))

omit [Finite G] in
theorem centralizer_mk_eq {H : Subgroup G} {x : G} (hx : x ∈ H) :
    centralizer ({(⟨x, hx⟩ : H)} : Set H) = (centralizer ({x} : Set G) ⊓ H).subgroupOf H := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf]
  exact ⟨fun h => ⟨mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h), y.2⟩,
    fun h => Subtype.ext (mem_centralizer_singleton_iff.mp h.1)⟩

theorem isTwoComponentAt_subgroupOf_iff {H Y : Subgroup G} (hYH : Y ≤ H) {x : G} (hx : x ∈ H) :
    IsTwoComponentAt (⟨x, hx⟩ : H) (Y.subgroupOf H) ↔ orderOf x = 2 ∧
      Y ≤ centralizer ({x} : Set G) ∧
      IsPComponent 2 (Y.subgroupOf (centralizer ({x} : Set G) ⊓ H)) := by
  unfold IsTwoComponentAt
  rw [Subgroup.orderOf_mk, centralizer_mk_eq hx,
    isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
  refine and_congr_right fun _ => and_congr_left fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have := h (show (⟨y, hYH hy⟩ : H) ∈ Y.subgroupOf H from hy)
    exact (mem_inf.mp (mem_subgroupOf.mp this)).1
  · exact mem_subgroupOf.mpr (mem_inf.mpr ⟨h (mem_subgroupOf.mp hy), y.2⟩)

omit [Finite G] in
theorem mem_coreActionKernel_subgroupOf_iff {H L : Subgroup G} (hLH : L ≤ H) (g : H) :
    g ∈ coreActionKernel (L.subgroupOf H) ↔ (g : G) ∈ coreActionKernel L := by
  have hO : ((pPrimeCore 2 (L.subgroupOf H)).map (L.subgroupOf H).subtype).map H.subtype =
      (pPrimeCore 2 L).map L.subtype := pPrimeCore_map_subgroupOf 2 L H hLH
  have hOmem : ∀ y : H, y ∈ (pPrimeCore 2 (L.subgroupOf H)).map (L.subgroupOf H).subtype ↔
      (y : G) ∈ (pPrimeCore 2 L).map L.subtype := fun y => by
    rw [← hO]
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  rw [mem_coreActionKernel, mem_coreActionKernel, ← subgroupOf_normalizer_eq hLH, mem_subgroupOf]
  refine and_congr_right fun _ => ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · have h1 := h ⟨j, hLH hj⟩ (show (⟨j, hLH hj⟩ : H) ∈ L.subgroupOf H from hj)
    rw [hOmem] at h1
    simpa using h1
  · have h1 := h (j : G) (mem_subgroupOf.mp hj)
    rw [hOmem]
    simpa using h1

theorem footePointedStep_of_subgroupOf (hLB : FooteLBalanceInput) {H : Subgroup G}
    (hlift : ComponentsLift H) {a b : G} (haH : a ∈ H) (hbH : b ∈ H) {L K : Subgroup G}
    (hLH : L ≤ H) (hKH : K ≤ H)
    (h : FootePointedStep (⟨a, haH⟩ : H) (L.subgroupOf H) (⟨b, hbH⟩ : H) (K.subgroupOf H)) :
    FootePointedStep a L b K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL', hK', hab', hne', hbL', hcl'⟩ := h
  obtain ⟨ha, hLa, hLpc⟩ := (isTwoComponentAt_subgroupOf_iff hLH haH).mp hL'
  obtain ⟨hb, hKb, hKpc⟩ := (isTwoComponentAt_subgroupOf_iff hKH hbH).mp hK'
  have hL : IsTwoComponentAt a L := ⟨ha, hLa, hlift a haH L (le_inf hLa hLH) hLpc⟩
  have hK : IsTwoComponentAt b K := ⟨hb, hKb, hlift b hbH K (le_inf hKb hKH) hKpc⟩
  have hab : a * b = b * a := congrArg Subtype.val hab'
  have hne : a ≠ b := fun h => hne' (Subtype.ext h)
  have hbL : b ∈ coreActionKernel L := (mem_coreActionKernel_subgroupOf_iff hLH _).mp hbL'
  refine ⟨hL, hK, hab, hne, hbL, ?_⟩
  set T := UnbalancedGS.gsFixedLayer L b with hTdef
  have hTH : T ≤ H := (UnbalancedGS.gsFixedLayer_le_inf L b).trans (inf_le_left.trans hLH)
  have hKaH : conjugate K a ≤ H := conjugate_le_of_mem hKH haH
  have hTK : T ≤ K ⊔ conjugate K a := by
    have h1 : UnbalancedGS.gsFixedLayer (L.subgroupOf H) (⟨b, hbH⟩ : H) ≤
        K.subgroupOf H ⊔ conjugate (K.subgroupOf H) (⟨a, haH⟩ : H) := by
      rw [← hcl']
      exact (gsFixedLayer_le_footeFixed hL' hK'.1 hab' hbL').trans (le_conjClosure _ _)
    rw [← UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf hLH hbH,
      conjugate_subgroupOf_eq, ← subgroupOf_sup hKH hKaH] at h1
    intro x hx
    exact mem_subgroupOf.mp (h1 (show (⟨x, hTH hx⟩ : H) ∈ T.subgroupOf H from hx))
  obtain ⟨B, hBb, -, hTB, hclB, -⟩ := exists_footeStep hLB hL hb hab hne hbL
  obtain ⟨-, hLa', hLpc'⟩ := hL
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have haCb : a ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hab
  have hLq := isQuasisimple_quotient_of_isPComponent hLa' hLpc'
  have hLsub : (L.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hLpc'
    exact hs
  have hTpc := gsFixedLayer_isPComponent hLa' hLsub hbCa hb hbL.1 hLq hbL.2
  have hTC : T ≤ centralizer ({b} : Set G) ⊓ centralizer ({a} : Set G) := by
    have h1 := UnbalancedGS.gsFixedLayer_le_inf L b
    exact le_inf (h1.trans inf_le_right) (h1.trans (inf_le_left.trans hLa'))
  have hTpc' : IsPComponent 2 (T.subgroupOf (centralizer ({b} : Set G) ⊓
      centralizer ({a} : Set G))) := by
    rw [inf_comm]; exact hTpc
  have h1 := conjClosure_eq_sup_conjugate_subgroup haCb ha hTC hTpc' hBb.2.1 hBb.2.2 hTB
  have h2 := conjClosure_eq_sup_conjugate_subgroup haCb ha hTC hTpc' hK.2.1 hK.2.2 hTK
  rw [hclB, ← h1, h2]

theorem footePointedReach_map (hLB : FooteLBalanceInput) {H : Subgroup G}
    (hlift : ComponentsLift H) {a b : H} {L K : Subgroup H}
    (h : FootePointedReach a L b K) :
    FootePointedReach (a : G) (L.map H.subtype) (b : G) (K.map H.subtype) := by
  have key := Relation.ReflTransGen.lift
    (fun p : H × Subgroup H => ((p.1 : G), p.2.map H.subtype))
    (p := fun p q : G × Subgroup G => FootePointedStep p.1 p.2 q.1 q.2)
    (r := fun p q : H × Subgroup H => FootePointedStep p.1 p.2 q.1 q.2) ?_ _ _ h
  · exact key
  · rintro ⟨x, X⟩ ⟨y, Y⟩ hstep
    have hX : X = (X.map H.subtype).subgroupOf H :=
      (comap_map_eq_self_of_injective H.subtype_injective X).symm
    have hY : Y = (Y.map H.subtype).subgroupOf H :=
      (comap_map_eq_self_of_injective H.subtype_injective Y).symm
    change FootePointedStep (x : G) (X.map H.subtype) (y : G) (Y.map H.subtype)
    rw [hX, hY] at hstep
    exact footePointedStep_of_subgroupOf hLB hlift x.2 y.2 (map_subtype_le _) (map_subtype_le _)
      hstep

theorem footePointedMaximal_subgroupOf (hLB : FooteLBalanceInput) {H : Subgroup G}
    (hlift : ComponentsLift H) {t : G} (htH : t ∈ H) {L : Subgroup G} (hLH : L ≤ H)
    (hmax : FootePointedMaximal t L) :
    FootePointedMaximal (⟨t, htH⟩ : H) (L.subgroupOf H) := by
  obtain ⟨⟨ht, hLt, hLpc⟩, hreach⟩ := hmax
  refine ⟨(isTwoComponentAt_subgroupOf_iff hLH htH).mpr ⟨ht, hLt,
    isPComponent_subgroupOf_of_le (le_inf hLt hLH) inf_le_left hLpc⟩, fun b K hK => ?_⟩
  have h := footePointedReach_map hLB hlift hK
  rw [map_subgroupOf_eq_of_le hLH] at h
  obtain ⟨e⟩ := hreach (b : G) (K.map H.subtype) h
  obtain ⟨e₁⟩ := nonempty_quotient_fusionZStar_equiv (subgroupOfEquivOfLe hLH)
  obtain ⟨e₂⟩ := nonempty_quotient_fusionZStar_equiv
    (K.equivMapOfInjective H.subtype H.subtype_injective)
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

theorem componentsLift_sup_zpowers {G₀ : Subgroup G} (hG₀ : IsComponent G₀) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) : ComponentsLift (G₀ ⊔ zpowers t) :=
  fun _ _ _ hKC hK => (isPComponent_centralizer_of_sup_zpowers hG₀ htN hKC hK).2

end CFSG.ComponentClassification.FooteLit
