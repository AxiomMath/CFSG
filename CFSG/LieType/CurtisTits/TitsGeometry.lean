module

public import CFSG.Monster.B.Recog.GenericTits
public import CFSG.LieType.CurtisTits.Amalgam
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LieType.CurtisTits

open Subgroup
open CFSG.Monster.B.Recog

universe u v w

variable {I : Type u}
variable {X : Type v} {typ : X → I} {Γ : SimpleGraph X}
variable {G : Type v} [Group G] [MulAction G X]

@[expose] def parabolic (G : Type v) [Group G] [MulAction G X] (F : I → X) (J : Set I) :
    Subgroup G :=
  ⨅ j ∈ J, MulAction.stabilizer G (F j)

@[expose] def IsFlag (Γ : SimpleGraph X) (S : Set X) : Prop := S.Finite ∧ S.Pairwise Γ.Adj

@[expose] def FlagTransitive (G : Type v) [Group G] [MulAction G X] (Γ : SimpleGraph X)
    (F : I → X) : Prop :=
  ∀ S : Set X, IsFlag Γ S → ∃ g : G, ∀ x ∈ S, g • x ∈ Set.range F

theorem mem_parabolic_iff {F : I → X} {J : Set I} {g : G} :
    g ∈ parabolic G F J ↔ ∀ j ∈ J, g • F j = F j := by
  simp [parabolic]

theorem mem_parabolic_singleton_iff {F : I → X} {i : I} {g : G} :
    g ∈ parabolic G F {i} ↔ g • F i = F i := by
  rw [mem_parabolic_iff]
  simp

theorem parabolic_singleton {F : I → X} (i : I) :
    parabolic G F {i} = MulAction.stabilizer G (F i) := by
  ext g
  rw [mem_parabolic_singleton_iff, MulAction.mem_stabilizer_iff]

private theorem isFlag_pair {Γ : SimpleGraph X} {a b : X} (h : Γ.Adj a b) :
    IsFlag Γ ({a, b} : Set X) := by
  refine ⟨?_, ?_⟩
  · exact (Set.finite_singleton b).insert a
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [Γ.adj_comm]

private theorem isFlag_triple {Γ : SimpleGraph X} {a b c : X} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hca : Γ.Adj c a) : IsFlag Γ ({a, b, c} : Set X) := by
  refine ⟨?_, ?_⟩
  · exact ((Set.finite_singleton c).insert b).insert a
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [Γ.adj_comm]

private theorem eq_F_of_mem_range {F : I → X} (hFtyp : ∀ i, typ (F i) = i) {x : X}
    (hx : x ∈ Set.range F) : x = F (typ x) := by
  obtain ⟨i, rfl⟩ := hx
  rw [hFtyp]

private theorem exists_smul_eq_of_adj {Γ : SimpleGraph X} {F : I → X} (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hflag : FlagTransitive G Γ F) {u v : X} (h : Γ.Adj u v) :
    ∃ s : G, s • F (typ u) = u ∧ s • F (typ v) = v := by
  obtain ⟨t, ht⟩ := hflag {u, v} (isFlag_pair h)
  have hu : t • u ∈ Set.range F := ht u (by simp)
  have hv : t • v ∈ Set.range F := ht v (by simp)
  have hu' : t • u = F (typ u) := by
    rw [eq_F_of_mem_range hFtyp hu, htyp]
  have hv' : t • v = F (typ v) := by
    rw [eq_F_of_mem_range hFtyp hv, htyp]
  refine ⟨t⁻¹, ?_, ?_⟩
  · rw [← hu', inv_smul_smul]
  · rw [← hv', inv_smul_smul]

private theorem exists_mem_stabilizer_smul_eq_of_adj {Γ : SimpleGraph X} {F : I → X}
    (hFtyp : ∀ i, typ (F i) = i) (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hflag : FlagTransitive G Γ F) {i : I} {y : X} (hy : Γ.Adj (F i) y) :
    ∃ g ∈ MulAction.stabilizer G (F i), g • F (typ y) = y := by
  obtain ⟨s, hsF, hsy⟩ := exists_smul_eq_of_adj hFtyp htyp hflag hy
  refine ⟨s, ?_, hsy⟩
  rw [MulAction.mem_stabilizer_iff]
  simpa [hFtyp i] using hsF

private theorem exists_smul_eq_triangle {Γ : SimpleGraph X} {F : I → X}
    (hFtyp : ∀ i, typ (F i) = i) (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hflag : FlagTransitive G Γ F) {i : I} {y z : X} (hy : Γ.Adj (F i) y)
    (hyz : Γ.Adj y z) (hz : Γ.Adj z (F i)) :
    ∃ g : G, g • F i = F i ∧ g • F (typ y) = y ∧ g • F (typ z) = z := by
  obtain ⟨t, ht⟩ := hflag {F i, y, z} (isFlag_triple hy hyz hz)
  have h1 : t • F i = F i := by
    rw [eq_F_of_mem_range hFtyp (ht _ (by simp)), htyp, hFtyp]
  have h2 : t • y = F (typ y) := by
    rw [eq_F_of_mem_range hFtyp (ht _ (by simp)), htyp]
  have h3 : t • z = F (typ z) := by
    rw [eq_F_of_mem_range hFtyp (ht _ (by simp)), htyp]
  refine ⟨t⁻¹, ?_, ?_, ?_⟩
  · calc t⁻¹ • F i = t⁻¹ • (t • F i) := by rw [h1]
      _ = F i := inv_smul_smul t (F i)
  · calc t⁻¹ • F (typ y) = t⁻¹ • (t • y) := by rw [h2]
      _ = y := inv_smul_smul t y
  · calc t⁻¹ • F (typ z) = t⁻¹ • (t • z) := by rw [h3]
      _ = z := inv_smul_smul t z

section NonemptyIndex

variable [Nonempty I]

theorem iSup_stabilizer_eq_top_of_connected {Γ : SimpleGraph X} {F : I → X}
    (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hflag : FlagTransitive G Γ F) (hconn : Γ.Preconnected) :
    (⨆ i : I, MulAction.stabilizer G (F i)) = ⊤ := by
  set H : Subgroup G := ⨆ i : I, MulAction.stabilizer G (F i)
  have key : ∀ {u v : X} (_p : Γ.Walk u v), (∃ k ∈ H, k • F (typ u) = u) →
      ∃ k ∈ H, k • F (typ v) = v := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons a b c hab q ih =>
      rintro ⟨k, hk, hkF⟩
      obtain ⟨s, hsF, hsF'⟩ := exists_smul_eq_of_adj hFtyp htyp hflag hab
      have hks : k⁻¹ * s ∈ MulAction.stabilizer G (F (typ a)) := by
        rw [MulAction.mem_stabilizer_iff]
        calc (k⁻¹ * s) • F (typ a) = k⁻¹ • (s • F (typ a)) := mul_smul _ _ _
          _ = k⁻¹ • a := by rw [hsF]
          _ = k⁻¹ • (k • F (typ a)) := by rw [hkF]
          _ = F (typ a) := inv_smul_smul _ _
      have hsH : s ∈ H := by
        have hs : s = k * (k⁻¹ * s) := by group
        rw [hs]
        exact H.mul_mem hk (Subgroup.mem_iSup_of_mem (typ a) hks)
      exact ih ⟨s, hsH, hsF'⟩
  refine eq_top_iff.2 fun g _ => ?_
  let i0 : I := Classical.choice ‹Nonempty I›
  have hr : Γ.Reachable (F i0) (g • F i0) := hconn _ _
  obtain ⟨p⟩ := hr
  obtain ⟨k, hk, hkF⟩ := key p ⟨1, H.one_mem, by simp [hFtyp]⟩
  have hkg : k⁻¹ * g ∈ MulAction.stabilizer G (F i0) := by
    rw [MulAction.mem_stabilizer_iff]
    rw [mul_smul, ← hkF]
    rw [htyp, hFtyp, inv_smul_smul]
  have hg : g = k * (k⁻¹ * g) := by group
  rw [hg]
  exact H.mul_mem hk (Subgroup.mem_iSup_of_mem i0 hkg)

end NonemptyIndex

variable {F : I → X}

section Cover

theorem parabolic_antitone {J K : Set I} (hJK : J ⊆ K) : parabolic G F K ≤ parabolic G F J := by
  intro g hg
  rw [mem_parabolic_iff] at hg ⊢
  exact fun j hj => hg j (hJK hj)

variable {Y : Type w} [Group Y]
variable (φ : ∀ J : Set I, J.Nonempty → parabolic G F J →* Y)

def IsCompatibleFamily (G : Type v) [Group G] [MulAction G X] (F : I → X)
    (φ : ∀ J : Set I, J.Nonempty → parabolic G F J →* Y) : Prop :=
  ∀ (J K : Set I) (hJ : J.Nonempty) (hK : K.Nonempty) (_ : J ⊆ K) (a : G)
    (haK : a ∈ parabolic G F K) (haJ : a ∈ parabolic G F J),
    φ K hK ⟨a, haK⟩ = φ J hJ ⟨a, haJ⟩

variable (hφ : IsCompatibleFamily G F φ)

@[expose] def parabolicGraph (J : Set I) (hJ : J.Nonempty) : Subgroup (Y × G) := homGraph (φ J hJ)

include hφ in
theorem parabolicGraph_le_parabolicGraph {J K : Set I} (hJ : J.Nonempty)
    (hK : K.Nonempty) (hJK : J ⊆ K) :
    parabolicGraph φ K hK ≤ parabolicGraph φ J hJ := by
  rintro ⟨y, a⟩ hq
  obtain ⟨b, hb⟩ := mem_homGraph.1 hq
  have hba : (b : G) = a := congrArg Prod.snd hb
  have haK : a ∈ parabolic G F K := hba ▸ b.2
  have haJ : a ∈ parabolic G F J := parabolic_antitone hJK haK
  refine mem_homGraph.2 ⟨⟨a, haJ⟩, ?_⟩
  have hb' : (⟨a, haK⟩ : parabolic G F K) = b := Subtype.ext hba.symm
  have hcomp := hφ J K hJ hK hJK a haK haJ
  have hfst : (φ K hK) ⟨a, haK⟩ = y := by
    simpa [← hb'] using congrArg Prod.fst hb
  exact Prod.ext (hcomp.symm.trans hfst) rfl

@[expose] def generatedSubgroup : Subgroup (Y × G) :=
  Subgroup.closure (⋃ i : I, (parabolicGraph φ {i} (Set.singleton_nonempty i) : Set (Y × G)))

include hφ in
theorem parabolicGraph_le_generatedSubgroup (J : Set I) (hJ : J.Nonempty) :
    parabolicGraph φ J hJ ≤ generatedSubgroup φ := by
  obtain ⟨i, hi⟩ := hJ
  refine (parabolicGraph_le_parabolicGraph φ hφ (Set.singleton_nonempty i)
    ⟨i, hi⟩ ?_).trans ?_
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hi
  · intro q hq
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hq⟩)

@[expose] def generatedProjection : generatedSubgroup φ →* G :=
  (MonoidHom.snd Y G).comp (generatedSubgroup φ).subtype

@[expose] def vertexStabilizer (i : I) : Subgroup (generatedSubgroup φ) :=
  (parabolicGraph φ {i} (Set.singleton_nonempty i)).subgroupOf (generatedSubgroup φ)

include hφ in
theorem map_generatedProjection_vertexStabilizer (i : I) :
    (vertexStabilizer φ i).map (generatedProjection φ) = parabolic G F {i} := by
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (map_snd_homGraph (φ {i} (Set.singleton_nonempty i))).symm ▸
      Subgroup.mem_map_of_mem (MonoidHom.snd Y G) (Subgroup.mem_subgroupOf.1 hz)
  · intro ha
    have ha' : a ∈ (parabolicGraph φ {i} (Set.singleton_nonempty i)).map (MonoidHom.snd Y G) := by
      rw [parabolicGraph, map_snd_homGraph]
      exact ha
    obtain ⟨q, hq, hqa⟩ := Subgroup.mem_map.1 ha'
    exact Subgroup.mem_map.2
      ⟨⟨q, parabolicGraph_le_generatedSubgroup φ hφ {i} (Set.singleton_nonempty i) hq⟩,
        Subgroup.mem_subgroupOf.2 hq, by simpa [generatedProjection] using hqa⟩

private theorem smul_fixed_of_mem_vertexStabilizer {i : I}
    {z : generatedSubgroup φ} (hz : z ∈ vertexStabilizer φ i) :
    generatedProjection φ z • F i = F i := by
  obtain ⟨a, ha⟩ := mem_homGraph.1 (Subgroup.mem_subgroupOf.1 hz)
  have h2 : generatedProjection φ z = (a : G) := congrArg Prod.snd ha.symm
  rw [h2]
  exact mem_parabolic_singleton_iff.1 a.2

include hφ in
private theorem mem_vertexStabilizer_of_mem_vertexStabilizer_of_smul_fixed {i j : I}
    {z : generatedSubgroup φ} (hz : z ∈ vertexStabilizer φ i)
    (h : generatedProjection φ z • F j = F j) : z ∈ vertexStabilizer φ j := by
  obtain ⟨b, hb⟩ := mem_homGraph.1 (Subgroup.mem_subgroupOf.1 hz)
  have hzb : generatedProjection φ z = (b : G) := congrArg Prod.snd hb.symm
  have hbPj : (b : G) ∈ parabolic G F {j} := by
    rw [mem_parabolic_singleton_iff]
    rw [← hzb]
    exact h
  refine Subgroup.mem_subgroupOf.2 ?_
  refine mem_homGraph.2 ⟨⟨(b : G), hbPj⟩, ?_⟩
  have hbij : (b : G) ∈ parabolic G F ({i, j} : Set I) := by
    rw [mem_parabolic_iff]
    intro t ht
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · exact mem_parabolic_singleton_iff.1 b.2
    · have : t = j := Set.mem_singleton_iff.1 ht
      subst this
      exact mem_parabolic_singleton_iff.1 hbPj
  have hcomp := hφ {i} {i, j} (Set.singleton_nonempty i) (Set.insert_nonempty i {j})
    (by intro t ht; rw [Set.mem_singleton_iff] at ht; subst ht; exact Set.mem_insert _ _)
    (b : G) hbij b.2
  rw [← hb]
  exact Prod.ext (by
    have h2 := hφ {j} {i, j} (Set.singleton_nonempty j) (Set.insert_nonempty i {j})
      (by intro t ht; rw [Set.mem_singleton_iff] at ht; subst ht; exact Set.mem_insert_of_mem _ rfl)
      (b : G) hbij hbPj
    exact h2.symm.trans hcomp) rfl

private def cosetRel (x y : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) : Prop :=
  ∃ u : generatedSubgroup φ,
    (u : generatedSubgroup φ ⧸ vertexStabilizer φ x.1) = x.2 ∧
      (u : generatedSubgroup φ ⧸ vertexStabilizer φ y.1) = y.2

private def cosetGraph : SimpleGraph (Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) :=
  SimpleGraph.fromRel (cosetRel φ)

private theorem cosetGraph_adj {i j : I} {k l : generatedSubgroup φ} :
    (cosetGraph φ).Adj
        ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
        ⟨j, (l : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩ ↔
      i ≠ j ∧ ∃ u : generatedSubgroup φ,
        (u : generatedSubgroup φ ⧸ vertexStabilizer φ i) =
          (k : generatedSubgroup φ ⧸ vertexStabilizer φ i) ∧
        (u : generatedSubgroup φ ⧸ vertexStabilizer φ j) =
          (l : generatedSubgroup φ ⧸ vertexStabilizer φ j) := by
  rw [cosetGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨u, hu1, hu2⟩ := h
      have hij : i ≠ j := by
        rintro rfl
        exact hne (Sigma.ext rfl (heq_of_eq (hu1.symm.trans hu2)))
      exact ⟨hij, u, hu1, hu2⟩
    · obtain ⟨u, hu1, hu2⟩ := h
      have hij : i ≠ j := by
        rintro rfl
        exact hne (Sigma.ext rfl (heq_of_eq (hu2.symm.trans hu1)))
      exact ⟨hij, u, hu2, hu1⟩
  · rintro ⟨hij, ⟨u, hu1, hu2⟩⟩
    exact ⟨fun h => hij (congrArg Sigma.fst h), Or.inl ⟨u, hu1, hu2⟩⟩

private theorem cosetGraph_adj_mul_of_mem {i j : I} (hij : i ≠ j)
    {k : generatedSubgroup φ} {a : generatedSubgroup φ}
    (ha : a ∈ vertexStabilizer φ i) :
    (cosetGraph φ).Adj ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
      ⟨j, ((k * a : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩ := by
  rw [cosetGraph_adj]
  refine ⟨hij, k * a, ?_, rfl⟩
  rw [QuotientGroup.eq]
  simpa using (vertexStabilizer φ i).inv_mem ha

private theorem cosetGraph_adj_exists_mul {i j : I} {k : generatedSubgroup φ}
    {l : generatedSubgroup φ ⧸ vertexStabilizer φ j}
    (h : (cosetGraph φ).Adj
      ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ ⟨j, l⟩) :
    ∃ a ∈ vertexStabilizer φ i,
      l = ((k * a : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ j) := by
  obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective l
  rw [cosetGraph_adj] at h
  obtain ⟨-, u, hu1, hu2⟩ := h
  refine ⟨k⁻¹ * u, ?_, ?_⟩
  · simpa using (QuotientGroup.eq.mp hu1.symm)
  · rw [← hu2]
    congr 1
    group

private def cosetVertexMap (i : I) : generatedSubgroup φ ⧸ vertexStabilizer φ i → X :=
  cosetMap (generatedProjection φ) (vertexStabilizer φ i) (F i)
    (fun _ ha => smul_fixed_of_mem_vertexStabilizer φ ha)

private theorem cosetVertexMap_mk (i : I) (k : generatedSubgroup φ) :
    cosetVertexMap φ i (k : generatedSubgroup φ ⧸ vertexStabilizer φ i) =
      generatedProjection φ k • F i :=
  cosetMap_mk (generatedProjection φ) (vertexStabilizer φ i) (F i)
    (fun _ ha => smul_fixed_of_mem_vertexStabilizer φ ha) k

private def cosetGraphProj (x : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) : X :=
  cosetVertexMap φ x.1 x.2

private theorem cosetGraphProj_mk (i : I) (k : generatedSubgroup φ) :
    cosetGraphProj φ ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ =
      generatedProjection φ k • F i :=
  cosetVertexMap_mk φ i k

variable (hFtyp : ∀ i, typ (F i) = i)
variable (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)

private theorem cosetGraphProj_adj (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j)) {i j : I}
    {k : generatedSubgroup φ ⧸ vertexStabilizer φ i}
    {l : generatedSubgroup φ ⧸ vertexStabilizer φ j}
    (h : (cosetGraph φ).Adj ⟨i, k⟩ ⟨j, l⟩) :
    Γ.Adj (cosetGraphProj φ ⟨i, k⟩) (cosetGraphProj φ ⟨j, l⟩) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
  rw [cosetGraph_adj] at h
  obtain ⟨hij, u, hu1, hu2⟩ := h
  have hui : generatedProjection φ u • F i = generatedProjection φ k • F i := by
    have ha : k⁻¹ * u ∈ vertexStabilizer φ i := by simpa using (QuotientGroup.eq.mp hu1.symm)
    have hu : u = k * (k⁻¹ * u) := by group
    rw [hu, map_mul, mul_smul, smul_fixed_of_mem_vertexStabilizer φ ha]
  have huj : generatedProjection φ u • F j = generatedProjection φ l • F j := by
    have ha : l⁻¹ * u ∈ vertexStabilizer φ j := by simpa using (QuotientGroup.eq.mp hu2.symm)
    have hu : u = l * (l⁻¹ * u) := by group
    rw [hu, map_mul, mul_smul, smul_fixed_of_mem_vertexStabilizer φ ha]
  rw [cosetGraphProj_mk, cosetGraphProj_mk, ← hui, ← huj]
  exact hadj (generatedProjection φ u) (hFadj i j hij)

private def cosetGraphHom (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j)) : cosetGraph φ →g Γ where
  toFun := cosetGraphProj φ
  map_rel' {x y} h := by
    rcases x with ⟨i, k⟩
    rcases y with ⟨j, l⟩
    exact cosetGraphProj_adj φ hadj hFadj h

private theorem cosetGraphHom_apply (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (x : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) :
    (cosetGraphHom φ hadj hFadj) x = cosetGraphProj φ x := rfl

include hφ in
private theorem isCovering_cosetGraphHom (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F) :
    IsCovering (cosetGraphHom φ hadj hFadj) := by
  refine IsCovering.of_existsUnique ?_
  rintro ⟨i, q⟩ y hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  change Γ.Adj (cosetGraphProj φ ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩) y at hy
  rw [cosetGraphProj_mk] at hy
  set j : I := typ y with hjdef
  have htypi : typ (generatedProjection φ k • F i) = i := by rw [htyp, hFtyp]
  have hij : i ≠ j := by
    have hne := htyp_adj hy
    rw [htypi] at hne
    rwa [← hjdef] at hne
  let y0 : X := (generatedProjection φ k)⁻¹ • y
  have hy0 : Γ.Adj (F i) y0 := by
    simpa [y0] using hadj (generatedProjection φ k)⁻¹ hy
  have hy0typ : typ y0 = j := by simp [y0, htyp, hjdef]
  obtain ⟨g, hgstab, hgy⟩ :=
    exists_mem_stabilizer_smul_eq_of_adj hFtyp htyp hflag hy0
  have hgy' : g • F j = y0 := by
    rw [← hy0typ]
    exact hgy
  have hgP : g ∈ parabolic G F {i} :=
    mem_parabolic_singleton_iff.2 (MulAction.mem_stabilizer_iff.1 hgstab)
  have hgmap : g ∈ (vertexStabilizer φ i).map (generatedProjection φ) := by
    rw [map_generatedProjection_vertexStabilizer φ hφ]
    exact hgP
  obtain ⟨a, haZ, haG⟩ := Subgroup.mem_map.1 hgmap
  refine ⟨⟨j, ((k * a : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩, ?_, ?_⟩
  · refine ⟨cosetGraph_adj_mul_of_mem φ hij haZ, ?_⟩
    rw [cosetGraphHom_apply, cosetGraphProj_mk, map_mul, mul_smul, haG, hgy']
    exact smul_inv_smul (generatedProjection φ k) y
  · rintro ⟨j', l⟩ ⟨hb', hproj⟩
    rw [cosetGraphHom_apply φ hadj hFadj] at hproj
    have hj' : j' = j := by
      have h1 : typ (cosetGraphProj φ ⟨j', l⟩) = j' := by
        obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective l
        rw [cosetGraphProj_mk, htyp, hFtyp]
      rw [hproj] at h1
      exact h1.symm
    subst hj'
    obtain ⟨a', ha'vertexStabilizer, hl⟩ := cosetGraph_adj_exists_mul φ hb'
    have hproj' : generatedProjection φ k • (generatedProjection φ a' • F j) = y := by
      rw [← hproj, hl, cosetGraphProj_mk, map_mul, mul_smul]
    have ha'y : generatedProjection φ a' • F j = y0 := by
      refine MulAction.injective (generatedProjection φ k) ?_
      change generatedProjection φ k • (generatedProjection φ a' • F j) =
        (generatedProjection φ k) • ((generatedProjection φ k)⁻¹ • y)
      rw [hproj', smul_inv_smul]
    set x : G := (generatedProjection φ a')⁻¹ * g with hx
    have hxfix : x • F j = F j := by
      rw [hx, mul_smul, hgy', ← ha'y, inv_smul_smul]
    have hmemZi : a⁻¹ * a' ∈ vertexStabilizer φ i :=
      (vertexStabilizer φ i).mul_mem ((vertexStabilizer φ i).inv_mem haZ)
        ha'vertexStabilizer
    have hfix' : generatedProjection φ (a⁻¹ * a') • F j = F j := by
      have hxinv : g⁻¹ * generatedProjection φ a' = x⁻¹ := by rw [hx]; group
      rw [map_mul, map_inv, haG, hxinv]
      calc x⁻¹ • F j = x⁻¹ • (x • F j) := by rw [hxfix]
        _ = F j := inv_smul_smul x (F j)
    have hmemZj : a⁻¹ * a' ∈ vertexStabilizer φ j :=
      mem_vertexStabilizer_of_mem_vertexStabilizer_of_smul_fixed φ hφ hmemZi hfix'
    have hcoset : (l : generatedSubgroup φ ⧸ vertexStabilizer φ j) =
        ((k * a : generatedSubgroup φ) :
          generatedSubgroup φ ⧸ vertexStabilizer φ j) := by
      rw [hl]
      refine QuotientGroup.eq.mpr ?_
      have h1 : (k * a')⁻¹ * (k * a) = a'⁻¹ * a := by group
      rw [h1]
      simpa using (vertexStabilizer φ j).inv_mem hmemZj
    exact Sigma.ext rfl (heq_of_eq hcoset)

include hφ in
private theorem liftsTriangles_cosetGraphHom (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F) :
    LiftsTriangles (cosetGraphHom φ hadj hFadj) := by
  rintro ⟨i, q⟩ y z hxy hyz hzx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [cosetGraphHom_apply, cosetGraphProj_mk] at hxy hzx
  let j : I := typ y
  let l : I := typ z
  have hji : j ≠ i := by
    have h := htyp_adj hxy
    rw [htyp, hFtyp] at h
    exact h.symm
  have hli : l ≠ i := by
    have h := htyp_adj hzx
    rw [htyp, hFtyp] at h
    exact h
  have hjl : j ≠ l := htyp_adj hyz
  have hy0 : Γ.Adj (F i) ((generatedProjection φ k)⁻¹ • y) := by
    simpa using hadj (generatedProjection φ k)⁻¹ hxy
  have hyz0 : Γ.Adj ((generatedProjection φ k)⁻¹ • y) ((generatedProjection φ k)⁻¹ • z) :=
    hadj (generatedProjection φ k)⁻¹ hyz
  have hz0 : Γ.Adj ((generatedProjection φ k)⁻¹ • z) (F i) := by
    simpa using hadj (generatedProjection φ k)⁻¹ hzx
  obtain ⟨g, hgF, hgy, hgz⟩ :=
    exists_smul_eq_triangle hFtyp htyp hflag hy0 hyz0 hz0
  have hgy' : g • F j = (generatedProjection φ k)⁻¹ • y := by
    simpa [j, htyp] using hgy
  have hgz' : g • F l = (generatedProjection φ k)⁻¹ • z := by
    simpa [l, htyp] using hgz
  have hgP : g ∈ parabolic G F {i} := mem_parabolic_singleton_iff.2 hgF
  have hgmap : g ∈ (vertexStabilizer φ i).map (generatedProjection φ) := by
    rw [map_generatedProjection_vertexStabilizer φ hφ]
    exact hgP
  obtain ⟨a, haZ, haG⟩ := Subgroup.mem_map.1 hgmap
  refine ⟨⟨j, ((k * a : generatedSubgroup φ) :
      generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩,
    ⟨l, ((k * a : generatedSubgroup φ) :
      generatedSubgroup φ ⧸ vertexStabilizer φ l)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact cosetGraph_adj_mul_of_mem (i := i) (j := j) φ (Ne.symm hji) haZ
  · rw [cosetGraph_adj]
    exact ⟨hjl, k * a, rfl, rfl⟩
  · exact (cosetGraph_adj_mul_of_mem (i := i) (j := l) φ (Ne.symm hli) haZ).symm
  · rw [cosetGraphHom_apply, cosetGraphProj_mk, map_mul, mul_smul, haG, hgy']
    exact smul_inv_smul (generatedProjection φ k) y
  · rw [cosetGraphHom_apply, cosetGraphProj_mk, map_mul, mul_smul, haG, hgz']
    exact smul_inv_smul (generatedProjection φ k) z

private def cosetGraphSmul (k : generatedSubgroup φ)
    (x : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) :
    Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i :=
  ⟨x.1, k • x.2⟩

private theorem cosetGraphProj_smul (k : generatedSubgroup φ)
    (x : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i) :
    cosetGraphProj φ (cosetGraphSmul φ k x) = generatedProjection φ k • cosetGraphProj φ x := by
  rcases x with ⟨i, q⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change cosetGraphProj φ ⟨i, k • (a : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ =
    generatedProjection φ k • (generatedProjection φ a • F i)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetGraphProj_mk, map_mul, mul_smul]

private theorem closure_vertexStabilizer_eq_top :
    (⊤ : Subgroup (generatedSubgroup φ)) =
      Subgroup.closure (⋃ i : I, (vertexStabilizer φ i : Set (generatedSubgroup φ))) := by
  have h : (⋃ i : I, (vertexStabilizer φ i : Set (generatedSubgroup φ))) =
      ((↑) : generatedSubgroup φ → Y × G) ⁻¹'
        (⋃ i : I, (parabolicGraph φ {i} (Set.singleton_nonempty i) : Set (Y × G))) := by
    ext z
    simp [vertexStabilizer, Subgroup.mem_subgroupOf]
  rw [h, generatedSubgroup]
  exact Subgroup.closure_closure_coe_preimage.symm

private theorem reachable_cosetGraph_mul (i : I) (k : generatedSubgroup φ) {m : I}
    {z : generatedSubgroup φ} (hz : z ∈ vertexStabilizer φ m) :
    (cosetGraph φ).Reachable ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
      ⟨i, ((k * z : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ := by
  by_cases him : i = m
  · subst him
    have hq : ((k * z : generatedSubgroup φ) :
        generatedSubgroup φ ⧸ vertexStabilizer φ i) =
        (k : generatedSubgroup φ ⧸ vertexStabilizer φ i) := by
      rw [QuotientGroup.eq]
      simpa using hz
    rw [hq]
  · have h1 : (cosetGraph φ).Adj ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
        ⟨m, (k : generatedSubgroup φ ⧸ vertexStabilizer φ m)⟩ := by
      rw [cosetGraph_adj]
      exact ⟨him, k, rfl, rfl⟩
    have h2 : (cosetGraph φ).Adj ⟨m, (k : generatedSubgroup φ ⧸ vertexStabilizer φ m)⟩
        ⟨i, ((k * z : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ := by
      rw [cosetGraph_adj]
      refine ⟨Ne.symm him, k * z, ?_, rfl⟩
      rw [QuotientGroup.eq]
      simpa using hz
    exact h1.reachable.trans h2.reachable

private theorem reachable_cosetGraph_mk (i : I) {k : generatedSubgroup φ}
    (hk : k ∈ Subgroup.closure (⋃ m : I, (vertexStabilizer φ m : Set (generatedSubgroup φ)))) :
    (cosetGraph φ).Reachable
      ⟨i, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
      ⟨i, (k : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ := by
  induction hk using Subgroup.closure_induction_right with
  | one => exact SimpleGraph.Reachable.rfl
  | mul_right x hx y hy ih =>
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hy
    exact ih.trans (reachable_cosetGraph_mul φ i x hm)
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hy
    have hstep := reachable_cosetGraph_mul φ i (x * y⁻¹) hm
    have hxy : (x * y⁻¹ * y : generatedSubgroup φ) = x := by group
    rw [hxy] at hstep
    exact ih.trans hstep.symm

section NonemptyCoset

variable [Nonempty I]

private theorem preconnected_cosetGraph : (cosetGraph φ).Preconnected := by
  intro x y
  let i0 : I := Classical.choice ‹Nonempty I›
  rcases x with ⟨i, qx⟩
  rcases y with ⟨j, qy⟩
  obtain ⟨kx, rfl⟩ := QuotientGroup.mk_surjective qx
  obtain ⟨ky, rfl⟩ := QuotientGroup.mk_surjective qy
  have hx : (cosetGraph φ).Reachable
      ⟨i0, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0)⟩
      ⟨i, (kx : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ := by
    have hk : (cosetGraph φ).Reachable
        ⟨i, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩
        ⟨i, (kx : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ :=
      reachable_cosetGraph_mk φ i
        ((by rw [← closure_vertexStabilizer_eq_top]; exact Subgroup.mem_top kx))
    by_cases hi : i = i0
    · subst hi
      exact hk
    · have h1 : (cosetGraph φ).Adj
          ⟨i0, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0)⟩
          ⟨i, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i)⟩ := by
        rw [cosetGraph_adj]
        exact ⟨Ne.symm hi, 1, rfl, rfl⟩
      exact h1.reachable.trans hk
  have hy : (cosetGraph φ).Reachable
      ⟨i0, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0)⟩
      ⟨j, (ky : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩ := by
    have hk : (cosetGraph φ).Reachable
        ⟨j, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩
        ⟨j, (ky : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩ :=
      reachable_cosetGraph_mk φ j
        ((by rw [← closure_vertexStabilizer_eq_top]; exact Subgroup.mem_top ky))
    by_cases hj : j = i0
    · subst hj
      exact hk
    · have h1 : (cosetGraph φ).Adj
          ⟨i0, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0)⟩
          ⟨j, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ j)⟩ := by
        rw [cosetGraph_adj]
        exact ⟨Ne.symm hj, 1, rfl, rfl⟩
      exact h1.reachable.trans hk
  exact hx.symm.trans hy

include hφ in
private theorem injective_generatedProjection (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F) (htri : Triangulable Γ) :
    Function.Injective (generatedProjection φ) := by
  intro a b hab
  set c : generatedSubgroup φ := a⁻¹ * b with hc
  have hc1 : generatedProjection φ c = 1 := by
    rw [hc, map_mul, map_inv, hab, inv_mul_cancel]
  have hcov : IsCovering (cosetGraphHom φ hadj hFadj) :=
    isCovering_cosetGraphHom φ hφ hFtyp htyp htyp_adj hadj hFadj hflag
  have hlift : LiftsTriangles (cosetGraphHom φ hadj hFadj) :=
    liftsTriangles_cosetGraphHom φ hφ hFtyp htyp htyp_adj hadj hFadj hflag
  have hpre : (cosetGraph φ).Preconnected := preconnected_cosetGraph φ
  have hinj : Function.Injective (cosetGraphHom φ hadj hFadj) :=
    hcov.injective_of_triangulable hlift htri hpre
  have hfix : ∀ x : Σ i : I, generatedSubgroup φ ⧸ vertexStabilizer φ i,
      cosetGraphSmul φ c x = x := by
    intro x
    apply hinj
    rw [cosetGraphHom_apply, cosetGraphHom_apply, cosetGraphProj_smul, hc1, one_smul]
  let i0 : I := Classical.choice ‹Nonempty I›
  have hcZ : c ∈ vertexStabilizer φ i0 := by
    have h := hfix ⟨i0, ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0)⟩
    have h2 : (c : generatedSubgroup φ ⧸ vertexStabilizer φ i0) =
        ((1 : generatedSubgroup φ) : generatedSubgroup φ ⧸ vertexStabilizer φ i0) := by
      have h' := h
      simp only [cosetGraphSmul, Sigma.mk.injEq] at h'
      simpa using eq_of_heq h'.2
    have hcinv : c⁻¹ ∈ vertexStabilizer φ i0 := by
      simpa using (QuotientGroup.eq.mp h2)
    simpa using (vertexStabilizer φ i0).inv_mem hcinv
  obtain ⟨q, hq⟩ := mem_homGraph.1 (Subgroup.mem_subgroupOf.1 hcZ)
  have hcG : generatedProjection φ c = (q : G) := congrArg Prod.snd hq.symm
  have hq1 : (q : G) = 1 := by rw [← hcG, hc1]
  have hqsub : q = 1 := Subtype.ext hq1
  have hc_eq : c = 1 := by
    apply Subtype.ext
    rw [← hq, hqsub]
    simp
  have : a⁻¹ * b = 1 := by rw [← hc]; exact hc_eq
  exact inv_mul_eq_one.mp this

end NonemptyCoset

include hφ in
private theorem surjective_generatedProjection
    (hgen : (⨆ i : I, MulAction.stabilizer G (F i)) = ⊤) :
    Function.Surjective (generatedProjection φ) := by
  have htop : (⊤ : Subgroup G) ≤
      (⊤ : Subgroup (generatedSubgroup φ)).map (generatedProjection φ) := by
    rw [← hgen]
    refine iSup_le fun i => ?_
    rw [← parabolic_singleton (F := F) i, ← map_generatedProjection_vertexStabilizer φ hφ i]
    exact Subgroup.map_mono le_top
  have hmap : (⊤ : Subgroup (generatedSubgroup φ)).map (generatedProjection φ) = ⊤ :=
    top_unique htop
  intro g
  have hg : g ∈ (⊤ : Subgroup (generatedSubgroup φ)).map (generatedProjection φ) := by
    rw [hmap]; exact Subgroup.mem_top g
  obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 hg
  exact ⟨z, hz⟩

section NonemptyUniversal

variable [Nonempty I]

theorem existsUnique_hom (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F)
    (hgen : (⨆ i : I, MulAction.stabilizer G (F i)) = ⊤) (htri : Triangulable Γ)
    {Y : Type w} [Group Y] (φ : ∀ J : Set I, J.Nonempty → parabolic G F J →* Y)
    (hφ : IsCompatibleFamily G F φ) :
    ∃! ψ : G →* Y, ∀ (J : Set I) (hJ : J.Nonempty) (a : parabolic G F J),
      ψ a = φ J hJ a := by
  have hinj : Function.Injective (generatedProjection φ) :=
    injective_generatedProjection φ hφ hFtyp htyp htyp_adj hadj hFadj hflag htri
  have hsurj : Function.Surjective (generatedProjection φ) :=
    surjective_generatedProjection φ hφ hgen
  let e : generatedSubgroup φ ≃* G := MulEquiv.ofBijective (generatedProjection φ) ⟨hinj, hsurj⟩
  have he : ∀ (q : Y × G) (hq : q ∈ generatedSubgroup φ), e.symm q.2 = ⟨q, hq⟩ := fun q hq =>
    e.symm_apply_eq.2 rfl
  let Φ : G →* Y := (MonoidHom.fst Y G).comp ((generatedSubgroup φ).subtype.comp e.symm.toMonoidHom)
  have hΦ : ∀ (q : Y × G), q ∈ generatedSubgroup φ → Φ q.2 = q.1 := fun q hq => by
    change ((e.symm q.2 : generatedSubgroup φ) : Y × G).1 = q.1
    rw [he q hq]
  refine ⟨Φ, ?_, ?_⟩
  · intro J hJ a
    exact hΦ (φ J hJ a, (a : G))
      (parabolicGraph_le_generatedSubgroup φ hφ J hJ (mk_mem_homGraph (φ J hJ) a))
  · intro Ψ hΨ
    have hle : (⨆ i : I, MulAction.stabilizer G (F i)) ≤ MonoidHom.eqLocus Ψ Φ := by
      refine iSup_le fun i => ?_
      intro a ha
      have haP : a ∈ parabolic G F {i} :=
        mem_parabolic_singleton_iff.2 (MulAction.mem_stabilizer_iff.1 ha)
      have hmem : (φ {i} (Set.singleton_nonempty i) ⟨a, haP⟩, a) ∈ generatedSubgroup φ :=
        parabolicGraph_le_generatedSubgroup φ hφ {i} (Set.singleton_nonempty i)
          (mk_mem_homGraph (φ {i} (Set.singleton_nonempty i)) ⟨a, haP⟩)
      exact (hΨ {i} (Set.singleton_nonempty i) ⟨a, haP⟩).trans
        (hΦ _ hmem).symm
    rw [hgen] at hle
    exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

abbrev ParabolicIndex (I : Type u) := {J : (Set I)ᵒᵈ // (OrderDual.ofDual J).Nonempty}

theorem tits_geometry_isUniversalCompletion (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F) (hconn : Γ.Connected) (htri : Triangulable Γ) :
    IsUniversalCompletion.{v, u, w}
      (fun J : ParabolicIndex I => parabolic G F (OrderDual.ofDual J.1)) := by
  intro Y _ φ hφ
  have hgen : (⨆ i : I, MulAction.stabilizer G (F i)) = ⊤ :=
    iSup_stabilizer_eq_top_of_connected hFtyp htyp hflag hconn.preconnected
  let φ' : ∀ J : Set I, J.Nonempty → parabolic G F J →* Y :=
    fun J hJ => φ ⟨OrderDual.toDual J, hJ⟩
  have hφ' : IsCompatibleFamily G F φ' := by
    intro J K hJ hK hJK a haK haJ
    have hle : (⟨OrderDual.toDual K, hK⟩ : ParabolicIndex I) ≤
        ⟨OrderDual.toDual J, hJ⟩ := by
      change (J : Set I) ≤ K
      exact hJK
    exact hφ ⟨OrderDual.toDual K, hK⟩ ⟨OrderDual.toDual J, hJ⟩ hle
      ⟨a, haK⟩ ⟨a, haJ⟩ rfl
  obtain ⟨ψ, hψ, huniq⟩ :=
    existsUnique_hom hFtyp htyp htyp_adj hadj hFadj hflag hgen htri φ' hφ'
  refine ⟨ψ, ?_, ?_⟩
  · intro J a
    exact hψ (OrderDual.ofDual J.1) J.2 a
  · intro ψ' h'
    exact huniq ψ' (fun J hJ a => h' ⟨OrderDual.toDual J, hJ⟩ a)

end NonemptyUniversal

end Cover

end CFSG.LieType.CurtisTits