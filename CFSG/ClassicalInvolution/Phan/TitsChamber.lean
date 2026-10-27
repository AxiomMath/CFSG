module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.ClassicalInvolution.Phan.TitsChamber

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

universe u v w

variable {I : Type u} {C : Type v} {D : Type w}

inductive ElemMoveOn (X : ChamberSystem I C) (𝒥 : Set I → Prop) (x : C) :
    List (I × C) → List (I × C) → Prop
  | mk (γ₁ η η' γ₂ : List (I × C)) (J : Set I) (hJ : 𝒥 J)
      (hη : X.IsGallery (galleryEnd x γ₁) η) (hη' : X.IsGallery (galleryEnd x γ₁) η')
      (hηJ : ∀ i ∈ galleryType η, i ∈ J) (hη'J : ∀ i ∈ galleryType η', i ∈ J)
      (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
      ElemMoveOn X 𝒥 x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂)

@[expose] def HomotopicOn (X : ChamberSystem I C) (𝒥 : Set I → Prop) (x : C) :
    List (I × C) → List (I × C) → Prop :=
  Relation.EqvGen (ElemMoveOn X 𝒥 x)

@[expose] def SimplyConnectedOn (X : ChamberSystem I C) (𝒥 : Set I → Prop) : Prop :=
  ∀ (x : C) (γ : List (I × C)), X.IsGallery x γ → galleryEnd x γ = x → HomotopicOn X 𝒥 x γ []

theorem elemMove_eq (X : ChamberSystem I C) (x : C) :
    X.ElemMove x = ElemMoveOn X (fun J => J.encard ≤ 2) x := by
  funext γ γ'
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
    exact .mk γ₁ η η' γ₂ J hJ hη hη' hηJ hη'J hend
  · obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
    exact .mk γ₁ η η' γ₂ J hJ hη hη' hηJ hη'J hend

theorem simplyTwoConnected_iff (X : ChamberSystem I C) :
    X.SimplyTwoConnected ↔ SimplyConnectedOn X (fun J => J.encard ≤ 2) := by
  unfold ChamberSystem.SimplyTwoConnected SimplyConnectedOn ChamberSystem.TwoHomotopic HomotopicOn
  simp only [elemMove_eq]

namespace ElemMoveOn

variable {X : ChamberSystem I C} {𝒥 : Set I → Prop} {x : C} {γ γ' : List (I × C)}

theorem symm (h : ElemMoveOn X 𝒥 x γ γ') : ElemMoveOn X 𝒥 x γ' γ := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  exact .mk γ₁ η' η γ₂ J hJ hη' hη hη'J hηJ hend.symm

theorem isGallery_iff (h : ElemMoveOn X 𝒥 x γ γ') : X.IsGallery x γ ↔ X.IsGallery x γ' := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simp only [isGallery_append, galleryEnd_append, hend]
  tauto

theorem mono {𝒥' : Set I → Prop} (h : ∀ J, 𝒥 J → 𝒥' J) (hm : ElemMoveOn X 𝒥 x γ γ') :
    ElemMoveOn X 𝒥' x γ γ' := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := hm
  exact .mk γ₁ η η' γ₂ J (h J hJ) hη hη' hηJ hη'J hend

end ElemMoveOn

namespace HomotopicOn

variable {X : ChamberSystem I C} {𝒥 : Set I → Prop} {x : C} {γ γ' : List (I × C)}

theorem of_elemMoveOn (h : ElemMoveOn X 𝒥 x γ γ') : HomotopicOn X 𝒥 x γ γ' :=
  Relation.EqvGen.rel _ _ h

theorem reflTransGen_symm (h : Relation.ReflTransGen (ElemMoveOn X 𝒥 x) γ γ') :
    Relation.ReflTransGen (ElemMoveOn X 𝒥 x) γ' γ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact Relation.ReflTransGen.head h.symm ih

theorem iff_reflTransGen :
    HomotopicOn X 𝒥 x γ γ' ↔ Relation.ReflTransGen (ElemMoveOn X 𝒥 x) γ γ' := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .single h
    | refl => exact .refl
    | symm _ _ _ ih => exact reflTransGen_symm ih
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail _ h ih => exact Relation.EqvGen.trans _ _ _ ih (of_elemMoveOn h)

theorem isGallery_iff (h : HomotopicOn X 𝒥 x γ γ') : X.IsGallery x γ ↔ X.IsGallery x γ' := by
  induction h with
  | rel _ _ h => exact h.isGallery_iff
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem mono {𝒥' : Set I → Prop} (h : ∀ J, 𝒥 J → 𝒥' J) (hh : HomotopicOn X 𝒥 x γ γ') :
    HomotopicOn X 𝒥' x γ γ' := by
  induction hh with
  | rel _ _ h' => exact of_elemMoveOn (h'.mono h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

end HomotopicOn

theorem SimplyConnectedOn.mono {X : ChamberSystem I C} {𝒥 𝒥' : Set I → Prop}
    (h : ∀ J, 𝒥 J → 𝒥' J) (hS : SimplyConnectedOn X 𝒥) : SimplyConnectedOn X 𝒥' :=
  fun x γ hγ hend => (hS x γ hγ hend).mono h

theorem homotopicOn_replace {X : ChamberSystem I C} {𝒥 : Set I → Prop} {x : C}
    (γ₁ η η' γ₂ : List (I × C)) {J : Set I} (hJ : 𝒥 J)
    (hη : X.IsGallery (galleryEnd x γ₁) η) (hη' : X.IsGallery (galleryEnd x γ₁) η')
    (hηJ : ∀ i ∈ galleryType η, i ∈ J) (hη'J : ∀ i ∈ galleryType η', i ∈ J)
    (hend : galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η') :
    HomotopicOn X 𝒥 x (γ₁ ++ η ++ γ₂) (γ₁ ++ η' ++ γ₂) :=
  .of_elemMoveOn (.mk γ₁ η η' γ₂ J hJ hη hη' hηJ hη'J hend)

section Cover

variable {X : ChamberSystem I C} {Y : ChamberSystem I D} {q : D → C}

theorem galleryEnd_liftGallery_eqOn
    (hq : ∀ i d, Set.BijOn q (Y.residue {i} d) (X.residue {i} (q d)))
    {𝒥 : Set I → Prop} (hinj : ∀ J, 𝒥 J → ∀ d, Set.InjOn q (Y.residue J d))
    {d : D} {γ γ' : List (I × C)} (h : HomotopicOn X 𝒥 (q d) γ γ') (hγ : X.IsGallery (q d) γ) :
    galleryEnd d (liftGallery Y q d γ) = galleryEnd d (liftGallery Y q d γ') := by
  rw [HomotopicOn.iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail γ₁ γ₂ h12 hm ih =>
    rw [ih]
    have hγ₁ : X.IsGallery (q d) γ₁ :=
      (HomotopicOn.iff_reflTransGen.mpr h12 |>.isGallery_iff).mp hγ
    clear ih h12
    obtain ⟨α, η, η', β, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := hm
    rw [List.append_assoc] at hγ₁
    have hα := hγ₁.of_append_left
    set e := galleryEnd d (liftGallery Y q d α) with he
    have hqe : q e = galleryEnd (q d) α := galleryEnd_liftGallery hq hα
    rw [← hqe] at hη hη' hend
    obtain ⟨hl1, -⟩ := isGallery_liftGallery hq hη
    obtain ⟨hl1', -⟩ := isGallery_liftGallery hq hη'
    have key : galleryEnd e (liftGallery Y q e η) = galleryEnd e (liftGallery Y q e η') := by
      refine hinj J hJ e (galleryEnd_mem_residue hl1 (by simpa using hηJ))
        (galleryEnd_mem_residue hl1' (by simpa using hη'J)) ?_
      rw [galleryEnd_liftGallery hq hη, galleryEnd_liftGallery hq hη', hend]
    simp only [liftGallery_append, galleryEnd_append, ← he, key]

theorem eq_of_galleryEnd_of_simplyConnectedOn {𝒥 : Set I → Prop} (hS : SimplyConnectedOn X 𝒥)
    (hq : ∀ i d, Set.BijOn q (Y.residue {i} d) (X.residue {i} (q d)))
    (hinj : ∀ J, 𝒥 J → ∀ d, Set.InjOn q (Y.residue J d)) {x : D} {Δ : List (I × D)}
    (hΔ : Y.IsGallery x Δ) (h : q (galleryEnd x Δ) = q x) : galleryEnd x Δ = x := by
  have hqm : IsMorphism Y X q := fun i d e h =>
    mem_residue_singleton.mp ((hq i d).mapsTo (mem_residue_singleton.mpr h))
  have hγ : X.IsGallery (q x) (galleryMap q Δ) := hqm.isGallery hΔ
  have hend : galleryEnd (q x) (galleryMap q Δ) = q x := by rw [galleryEnd_galleryMap, h]
  have key := galleryEnd_liftGallery_eqOn hq hinj (hS (q x) _ hγ hend) hγ
  rw [liftGallery_galleryMap hq hΔ] at key
  simpa using key

end Cover

section Coset

variable {A : Type*} [Group A] (B : Subgroup A) (Q : I → Subgroup A)

def cosetAdj (i : I) (x y : A ⧸ B) : Prop :=
  ∃ a b : A, (a : A ⧸ B) = x ∧ (b : A ⧸ B) = y ∧ a⁻¹ * b ∈ Q i

variable {B Q}

theorem cosetAdj_mk (hQ : ∀ i, B ≤ Q i) {i : I} {a b : A} :
    cosetAdj B Q i (a : A ⧸ B) b ↔ a⁻¹ * b ∈ Q i := by
  refine ⟨?_, fun h => ⟨a, b, rfl, rfl, h⟩⟩
  rintro ⟨a', b', ha, hb, h⟩
  rw [QuotientGroup.eq] at ha hb
  have e : a⁻¹ * b = (a'⁻¹ * a)⁻¹ * (a'⁻¹ * b') * (b'⁻¹ * b) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (hQ i ha)) h) (hQ i hb)

variable (B Q)

def cosetSystem (hQ : ∀ i, B ≤ Q i) : ChamberSystem I (A ⧸ B) where
  adj := cosetAdj B Q
  equivalence _ :=
    { refl := fun x => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        exact (cosetAdj_mk hQ).mpr (by simp)
      symm := fun {x y} h => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        rw [cosetAdj_mk hQ] at h ⊢
        simpa using inv_mem h
      trans := fun {x y z} h h' => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
        rw [cosetAdj_mk hQ] at h h' ⊢
        simpa using mul_mem h h' }

variable {B Q}

theorem cosetSystem_adj_mk (hQ : ∀ i, B ≤ Q i) {i : I} {a b : A} :
    (cosetSystem B Q hQ).adj i (a : A ⧸ B) b ↔ a⁻¹ * b ∈ Q i :=
  cosetAdj_mk hQ

theorem exists_mem_of_mem_residue (hQ : ∀ i, B ≤ Q i) (S : Subgroup A) {J : Set I}
    (hS : ∀ j ∈ J, Q j ≤ S) (a : A) {y : A ⧸ B}
    (hy : y ∈ (cosetSystem B Q hQ).residue J (a : A ⧸ B)) :
    ∃ s ∈ S, y = ((a * s : A) : A ⧸ B) := by
  obtain ⟨γ, hγ, hJ, rfl⟩ := hy
  induction γ generalizing a with
  | nil => exact ⟨1, one_mem S, by simp⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective p.2
    rw [← hb, cosetSystem_adj_mk hQ] at h1
    have hp : p.1 ∈ J := hJ p.1 (by simp)
    obtain ⟨s', hs', hend⟩ := ih b (hb ▸ h2) (fun i hi => hJ i (by simp [hi]))
    refine ⟨a⁻¹ * b * s', mul_mem (hS _ hp h1) hs', ?_⟩
    rw [galleryEnd_cons, ← hb, hend]
    simp [mul_assoc]

end Coset

section Parabolics

structure Data (X : ChamberSystem I C) (𝒥 : Set I → Prop) (G : Type*) (Y : Type*)
    [Group G] [Group Y] [MulAction G C] where
  c₀ : C
  adj_smul : ∀ (g : G) (i : I) (x y : C), X.adj i x y → X.adj i (g • x) (g • y)
  exists_smul : ∀ c : C, ∃ g : G, g • c₀ = c
  P : Set I → Subgroup G
  mem_P : ∀ J : Set I, 𝒥 J → ∀ g : G, g ∈ P J ↔ g • c₀ ∈ X.residue J c₀
  φ : ∀ J : Set I, 𝒥 J → P J →* Y
  compat : ∀ (J K : Set I) (hJ : 𝒥 J) (hK : 𝒥 K), K ⊆ J → ∀ (g : G) (hgK : g ∈ P K)
    (hgJ : g ∈ P J), φ K hK ⟨g, hgK⟩ = φ J hJ ⟨g, hgJ⟩
  empty_mem : 𝒥 ∅
  singleton_mem : ∀ i : I, 𝒥 {i}

namespace Data

variable {X : ChamberSystem I C} {𝒥 : Set I → Prop} {G Y : Type*} [Group G] [Group Y]
  [MulAction G C] (T : Data X 𝒥 G Y)

def graph (J : Set I) (hJ : 𝒥 J) : Subgroup (G × Y) :=
  ((T.P J).subtype.prod (T.φ J hJ)).range

theorem mem_graph {J : Set I} {hJ : 𝒥 J} {k : G × Y} :
    k ∈ T.graph J hJ ↔ ∃ hk : k.1 ∈ T.P J, k.2 = T.φ J hJ ⟨k.1, hk⟩ := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.2, rfl⟩
  · rintro ⟨hk, h2⟩
    exact ⟨⟨k.1, hk⟩, Prod.ext rfl h2.symm⟩

theorem P_mono {J K : Set I} (hJ : 𝒥 J) (hK : 𝒥 K) (h : K ⊆ J) : T.P K ≤ T.P J := fun g hg =>
  (T.mem_P J hJ g).2 (residue_mono h _ ((T.mem_P K hK g).1 hg))

theorem graph_mono {J K : Set I} (hJ : 𝒥 J) (hK : 𝒥 K) (h : K ⊆ J) :
    T.graph K hK ≤ T.graph J hJ := by
  intro k hk
  obtain ⟨hk1, hk2⟩ := (T.mem_graph).1 hk
  exact (T.mem_graph).2 ⟨T.P_mono hJ hK h hk1, by rw [hk2]; exact T.compat J K hJ hK h _ _ _⟩

theorem mem_P_empty {g : G} : g ∈ T.P ∅ ↔ g • T.c₀ = T.c₀ := by
  rw [T.mem_P ∅ T.empty_mem, residue_empty, Set.mem_singleton_iff]

def cover : ChamberSystem I ((G × Y) ⧸ T.graph ∅ T.empty_mem) :=
  cosetSystem _ (fun i => T.graph {i} (T.singleton_mem i))
    (fun _ => T.graph_mono _ _ (Set.empty_subset _))

abbrev Chamber : Type _ := (G × Y) ⧸ T.graph ∅ T.empty_mem

@[expose] def proj : T.Chamber → C :=
  Quotient.lift (s := QuotientGroup.leftRel (T.graph ∅ T.empty_mem))
    (fun k : G × Y => k.1 • T.c₀) fun a b hab => by
      obtain ⟨hk, -⟩ := (T.mem_graph).1 (QuotientGroup.leftRel_apply.mp hab)
      have h1 := (T.mem_P_empty).1 hk
      simp only [Prod.fst_mul, Prod.fst_inv, mul_smul] at h1
      calc a.1 • T.c₀ = a.1 • (a.1⁻¹ • b.1 • T.c₀) := by rw [h1]
        _ = b.1 • T.c₀ := smul_inv_smul _ _

theorem proj_mk (k : G × Y) : T.proj (k : T.Chamber) = k.1 • T.c₀ := rfl

theorem cover_adj_mk {i : I} {a b : G × Y} :
    T.cover.adj i (a : T.Chamber) b ↔ a⁻¹ * b ∈ T.graph {i} (T.singleton_mem i) :=
  cosetSystem_adj_mk _

include T in
theorem isMorphism_smul (g : G) : IsMorphism X X (g • ·) :=
  fun i x y h => T.adj_smul g i x y h

theorem isMorphism_proj : IsMorphism T.cover X T.proj := by
  intro i x y h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [cover_adj_mk] at h
  obtain ⟨hk, -⟩ := (T.mem_graph).1 h
  have h1 : (a⁻¹ * b).1 • T.c₀ ∈ X.residue {i} T.c₀ := (T.mem_P _ (T.singleton_mem i) _).1 hk
  rw [mem_residue_singleton] at h1
  have h2 := T.adj_smul a.1 i _ _ h1
  rw [proj_mk, proj_mk]
  simpa [mul_smul] using h2

theorem mk_eq_of_smul_eq {J : Set I} {hJ : 𝒥 J} {k s s' : G × Y} (hs : s ∈ T.graph J hJ)
    (hs' : s' ∈ T.graph J hJ) (h : (k * s).1 • T.c₀ = (k * s').1 • T.c₀) :
    ((k * s : G × Y) : T.Chamber) = ((k * s' : G × Y) : T.Chamber) := by
  rw [QuotientGroup.eq]
  have e : (k * s)⁻¹ * (k * s') = s⁻¹ * s' := by group
  rw [e]
  have h' : s.1 • T.c₀ = s'.1 • T.c₀ := by
    simp only [Prod.fst_mul, mul_smul] at h
    exact MulAction.injective k.1 h
  have h1 : (s⁻¹ * s').1 ∈ T.P ∅ := by
    rw [T.mem_P_empty]
    simp only [Prod.fst_mul, Prod.fst_inv, mul_smul]
    rw [← h', inv_smul_smul]
  obtain ⟨hk, h2⟩ := (T.mem_graph).1 (mul_mem (inv_mem hs) hs')
  refine (T.mem_graph).2 ⟨h1, ?_⟩
  rw [h2]
  exact (T.compat J ∅ hJ T.empty_mem (Set.empty_subset _) _ h1 hk).symm

theorem injOn_proj_residue {J : Set I} (hJ : 𝒥 J) (x : T.Chamber) :
    Set.InjOn T.proj (T.cover.residue J x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  intro y hy y' hy' hyy'
  have hS : ∀ j ∈ J, T.graph {j} (T.singleton_mem j) ≤ T.graph J hJ := fun j hj =>
    T.graph_mono hJ _ (Set.singleton_subset_iff.2 hj)
  obtain ⟨s, hs, rfl⟩ := exists_mem_of_mem_residue _ (T.graph J hJ) hS a hy
  obtain ⟨s', hs', rfl⟩ := exists_mem_of_mem_residue _ (T.graph J hJ) hS a hy'
  exact T.mk_eq_of_smul_eq hs hs' hyy'

theorem bijOn_proj_panel (i : I) (x : T.Chamber) :
    Set.BijOn T.proj (T.cover.residue {i} x) (X.residue {i} (T.proj x)) := by
  refine ⟨T.isMorphism_proj.mapsTo_residue {i} x, T.injOn_proj_residue (T.singleton_mem i) x, ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  intro z hz
  rw [mem_residue_singleton] at hz
  have h1 := T.adj_smul a.1⁻¹ i _ _ hz
  rw [proj_mk, inv_smul_smul] at h1
  obtain ⟨u, hu⟩ := T.exists_smul (a.1⁻¹ • z)
  have hu' : u ∈ T.P {i} :=
    (T.mem_P _ (T.singleton_mem i) _).2 (mem_residue_singleton.2 (hu ▸ h1))
  have hs : (u, T.φ {i} (T.singleton_mem i) ⟨u, hu'⟩) ∈ T.graph {i} (T.singleton_mem i) :=
    (T.mem_graph).2 ⟨hu', rfl⟩
  refine ⟨((a * (u, T.φ {i} (T.singleton_mem i) ⟨u, hu'⟩) : G × Y) : T.Chamber), ?_, ?_⟩
  · rw [mem_residue_singleton, cover_adj_mk]
    simpa using hs
  · rw [proj_mk]
    show (a.1 * u) • T.c₀ = z
    rw [mul_smul, hu, smul_inv_smul]

theorem mk_mul_mem_residue {J : Set I} (hJ : 𝒥 J) {s : G × Y} (hs : s ∈ T.graph J hJ)
    (k : G × Y) : ((k * s : G × Y) : T.Chamber) ∈ T.cover.residue J (k : T.Chamber) := by
  obtain ⟨hs1, -⟩ := (T.mem_graph).1 hs
  obtain ⟨γ, hγ, hJγ, hend⟩ := (T.mem_P J hJ s.1).1 hs1
  have hγ' : X.IsGallery (T.proj (k : T.Chamber)) (galleryMap (k.1 • ·) γ) :=
    (T.isMorphism_smul k.1).isGallery hγ
  have hend' : galleryEnd (T.proj (k : T.Chamber)) (galleryMap (k.1 • ·) γ) =
      (k * s).1 • T.c₀ := by
    rw [proj_mk, galleryEnd_galleryMap, hend, Prod.fst_mul, mul_smul]
  obtain ⟨hL, -⟩ := isGallery_liftGallery T.bijOn_proj_panel hγ'
  have hy : galleryEnd (k : T.Chamber) (liftGallery T.cover T.proj (k : T.Chamber)
      (galleryMap (k.1 • ·) γ)) ∈ T.cover.residue J (k : T.Chamber) :=
    galleryEnd_mem_residue hL (by simpa using hJγ)
  have hpy : T.proj (galleryEnd (k : T.Chamber) (liftGallery T.cover T.proj (k : T.Chamber)
      (galleryMap (k.1 • ·) γ))) = (k * s).1 • T.c₀ := by
    rw [galleryEnd_liftGallery T.bijOn_proj_panel hγ', hend']
  have hS : ∀ j ∈ J, T.graph {j} (T.singleton_mem j) ≤ T.graph J hJ := fun j hj =>
    T.graph_mono hJ _ (Set.singleton_subset_iff.2 hj)
  obtain ⟨s', hs', hys'⟩ := exists_mem_of_mem_residue _ (T.graph J hJ) hS k hy
  have hmk : ((k * s : G × Y) : T.Chamber) = ((k * s' : G × Y) : T.Chamber) :=
    T.mk_eq_of_smul_eq hs hs' (by rw [← hpy, hys']; rfl)
  rw [hmk, ← hys']
  exact hy

def gen : Subgroup (G × Y) :=
  Subgroup.closure {k | ∃ (J : Set I) (hJ : 𝒥 J), k ∈ T.graph J hJ}

theorem graph_le_gen (J : Set I) (hJ : 𝒥 J) : T.graph J hJ ≤ T.gen := fun _ hk =>
  Subgroup.subset_closure ⟨J, hJ, hk⟩

theorem mk_mem_residue_univ {h : G × Y} (hh : h ∈ T.gen) :
    (h : T.Chamber) ∈ T.cover.residue Set.univ ((1 : G × Y) : T.Chamber) := by
  induction hh using Subgroup.closure_induction_right with
  | one => exact self_mem_residue _ _
  | mul_right x _ y hy ih =>
    obtain ⟨J, hJ, hy⟩ := hy
    exact mem_residue_trans ih
      (residue_mono (Set.subset_univ J) _ (T.mk_mul_mem_residue hJ hy x))
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨J, hJ, hy⟩ := hy
    exact mem_residue_trans ih
      (residue_mono (Set.subset_univ J) _ (T.mk_mul_mem_residue hJ (inv_mem hy) x))

theorem mk_eq_one (hS : SimplyConnectedOn X 𝒥) {h : G × Y} (hh : h ∈ T.gen)
    (hproj : h.1 • T.c₀ = T.c₀) : (h : T.Chamber) = ((1 : G × Y) : T.Chamber) := by
  obtain ⟨Δ, hΔ, -, hend⟩ := T.mk_mem_residue_univ hh
  have key := eq_of_galleryEnd_of_simplyConnectedOn hS T.bijOn_proj_panel
    (fun J hJ x => T.injOn_proj_residue hJ x) hΔ
    (by rw [hend, proj_mk, proj_mk]; simpa using hproj)
  rw [← hend]
  exact key

theorem eq_one_of_fst_eq_one (hS : SimplyConnectedOn X 𝒥) {h : G × Y} (hh : h ∈ T.gen)
    (h1 : h.1 = 1) : h = 1 := by
  have hm := (T.mk_eq_one hS hh (by rw [h1, one_smul])).symm
  rw [QuotientGroup.eq, inv_one, one_mul] at hm
  obtain ⟨hk, h2⟩ := (T.mem_graph).1 hm
  refine Prod.ext h1 ?_
  rw [h2, show (⟨h.1, hk⟩ : T.P ∅) = 1 from Subtype.ext h1, map_one]
  rfl

theorem exists_mem_gen_fst_eq (hX : X.Connected) (g : G) : ∃ h ∈ T.gen, h.1 = g := by
  obtain ⟨γ, hγ, hend⟩ := hX T.c₀ (g • T.c₀)
  have h1 : T.proj ((1 : G × Y) : T.Chamber) = T.c₀ := one_smul G T.c₀
  have hγ' : X.IsGallery (T.proj ((1 : G × Y) : T.Chamber)) γ := h1 ▸ hγ
  obtain ⟨hL, -⟩ := isGallery_liftGallery T.bijOn_proj_panel hγ'
  have hpy : T.proj (galleryEnd ((1 : G × Y) : T.Chamber)
      (liftGallery T.cover T.proj ((1 : G × Y) : T.Chamber) γ)) = g • T.c₀ := by
    rw [galleryEnd_liftGallery T.bijOn_proj_panel hγ', h1, hend]
  have hyres := galleryEnd_mem_residue (J := Set.univ) hL (fun _ _ => Set.mem_univ _)
  obtain ⟨h, hh, hyh⟩ := exists_mem_of_mem_residue _ T.gen
    (fun j _ => T.graph_le_gen {j} (T.singleton_mem j)) 1 hyres
  rw [one_mul] at hyh
  have hhg : h.1 • T.c₀ = g • T.c₀ := by rw [← hpy, hyh]; rfl
  have hu : h.1⁻¹ * g ∈ T.P ∅ := by
    rw [T.mem_P_empty, mul_smul, ← hhg, inv_smul_smul]
  have hmem : (h.1⁻¹ * g, T.φ ∅ T.empty_mem ⟨h.1⁻¹ * g, hu⟩) ∈ T.graph ∅ T.empty_mem :=
    (T.mem_graph).2 ⟨hu, rfl⟩
  exact ⟨h * (h.1⁻¹ * g, T.φ ∅ T.empty_mem ⟨h.1⁻¹ * g, hu⟩),
    mul_mem hh (T.graph_le_gen _ _ hmem), by simp⟩

def pr : T.gen →* G := (MonoidHom.fst G Y).comp T.gen.subtype

theorem pr_bijective (hX : X.Connected) (hS : SimplyConnectedOn X 𝒥) :
    Function.Bijective T.pr := by
  refine ⟨(injective_iff_map_eq_one T.pr).2 fun h hh => ?_, fun g => ?_⟩
  · exact Subtype.ext (T.eq_one_of_fst_eq_one hS h.2 hh)
  · obtain ⟨h, hh, hg⟩ := T.exists_mem_gen_fst_eq hX g
    exact ⟨⟨h, hh⟩, hg⟩

noncomputable def lift (hX : X.Connected) (hS : SimplyConnectedOn X 𝒥) : G →* Y :=
  ((MonoidHom.snd G Y).comp T.gen.subtype).comp
    (MulEquiv.ofBijective T.pr (T.pr_bijective hX hS)).symm.toMonoidHom

theorem lift_apply (hX : X.Connected) (hS : SimplyConnectedOn X 𝒥) {J : Set I} (hJ : 𝒥 J)
    (g : T.P J) : T.lift hX hS g = T.φ J hJ g := by
  have hmem : ((g : G), T.φ J hJ g) ∈ T.gen := T.graph_le_gen J hJ ((T.mem_graph).2 ⟨g.2, rfl⟩)
  have : (MulEquiv.ofBijective T.pr (T.pr_bijective hX hS)).symm (g : G) =
      ⟨((g : G), T.φ J hJ g), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp [lift, this]

theorem lift_unique (hX : X.Connected) (hS : SimplyConnectedOn X 𝒥) {ψ : G →* Y}
    (h : ∀ (J : Set I) (hJ : 𝒥 J) (g : T.P J), ψ g = T.φ J hJ g) : ψ = T.lift hX hS := by
  have hle : T.gen ≤ MonoidHom.eqLocus (ψ.comp (MonoidHom.fst G Y)) (MonoidHom.snd G Y) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨J, hJ, hk⟩
    obtain ⟨hk1, hk2⟩ := (T.mem_graph).1 hk
    show ψ k.1 = k.2
    rw [hk2]
    exact h J hJ ⟨k.1, hk1⟩
  ext g
  set e := MulEquiv.ofBijective T.pr (T.pr_bijective hX hS)
  have h1 : ψ (e.symm g).1.1 = (e.symm g).1.2 := hle (e.symm g).2
  have h2 : (e.symm g).1.1 = g := e.apply_symm_apply g
  rw [h2] at h1
  rw [h1]
  rfl

end Data

end Parabolics

end CFSG.ClassicalInvolution.Phan.TitsChamber

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

theorem tits_chamber_universal_completion_of_family
    {I : Type*} {C : Type*} (X : ChamberSystem I C) (𝒥 : Set I → Prop) (hempty : 𝒥 ∅)
    (hsing : ∀ i : I, 𝒥 {i}) (hX : X.Connected) (hS : TitsChamber.SimplyConnectedOn X 𝒥)
    {G : Type*} [Group G] [MulAction G C]
    (hadj : ∀ (g : G) (i : I) (x y : C), X.adj i x y → X.adj i (g • x) (g • y))
    (c₀ : C) (htrans : ∀ c : C, ∃ g : G, g • c₀ = c)
    (P : Set I → Subgroup G)
    (hP : ∀ J : Set I, 𝒥 J → ∀ g : G, g ∈ P J ↔ g • c₀ ∈ X.residue J c₀)
    {Y : Type*} [Group Y] (φ : ∀ J : Set I, 𝒥 J → P J →* Y)
    (hφ : ∀ (J K : Set I) (hJ : 𝒥 J) (hK : 𝒥 K), K ⊆ J → ∀ (g : G) (hgK : g ∈ P K)
      (hgJ : g ∈ P J), φ K hK ⟨g, hgK⟩ = φ J hJ ⟨g, hgJ⟩) :
    ∃! ψ : G →* Y, ∀ (J : Set I) (hJ : 𝒥 J) (g : P J), ψ g = φ J hJ g :=
  let T : TitsChamber.Data X 𝒥 G Y := ⟨c₀, hadj, htrans, P, hP, φ, hφ, hempty, hsing⟩
  ⟨T.lift hX hS, fun _ hJ g => T.lift_apply hX hS hJ g, fun _ h => T.lift_unique hX hS h⟩

theorem tits_chamber_universal_completion
    {I C : Type*} (X : ChamberSystem I C) (hX : X.Connected) (hS : X.SimplyTwoConnected)
    {G : Type*} [Group G] (ρ : G →* X.typeAut) (c₀ : C)
    (htrans : ∀ c : C, ∃ g : G, ((ρ g : X.typeAut) : Equiv.Perm C) c₀ = c)
    (P : Set I → Subgroup G)
    (hP : ∀ J : Set I, J.encard ≤ 2 → ∀ g : G,
      g ∈ P J ↔ ((ρ g : X.typeAut) : Equiv.Perm C) c₀ ∈ X.residue J c₀)
    {Y : Type*} [Group Y] (φ : ∀ J : Set I, J.encard ≤ 2 → P J →* Y)
    (hφ : ∀ (J K : Set I) (hJ : J.encard ≤ 2) (hK : K.encard ≤ 2), K ⊆ J → ∀ (g : G)
      (hgK : g ∈ P K) (hgJ : g ∈ P J), φ K hK ⟨g, hgK⟩ = φ J hJ ⟨g, hgJ⟩) :
    ∃! ψ : G →* Y, ∀ (J : Set I) (hJ : J.encard ≤ 2) (g : P J), ψ g = φ J hJ g := by
  let _ : MulAction G C := MulAction.compHom C (X.typeAut.subtype.comp ρ)
  exact tits_chamber_universal_completion_of_family X (fun J => J.encard ≤ 2)
    (by simp) (fun i => encard_singleton_le_two i) hX
    ((TitsChamber.simplyTwoConnected_iff X).1 hS)
    (fun g i x y h => ((ρ g).2 i x y).2 h) c₀ htrans P hP φ hφ

end CFSG.ClassicalInvolution.Phan
