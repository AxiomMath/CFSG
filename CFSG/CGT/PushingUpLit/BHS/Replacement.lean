module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.G6PGroup
public import Mathlib

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.B1

variable {V : Type*} [CommGroup V]

@[expose] def cenIn (A : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {a | a ∈ A ∧ ∀ u ∈ U, a u = u}
  one_mem' := ⟨A.one_mem, fun u _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    exact ⟨A.mul_mem ha hb, fun u hu => by rw [MulAut.mul_apply, hfb u hu, hfa u hu]⟩
  inv_mem' := by
    rintro a ⟨ha, hfa⟩
    refine ⟨A.inv_mem ha, fun u hu => ?_⟩
    calc a⁻¹ u = a⁻¹ (a u) := by rw [hfa u hu]
      _ = u := by simp

theorem mem_cenIn {A : Subgroup (MulAut V)} {U : Subgroup V} {a : MulAut V} :
    a ∈ cenIn A U ↔ a ∈ A ∧ ∀ u ∈ U, a u = u := Iff.rfl

theorem cenIn_le (A : Subgroup (MulAut V)) (U : Subgroup V) : cenIn A U ≤ A := fun _ h => h.1

@[expose] def commSet (A : Subgroup (MulAut V)) (S : Set V) : Subgroup V :=
  Subgroup.closure {w | ∃ a ∈ A, ∃ s ∈ S, a s * s⁻¹ = w}

@[expose] def commOn (U : Subgroup V) (A : Subgroup (MulAut V)) : Subgroup V :=
  commSet A (U : Set V)

@[expose] noncomputable def wt (A : Subgroup (MulAut V)) : ℕ := Nat.card A * Nat.card (fixV A)

theorem commSet_univ (A : Subgroup (MulAut V)) : commSet A Set.univ = commV A := by
  unfold commSet commV
  congr 1
  ext w
  simp

theorem commOn_top (A : Subgroup (MulAut V)) : commOn ⊤ A = commV A := by
  rw [commOn, Subgroup.coe_top, commSet_univ]

theorem mem_commSet_of_mem {A : Subgroup (MulAut V)} {S : Set V} {a : MulAut V} (ha : a ∈ A)
    {s : V} (hs : s ∈ S) : a s * s⁻¹ ∈ commSet A S :=
  Subgroup.subset_closure ⟨a, ha, s, hs, rfl⟩

theorem commSet_union (A : Subgroup (MulAut V)) (S T : Set V) :
    commSet A (S ∪ T) = commSet A S ⊔ commSet A T := by
  unfold commSet
  rw [← Subgroup.closure_union]
  congr 1
  ext w
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, s, hs | hs, rfl⟩
    · exact Or.inl ⟨a, ha, s, hs, rfl⟩
    · exact Or.inr ⟨a, ha, s, hs, rfl⟩
  · rintro (⟨a, ha, s, hs, rfl⟩ | ⟨a, ha, s, hs, rfl⟩)
    · exact ⟨a, ha, s, Or.inl hs, rfl⟩
    · exact ⟨a, ha, s, Or.inr hs, rfl⟩

theorem commSet_empty (A : Subgroup (MulAut V)) : commSet A ∅ = ⊥ := by
  unfold commSet
  rw [eq_bot_iff, Subgroup.closure_le]
  rintro w ⟨a, ha, s, hs, rfl⟩
  exact absurd hs (Set.notMem_empty s)

theorem mem_fixV_iff_le {X : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV X ↔ X ≤ MulAction.stabilizer (MulAut V) v := by
  constructor
  · intro h x hx
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h x hx
  · intro h x hx
    have := h hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem fixV_sup (X Y : Subgroup (MulAut V)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y


section Commuting

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup' {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have : x * n * x⁻¹ = n := by rw [h x hx n hn]; group
      rwa [this]
    · intro hn
      have h1 := h x hx _ hn
      have : x * n * x⁻¹ = n := by
        have h2 : x * (x * n * x⁻¹) = x * n := by rw [h1]; group
        exact mul_left_cancel h2
      rwa [this] at hn
  have hg' : g ∈ (↑(X ⊔ Y) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem card_sup_mul_card_inf' [Finite G] {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  let φ : X × Y →* G := X.subtype.noncommCoprod Y.subtype (fun x y => h x x.2 y y.2)
  have hφ : ∀ (x : X) (y : Y), φ (x, y) = (x : G) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hrange : φ.range = X ⊔ Y := by
    ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact Subgroup.mul_mem_sup x.2 y.2
    · intro hg
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup' h hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hφ _ _⟩
  have hker : Nat.card φ.ker = Nat.card (X ⊓ Y : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : G), k.1.1.2, by
          have h1 : (k.1.1 : G) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          have h2 : (k.1.1 : G) = (k.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [h2]
          exact Y.inv_mem k.1.2.2⟩
        invFun := fun g => ⟨(⟨g, g.2.1⟩, ⟨(g : G)⁻¹, Y.inv_mem g.2.2⟩), by
          rw [MonoidHom.mem_ker, hφ]
          exact mul_inv_cancel _⟩
        left_inv := fun k => by
          refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext ?_))
          have h1 : (k.1.1 : G) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          exact inv_eq_of_mul_eq_one_right h1
        right_inv := fun g => Subtype.ext rfl }
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h

end Commuting


section Main

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

@[expose] def fixEl (a : MulAut V) : Subgroup V where
  carrier := {w | a w = w}
  one_mem' := map_one a
  mul_mem' := fun {x y} hx hy => by
    have hx' : a x = x := hx
    have hy' : a y = y := hy
    show a (x * y) = x * y
    rw [map_mul, hx', hy']
  inv_mem' := fun {x} hx => by
    have hx' : a x = x := hx
    show a x⁻¹ = x⁻¹
    rw [map_inv, hx']

theorem mem_fixEl {a : MulAut V} {w : V} : w ∈ fixEl a ↔ a w = w := Iff.rfl

theorem mem_cenIn_iff {A : Subgroup (MulAut V)} {U : Subgroup V} {a : MulAut V} :
    a ∈ cenIn A U ↔ a ∈ A ∧ U ≤ fixEl a :=
  ⟨fun h => ⟨h.1, fun _ hu => h.2 _ hu⟩, fun h => ⟨h.1, fun _ hu => h.2 hu⟩⟩

theorem commSet_le_fixEl_iff {A : Subgroup (MulAut V)} {S : Set V} {a : MulAut V} :
    commSet A S ≤ fixEl a ↔ ∀ b ∈ A, ∀ s ∈ S, a (b s * s⁻¹) = b s * s⁻¹ := by
  unfold commSet
  rw [Subgroup.closure_le]
  constructor
  · intro h b hb s hs
    exact h ⟨b, hb, s, hs, rfl⟩
  · rintro h w ⟨b, hb, s, hs, rfl⟩
    exact h b hb s hs

theorem cenIn_union (A : Subgroup (MulAut V)) (S T : Set V) :
    cenIn A (commSet A (S ∪ T)) = cenIn A (commSet A S) ⊓ cenIn A (commSet A T) := by
  ext a
  simp only [Subgroup.mem_inf, mem_cenIn_iff, commSet_union, sup_le_iff]
  tauto

theorem cenIn_commSet_empty (A : Subgroup (MulAut V)) : cenIn A (commSet A ∅) = A := by
  ext a
  rw [commSet_empty, mem_cenIn_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, bot_le⟩⟩

variable {A : Subgroup (MulAut V)}

theorem cen_comm_mem_fixV (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {S : Set V} {c : MulAut V}
    (hcS : c ∈ cenIn A (commSet A S)) {s : V} (hs : s ∈ S) : c s * s⁻¹ ∈ fixV A := by
  intro a ha
  have h1 : a (c s) = c (a s) := by
    have := congrArg (fun t : MulAut V => t s) (hc a ha c hcS.1)
    simpa only [MulAut.mul_apply] using this
  have h2 : c (a s * s⁻¹) = a s * s⁻¹ := hcS.2 _ (mem_commSet_of_mem ha hs)
  have h3 : c (a s) = a s * s⁻¹ * c s := by
    calc c (a s) = c (a s * s⁻¹ * s) := by rw [inv_mul_cancel_right]
      _ = c (a s * s⁻¹) * c s := by rw [map_mul]
      _ = a s * s⁻¹ * c s := by rw [h2]
  show a (c s * s⁻¹) = c s * s⁻¹
  rw [map_mul, map_inv, h1, h3]
  comm_group

theorem mem_cenIn_singleton_iff (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (v : V) {a : MulAut V} :
    a ∈ cenIn A (commSet A {v}) ↔ a ∈ A ∧ a v * v⁻¹ ∈ fixV A := by
  rw [mem_cenIn_iff, commSet_le_fixEl_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, cen_comm_mem_fixV hc (mem_cenIn_iff.2 ⟨ha, commSet_le_fixEl_iff.2 h⟩)
      (Set.mem_singleton v)⟩
  · rintro ⟨ha, hfix⟩
    refine ⟨ha, fun b hb s hs => ?_⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have h2 : b (a s) = a (b s) := by
      have := congrArg (fun t : MulAut V => t s) (hc b hb a ha)
      simpa only [MulAut.mul_apply] using this
    have h4 : b (a s * s⁻¹) = a s * s⁻¹ := hfix b hb
    have h3 : a (b s) = b (a s * s⁻¹ * s) := by rw [inv_mul_cancel_right, h2]
    have h5 : a (b s) = a s * s⁻¹ * b s := by rw [h3, map_mul, h4]
    show a (b s * s⁻¹) = b s * s⁻¹
    rw [map_mul, map_inv, h5]
    comm_group

@[expose] def Repl (A : Subgroup (MulAut V)) (S : Set V) : Prop :=
  wt (cenIn A (commSet A S)) = wt A ∧ fixV (cenIn A (commSet A S)) = commSet A S ⊔ fixV A

theorem repl_empty (A : Subgroup (MulAut V)) : Repl A ∅ := by
  rw [Repl, cenIn_commSet_empty, commSet_empty, bot_sup_eq]
  exact ⟨rfl, rfl⟩

theorem repl_singleton [Finite V] (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B ≤ A, wt B ≤ wt A) (v : V) : Repl A {v} := by
  classical
  set C : Subgroup (MulAut V) := cenIn A (commSet A {v}) with hC
  set X : Subgroup V := commSet A {v} with hX
  set Y : Subgroup V := fixV A with hY
  have hCA : C ≤ A := cenIn_le _ _
  have hXC : X ⊔ Y ≤ fixV C := sup_le (fun u hu c hc => hc.2 u hu) (fixV_le_fixV hCA)
  let Fm : (↥A ⧸ C.subgroupOf A) × ↥Y → ↥(X ⊔ Y) := fun p =>
    ⟨(((Quotient.out p.1 : ↥A) : MulAut V) v * v⁻¹) * (p.2 : V),
      Subgroup.mul_mem_sup (mem_commSet_of_mem (Quotient.out p.1 : ↥A).2 (Set.mem_singleton v))
        p.2.2⟩
  have hFm : Function.Injective Fm := by
    rintro ⟨q, u⟩ ⟨q', u'⟩ h
    have h1 : (((Quotient.out q : ↥A) : MulAut V) v * v⁻¹) * (u : V) =
        (((Quotient.out q' : ↥A) : MulAut V) v * v⁻¹) * (u' : V) := congrArg Subtype.val h
    set a : MulAut V := ((Quotient.out q : ↥A) : MulAut V) with ha_def
    set a' : MulAut V := ((Quotient.out q' : ↥A) : MulAut V) with ha'_def
    have ha : a ∈ A := (Quotient.out q : ↥A).2
    have ha' : a' ∈ A := (Quotient.out q' : ↥A).2
    have hdiv : (a' v * v⁻¹) * (a v * v⁻¹)⁻¹ = (u : V) * (u' : V)⁻¹ := by
      calc (a' v * v⁻¹) * (a v * v⁻¹)⁻¹
          = ((a' v * v⁻¹) * (u' : V)) * ((a v * v⁻¹)⁻¹ * (u' : V)⁻¹) := by comm_group
        _ = ((a v * v⁻¹) * (u : V)) * ((a v * v⁻¹)⁻¹ * (u' : V)⁻¹) := by rw [h1]
        _ = (u : V) * (u' : V)⁻¹ := by comm_group
    have hfix : (u : V) * (u' : V)⁻¹ ∈ Y := Y.mul_mem u.2 (Y.inv_mem u'.2)
    have hmem : a⁻¹ * a' ∈ C := by
      refine (mem_cenIn_singleton_iff hc v).2 ⟨A.mul_mem (A.inv_mem ha) ha', ?_⟩
      have h5 : (a⁻¹ * a') v * v⁻¹ = a⁻¹ ((a' v * v⁻¹) * (a v * v⁻¹)⁻¹) := by
        simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
        comm_group
      rw [h5, hdiv]
      have := mem_fixV.1 hfix a⁻¹ (A.inv_mem ha)
      rw [this]
      exact hfix
    have hq : q = q' := by
      have h3 : (Quotient.out q : ↥A)⁻¹ * Quotient.out q' ∈ C.subgroupOf A := hmem
      have h2 := QuotientGroup.eq.2 h3
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
    subst hq
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))
  have hcard : Nat.card ((↥A ⧸ C.subgroupOf A) × ↥Y) ≤ Nat.card ↥(X ⊔ Y) :=
    Nat.card_le_card_of_injective Fm hFm
  have hdom : Nat.card ((↥A ⧸ C.subgroupOf A) × ↥Y) = C.relIndex A * Nat.card Y := by
    rw [Nat.card_prod]
    rfl
  have hidx : C.relIndex A * Nat.card C = Nat.card A := by
    have := Subgroup.relIndex_mul_card C A
    rwa [inf_eq_left.2 hCA] at this
  have hsup : Nat.card ↥(X ⊔ Y) ≤ Nat.card (fixV C) := Subgroup.card_le_of_le hXC
  have hle : wt A ≤ wt C := by
    unfold wt
    calc Nat.card A * Nat.card (fixV A)
        = C.relIndex A * Nat.card C * Nat.card Y := by rw [hidx]
      _ = Nat.card C * (C.relIndex A * Nat.card Y) := by ring
      _ ≤ Nat.card C * Nat.card (fixV C) :=
          Nat.mul_le_mul_left _ (hdom ▸ hcard |>.trans hsup)
  have heq : wt C = wt A := le_antisymm (hmax C hCA) hle
  refine ⟨heq, ?_⟩
  have hfix_card : Nat.card (fixV C) ≤ Nat.card ↥(X ⊔ Y) := by
    have h1 : Nat.card C * Nat.card (fixV C) = Nat.card C * (C.relIndex A * Nat.card Y) := by
      have h2 : wt C = wt A := heq
      unfold wt at h2
      rw [h2, ← hidx]
      ring
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have h3 := Nat.eq_of_mul_eq_mul_left hCpos h1
    rw [h3, ← hdom]
    exact hcard
  exact (Subgroup.eq_of_le_of_card_ge hXC hfix_card).symm

theorem repl_union [Finite V] (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B ≤ A, wt B ≤ wt A) {S T : Set V} (hS : Repl A S) (hT : Repl A T) :
    Repl A (S ∪ T) := by
  classical
  set A₁ : Subgroup (MulAut V) := cenIn A (commSet A S) with hA₁d
  set A₂ : Subgroup (MulAut V) := cenIn A (commSet A T) with hA₂d
  have hA₁ : A₁ ≤ A := cenIn_le _ _
  have hA₂ : A₂ ≤ A := cenIn_le _ _
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy => hc x (hA₁ hx) y (hA₂ hy)
  have hunion : cenIn A (commSet A (S ∪ T)) = A₁ ⊓ A₂ := cenIn_union A S T
  rw [Repl, hunion]
  have hAcard : Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(A₁ ⊓ A₂) = Nat.card A₁ * Nat.card A₂ :=
    card_sup_mul_card_inf' hcomm
  have hWcard : Nat.card ↥(fixV A₁ ⊔ fixV A₂) * Nat.card ↥(fixV A₁ ⊓ fixV A₂) =
      Nat.card (fixV A₁) * Nat.card (fixV A₂) :=
    card_sup_mul_card_inf' (fun x _ y _ => mul_comm x y)
  have hw1 : Nat.card A₁ * Nat.card (fixV A₁) = wt A := hS.1
  have hw2 : Nat.card A₂ * Nat.card (fixV A₂) = wt A := hT.1
  have hsupA : Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixV A₁ ⊓ fixV A₂) ≤ wt A := by
    have := hmax _ (sup_le hA₁ hA₂)
    unfold wt at this
    rwa [fixV_sup] at this
  have hNpos : 0 < wt A := Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : wt A * wt A ≤ wt A * (Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂)) := by
    calc wt A * wt A = (Nat.card A₁ * Nat.card (fixV A₁)) * (Nat.card A₂ * Nat.card (fixV A₂)) := by
          rw [hw1, hw2]
      _ = (Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(A₁ ⊓ A₂)) *
          (Nat.card ↥(fixV A₁ ⊔ fixV A₂) * Nat.card ↥(fixV A₁ ⊓ fixV A₂)) := by
          rw [hAcard, hWcard]; ring
      _ = (Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixV A₁ ⊓ fixV A₂)) *
          (Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂)) := by ring
      _ ≤ wt A * (Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂)) :=
          Nat.mul_le_mul_right _ hsupA
  have hge : wt A ≤ Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂) :=
    Nat.le_of_mul_le_mul_left key hNpos
  have hWle : fixV A₁ ⊔ fixV A₂ ≤ fixV (A₁ ⊓ A₂) :=
    sup_le (fixV_le_fixV inf_le_left) (fixV_le_fixV inf_le_right)
  have hle1 : Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂) ≤
      Nat.card ↥(A₁ ⊓ A₂) * Nat.card (fixV (A₁ ⊓ A₂)) :=
    Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hWle)
  have hle2 : Nat.card ↥(A₁ ⊓ A₂) * Nat.card (fixV (A₁ ⊓ A₂)) ≤ wt A :=
    hmax _ (inf_le_left.trans hA₁)
  have hmid : Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixV A₁ ⊔ fixV A₂) =
      Nat.card ↥(A₁ ⊓ A₂) * Nat.card (fixV (A₁ ⊓ A₂)) := by omega
  have hpos12 : 0 < Nat.card ↥(A₁ ⊓ A₂) := Nat.card_pos
  have hcardW : Nat.card (fixV (A₁ ⊓ A₂)) = Nat.card ↥(fixV A₁ ⊔ fixV A₂) :=
    (Nat.eq_of_mul_eq_mul_left hpos12 hmid).symm
  have hWeq : fixV (A₁ ⊓ A₂) = fixV A₁ ⊔ fixV A₂ :=
    (Subgroup.eq_of_le_of_card_ge hWle hcardW.le).symm
  refine ⟨?_, ?_⟩
  · show Nat.card ↥(A₁ ⊓ A₂) * Nat.card (fixV (A₁ ⊓ A₂)) = wt A
    omega
  · rw [hWeq, hS.2, hT.2, commSet_union, sup_sup_sup_comm, sup_idem]

theorem repl_of_finite [Finite V] (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B ≤ A, wt B ≤ wt A) {S : Set V} (hS : S.Finite) : Repl A S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact repl_empty A
  | insert hv _ ih =>
    rw [Set.insert_eq]
    exact repl_union hc hmax (repl_singleton hc hmax _) ih

theorem replacement_on [Finite V] (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B ≤ A, wt B ≤ wt A) (U : Subgroup V) :
    wt (cenIn A (commOn U A)) = wt A ∧ fixV (cenIn A (commOn U A)) = commOn U A ⊔ fixV A :=
  repl_of_finite hc hmax (Set.toFinite (U : Set V))

theorem replacement [Finite V] (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B ≤ A, wt B ≤ wt A) :
    wt (cenIn A (commV A)) = wt A ∧ fixV (cenIn A (commV A)) = commV A ⊔ fixV A ∧
      commV (cenIn A (commV A)) ≤ fixV A := by
  have h : Repl A Set.univ := repl_of_finite hc hmax Set.finite_univ
  rw [Repl, commSet_univ] at h
  refine ⟨h.1, h.2, ?_⟩
  rw [G6.commV_le_iff]
  intro c hcA v
  have hcen : c ∈ cenIn A (commSet A Set.univ) := by rwa [commSet_univ]
  exact cen_comm_mem_fixV hc hcen (Set.mem_univ v)

@[expose] def resAut (A : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) : A →* MulAut W where
  toFun a :=
    { toFun := fun w => ⟨(a : MulAut V) w, hW a a.2 w w.2⟩
      invFun := fun w => ⟨(a : MulAut V)⁻¹ w, hW a⁻¹ (A.inv_mem a.2) w w.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := MulEquiv.ext fun w => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun w => Subtype.ext (by simp)

theorem resAut_apply (A : Subgroup (MulAut V)) (W : Subgroup V) (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (a : A) (w : W) : ((resAut A W hW a w : W) : V) = (a : MulAut V) w := rfl

theorem commV_eq_bot_of_sup_eq_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (h : commV A ⊔ fixV A = ⊤) : commV A = ⊥ := by
  by_contra hne
  set W : Subgroup V := commV A with hW
  have hWinv : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    have h1 : a w * w⁻¹ ∈ commV A := G6.mem_commV_of_mem ha w
    have h2 : a w = (a w * w⁻¹) * w := by rw [inv_mul_cancel_right]
    rw [h2]
    exact W.mul_mem h1 hw
  have hWle : W ≤ commSet A (W : Set V) := by
    rw [hW]
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, v, rfl⟩
    have hv : v ∈ commV A ⊔ fixV A := h ▸ Subgroup.mem_top v
    obtain ⟨w, hw, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
    have hay : a y = y := mem_fixV.1 hy a ha
    have h3 : a (w * y) * (w * y)⁻¹ = a w * w⁻¹ := by
      rw [map_mul, hay]
      comm_group
    rw [h3]
    exact mem_commSet_of_mem ha hw
  let ρ := resAut A W hWinv
  let K : Subgroup (MulAut W) := ρ.range
  have hK : commV K = ⊤ := by
    have hle : commSet A (W : Set V) ≤ (commV K).map W.subtype := by
      unfold commSet
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, u, hu, rfl⟩
      refine ⟨(ρ ⟨a, ha⟩) ⟨u, hu⟩ * ⟨u, hu⟩⁻¹,
        G6.mem_commV_of_mem (X := K) (x := ρ ⟨a, ha⟩) (MonoidHom.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)
          ⟨u, hu⟩, rfl⟩
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨x, hx, hxw⟩ := hle (hWle w.2)
    have : x = w := Subtype.ext hxw
    rwa [this] at hx
  have hVW : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (hV w)
  have hne' : commV (⊥ : Subgroup (MulAut W)) ≠ ⊤ := by
    intro htop
    apply hne
    have hbot : commV (⊥ : Subgroup (MulAut W)) ≤ ⊥ := by
      rw [G6.commV_le_iff]
      intro x hx w
      rw [Subgroup.mem_bot] at hx
      subst hx
      simp
    have hall : ∀ w : W, w = 1 := fun w => by
      have : w ∈ commV (⊥ : Subgroup (MulAut W)) := htop ▸ Subgroup.mem_top w
      exact Subgroup.mem_bot.1 (hbot this)
    refine eq_bot_iff.2 fun w hw => ?_
    have := hall ⟨w, hw⟩
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  refine G6.commV_ne_top_of_two_power hVW (K := K) (N := ⊥) (fun k _ n hn => ?_) (fun k hk => ?_)
    hne' hK
  · rw [Subgroup.mem_bot] at hn
    subst hn
    simp
  · obtain ⟨a, rfl⟩ := hk
    refine ⟨1, ?_⟩
    have h2 : a ^ 2 = 1 := Subtype.ext (hA2 a a.2)
    rw [Subgroup.mem_bot, pow_one, ← map_pow, h2, map_one]

@[expose] def IsAV (A : Subgroup (MulAut V)) : Prop :=
  IsElemAbelian2 A ∧ ∀ B ≤ A, wt B ≤ wt A

theorem isFFStarOffender_iff_isAV {X A : Subgroup (MulAut V)} :
    IsFFStarOffender X A ↔ A ≤ X ∧ A ≠ ⊥ ∧ IsAV A :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem commV_eq_bot_iff {A : Subgroup (MulAut V)} : commV A = ⊥ ↔ A = ⊥ := by
  constructor
  · intro h
    refine (Subgroup.eq_bot_iff_forall A).2 fun a ha => ?_
    refine MulEquiv.ext fun v => ?_
    have h1 : a v * v⁻¹ ∈ commV A := G6.mem_commV_of_mem ha v
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
    rw [h1]
    rfl
  · rintro rfl
    rw [eq_bot_iff, G6.commV_le_iff]
    intro x hx v
    rw [Subgroup.mem_bot] at hx
    subst hx
    simp

theorem timmesfeld_replacement [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : IsAV A) (U : Subgroup V) :
    IsAV (cenIn A (commOn U A)) ∧ fixV (cenIn A (commOn U A)) = commOn U A ⊔ fixV A ∧
      (commV A ≠ ⊥ → commV (cenIn A (commOn U A)) ≠ ⊥) := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.1.1
  obtain ⟨hw, hfix⟩ := replacement_on hc hA.2 U
  refine ⟨⟨⟨fun a ha b hb => hA.1.1 a (cenIn_le _ _ ha) b (cenIn_le _ _ hb),
    fun a ha => hA.1.2 a (cenIn_le _ _ ha)⟩, fun B hB => ?_⟩, hfix, fun hne hbot => ?_⟩
  · rw [hw]
    exact hA.2 B (hB.trans (cenIn_le _ _))
  · have h1 : fixV (cenIn A (commOn U A)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ c hcc
      have h2 : c v * v⁻¹ ∈ commV (cenIn A (commOn U A)) := G6.mem_commV_of_mem hcc v
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h2
      exact h2
    have hUle : commOn U A ≤ commV A := by
      unfold commOn commSet
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, u, _, rfl⟩
      exact G6.mem_commV_of_mem ha u
    have h3 : commV A ⊔ fixV A = ⊤ :=
      eq_top_iff.2 (h1 ▸ hfix ▸ sup_le_sup_right hUle _)
    exact hne (commV_eq_bot_of_sup_eq_top hV hA.1.2 h3)

theorem exists_replacement [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) :
    ∃ A₀ : Subgroup (MulAut V), A₀ ≤ A ∧ IsFFStarOffender X A₀ ∧ commV A₀ ≤ fixV A := by
  obtain ⟨hAX, hA0, hAV⟩ := isFFStarOffender_iff_isAV.1 hA
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hAV.1.1
  obtain ⟨hAV', -, hne⟩ := timmesfeld_replacement hV hAV ⊤
  rw [commOn_top] at hAV' hne
  have hcomm : commV A ≠ ⊥ := fun h => hA0 (commV_eq_bot_iff.1 h)
  have hne' := hne hcomm
  obtain ⟨-, -, hcomm0⟩ := replacement hc hAV.2
  refine ⟨cenIn A (commV A), cenIn_le _ _, ?_, hcomm0⟩
  exact isFFStarOffender_iff_isAV.2 ⟨(cenIn_le _ _).trans hAX,
    fun h => hne' (commV_eq_bot_iff.2 h), hAV'⟩

end Main

end CFSG.CGT.PushingUpLit.BHS
