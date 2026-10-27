module

public import CFSG.GH74.KGroups.Checks
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GH74.KGroups

variable {G : Type*} [Group G]

@[expose] def conjSet (A : Subgroup G) (r : G) : Set G := {x | ∃ g ∈ A, x = g * r * g⁻¹}

@[expose] noncomputable def centCard (B : Subgroup G) (r : G) : ℕ :=
  Nat.card {g // g ∈ B ∧ g * r = r * g}

@[reducible] def conjAction (A : Subgroup G) : MulAction A G where
  smul g x := (g : G) * x * (g : G)⁻¹
  one_smul x := by
    change ((1 : A) : G) * x * ((1 : A) : G)⁻¹ = x
    simp
  mul_smul g h x := by
    change ((g * h : A) : G) * x * ((g * h : A) : G)⁻¹ = (g : G) * ((h : G) * x * (h : G)⁻¹) * (g : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

theorem conj_eq_iff (g r : G) : g * r * g⁻¹ = r ↔ g * r = r * g := by
  rw [mul_inv_eq_iff_eq_mul]

theorem ncard_conjSet_mul (A : Subgroup G) [Finite A] (r : G) :
    (conjSet A r).ncard * centCard A r = Nat.card A := by
  let := conjAction A
  have h1 : MulAction.orbit A r = conjSet A r := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have h2 : Nat.card (MulAction.stabilizer A r) = centCard A r := by
    unfold centCard
    have e : (MulAction.stabilizer A r) ≃ {g : A // (g : G) * r = r * g} :=
      Equiv.subtypeEquivRight fun g => by
        rw [MulAction.mem_stabilizer_iff]
        exact conj_eq_iff (g : G) r
    rw [Nat.card_congr e]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ A) fun g => g * r = r * g)
  rw [← h1, ← MulAction.index_stabilizer, ← h2, mul_comm, Subgroup.card_mul_index]

theorem conjSet_finite (A : Subgroup G) [Finite A] (r : G) : (conjSet A r).Finite := by
  have : conjSet A r = Set.range fun g : A => (g : G) * r * (g : G)⁻¹ := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  rw [this]
  exact Set.finite_range _

theorem centCard_pos (A : Subgroup G) [Finite A] (r : G) : 0 < centCard A r := by
  unfold centCard
  have : Finite {g // g ∈ A ∧ g * r = r * g} :=
    Finite.of_injective (fun g => (⟨g.1, g.2.1⟩ : A)) fun x y h => Subtype.ext
      (congrArg Subtype.val h :)
  exact Nat.card_pos_iff.2 ⟨⟨⟨1, A.one_mem, by simp⟩⟩, this⟩

theorem centCard_conj (B : Subgroup G) (g r : G) (hg : ∀ h, g⁻¹ * h * g ∈ B ↔ h ∈ B) :
    centCard B (g * r * g⁻¹) = centCard B r := by
  unfold centCard
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv fun h => ?_)
  have e0 : (MulAut.conj g⁻¹).toEquiv h = g⁻¹ * h * g := by simp
  rw [e0, hg]
  have e1 : (g⁻¹ * h * g) * r = g⁻¹ * (h * (g * r * g⁻¹)) * g := by group
  have e2 : r * (g⁻¹ * h * g) = g⁻¹ * ((g * r * g⁻¹) * h) * g := by group
  rw [e1, e2, mul_left_inj, mul_right_inj]

theorem normal_iff_of_mem {A : Subgroup G} {g : G} (hg : g ∈ A) (h : G) :
    g⁻¹ * h * g ∈ A ↔ h ∈ A := by
  constructor
  · intro hh
    have : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
    rw [this]
    exact A.mul_mem (A.mul_mem hg hh) (A.inv_mem hg)
  · intro hh
    exact A.mul_mem (A.mul_mem (A.inv_mem hg) hh) hg

theorem exists_conj_of_card (A : Subgroup G) [Finite A] (T : Set G) (hT : T.Finite) (rs : List G)
    (hcl : ∀ r ∈ rs, ∀ g ∈ A, g * r * g⁻¹ ∈ T) (hnd : (rs.map (centCard A)).Nodup)
    (hcard : T.ncard ≤ (rs.map fun r => Nat.card A / centCard A r).sum) :
    ∀ x ∈ T, ∃ r ∈ rs, x ∈ conjSet A r := by
  set U : Set G := {x | ∃ r ∈ rs, x ∈ conjSet A r} with hUdef
  have hUT : U ⊆ T := by
    rintro x ⟨r, hr, g, hg, rfl⟩
    exact hcl r hr g hg
  have hcc : ∀ r r' x, x ∈ conjSet A r → x ∈ conjSet A r' → centCard A r = centCard A r' := by
    rintro r r' x ⟨g, hg, rfl⟩ ⟨g', hg', he⟩
    rw [← centCard_conj A g r (normal_iff_of_mem hg), he,
      centCard_conj A g' r' (normal_iff_of_mem hg')]
  have hU : ∀ l : List G, (l.map (centCard A)).Nodup →
      ({x | ∃ r ∈ l, x ∈ conjSet A r} : Set G).Finite ∧
      ({x | ∃ r ∈ l, x ∈ conjSet A r} : Set G).ncard =
        (l.map fun r => Nat.card A / centCard A r).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons r l ih =>
      intro hl
      rw [List.map_cons, List.nodup_cons] at hl
      obtain ⟨hf, hn⟩ := ih hl.2
      have hs : ({x | ∃ r' ∈ r :: l, x ∈ conjSet A r'} : Set G) =
          conjSet A r ∪ {x | ∃ r' ∈ l, x ∈ conjSet A r'} := by
        ext x
        simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · rintro ⟨r', rfl | hr', hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨r', hr', hx⟩
        · rintro (hx | ⟨r', hr', hx⟩)
          · exact ⟨r, Or.inl rfl, hx⟩
          · exact ⟨r', Or.inr hr', hx⟩
      have hd : Disjoint (conjSet A r) {x | ∃ r' ∈ l, x ∈ conjSet A r'} := by
        rw [Set.disjoint_left]
        rintro x hx ⟨r', hr', hx'⟩
        exact hl.1 (List.mem_map.2 ⟨r', hr', (hcc r r' x hx hx').symm⟩)
      have hcr : (conjSet A r).ncard = Nat.card A / centCard A r :=
        (Nat.div_eq_of_eq_mul_left (centCard_pos A r) (ncard_conjSet_mul A r).symm).symm
      rw [hs, List.map_cons, List.sum_cons]
      exact ⟨(conjSet_finite A r).union hf, by
        rw [Set.ncard_union_eq hd (conjSet_finite A r) hf, hcr, hn]⟩
  obtain ⟨-, hUc⟩ := hU rs hnd
  have heq : U = T := Set.eq_of_subset_of_ncard_le hUT (hcard.trans hUc.ge) hT
  intro x hx
  rw [← heq] at hx
  exact hx

theorem conj_apply' (g r : G) : MulAut.conj g r = g * r * g⁻¹ := MulAut.conj_apply g r

theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← conj_apply', MulEquiv.orderOf_eq]

theorem conj_of_order_count (A B : Subgroup G) [Finite A] [Finite B]
    (hAB : ∀ g ∈ A, ∀ x ∈ B, g * x * g⁻¹ ∈ B) (m : ℕ) (rs : List G)
    (hrs : ∀ r ∈ rs, r ∈ B ∧ orderOf r = m) (hnd : (rs.map (centCard A)).Nodup)
    (hcard : Nat.card {x // x ∈ B ∧ orderOf x = m} ≤
      (rs.map fun r => Nat.card A / centCard A r).sum) :
    ∀ x ∈ B, orderOf x = m → ∃ r ∈ rs, x ∈ conjSet A r := by
  have hT : ({x | x ∈ B ∧ orderOf x = m} : Set G).Finite := by
    have : Finite {x // x ∈ B ∧ orderOf x = m} :=
      Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : B)) fun x y h => Subtype.ext
        (congrArg Subtype.val h :)
    exact Set.toFinite _
  intro x hx hxm
  refine exists_conj_of_card A _ hT rs (fun r hr g hg => ⟨hAB g hg r (hrs r hr).1, ?_⟩) hnd ?_ x
    ⟨hx, hxm⟩
  · rw [orderOf_conj']
    exact (hrs r hr).2
  · rw [← Nat.card_coe_set_eq]
    exact hcard

theorem normal_iff_of_conj {A B : Subgroup G} (hAB : ∀ g ∈ A, ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {g : G} (hg : g ∈ A) (h : G) : g⁻¹ * h * g ∈ B ↔ h ∈ B := by
  constructor
  · intro hh
    have := hAB g hg _ hh
    rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group] at this
  · intro hh
    have := hAB g⁻¹ (A.inv_mem hg) h hh
    rwa [inv_inv] at this

theorem conj_mem_self (B : Subgroup G) : ∀ g ∈ B, ∀ x ∈ B, g * x * g⁻¹ ∈ B :=
  fun _ hg _ hx => B.mul_mem (B.mul_mem hg hx) (B.inv_mem hg)

theorem card_pairs_le (P A : Subgroup G) [Finite P] (a : G)
    (hAP : ∀ g ∈ A, ∀ x ∈ P, g * x * g⁻¹ ∈ P) (oa ob : ℕ) (ws : List (List Bool × ℕ))
    (hcl : ∀ x ∈ P, orderOf x = oa → x ∈ conjSet A a) :
    Nat.card {p : P × P // orderOf p.1 = oa ∧ orderOf p.2 = ob ∧ PairInv ws p.1 p.2} ≤
      Nat.card {x // x ∈ P ∧ orderOf x = oa} *
        Nat.card {y // y ∈ P ∧ orderOf y = ob ∧ PairInv ws a y} := by
  classical
  have : Finite {x // x ∈ P ∧ orderOf x = oa} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : P)) fun x y h => Subtype.ext
      (congrArg Subtype.val h :)
  have : Finite {y // y ∈ P ∧ orderOf y = ob ∧ PairInv ws a y} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : P)) fun x y h => Subtype.ext
      (congrArg Subtype.val h :)
  let gx : G → G := fun x => if h : x ∈ conjSet A a then h.choose else 1
  have hgx : ∀ x ∈ conjSet A a, gx x ∈ A ∧ x = gx x * a * (gx x)⁻¹ := by
    intro x hx
    simp only [gx, dite_eq_left hx]
    exact hx.choose_spec
  have hx1 : ∀ p : {p : P × P // orderOf p.1 = oa ∧ orderOf p.2 = ob ∧ PairInv ws p.1 p.2},
      (p.1.1 : G) ∈ conjSet A a := fun p =>
    hcl _ p.1.1.2 (by rw [Subgroup.orderOf_coe]; exact p.2.1)
  refine (Nat.card_le_card_of_injective (fun p =>
    ((⟨p.1.1, p.1.1.2, by rw [Subgroup.orderOf_coe]; exact p.2.1⟩ :
      {x // x ∈ P ∧ orderOf x = oa}),
    (⟨(gx p.1.1)⁻¹ * p.1.2 * gx p.1.1, ?_, ?_, ?_⟩ :
      {y // y ∈ P ∧ orderOf y = ob ∧ PairInv ws a y}))) ?_).trans (Nat.card_prod _ _).le
  · have h := hAP _ (A.inv_mem (hgx _ (hx1 p)).1) _ p.1.2.2
    rwa [inv_inv] at h
  · have h := MulEquiv.orderOf_eq (MulAut.conj (gx p.1.1)⁻¹) (p.1.2 : G)
    rw [conj_apply', inv_inv] at h
    rw [h, Subgroup.orderOf_coe]
    exact p.2.2.1
  · have h := pairInv_map (MulAut.conj (gx p.1.1)⁻¹) ws
      ((pairInv_coe_iff P ws p.1.1 p.1.2).1 p.2.2.2)
    rw [conj_apply', conj_apply', inv_inv] at h
    have key : ∀ g x : G, x = g * a * g⁻¹ → g⁻¹ * x * g = a := by
      intro g x hx
      rw [hx]
      group
    rwa [key _ _ (hgx _ (hx1 p)).2] at h
  · rintro ⟨⟨x, y⟩, hp⟩ ⟨⟨x', y'⟩, hp'⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx : x = x' := Subtype.ext h1
    subst hx
    have hy : y = y' := Subtype.ext (by simpa using h2)
    subst hy
    rfl

theorem conj_mem_of_closure (P : Subgroup G) [Finite P] {a b : G} (hP : P = Subgroup.closure {a, b})
    (S : Set G) (hS : ∀ σ ∈ S, σ * a * σ⁻¹ ∈ P ∧ σ * b * σ⁻¹ ∈ P) :
    ∀ σ ∈ Subgroup.closure S, ∀ x ∈ P, σ * x * σ⁻¹ ∈ P := by
  have hle : Subgroup.closure S ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.closure_le]
    intro σ hσ
    apply mem_normalizer_of_conj_mem
    intro x hx
    have hle : Subgroup.closure ({a, b} : Set G) ≤ P.comap (MulAut.conj σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        exact (hS σ hσ).1
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hS σ hσ).2
    have hx' : x ∈ Subgroup.closure ({a, b} : Set G) := hP ▸ hx
    exact hle hx'
  intro σ hσ x hx
  exact ((Subgroup.mem_normalizer_iff.1 (hle hσ)) x).1 hx

theorem autModel_of_card (P A : Subgroup G) [Finite P] [Finite A] (a b : G)
    (hP : P = Subgroup.closure {a, b}) (oa ob : ℕ) (ws : List (List Bool × ℕ))
    (hA : orderOf a = oa) (hB : orderOf b = ob) (hI : PairInv ws a b)
    (hnorm : ∀ σ ∈ A, ∀ x ∈ P, σ * x * σ⁻¹ ∈ P)
    (hcent : ∀ σ ∈ A, σ * a = a * σ → σ * b = b * σ → σ = 1)
    (hcount : Nat.card {p : P × P // orderOf p.1 = oa ∧ orderOf p.2 = ob ∧ PairInv ws p.1 p.2} ≤
      Nat.card A)
    {K : Type*} [Group K] (e : K ≃* P) :
    ∃ M : AutModel K G, M.P = P ∧ M.A = A := by
  classical
  have hga : a ∈ P := by
    rw [hP]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hgb : b ∈ P := by
    rw [hP]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hnormA : A ≤ Subgroup.normalizer (P : Set G) := fun σ hσ =>
    mem_normalizer_of_conj_mem P σ (hnorm σ hσ)
  have hcentA : ∀ σ ∈ A, (∀ x ∈ P, σ * x = x * σ) → σ = 1 := fun σ hσ hc =>
    hcent σ hσ (hc a hga) (hc b hgb)
  have hcard : Nat.card (MulAut P) ≤ Nat.card A := by
    have hgen := closure_pair_top hP hga hgb
    let I : P → P → Prop := fun x y => orderOf x = oa ∧ orderOf y = ob ∧ PairInv ws x y
    have hIab : I ⟨a, hga⟩ ⟨b, hgb⟩ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← Subgroup.orderOf_coe]
        exact hA
      · rw [← Subgroup.orderOf_coe]
        exact hB
      · exact (pairInv_coe_iff P ws _ _).2 hI
    have hIaut : ∀ φ : MulAut P, I ⟨a, hga⟩ ⟨b, hgb⟩ → I (φ ⟨a, hga⟩) (φ ⟨b, hgb⟩) := by
      rintro φ ⟨h1, h2, h3⟩
      exact ⟨by rw [MulEquiv.orderOf_eq]; exact h1, by rw [MulEquiv.orderOf_eq]; exact h2,
        pairInv_map φ ws h3⟩
    exact (card_mulAut_le _ _ hgen I hIaut hIab).trans hcount
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_of_squeeze P A hnormA hcentA hcard
  exact ⟨AutModel.ofRealization P A e Φ' hΦ', rfl, rfl⟩

@[expose] def E9At (A : Subgroup G) (τ : G) : Prop :=
  ∀ X ∈ A, X ≠ 1 → ∀ Y ∈ A, X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X → X * τ = τ * X →
    Y * τ = τ * Y → Y = 1 ∨ Y = X ∨ Y = X ^ 2

@[expose] def E27At (A : Subgroup G) (X : G) : Prop :=
  ∀ Y ∈ A, ∀ Z ∈ A, Y ^ 3 = 1 → Z ^ 3 = 1 → X * Y = Y * X → X * Z = Z * X → Y * Z = Z * Y →
    Y ∈ ([1, X, X ^ 2] : List G) ∨ Z ∈ pow3list X Y

@[expose] def Cent3At (A : Subgroup G) (x : G) : Prop :=
  ∀ y ∈ A, y ^ 3 = 1 → x * y = y * x → y ∉ ([1, x, x ^ 2] : List G) →
    ∀ k ∈ A, k * x = x * k → k * y = y * k → k ∈ pow3list x y

section Transport

variable {A : Subgroup G} {g : G}

theorem conj_mem_iff (hg : g ∈ A) (x : G) : MulAut.conj g x ∈ A ↔ x ∈ A := by
  rw [conj_apply']
  have := normal_iff_of_mem (A.inv_mem hg) x
  rwa [inv_inv] at this

theorem exists_conj_preimage (φ : G ≃* G) (x : G) : ∃ x', x = φ x' :=
  ⟨φ.symm x, by simp⟩

theorem e9At_conj (hg : g ∈ A) {τ : G} (h : E9At A τ) : E9At A (g * τ * g⁻¹) := by
  rw [← conj_apply']
  intro X hX hX1 Y hY hX3 hY3 hXY hXτ hYτ
  obtain ⟨X, rfl⟩ := exists_conj_preimage (MulAut.conj g) X
  obtain ⟨Y, rfl⟩ := exists_conj_preimage (MulAut.conj g) Y
  simp only [← map_mul, ← map_pow, EmbeddingLike.apply_eq_iff_eq, MulEquiv.map_eq_one_iff,
    ne_eq] at hX1 hX3 hY3 hXY hXτ hYτ ⊢
  exact h X ((conj_mem_iff hg X).1 hX) hX1 Y ((conj_mem_iff hg Y).1 hY) hX3 hY3 hXY hXτ hYτ

theorem mem_list_map_iff (φ : G ≃* G) (x : G) (L : List G) : φ x ∈ L.map φ ↔ x ∈ L := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := List.mem_map.1 h
    rwa [← φ.injective he]
  · exact List.mem_map_of_mem

theorem e27At_conj (hg : g ∈ A) {X : G} (h : E27At A X) : E27At A (g * X * g⁻¹) := by
  rw [← conj_apply']
  set φ := MulAut.conj g
  intro Y hY Z hZ hY3 hZ3 hXY hXZ hYZ
  obtain ⟨Y, rfl⟩ := exists_conj_preimage φ Y
  obtain ⟨Z, rfl⟩ := exists_conj_preimage φ Z
  have e1 : ([1, φ X, φ X ^ 2] : List G) = ([1, X, X ^ 2] : List G).map φ := by simp
  have e2 : pow3list (φ X) (φ Y) = (pow3list X Y).map φ :=
    (pow3list_map φ.toMonoidHom X Y).symm
  rw [e1, e2, mem_list_map_iff, mem_list_map_iff]
  simp only [← map_mul, ← map_pow, EmbeddingLike.apply_eq_iff_eq, MulEquiv.map_eq_one_iff]
    at hY3 hZ3 hXY hXZ hYZ
  exact h Y ((conj_mem_iff hg Y).1 hY) Z ((conj_mem_iff hg Z).1 hZ) hY3 hZ3 hXY hXZ hYZ

theorem cent3At_conj (hg : g ∈ A) {x : G} (h : Cent3At A x) : Cent3At A (g * x * g⁻¹) := by
  rw [← conj_apply']
  set φ := MulAut.conj g
  intro y hy hy3 hxy hyn k hk hkx hky
  obtain ⟨y, rfl⟩ := exists_conj_preimage φ y
  obtain ⟨k, rfl⟩ := exists_conj_preimage φ k
  have e1 : ([1, φ x, φ x ^ 2] : List G) = ([1, x, x ^ 2] : List G).map φ := by simp
  have e2 : pow3list (φ x) (φ y) = (pow3list x y).map φ :=
    (pow3list_map φ.toMonoidHom x y).symm
  rw [e1, mem_list_map_iff] at hyn
  rw [e2, mem_list_map_iff]
  simp only [← map_mul, ← map_pow, EmbeddingLike.apply_eq_iff_eq, MulEquiv.map_eq_one_iff]
    at hy3 hxy hkx hky
  exact h y ((conj_mem_iff hg y).1 hy) hy3 hxy hyn k ((conj_mem_iff hg k).1 hk) hkx hky

end Transport

theorem forall_of_classes (A : Subgroup G) (T : Set G) (rs : List G) (Φ : G → Prop)
    (hT : ∀ x ∈ T, ∃ r ∈ rs, x ∈ conjSet A r) (hr : ∀ r ∈ rs, Φ r)
    (hΦ : ∀ g ∈ A, ∀ r, Φ r → Φ (g * r * g⁻¹)) : ∀ x ∈ T, Φ x := by
  intro x hx
  obtain ⟨r, hr', g, hg, rfl⟩ := hT x hx
  exact hΦ g hg r (hr r hr')

theorem card_inf_centralizer_eq (B : Subgroup G) (τ : G) :
    Nat.card ↥(B ⊓ Subgroup.centralizer ({τ} : Set G)) = centCard B τ := by
  unfold centCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

end CFSG.GH74.KGroups

end
