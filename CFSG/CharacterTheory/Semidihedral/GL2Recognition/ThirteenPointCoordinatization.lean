module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ThreePlaneCollineations

public section

namespace CFSG.Semidihedral.GL2Recognition

@[expose] def frameLines : Finset (Fin 13) := {0, 1, 2, 7, 8, 9}

@[expose] def fourthPointPairs : Finset (Fin 13 × Fin 13) :=
  {(7, 0), (7, 1), (7, 4), (8, 0), (8, 2), (8, 5), (9, 1), (9, 2), (9, 6), (10, 2), (10, 3),
    (10, 4), (11, 1), (11, 3), (11, 5), (12, 0), (12, 3), (12, 6)}

theorem frameLines_sep : ∀ j ∈ frameLines, ∀ j' ∈ frameLines, j ≠ j' →
    ∃ k : Fin 13, k.val < 4 ∧ k ∈ planeLine j ∧ k ∉ planeLine j' := by decide

theorem frameLines_meet : ∀ a : Fin 13, 4 ≤ a.val → ∀ j ∈ frameLines, a ∉ planeLine j →
    ∃ f ∈ frameLines, a ∈ planeLine f ∧ ∃ m, m < a ∧ m ∈ planeLine j ∧ m ∈ planeLine f := by
  decide

theorem frameLines_signature : ∀ a m : Fin 13, m < a →
    (a, m) ∈ fourthPointPairs ∨ ∃ j ∈ frameLines, a ∈ planeLine j ∧ m ∉ planeLine j := by
  decide

theorem frameLines_frame : ∀ k : Fin 13, k.val < 4 → ∀ j ∈ frameLines, k ∉ planeLine j →
    ∃ i i' : Fin 13, i.val < 4 ∧ i'.val < 4 ∧ i < i' ∧ i ≠ k ∧ i' ≠ k ∧ i ∈ planeLine j ∧
      i' ∈ planeLine j := by decide

@[expose] def IsOffFrameLines (a b x : Fin 13) : Prop :=
  ∀ i ∈ frameLines, (a ∈ planeLine i → x ∉ planeLine i) ∧ (b ∈ planeLine i → x ∉ planeLine i)

instance (a b x : Fin 13) : Decidable (IsOffFrameLines a b x) := by
  unfold IsOffFrameLines; infer_instance

@[expose] def IsLineWitness (j a b : Fin 13) : Prop :=
  a ≠ b ∧ a ∈ planeLine j ∧ b ∈ planeLine j ∧
    (∀ i ∈ frameLines, ¬(a ∈ planeLine i ∧ b ∈ planeLine i)) ∧
    ∀ x y, x ≠ y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → IsOffFrameLines a b x →
      IsOffFrameLines a b y → (∀ i ∈ frameLines, ¬(x ∈ planeLine i ∧ y ∈ planeLine i)) →
      x ∈ planeLine j ∧ y ∈ planeLine j

instance (j a b : Fin 13) : Decidable (IsLineWitness j a b) := by
  unfold IsLineWitness; infer_instance

theorem exists_isLineWitness : ∀ j ∉ frameLines, ∃ a b, IsLineWitness j a b := by decide

theorem card_planeLine : ∀ j, (planeLine j).card = 4 := by decide

theorem card_lines_through :
    ∀ a : Fin 13, (Finset.univ.filter fun j => a ∈ planeLine j).card = 4 := by
  decide

theorem card_planeLine_inter : ∀ j j' : Fin 13, j ≠ j' → (planeLine j ∩ planeLine j').card = 1 := by
  decide


theorem fin_thirteen_eq_of_val_lt_four :
    ∀ x : Fin 13, x.val < 4 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  decide

theorem FourBlockDesign.frame_labelling_injective {Ω : Type*} {B : Set (Set Ω)}
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    (p : Fin 13 → Ω) (ℓ : Fin 13 → Set Ω) (hℓB : ∀ j ∈ frameLines, ℓ j ∈ B)
    (hP : ∀ j ∈ frameLines, ∀ a ∈ planeLine j, p a ∈ ℓ j)
    (h012 : ∀ b ∈ B, ¬(p 0 ∈ b ∧ p 1 ∈ b ∧ p 2 ∈ b))
    (h013 : ∀ b ∈ B, ¬(p 0 ∈ b ∧ p 1 ∈ b ∧ p 3 ∈ b))
    (h023 : ∀ b ∈ B, ¬(p 0 ∈ b ∧ p 2 ∈ b ∧ p 3 ∈ b))
    (h123 : ∀ b ∈ B, ¬(p 1 ∈ b ∧ p 2 ∈ b ∧ p 3 ∈ b))
    (hIV : ∀ a m, (a, m) ∈ fourthPointPairs → p a ≠ p m) :
    (∀ a, ∀ j ∈ frameLines, p a ∈ ℓ j ↔ a ∈ planeLine j) ∧ Function.Injective p := by
  have hframe : ∀ k : Fin 13, k.val < 4 → ∀ j ∈ frameLines, p k ∈ ℓ j → k ∈ planeLine j := by
    intro k hk j hj hkj
    by_contra hkL
    obtain ⟨i, i', hi, hi', hii', hik, hi'k, hiL, hi'L⟩ := frameLines_frame k hk j hj hkL
    have hb := hℓB j hj
    have hpi := hP j hj i hiL
    have hpi' := hP j hj i' hi'L
    rcases fin_thirteen_eq_of_val_lt_four k hk with rfl | rfl | rfl | rfl <;>
    rcases fin_thirteen_eq_of_val_lt_four i hi with rfl | rfl | rfl | rfl <;>
    rcases fin_thirteen_eq_of_val_lt_four i' hi' with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hii' (by decide)
    | exact absurd rfl hik
    | exact absurd rfl hi'k
    | exact h012 _ hb ⟨‹_›, ‹_›, ‹_›⟩
    | exact h013 _ hb ⟨‹_›, ‹_›, ‹_›⟩
    | exact h023 _ hb ⟨‹_›, ‹_›, ‹_›⟩
    | exact h123 _ hb ⟨‹_›, ‹_›, ‹_›⟩
  have hℓne : ∀ j ∈ frameLines, ∀ j' ∈ frameLines, j ≠ j' → ℓ j ≠ ℓ j' := by
    intro j hj j' hj' hne heq
    obtain ⟨k, hk, hkj, hkj'⟩ := frameLines_sep j hj j' hj' hne
    exact hkj' (hframe k hk j' hj' (heq ▸ hP j hj k hkj))
  have hmeet : ∀ j ∈ frameLines, ∀ j' ∈ frameLines, j ≠ j' → ∀ x y : Ω, x ∈ ℓ j → x ∈ ℓ j' →
      y ∈ ℓ j → y ∈ ℓ j' → x = y := by
    intro j hj j' hj' hne x y hx hx' hy hy'
    by_contra hxy
    exact hℓne j hj j' hj' hne (hU _ (hℓB j hj) _ (hℓB j' hj') x y hxy hx hy hx' hy')
  have key : ∀ a : Fin 13, (∀ m < a, ∀ j ∈ frameLines, p m ∈ ℓ j → m ∈ planeLine j) →
      (∀ m < a, p a ≠ p m) ∧ ∀ j ∈ frameLines, p a ∈ ℓ j → a ∈ planeLine j := by
    intro a ih
    have hD : ∀ m < a, p a ≠ p m := by
      intro m hm heq
      rcases frameLines_signature a m hm with h | ⟨j, hj, haj, hmj⟩
      · exact hIV a m h heq
      · exact hmj (ih m hm j hj (heq ▸ hP j hj a haj))
    refine ⟨hD, fun j hj haj => ?_⟩
    by_cases ha4 : a.val < 4
    · exact hframe a ha4 j hj haj
    by_contra haL
    obtain ⟨f, hf, haf, m, hm, hmj, hmf⟩ := frameLines_meet a (by omega) j hj haL
    have hjf : j ≠ f := by
      rintro rfl
      exact haL haf
    exact hD m hm (hmeet j hj f hf hjf _ _ haj (hP f hf a haf) (hP j hj m hmj) (hP f hf m hmf))
  have hclaim : ∀ a : Fin 13, ∀ j ∈ frameLines, p a ∈ ℓ j → a ∈ planeLine j := by
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih => exact (key a ih).2
  refine ⟨fun a j hj => ⟨hclaim a j hj, hP j hj a⟩, ?_⟩
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (key b fun m _ => hclaim m).1 a h hab.symm
  · exact (key a fun m _ => hclaim m).1 b h hab


section Design

variable {Ω : Type*}

theorem FourBlockDesign.block_eq_of_mem {B : Set (Set Ω)}
    (hu : ∀ x y : Ω, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b) :
    ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b' :=
  fun _ hb _ hb' x y hxy hx hy hx' hy' => (hu x y hxy).unique ⟨hb, hx, hy⟩ ⟨hb', hx', hy'⟩

theorem FourBlockDesign.exists_mem_ne_three {b : Set Ω} (hb : b.ncard = 4) (u v w : Ω) :
    ∃ z ∈ b, z ≠ u ∧ z ≠ v ∧ z ≠ w := by
  by_contra h
  push Not at h
  have hsub : b ⊆ {u, v, w} := fun z hz => by
    by_cases hzu : z = u
    · simp [hzu]
    by_cases hzv : z = v
    · simp [hzv]
    simp [h z hz hzu hzv]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({u, v, w} : Set Ω).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    have := Set.ncard_insert_le v {w}
    rw [Set.ncard_singleton] at this
    omega
  omega

theorem FourBlockDesign.disjoint_sdiff_of_ne {B : Set (Set Ω)}
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    {x : Ω} {b b' : Set Ω} (hb : b ∈ B) (hb' : b' ∈ B) (hx : x ∈ b) (hx' : x ∈ b')
    (hne : b ≠ b') : Disjoint (b \ {x}) (b' \ {x}) := by
  rw [Set.disjoint_left]
  rintro z ⟨hz, hzx⟩ ⟨hz', -⟩
  exact hne (hU b hb b' hb' x z (Ne.symm hzx) hx hz hx' hz')

theorem FourBlockDesign.not_five_blocks [Finite Ω] (hΩ : Nat.card Ω = 13) {B : Set (Set Ω)}
    (h4 : ∀ b ∈ B, b.ncard = 4)
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    {x : Ω} {β₀ β₁ β₂ β₃ β₄ : Set Ω} (h₀ : β₀ ∈ B) (h₁ : β₁ ∈ B) (h₂ : β₂ ∈ B) (h₃ : β₃ ∈ B)
    (h₄ : β₄ ∈ B) (hx₀ : x ∈ β₀) (hx₁ : x ∈ β₁) (hx₂ : x ∈ β₂) (hx₃ : x ∈ β₃) (hx₄ : x ∈ β₄)
    (n01 : β₀ ≠ β₁) (n02 : β₀ ≠ β₂) (n03 : β₀ ≠ β₃) (n04 : β₀ ≠ β₄) (n12 : β₁ ≠ β₂)
    (n13 : β₁ ≠ β₃) (n14 : β₁ ≠ β₄) (n23 : β₂ ≠ β₃) (n24 : β₂ ≠ β₄) (n34 : β₃ ≠ β₄) : False := by
  have c : ∀ β ∈ B, x ∈ β → (β \ {x}).ncard = 3 := fun β hβ hxβ => by
    rw [Set.ncard_sdiff_singleton_of_mem hxβ, h4 β hβ]
  have d := fun {b b'} (hb : b ∈ B) (hb' : b' ∈ B) (hx : x ∈ b) (hx' : x ∈ b') (hne : b ≠ b') =>
    FourBlockDesign.disjoint_sdiff_of_ne hU hb hb' hx hx' hne
  have e1 : (β₀ \ {x} ∪ β₁ \ {x}).ncard = 6 := by
    rw [Set.ncard_union_eq (d h₀ h₁ hx₀ hx₁ n01), c _ h₀ hx₀, c _ h₁ hx₁]
  have e2 : (β₀ \ {x} ∪ β₁ \ {x} ∪ β₂ \ {x}).ncard = 9 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨d h₀ h₂ hx₀ hx₂ n02,
      d h₁ h₂ hx₁ hx₂ n12⟩), e1, c _ h₂ hx₂]
  have e3 : (β₀ \ {x} ∪ β₁ \ {x} ∪ β₂ \ {x} ∪ β₃ \ {x}).ncard = 12 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨d h₀ h₃ hx₀ hx₃ n03, d h₁ h₃ hx₁ hx₃ n13⟩, d h₂ h₃ hx₂ hx₃ n23⟩), e2, c _ h₃ hx₃]
  have e4 : (β₀ \ {x} ∪ β₁ \ {x} ∪ β₂ \ {x} ∪ β₃ \ {x} ∪ β₄ \ {x}).ncard = 15 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨d h₀ h₄ hx₀ hx₄ n04, d h₁ h₄ hx₁ hx₄ n14⟩,
        d h₂ h₄ hx₂ hx₄ n24⟩, d h₃ h₄ hx₃ hx₄ n34⟩), e3, c _ h₄ hx₄]
  have hsub : β₀ \ {x} ∪ β₁ \ {x} ∪ β₂ \ {x} ∪ β₃ \ {x} ∪ β₄ \ {x} ⊆ ({x}ᶜ : Set Ω) := by
    intro z hz
    simp only [Set.mem_union, Set.mem_sdiff] at hz
    rcases hz with (((⟨-, hz⟩ | ⟨-, hz⟩) | ⟨-, hz⟩) | ⟨-, hz⟩) | ⟨-, hz⟩ <;> exact hz
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [e4, Set.ncard_compl, Set.ncard_singleton, hΩ] at hle
  omega

theorem FourBlockDesign.exists_mem_inter [Finite Ω] (hΩ : Nat.card Ω = 13) {B : Set (Set Ω)}
    (h4 : ∀ b ∈ B, b.ncard = 4)
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    (hex : ∀ x y : Ω, x ≠ y → ∃ b ∈ B, x ∈ b ∧ y ∈ b) {b b' : Set Ω} (hb : b ∈ B)
    (hb' : b' ∈ B) : ∃ z, z ∈ b ∧ z ∈ b' := by
  by_contra hdisj
  push Not at hdisj
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := b') (by rw [h4 b' hb']; norm_num)
  have hxb : x ∉ b := fun h => hdisj x h hx
  obtain ⟨y₁, hy₁⟩ := Set.nonempty_of_ncard_ne_zero (s := b) (by rw [h4 b hb]; norm_num)
  obtain ⟨y₂, hy₂, n21, -, -⟩ := FourBlockDesign.exists_mem_ne_three (h4 b hb) y₁ y₁ y₁
  obtain ⟨y₃, hy₃, n31, n32, -⟩ := FourBlockDesign.exists_mem_ne_three (h4 b hb) y₁ y₂ y₂
  obtain ⟨y₄, hy₄, n41, n42, n43⟩ := FourBlockDesign.exists_mem_ne_three (h4 b hb) y₁ y₂ y₃
  have hxy : ∀ y ∈ b, x ≠ y := fun y hy h => hxb (h ▸ hy)
  obtain ⟨c₁, hc₁, hxc₁, hyc₁⟩ := hex x y₁ (hxy y₁ hy₁)
  obtain ⟨c₂, hc₂, hxc₂, hyc₂⟩ := hex x y₂ (hxy y₂ hy₂)
  obtain ⟨c₃, hc₃, hxc₃, hyc₃⟩ := hex x y₃ (hxy y₃ hy₃)
  obtain ⟨c₄, hc₄, hxc₄, hyc₄⟩ := hex x y₄ (hxy y₄ hy₄)
  have nb' : ∀ c y, y ∈ b → y ∈ c → b' ≠ c := fun c y hy hyc h => hdisj y hy (h ▸ hyc)
  have ncc : ∀ c c' y y', c ∈ B → y ∈ b → y' ∈ b → y ≠ y' → y ∈ c → y' ∈ c' → x ∈ c →
      c = c' → False := fun c c' y y' hc hy hy' hyy' hyc hyc' hxc h =>
    hxb (hU c hc b hb y y' hyy' hyc (h ▸ hyc') hy hy' ▸ hxc)
  exact FourBlockDesign.not_five_blocks hΩ h4 hU hb' hc₁ hc₂ hc₃ hc₄ hx hxc₁ hxc₂ hxc₃ hxc₄
    (nb' _ _ hy₁ hyc₁) (nb' _ _ hy₂ hyc₂) (nb' _ _ hy₃ hyc₃) (nb' _ _ hy₄ hyc₄)
    (ncc _ _ _ _ hc₁ hy₁ hy₂ n21.symm hyc₁ hyc₂ hxc₁)
    (ncc _ _ _ _ hc₁ hy₁ hy₃ n31.symm hyc₁ hyc₃ hxc₁)
    (ncc _ _ _ _ hc₁ hy₁ hy₄ n41.symm hyc₁ hyc₄ hxc₁)
    (ncc _ _ _ _ hc₂ hy₂ hy₃ n32.symm hyc₂ hyc₃ hxc₂)
    (ncc _ _ _ _ hc₂ hy₂ hy₄ n42.symm hyc₂ hyc₄ hxc₂)
    (ncc _ _ _ _ hc₃ hy₃ hy₄ n43.symm hyc₃ hyc₄ hxc₃)

theorem FourBlockDesign.exists_frame [Finite Ω] (hΩ : Nat.card Ω = 13) {B : Set (Set Ω)}
    (h4 : ∀ b ∈ B, b.ncard = 4)
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    (hex : ∀ x y : Ω, x ≠ y → ∃ b ∈ B, x ∈ b ∧ y ∈ b) :
    ∃ q₀ q₁ q₂ q₃ : Ω, q₀ ≠ q₁ ∧ q₀ ≠ q₂ ∧ q₀ ≠ q₃ ∧ q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ ∧
      (∀ b ∈ B, ¬(q₀ ∈ b ∧ q₁ ∈ b ∧ q₂ ∈ b)) ∧ (∀ b ∈ B, ¬(q₀ ∈ b ∧ q₁ ∈ b ∧ q₃ ∈ b)) ∧
      (∀ b ∈ B, ¬(q₀ ∈ b ∧ q₂ ∈ b ∧ q₃ ∈ b)) ∧ (∀ b ∈ B, ¬(q₁ ∈ b ∧ q₂ ∈ b ∧ q₃ ∈ b)) := by
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q₀, q₁, h01⟩ := exists_pair_ne Ω
  obtain ⟨b01, hb01, h0, h1⟩ := hex q₀ q₁ h01
  obtain ⟨q₂, hq₂⟩ : ∃ q₂, q₂ ∉ b01 := by
    by_contra h
    push Not at h
    have h' := h4 b01 hb01
    rw [Set.eq_univ_of_forall h, Set.ncard_univ, hΩ] at h'
    omega
  have h02 : q₀ ≠ q₂ := fun h => hq₂ (h ▸ h0)
  have h12 : q₁ ≠ q₂ := fun h => hq₂ (h ▸ h1)
  obtain ⟨b02, hb02, h0', h2'⟩ := hex q₀ q₂ h02
  obtain ⟨b12, hb12, h1'', h2''⟩ := hex q₁ q₂ h12
  obtain ⟨q₃, hq₃⟩ : ∃ q₃, q₃ ∉ b01 ∪ b02 ∪ b12 := by
    by_contra h
    push Not at h
    have hle := Set.ncard_le_ncard (fun z (_ : z ∈ (Set.univ : Set Ω)) => h z) (Set.toFinite _)
    have h3 := (Set.ncard_union_le (b01 ∪ b02) b12).trans
      (Nat.add_le_add_right (Set.ncard_union_le b01 b02) _)
    rw [Set.ncard_univ, hΩ] at hle
    rw [h4 _ hb01, h4 _ hb02, h4 _ hb12] at h3
    omega
  simp only [Set.mem_union, not_or] at hq₃
  obtain ⟨⟨hq₃a, hq₃b⟩, hq₃c⟩ := hq₃
  refine ⟨q₀, q₁, q₂, q₃, h01, h02, fun h => hq₃a (h ▸ h0), h12, fun h => hq₃a (h ▸ h1),
    fun h => hq₃b (h ▸ h2'), ?_, ?_, ?_, ?_⟩
  · rintro b hb ⟨hb0, hb1, hb2⟩
    exact hq₂ (hU b hb b01 hb01 q₀ q₁ h01 hb0 hb1 h0 h1 ▸ hb2)
  · rintro b hb ⟨hb0, hb1, hb3⟩
    exact hq₃a (hU b hb b01 hb01 q₀ q₁ h01 hb0 hb1 h0 h1 ▸ hb3)
  · rintro b hb ⟨hb0, hb2, hb3⟩
    exact hq₃b (hU b hb b02 hb02 q₀ q₂ h02 hb0 hb2 h0' h2' ▸ hb3)
  · rintro b hb ⟨hb1, hb2, hb3⟩
    exact hq₃c (hU b hb b12 hb12 q₁ q₂ h12 hb1 hb2 h1'' h2'' ▸ hb3)

theorem FourBlockDesign.image_planeLine_mem [Finite Ω] {B : Set (Set Ω)} (h4 : ∀ b ∈ B, b.ncard = 4)
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    (hex : ∀ x y : Ω, x ≠ y → ∃ b ∈ B, x ∈ b ∧ y ∈ b) {p : Fin 13 → Ω}
    (hp : Function.Bijective p) {ℓ : Fin 13 → Set Ω} (hℓB : ∀ j ∈ frameLines, ℓ j ∈ B)
    (hneg : ∀ a, ∀ j ∈ frameLines, p a ∈ ℓ j ↔ a ∈ planeLine j) (j : Fin 13) :
    p '' (planeLine j : Set (Fin 13)) ∈ B := by
  have hcard : (p '' (planeLine j : Set (Fin 13))).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ hp.1, Set.ncard_coe_finset, card_planeLine]
  by_cases hj : j ∈ frameLines
  · have hsub : p '' (planeLine j : Set (Fin 13)) ⊆ ℓ j := by
      rintro _ ⟨a, ha, rfl⟩
      exact (hneg a j hj).mpr ha
    rw [Set.eq_of_subset_of_ncard_le hsub (by rw [h4 _ (hℓB j hj), hcard]) (Set.toFinite _)]
    exact hℓB j hj
  obtain ⟨a, b, hab, haj, hbj, hnot, hwit⟩ := exists_isLineWitness j hj
  have hpab : p a ≠ p b := fun h => hab (hp.1 h)
  obtain ⟨β, hβ, hpa, hpb⟩ := hex (p a) (p b) hpab
  have h2 : (β \ {p a, p b}).ncard = 2 := by
    rw [Set.ncard_sdiff (by
      intro z hz
      rcases hz with rfl | rfl
      · exact hpa
      · exact hpb), h4 β hβ, Set.ncard_pair hpab]
  obtain ⟨z, w, hzw, hzw_eq⟩ := Set.ncard_eq_two.mp h2
  have hz : z ∈ β \ {p a, p b} := by
    rw [hzw_eq]
    exact Set.mem_insert _ _
  have hw : w ∈ β \ {p a, p b} := by
    rw [hzw_eq]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨x, rfl⟩ := hp.2 z
  obtain ⟨y, rfl⟩ := hp.2 w
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz hw
  obtain ⟨hx, hxa, hxb⟩ := hz
  obtain ⟨hy, hya, hyb⟩ := hw
  have hβℓ : ∀ i ∈ frameLines, ∀ u v : Fin 13, u ≠ v → p u ∈ β → p v ∈ β → u ∈ planeLine i →
      v ∈ planeLine i → β = ℓ i := fun i hi u v huv hu hv hui hvi =>
    hU β hβ (ℓ i) (hℓB i hi) (p u) (p v) (fun h => huv (hp.1 h)) hu hv ((hneg u i hi).mpr hui)
      ((hneg v i hi).mpr hvi)
  have hoffℓ : ∀ i ∈ frameLines, β ≠ ℓ i := fun i hi h =>
    hnot i hi ⟨(hneg a i hi).mp (h ▸ hpa), (hneg b i hi).mp (h ▸ hpb)⟩
  have hoff : ∀ u, u ≠ a → u ≠ b → p u ∈ β → IsOffFrameLines a b u := fun u hua hub hu i hi =>
    ⟨fun hai hui => hoffℓ i hi (hβℓ i hi a u (Ne.symm hua) hpa hu hai hui),
      fun hbi hui => hoffℓ i hi (hβℓ i hi b u (Ne.symm hub) hpb hu hbi hui)⟩
  have hxa' : x ≠ a := fun h => hxa (h ▸ rfl)
  have hxb' : x ≠ b := fun h => hxb (h ▸ rfl)
  have hya' : y ≠ a := fun h => hya (h ▸ rfl)
  have hyb' : y ≠ b := fun h => hyb (h ▸ rfl)
  have hxy : x ≠ y := fun h => hzw (h ▸ rfl)
  obtain ⟨hxj, hyj⟩ := hwit x y hxy hxa' hxb' hya' hyb' (hoff x hxa' hxb' hx)
    (hoff y hya' hyb' hy) fun i hi ⟨hxi, hyi⟩ => hoffℓ i hi (hβℓ i hi x y hxy hx hy hxi hyi)
  have hsub : β ⊆ p '' (planeLine j : Set (Fin 13)) := by
    intro u hu
    by_cases hu' : u ∈ ({p a, p b} : Set Ω)
    · rcases hu' with rfl | rfl
      · exact ⟨a, haj, rfl⟩
      · exact ⟨b, hbj, rfl⟩
    · have : u ∈ ({p x, p y} : Set Ω) := hzw_eq ▸ ⟨hu, hu'⟩
      rcases this with rfl | rfl
      · exact ⟨x, hxj, rfl⟩
      · exact ⟨y, hyj, rfl⟩
  rw [← Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, h4 β hβ]) (Set.toFinite _)]
  exact hβ

theorem FourBlockDesign.exists_plane_labelling [Finite Ω] (hΩ : Nat.card Ω = 13) {B : Set (Set Ω)}
    (h4 : ∀ b ∈ B, b.ncard = 4)
    (hU : ∀ b ∈ B, ∀ b' ∈ B, ∀ x y : Ω, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b')
    (hex : ∀ x y : Ω, x ≠ y → ∃ b ∈ B, x ∈ b ∧ y ∈ b) :
    ∃ p : Fin 13 → Ω, Function.Bijective p ∧ ∀ j, p '' (planeLine j : Set (Fin 13)) ∈ B := by
  obtain ⟨q₀, q₁, q₂, q₃, d01, d02, d03, d12, d13, d23, n012, n013, n023, n123⟩ :=
    FourBlockDesign.exists_frame hΩ h4 hU hex
  obtain ⟨l01, hl01, a01, b01⟩ := hex q₀ q₁ d01
  obtain ⟨l02, hl02, a02, b02⟩ := hex q₀ q₂ d02
  obtain ⟨l03, hl03, a03, b03⟩ := hex q₀ q₃ d03
  obtain ⟨l12, hl12, a12, b12⟩ := hex q₁ q₂ d12
  obtain ⟨l13, hl13, a13, b13⟩ := hex q₁ q₃ d13
  obtain ⟨l23, hl23, a23, b23⟩ := hex q₂ q₃ d23
  obtain ⟨r₄, r₄a, r₄b⟩ := FourBlockDesign.exists_mem_inter hΩ h4 hU hex hl01 hl23
  obtain ⟨r₅, r₅a, r₅b⟩ := FourBlockDesign.exists_mem_inter hΩ h4 hU hex hl02 hl13
  obtain ⟨r₆, r₆a, r₆b⟩ := FourBlockDesign.exists_mem_inter hΩ h4 hU hex hl03 hl12
  obtain ⟨r₇, r₇l, r₇0, r₇1, r₇4⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl01) q₀ q₁ r₄
  obtain ⟨r₈, r₈l, r₈0, r₈2, r₈5⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl02) q₀ q₂ r₅
  obtain ⟨r₉, r₉l, r₉1, r₉2, r₉6⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl12) q₁ q₂ r₆
  obtain ⟨r₁₀, r₁₀l, r₁₀2, r₁₀3, r₁₀4⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl23) q₂ q₃ r₄
  obtain ⟨r₁₁, r₁₁l, r₁₁1, r₁₁3, r₁₁5⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl13) q₁ q₃ r₅
  obtain ⟨r₁₂, r₁₂l, r₁₂0, r₁₂3, r₁₂6⟩ := FourBlockDesign.exists_mem_ne_three (h4 _ hl03) q₀ q₃ r₆
  let p : Fin 13 → Ω := ![q₀, q₁, q₂, q₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀, r₁₁, r₁₂]
  let ℓ : Fin 13 → Set Ω := ![l12, l02, l01, ∅, ∅, ∅, ∅, l23, l13, l03, ∅, ∅, ∅]
  have hℓB : ∀ j ∈ frameLines, ℓ j ∈ B := by
    intro j hj
    simp only [frameLines, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hP : ∀ j ∈ frameLines, ∀ a ∈ planeLine j, p a ∈ ℓ j := by
    intro j hj a ha
    simp only [frameLines, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases a <;> first | exact absurd ha (by decide) | assumption
  have hIV : ∀ a m, (a, m) ∈ fourthPointPairs → p a ≠ p m := by
    intro a m h
    fin_cases a <;> fin_cases m <;> first | exact absurd h (by decide) | assumption
  obtain ⟨hneg, hinj⟩ :=
    FourBlockDesign.frame_labelling_injective hU p ℓ hℓB hP n012 n013 n023 n123 hIV
  have hbij : Function.Bijective p :=
    hinj.bijective_of_nat_card_le (by rw [hΩ, Nat.card_eq_fintype_card, Fintype.card_fin])
  exact ⟨p, hbij, FourBlockDesign.image_planeLine_mem h4 hU hex hbij hℓB hneg⟩

end Design

theorem thirteen_point_four_block_plane_coordinatization {Ω : Type*} (hΩ : Nat.card Ω = 13)
    (B : Set (Set Ω)) (h4 : ∀ b ∈ B, b.ncard = 4)
    (hu : ∀ x y : Ω, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b) :
    (∃ f : Ω ≃ ProjPoint, (fun b => f '' b) '' B = projLineSets) ∧ B.ncard = 13 ∧
      (∀ u : Ω, {b ∈ B | u ∈ b}.ncard = 4) ∧
      ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (b ∩ b').ncard = 1 := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have hU := FourBlockDesign.block_eq_of_mem hu
  have hex : ∀ x y : Ω, x ≠ y → ∃ b ∈ B, x ∈ b ∧ y ∈ b := fun x y h => by
    obtain ⟨b, ⟨hb, hx, hy⟩, -⟩ := hu x y h
    exact ⟨b, hb, hx, hy⟩
  obtain ⟨p, hp, hpB⟩ := FourBlockDesign.exists_plane_labelling hΩ h4 hU hex
  have hB : ∀ b ∈ B, ∃ j, p '' (planeLine j : Set (Fin 13)) = b := by
    intro b hb
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := b) (by rw [h4 b hb]; norm_num)
    obtain ⟨y, hy, hyx, -, -⟩ := FourBlockDesign.exists_mem_ne_three (h4 b hb) x x x
    obtain ⟨a, rfl⟩ := hp.2 x
    obtain ⟨a', rfl⟩ := hp.2 y
    obtain ⟨j, ha, ha'⟩ := exists_planeLine_mem a a'
    exact ⟨j, hU _ (hpB j) b hb (p a) (p a') (Ne.symm hyx) ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩ hx hy⟩
  have hlinj : Function.Injective fun j => p '' (planeLine j : Set (Fin 13)) := fun j j' h =>
    planeLine_injective j j' (Finset.coe_injective (Set.image_injective.mpr hp.1 h))
  have hBeq : B = Set.range fun j => p '' (planeLine j : Set (Fin 13)) := by
    ext b
    constructor
    · intro hb
      exact hB b hb
    · rintro ⟨j, rfl⟩
      exact hpB j
  let e : Fin 13 ≃ Ω := Equiv.ofBijective p hp
  have hfp : ∀ j, (e.symm.trans projPointEquiv) '' (p '' (planeLine j : Set (Fin 13))) =
      projPointOf '' (planeLine j : Set (Fin 13)) := fun j => by
    rw [Set.image_image]
    refine Set.image_congr fun a _ => ?_
    simp [e, projPointEquiv_apply]
  refine ⟨⟨e.symm.trans projPointEquiv, ?_⟩, ?_, ?_, ?_⟩
  · ext S
    rw [mem_projLineSets_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨j, rfl⟩ := hB b hb
      exact ⟨j, (hfp j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, hpB j, hfp j⟩
  · rw [hBeq, Set.ncard_range_of_injective hlinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro u
    obtain ⟨a, rfl⟩ := hp.2 u
    have hset : {b ∈ B | p a ∈ b} = (fun j => p '' (planeLine j : Set (Fin 13))) ''
        ↑(Finset.univ.filter fun j => a ∈ planeLine j) := by
      ext b
      constructor
      · rintro ⟨hb, hab⟩
        obtain ⟨j, rfl⟩ := hB b hb
        refine ⟨j, ?_, rfl⟩
        simpa using (hp.1.mem_set_image).mp hab
      · rintro ⟨j, hj, rfl⟩
        refine ⟨hpB j, a, ?_, rfl⟩
        simpa using hj
    rw [hset, Set.ncard_image_of_injective _ hlinj, Set.ncard_coe_finset, card_lines_through]
  · intro b hb b' hb' hne
    obtain ⟨j, rfl⟩ := hB b hb
    obtain ⟨j', rfl⟩ := hB b' hb'
    have hjj' : j ≠ j' := by
      rintro rfl
      exact hne rfl
    rw [← Set.image_inter hp.1, Set.ncard_image_of_injective _ hp.1, ← Finset.coe_inter,
      Set.ncard_coe_finset, card_planeLine_inter j j' hjj']

end CFSG.Semidihedral.GL2Recognition
