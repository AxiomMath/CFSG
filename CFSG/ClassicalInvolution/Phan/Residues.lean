module

public import CFSG.ClassicalInvolution.Phan.Frames
public import CFSG.ClassicalInvolution.Phan.Frames.Product
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  Module

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def suppPos (J : Set (Fin n)) : Set (Fin (n + 1)) :=
  {k | ∃ j ∈ J, k = j.castSucc ∨ k = j.succ}

theorem castSucc_mem_suppPos {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) :
    j.castSucc ∈ suppPos J :=
  ⟨j, hj, Or.inl rfl⟩

theorem succ_mem_suppPos {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) : j.succ ∈ suppPos J :=
  ⟨j, hj, Or.inr rfl⟩

theorem residue_agree {J : Set (Fin n)} {c d : Frame σ (n + 1)}
    (h : d ∈ (frameSystem σ n).residue J c) {k : Fin (n + 1)} (hk : k ∉ suppPos J) :
    d.line k = c.line k := by
  refine mem_residue_induction (X := frameSystem σ n) (fun e => e.line k = c.line k) rfl ?_ d h
  intro e f j hj he hef
  have h1 : k ≠ j.castSucc := fun h' => hk (h' ▸ castSucc_mem_suppPos hj)
  have h2 : k ≠ j.succ := fun h' => hk (h' ▸ succ_mem_suppPos hj)
  rw [← he]
  exact (hef k h1 h2).symm

@[expose] def Separated (i j : Fin n) : Prop := i.val + 1 < j.val ∨ j.val + 1 < i.val

theorem Separated.symm {i j : Fin n} (h : Separated i j) : Separated j i := Or.symm h

theorem Separated.castSucc_ne_castSucc {i j : Fin n} (h : Separated i j) :
    j.castSucc ≠ i.castSucc := by
  rintro h'
  have := congrArg Fin.val h'
  simp only [Fin.val_castSucc] at this
  unfold Separated at h
  omega

theorem Separated.castSucc_ne_succ {i j : Fin n} (h : Separated i j) : j.castSucc ≠ i.succ := by
  rintro h'
  have := congrArg Fin.val h'
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  unfold Separated at h
  omega

theorem Separated.succ_ne_castSucc {i j : Fin n} (h : Separated i j) : j.succ ≠ i.castSucc := by
  rintro h'
  have := congrArg Fin.val h'
  simp only [Fin.val_succ, Fin.val_castSucc] at this
  unfold Separated at h
  omega

theorem Separated.succ_ne_succ {i j : Fin n} (h : Separated i j) : j.succ ≠ i.succ := by
  rintro h'
  have := congrArg Fin.val h'
  simp only [Fin.val_succ] at this
  unfold Separated at h
  omega

theorem commuteTypes_of_separated (hσ : IsUnitaryInvolution σ) {i j : Fin n}
    (h : Separated i j) : CommuteTypes (frameSystem σ n) i j := by
  intro x y z hxy hyz
  have e1 : x.line j.castSucc = y.line j.castSucc := hxy _ h.castSucc_ne_castSucc h.castSucc_ne_succ
  have e2 : x.line j.succ = y.line j.succ := hxy _ h.succ_ne_castSucc h.succ_ne_succ
  have hplane : x.line j.castSucc ⊔ x.line j.succ = z.line j.castSucc ⊔ z.line j.succ := by
    rw [e1, e2]
    exact adj_sup_eq hσ hyz
  have hmem : ∀ l, l = j.castSucc ∨ l = j.succ →
      z.line l ∈ nsPts σ (x.line j.castSucc ⊔ x.line j.succ) := by
    intro l hl
    refine ⟨?_, z.finrank_line l, z.nondeg_line l⟩
    rw [hplane]
    rcases hl with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  refine ⟨x.replace hσ j.castSucc j.succ (castSucc_ne_succ j) (z.line j.castSucc)
    (z.line j.succ) (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
    (z.orth_line _ _ (castSucc_ne_succ j)), ?_, ?_⟩
  · intro k hk1 hk2
    exact (Frame.replaceLine_of_ne x hk1 hk2 _ _).symm
  · intro k hk1 hk2
    by_cases hkc : k = j.castSucc
    · subst hkc
      exact Frame.replaceLine_left x _ _
    · by_cases hks : k = j.succ
      · subst hks
        exact Frame.replaceLine_right x (castSucc_ne_succ j) _ _
      · change Frame.replaceLine x j.castSucc j.succ _ _ k = _
        rw [Frame.replaceLine_of_ne x hkc hks, hxy k hk1 hk2, hyz k hkc hks]

theorem eq_of_mem_residue_inter {J₁ J₂ : Set (Fin n)} (hsep : ∀ i ∈ J₁, ∀ j ∈ J₂, Separated i j)
    {c d : Frame σ (n + 1)} (h₁ : d ∈ (frameSystem σ n).residue J₁ c)
    (h₂ : d ∈ (frameSystem σ n).residue J₂ c) : d = c := by
  refine Frame.ext (funext fun k => ?_)
  by_cases hk1 : k ∈ suppPos J₁
  · by_cases hk2 : k ∈ suppPos J₂
    · exfalso
      obtain ⟨i, hi, hki⟩ := hk1
      obtain ⟨j, hj, hkj⟩ := hk2
      have hij := hsep i hi j hj
      unfold Separated at hij
      rcases hki with hki | hki <;> rcases hkj with hkj | hkj <;>
        · have := congrArg Fin.val (hki.symm.trans hkj)
          simp only [Fin.val_castSucc, Fin.val_succ] at this
          omega
    · exact residue_agree h₂ hk2
  · exact residue_agree h₁ hk1

variable (σ n) in
@[expose] def NullOn (J : Set (Fin n)) : Prop :=
  ∀ (c : Frame σ (n + 1)) (γ : List (Fin n × Frame σ (n + 1))),
    (frameSystem σ n).IsGallery c γ → (∀ i ∈ galleryType γ, i ∈ J) → galleryEnd c γ = c →
      (frameSystem σ n).TwoHomotopic c γ []

theorem NullOn.mono {J J' : Set (Fin n)} (h : J ⊆ J') (hJ' : NullOn σ n J') : NullOn σ n J :=
  fun c γ hγ hJ hend => hJ' c γ hγ (fun i hi => h (hJ i hi)) hend

theorem nullOn_of_encard_le_two {J : Set (Fin n)} (hJ : J.encard ≤ 2) : NullOn σ n J :=
  fun c γ hγ hJγ hend => by
    have := twoHomotopic_replace (X := frameSystem σ n) (x := c) [] γ [] [] hJ
      (by simpa using hγ) (by simp) (by simpa using hJγ) (by simp) (by simpa using hend)
    simpa using this

theorem simplyTwoConnected_iff_nullOn_univ :
    (frameSystem σ n).SimplyTwoConnected ↔ NullOn σ n Set.univ :=
  ⟨fun h c γ hγ _ hend => h c γ hγ hend, fun h c γ hγ hend => h c γ hγ (fun _ _ => trivial) hend⟩

theorem NullOn.union (hσ : IsUnitaryInvolution σ) {J₁ J₂ : Set (Fin n)}
    (hsep : ∀ i ∈ J₁, ∀ j ∈ J₂, Separated i j) (h₁ : NullOn σ n J₁) (h₂ : NullOn σ n J₂) :
    NullOn σ n (J₁ ∪ J₂) := fun c γ hγ hJ hend =>
  twoHomotopic_nil_of_union (X := frameSystem σ n)
    (fun j hj i hi => commuteTypes_of_separated hσ (hsep i hi j hj).symm)
    (fun _ _ hd₁ hd₂ => eq_of_mem_residue_inter hsep hd₁ hd₂) h₁ h₂ c γ hγ hJ hend

@[expose] def typeInt (n a b : ℕ) : Set (Fin n) := {j | a ≤ j.val ∧ j.val < b}

@[expose] def posInt (n a b : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun k => a ≤ k.val ∧ k.val ≤ b

theorem mem_typeInt {a b : ℕ} {j : Fin n} : j ∈ typeInt n a b ↔ a ≤ j.val ∧ j.val < b :=
  Iff.rfl

theorem mem_posInt {a b : ℕ} {k : Fin (n + 1)} : k ∈ posInt n a b ↔ a ≤ k.val ∧ k.val ≤ b := by
  simp [posInt]

theorem typeInt_mono {a a' b b' : ℕ} (h₁ : a ≤ a') (h₂ : b' ≤ b) :
    typeInt n a' b' ⊆ typeInt n a b :=
  fun _ hj => ⟨h₁.trans hj.1, hj.2.trans_le h₂⟩

theorem encard_typeInt_le_two {a b : ℕ} (h : b ≤ a + 2) : (typeInt n a b).encard ≤ 2 := by
  have h1 : ∀ c : ℕ, ({j : Fin n | j.val = c} : Set (Fin n)).encard ≤ 1 := fun c =>
    Set.encard_le_one_iff.2 fun x y hx hy => Fin.ext (by
      have h1 : x.val = c := hx
      have h2 : y.val = c := hy
      omega)
  have hsub : typeInt n a b ⊆ {j : Fin n | j.val = a} ∪ {j : Fin n | j.val = a + 1} := by
    intro j hj
    obtain ⟨h₁, h₂⟩ := hj
    show j.val = a ∨ j.val = a + 1
    omega
  calc (typeInt n a b).encard
      ≤ ({j : Fin n | j.val = a} ∪ {j : Fin n | j.val = a + 1}).encard :=
        Set.encard_le_encard hsub
    _ ≤ ({j : Fin n | j.val = a}).encard + ({j : Fin n | j.val = a + 1}).encard :=
        Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add (h1 a) (h1 (a + 1))
    _ = 2 := by norm_num

theorem nullOn_typeInt_of_le_two {a b : ℕ} (h : b ≤ a + 2) : NullOn σ n (typeInt n a b) :=
  nullOn_of_encard_le_two (encard_typeInt_le_two h)

theorem typeInt_zero_self : typeInt n 0 n = Set.univ :=
  Set.eq_univ_of_forall fun j => ⟨Nat.zero_le _, j.isLt⟩

theorem separated_of_typeInt {a k b : ℕ} {i j : Fin n} (hi : i ∈ typeInt n a k)
    (hj : j ∈ typeInt n (k + 1) b) : Separated i j :=
  Or.inl (by have := hi.2; have := hj.1; omega)

theorem typeInt_union_eq_diff {a k b : ℕ} (hak : a ≤ k) (hkb : k < b) (hbn : b ≤ n) :
    typeInt n a k ∪ typeInt n (k + 1) b = typeInt n a b \ {(⟨k, by omega⟩ : Fin n)} := by
  ext j
  simp only [Set.mem_union, mem_typeInt, Set.mem_sdiff, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem NullOn.typeInt_union (hσ : IsUnitaryInvolution σ) {a k b : ℕ}
    (h₁ : NullOn σ n (typeInt n a k)) (h₂ : NullOn σ n (typeInt n (k + 1) b)) :
    NullOn σ n (typeInt n a k ∪ typeInt n (k + 1) b) :=
  NullOn.union hσ (fun _ hi _ hj => separated_of_typeInt hi hj) h₁ h₂

theorem nullOn_of_runs (hσ : IsUnitaryInvolution σ)
    (h : ∀ a b : ℕ, a + 3 ≤ b → b ≤ n →
      (∀ J' : Set (Fin n), J'.ncard < (typeInt n a b).ncard → NullOn σ n J') →
        NullOn σ n (typeInt n a b))
    (J : Set (Fin n)) : NullOn σ n J := by
  suffices key : ∀ N : ℕ, ∀ J : Set (Fin n), J.ncard = N → NullOn σ n J from key _ J rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro J hN
  by_cases hsmall : J.ncard ≤ 2
  · refine nullOn_of_encard_le_two ?_
    rw [← Set.Finite.cast_ncard_eq (Set.toFinite J)]
    exact_mod_cast hsmall
  push Not at hsmall
  have hne : J.Nonempty := Set.nonempty_iff_ne_empty.2 fun hJ => by
    rw [hJ, Set.ncard_empty] at hsmall
    omega
  by_cases hconv : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ∀ g : Fin n, j₁ < g → g < j₂ → g ∈ J
  ·
    obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image J id (Set.toFinite J) hne
    obtain ⟨b₀, hb₀, hmax⟩ := Set.exists_max_image J id (Set.toFinite J) hne
    have hJ : J = typeInt n a₀.val (b₀.val + 1) := by
      ext j
      refine ⟨fun hj => ⟨hmin j hj, Nat.lt_succ_of_le (hmax j hj)⟩, fun hj => ?_⟩
      obtain ⟨hj1, hj2⟩ := hj
      rcases lt_trichotomy j a₀ with hlt | heq | hgt
      · exact absurd hj1 (not_le.2 (Fin.lt_def.1 hlt))
      · exact heq ▸ ha₀
      · rcases lt_trichotomy j b₀ with hlt | heq | hgt'
        · exact hconv a₀ ha₀ b₀ hb₀ j hgt hlt
        · exact heq ▸ hb₀
        · exact absurd (Nat.lt_succ_iff.1 hj2) (not_le.2 (Fin.lt_def.1 hgt'))
    have hN' : (typeInt n a₀.val (b₀.val + 1)).ncard = N := hJ ▸ hN
    rw [hJ]
    refine h _ _ ?_ b₀.isLt fun J' hJ' => ih _ (hN' ▸ hJ') J' rfl
    by_contra hlt
    have := encard_typeInt_le_two (n := n) (a := a₀.val) (b := b₀.val + 1) (by omega)
    rw [← Set.Finite.cast_ncard_eq (Set.toFinite _)] at this
    have : (typeInt n a₀.val (b₀.val + 1)).ncard ≤ 2 := by exact_mod_cast this
    omega
  · push Not at hconv
    obtain ⟨j₁, hj₁, j₂, hj₂, g, hg₁, hg₂, hgJ⟩ := hconv
    have hU : J = {j ∈ J | j < g} ∪ {j ∈ J | g < j} := by
      ext j
      refine ⟨fun hj => ?_, fun hj => hj.elim (fun h => h.1) fun h => h.1⟩
      rcases lt_trichotomy j g with hlt | heq | hgt
      · exact Or.inl ⟨hj, hlt⟩
      · exact absurd (heq ▸ hj) hgJ
      · exact Or.inr ⟨hj, hgt⟩
    have hlt₁ : {j ∈ J | j < g}.ncard < N := by
      rw [← hN]
      exact Set.ncard_lt_ncard ⟨fun j hj => hj.1, fun hsub => (hsub hj₂).2.not_gt hg₂⟩
        (Set.toFinite J)
    have hlt₂ : {j ∈ J | g < j}.ncard < N := by
      rw [← hN]
      exact Set.ncard_lt_ncard ⟨fun j hj => hj.1, fun hsub => (hsub hj₁).2.not_gt hg₁⟩
        (Set.toFinite J)
    rw [hU]
    refine NullOn.union hσ (fun i hi j hj => Or.inl ?_) (ih _ hlt₁ _ rfl) (ih _ hlt₂ _ rfl)
    have h1 : i.val < g.val := hi.2
    have h2 : g.val < j.val := hj.2
    omega

theorem simplyTwoConnected_of_runs (hσ : IsUnitaryInvolution σ)
    (h : ∀ a b : ℕ, a + 3 ≤ b → b ≤ n →
      (∀ J' : Set (Fin n), J'.ncard < (typeInt n a b).ncard → NullOn σ n J') →
        NullOn σ n (typeInt n a b)) :
    (frameSystem σ n).SimplyTwoConnected :=
  simplyTwoConnected_iff_nullOn_univ.2 (nullOn_of_runs hσ h Set.univ)

theorem mem_posInt_of_mem_suppPos {a b : ℕ} {k : Fin (n + 1)}
    (hk : k ∈ suppPos (typeInt n a b)) : k ∈ posInt n a b := by
  obtain ⟨j, hj, hkj⟩ := hk
  rw [mem_posInt]
  obtain ⟨hj1, hj2⟩ := hj
  rcases hkj with rfl | rfl <;> simp <;> omega

theorem posInt_self {a : ℕ} (ha : a ≤ n) : posInt n a a = {⟨a, by omega⟩} := by
  ext k
  simp only [mem_posInt, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem card_posInt {a b : ℕ} (hb : b ≤ n) : (posInt n a b).card = b + 1 - a := by
  have : (posInt n a b).map Fin.valEmbedding = Finset.Icc a b := by
    ext v
    simp only [Finset.mem_map, mem_posInt, Fin.valEmbedding_apply, Finset.mem_Icc]
    constructor
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨v, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Icc]

theorem residue_typeInt_agree {a b : ℕ} {c d : Frame σ (n + 1)}
    (h : d ∈ (frameSystem σ n).residue (typeInt n a b) c) {k : Fin (n + 1)}
    (hk : k ∉ posInt n a b) : d.line k = c.line k :=
  residue_agree h fun h' => hk (mem_posInt_of_mem_suppPos h')

theorem spanAt_posInt_of_mem_residue (hσ : IsUnitaryInvolution σ) {a b : ℕ} {c d : Frame σ (n + 1)}
    (h : d ∈ (frameSystem σ n).residue (typeInt n a b) c) :
    d.spanAt (posInt n a b) = c.spanAt (posInt n a b) :=
  d.spanAt_eq_of_agree hσ fun _ hk => residue_typeInt_agree h hk

section Block

variable [Finite K] {q : ℕ}

theorem exists_residue_line_eq (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2)
    (hq : 3 ≤ q) :
    ∀ (r a b : ℕ) (hb : b = a + r) (hbn : b ≤ n) (c : Frame σ (n + 1))
      (x : Submodule K (Fin (n + 1) → K)), x ∈ nsPts σ (c.spanAt (posInt n a b)) →
      ∃ c' ∈ (frameSystem σ n).residue (typeInt n a b) c, c'.line ⟨a, by omega⟩ = x := by
  intro r
  induction r with
  | zero =>
    intro a b hb hbn c x hx
    obtain rfl : b = a := by omega
    refine ⟨c, self_mem_residue _ _, ?_⟩
    rw [posInt_self hbn, Frame.spanAt_singleton] at hx
    exact (Submodule.eq_of_le_of_finrank_eq hx.1 (by rw [hx.2.1, c.finrank_line])).symm
  | succ r ih =>
    intro a b hb hbn c x hx
    have han : a < n := by omega
    set i : Fin n := ⟨a, han⟩ with hi
    have hJi : i ∈ typeInt n a b := ⟨le_refl a, by simp [hi]; omega⟩
    have hpaV : i.castSucc ∈ posInt n a b := mem_posInt.2 ⟨le_refl a, by simp [hi]; omega⟩
    have claim1 : ∀ (c₁ : Frame σ (n + 1)) (x₁ : Submodule K (Fin (n + 1) → K)),
        x₁ ∈ nsPts σ (c₁.spanAt (posInt n a b)) → IsCollinear σ (c₁.line i.castSucc) x₁ →
        ∃ c₂ ∈ (frameSystem σ n).residue (typeInt n a b) c₁, c₂.line i.castSucc = x₁ := by
      intro c₁ x₁ hx₁ hcol
      set P : Submodule K (Fin (n + 1) → K) := c₁.line i.castSucc ⊔ x₁ with hP
      have hPnd : Nondeg σ P := hcol.2
      have hP2 : finrank K P = 2 :=
        finrank_sup_of_ne_pts (c₁.finrank_line _) hx₁.2.1 hcol.1
      have hL : c₁.line i.castSucc ∈ nsPts σ P :=
        ⟨le_sup_left, c₁.finrank_line _, c₁.nondeg_line _⟩
      obtain ⟨z, hz, hzo, hzP⟩ := exists_orth_complement_in_plane hσ hP2 hPnd hL
      have hPle : P ≤ c₁.spanAt (posInt n a b) := sup_le (c₁.line_le_spanAt hpaV) hx₁.1
      have hzV' : z ∈ nsPts σ (c₁.spanAt (posInt n (a + 1) b)) := by
        refine ⟨(c₁.le_spanAt_iff hσ).2 fun l hl => ?_, hz.2.1, hz.2.2⟩
        by_cases hlp : l = i.castSucc
        · rw [hlp]
          exact hzo
        · have hl' : l ∉ posInt n a b := by
            rw [mem_posInt] at hl ⊢
            have : l.val ≠ a := fun h => hlp (Fin.ext (by simpa [hi] using h))
            omega
          exact (c₁.orth_spanAt hl').mono le_rfl (hz.1.trans hPle)
      obtain ⟨cs, hcs, hcsz⟩ := ih (a + 1) b (by omega) hbn c₁ z hzV'
      have hcspa : cs.line i.castSucc = c₁.line i.castSucc :=
        residue_typeInt_agree hcs (by rw [mem_posInt]; simp [hi])
      have hcsz' : cs.line i.succ = z := hcsz
      have hplane : cs.line i.castSucc ⊔ cs.line i.succ = P := by
        rw [hcspa, hcsz', hzP]
      have hx' : x₁ ∈ nsPts σ (cs.line i.castSucc ⊔ cs.line i.succ) := by
        rw [hplane]
        exact ⟨le_sup_right, hx₁.2.1, hx₁.2.2⟩
      obtain ⟨c', hadj, hc'⟩ := exists_adj_line_eq hσ cs i hx'
      refine ⟨c', mem_residue_trans (residue_mono (typeInt_mono (Nat.le_succ a) le_rfl) c₁ hcs) ?_,
        hc'⟩
      refine residue_mono (Set.singleton_subset_iff.2 hJi) _ ?_
      rw [mem_residue_singleton]
      exact hadj
    by_cases hxc : x = c.line i.castSucc
    · exact ⟨c, self_mem_residue _ _, hxc.symm⟩
    by_cases hcol : IsCollinear σ (c.line i.castSucc) x
    · exact claim1 c x hx hcol
    have hV := c.nondeg_spanAt hσ (posInt n a b)
    have hdim : finrank K (c.spanAt (posInt n a b)) = r + 2 := by
      rw [c.finrank_spanAt, card_posInt hbn]
      omega
    have hpa_mem : c.line i.castSucc ∈ nsPts σ (c.spanAt (posInt n a b)) :=
      ⟨c.line_le_spanAt hpaV, c.finrank_line _, c.nondeg_line _⟩
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exact absurd (isCollinear_of_le_plane (by rw [hdim, hr]) hV ⟨hpa_mem.1, hpa_mem.2.1⟩
        ⟨hx.1, hx.2.1⟩ (Ne.symm hxc)) hcol
    · rcases isCollinear_or_exists_common hσ hK hq hV (by omega) hpa_mem hx with
        h | ⟨y₁, hy₁, hay, hyb⟩
      · exact absurd h hcol
      · obtain ⟨c₁, hc₁, hc₁pa⟩ := claim1 c y₁ hy₁ hay
        have hx₁ : x ∈ nsPts σ (c₁.spanAt (posInt n a b)) := by
          rw [spanAt_posInt_of_mem_residue hσ hc₁]
          exact hx
        obtain ⟨c₂, hc₂, hc₂pa⟩ := claim1 c₁ x hx₁ (by rw [hc₁pa]; exact hyb)
        exact ⟨c₂, mem_residue_trans hc₁ hc₂, hc₂pa⟩

theorem mem_residue_typeInt (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q) :
    ∀ (r a b : ℕ), b = a + r → b ≤ n → ∀ (c e : Frame σ (n + 1)),
      (∀ k, k ∉ posInt n a b → e.line k = c.line k) →
      e ∈ (frameSystem σ n).residue (typeInt n a b) c := by
  intro r
  induction r with
  | zero =>
    intro a b hb hbn c e h
    obtain rfl : b = a := by omega
    have hpos : e.line ⟨b, by omega⟩ = c.line ⟨b, by omega⟩ := by
      refine Frame.line_eq_of_agree_except hσ (c := e) (d := c) fun k hk => h k ?_
      rw [mem_posInt]
      intro hk'
      exact hk (Fin.ext (by simp; omega))
    have : e = c := Frame.ext (funext fun k => by
      by_cases hk : k = ⟨b, by omega⟩
      · rw [hk]
        exact hpos
      · exact h k (by rw [mem_posInt]; intro hk'; exact hk (Fin.ext (by simp; omega))))
    rw [this]
    exact self_mem_residue _ _
  | succ r ih =>
    intro a b hb hbn c e h
    have han : a < n := by omega
    set i : Fin n := ⟨a, han⟩ with hi
    have hpaV : i.castSucc ∈ posInt n a b := mem_posInt.2 ⟨le_refl a, by simp [hi]; omega⟩
    have hx : e.line i.castSucc ∈ nsPts σ (c.spanAt (posInt n a b)) := by
      refine ⟨(c.le_spanAt_iff hσ).2 fun l hl => ?_, e.finrank_line _, e.nondeg_line _⟩
      rw [← h l hl]
      exact e.orth_line l _ (fun h' => hl (h' ▸ hpaV))
    obtain ⟨c', hc', hc'pa⟩ := exists_residue_line_eq hσ hK hq (r + 1) a b hb hbn c _ hx
    have hih := ih (a + 1) b (by omega) hbn c' e (fun k hk => by
      by_cases hkp : k = i.castSucc
      · rw [hkp]
        exact hc'pa.symm
      · have hk' : k ∉ posInt n a b := by
          rw [mem_posInt] at hk ⊢
          have : k.val ≠ a := fun h' => hkp (Fin.ext (by simpa [hi] using h'))
          omega
        rw [h k hk', residue_typeInt_agree hc' hk'])
    exact mem_residue_trans hc' (residue_mono (typeInt_mono (Nat.le_succ a) le_rfl) c' hih)

theorem mem_residue_typeInt_iff (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2)
    (hq : 3 ≤ q) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) {c e : Frame σ (n + 1)} :
    e ∈ (frameSystem σ n).residue (typeInt n a b) c ↔
      ∀ k, k ∉ posInt n a b → e.line k = c.line k :=
  ⟨fun h _ hk => residue_typeInt_agree h hk,
    mem_residue_typeInt hσ hK hq (b - a) a b (by omega) hbn c e⟩

theorem mem_residue_typeInt_union_iff (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2)
    (hq : 3 ≤ q) {a k b : ℕ} (hak : a ≤ k) (hkb : k < b) (hbn : b ≤ n) {c e : Frame σ (n + 1)} :
    e ∈ (frameSystem σ n).residue (typeInt n a k ∪ typeInt n (k + 1) b) c ↔
      (∀ l, l ∉ posInt n a b → e.line l = c.line l) ∧
        e.spanAt (posInt n a k) = c.spanAt (posInt n a k) := by
  have hcomm : ∀ j ∈ typeInt n (k + 1) b, ∀ i ∈ typeInt n a k,
      CommuteTypes (frameSystem σ n) j i := fun j hj i hi =>
    commuteTypes_of_separated hσ (Or.inr (by have := hj.1; have := hi.2; omega))
  rw [mem_residue_union_iff hcomm]
  constructor
  · rintro ⟨f, hf, hef⟩
    have hf' := (mem_residue_typeInt_iff hσ hK hq hak (by omega : k ≤ n)).1 hf
    have he' := (mem_residue_typeInt_iff hσ hK hq (by omega : k + 1 ≤ b) hbn).1 hef
    refine ⟨fun l hl => ?_, ?_⟩
    · have h1 : l ∉ posInt n a k := by
        rw [mem_posInt] at hl ⊢
        omega
      have h2 : l ∉ posInt n (k + 1) b := by
        rw [mem_posInt] at hl ⊢
        omega
      rw [he' l h2, hf' l h1]
    · rw [Frame.spanAt_congr (d := f) fun l hl => he' l (by
        rw [mem_posInt] at hl ⊢
        omega), spanAt_posInt_of_mem_residue hσ hf]
  · rintro ⟨hagree, hspan⟩
    refine ⟨c.glue e (posInt n a k) hspan, ?_, ?_⟩
    · exact (mem_residue_typeInt_iff hσ hK hq hak (by omega : k ≤ n)).2 fun l hl =>
        Frame.glue_line_of_not_mem c e hspan hl
    · refine (mem_residue_typeInt_iff hσ hK hq (by omega : k + 1 ≤ b) hbn).2 fun l hl => ?_
      by_cases hl1 : l ∈ posInt n a k
      · rw [Frame.glue_line_of_mem c e hspan hl1]
      · have hl2 : l ∉ posInt n a b := by
          rw [mem_posInt] at hl hl1 ⊢
          omega
        rw [Frame.glue_line_of_not_mem c e hspan hl1, hagree l hl2]

theorem frameSystem_connected (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2)
    (hq : 3 ≤ q) : (frameSystem σ n).Connected := by
  intro c e
  obtain ⟨γ, hγ, -, hend⟩ := mem_residue_typeInt hσ hK hq n 0 n (by omega) le_rfl c e
    (fun k hk => absurd (mem_posInt.2 ⟨Nat.zero_le _, Nat.lt_succ_iff.mp k.isLt⟩) hk)
  exact ⟨γ, hγ, hend⟩

end Block

end CFSG.ClassicalInvolution.Phan
