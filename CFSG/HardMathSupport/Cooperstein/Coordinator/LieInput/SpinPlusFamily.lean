module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusComm
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section P142
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti


section Frame

variable {n m : ℕ}

structure DFrame (n m : ℕ) where
  ν : Fin m → Fin n
  pos : Fin (m + 1) → Fin n ⊕ Fin n
  pos_inj : Function.Injective pos
  pos_swap : ∀ i j, pos i ≠ (pos j).swap
  dg : ∀ k : Fin m, Dgamma (pos k.castSucc) (pos k.succ) = Pi.single (ν k) 1

namespace DFrame

variable (fr : DFrame n m)

theorem supp_aux (j : Fin n) : ∀ d : ℕ, ∀ u v : Fin (m + 1), v.val = u.val + d →
    (∀ k : Fin m, u.val ≤ k.val → k.val < v.val → fr.ν k ≠ j) →
    Dgamma (fr.pos u) (fr.pos v) j = 0 := by
  intro d
  induction d with
  | zero =>
    intro u v hv _
    have : u = v := Fin.ext (by omega)
    subst this
    have := two_mul_Dgamma (fr.pos u) (fr.pos u) j
    omega
  | succ d ih =>
    intro u v hv h
    have hvlt := v.isLt
    have hw : u.val + d < m + 1 := by omega
    have hk : u.val + d < m := by omega
    let w : Fin (m + 1) := ⟨u.val + d, hw⟩
    let kw : Fin m := ⟨u.val + d, hk⟩
    have e1 := ih u w rfl (fun k hk1 hk2 => h k hk1 (by simp only [w] at hk2; omega))
    have hcw : kw.castSucc = w := Fin.ext rfl
    have hsv : kw.succ = v := Fin.ext (by simp [kw]; omega)
    have e2 := fr.dg kw
    rw [hcw, hsv] at e2
    have e3 := Dgamma_add (fr.pos u) (fr.pos w) (fr.pos v)
    have h6 : (Pi.single (fr.ν kw) 1 : Fin n → ℤ) j = 0 :=
      Pi.single_eq_of_ne (fun e => h kw (by simp [kw]) (by simp [kw]; omega) e.symm) _
    have := congrFun e3 j
    simp only [Pi.add_apply] at this
    rw [e2, h6, e1] at this
    omega


open Classical in
@[expose] noncomputable def blockOf (S : Set (Fin m)) (p : Fin (m + 1)) : DBlk n ↥(blkSet S p) where
  pos u := fr.pos u.1
  nodes := fr.ν '' nodesOf (blkSet S p)
  pos_inj := fun u v h => Subtype.ext (fr.pos_inj h)
  pos_swap := fun i j => fr.pos_swap i.1 j.1
  supp := by
    intro u v j hj
    have key : ∀ u v : ↥(blkSet S p), u.1 ≤ v.1 → Dgamma (fr.pos u.1) (fr.pos v.1) j = 0 := by
      intro u v huv
      refine fr.supp_aux j (v.1.val - u.1.val) u.1 v.1 (by have := Fin.le_def.mp huv; omega) ?_
      intro k hk1 hk2 hkj
      apply hj
      refine ⟨k, ?_, hkj⟩
      have hu := u.2
      have hv := v.2
      refine ⟨blkSet_convex hu hv (by simp only [Fin.le_def, Fin.val_castSucc]; omega)
        (by simp only [Fin.le_def, Fin.val_castSucc]; omega),
        blkSet_convex hu hv (by simp only [Fin.le_def, Fin.val_succ]; omega)
        (by simp only [Fin.le_def, Fin.val_succ]; omega)⟩
    rcases le_total u.1 v.1 with h | h
    · exact key u v h
    · have := key v u h
      have h2 := Dgamma_neg (fr.pos v.1) (fr.pos u.1)
      have h3 := congrFun h2 j
      simp only [Pi.neg_apply] at h3
      rw [this] at h3
      omega
  gen := by
    rintro i ⟨k, hk, rfl⟩
    refine ⟨⟨k.castSucc, hk.1⟩, ⟨k.succ, hk.2⟩, ?_, fr.dg k⟩
    intro e
    have := congrArg (fun z : ↥(blkSet S p) => z.1.val) e
    simp at this

end DFrame

@[expose] def IsABlock {n : ℕ} (J : Set (Fin n)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (ch : DBlk n ι),
    ch.nodes = J ∧ 2 ≤ Fintype.card ι

theorem DFrame.isABlock (fr : DFrame n m) (S : Set (Fin m)) (p : Fin (m + 1))
    (hne : (nodesOf (blkSet S p)).Nonempty) : IsABlock (fr.ν '' nodesOf (blkSet S p)) := by
  classical
  obtain ⟨k, hk⟩ := hne
  refine ⟨↥(blkSet S p), inferInstance, inferInstance, fr.blockOf S p, rfl, ?_⟩
  have : ({(⟨k.castSucc, hk.1⟩ : ↥(blkSet S p)), ⟨k.succ, hk.2⟩} : Finset ↥(blkSet S p)).card = 2 := by
    rw [Finset.card_pair]
    intro e
    have := congrArg (fun z : ↥(blkSet S p) => z.1.val) e
    simp at this
  rw [← this]
  exact Finset.card_le_univ _



section Frames

@[expose] def frameId (m : ℕ) : DFrame (m + 1) m where
  ν := Fin.castSucc
  pos := fun c => Sum.inl c
  pos_inj := fun a b h => Sum.inl.inj h
  pos_swap := fun i j => by simp
  dg := fun k => by
    have := Dgamma_inl_succ (n := m + 1) k.castSucc (by simp)
    exact this

theorem frameId_ν (m : ℕ) (k : Fin m) : (frameId m).ν k = k.castSucc := rfl

@[expose] def frameTau (m : ℕ) (hm : 2 ≤ m) : DFrame (m + 1) m where
  ν := fun k => if k.val + 1 < m then k.castSucc else Fin.last m
  pos := fun c => if h : c.val < m then Sum.inl ⟨c.val, by omega⟩ else Sum.inr (Fin.last m)
  pos_inj := by
    intro a b h
    apply Fin.ext
    by_cases ha : a.val < m <;> by_cases hb : b.val < m <;> simp [ha, hb] at h
    · have := congrArg Fin.val h; simpa using this
    · have := a.isLt; have := b.isLt; omega
  pos_swap := by
    intro i j
    by_cases hi : i.val < m <;> by_cases hj : j.val < m <;> simp [hi, hj, Fin.ext_iff] <;> omega
  dg := by
    intro k
    by_cases hk : k.val + 1 < m
    · have := Dgamma_inl_succ (n := m + 1) k.castSucc (by simp [hk])
      simp only [hk, if_true]
      have e1 : (k.castSucc : Fin (m + 1)).val < m := by simp
      have e2 : (k.succ : Fin (m + 1)).val < m := by simp [hk]
      simp only [e1, e2, dite_true]
      exact this
    · have hk2 : k.val + 1 = m := by have := k.isLt; omega
      have e1 : (k.castSucc : Fin (m + 1)).val < m := by simp
      have e2 : ¬ (k.succ : Fin (m + 1)).val < m := by simp; omega
      simp only [hk, if_false, e1, e2, dite_true, dite_false]
      have := Dgamma_flag (n := m + 1) (by omega)
      convert this using 3 <;> first | rfl | (apply Fin.ext; simp; omega)

end Frames

end Frame


section Family

variable {n m : ℕ}

open Classical in
@[expose] noncomputable def blocksOf (S : Set (Fin m)) : Finset (Finset (Fin (m + 1))) :=
  (Finset.univ.image (blkSet S)).filter fun B => (nodesOf B).Nonempty

theorem mem_blocksOf {S : Set (Fin m)} {B : Finset (Fin (m + 1))} :
    B ∈ blocksOf S ↔ (∃ p, B = blkSet S p) ∧ (nodesOf B).Nonempty := by
  classical
  unfold blocksOf
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨p, rfl⟩, h⟩; exact ⟨⟨p, rfl⟩, h⟩
  · rintro ⟨⟨p, rfl⟩, h⟩; exact ⟨⟨p, rfl⟩, h⟩

theorem frame_nonadj (fr : DFrame n m) (hνinj : Function.Injective fr.ν)
    (hν : ∀ k k' : Fin m, DAdj n (fr.ν k) (fr.ν k') → k.val + 1 = k'.val ∨ k'.val + 1 = k.val)
    {S : Set (Fin m)} {p q : Fin (m + 1)} (h : blkSet S p ≠ blkSet S q) :
    ∀ i ∈ fr.ν '' nodesOf (blkSet S p), ∀ j ∈ fr.ν '' nodesOf (blkSet S q), i ≠ j ∧ ¬ DAdj n i j := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
  have hd := disjoint_blkSet h
  have hnd : ∀ c, c ∈ blkSet S p → c ∈ blkSet S q → False := fun c h1 h2 =>
    Finset.disjoint_left.mp hd h1 h2
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := hνinj e
    subst this
    exact hnd _ hk.1 hk'.1
  · rcases hν k k' e with e1 | e1
    · exact hnd k.succ hk.2 (by
        have : k.succ = k'.castSucc := Fin.ext (by simp; omega)
        rw [this]; exact hk'.1)
    · exact hnd k.castSucc hk.1 (by
        have : k.castSucc = k'.succ := Fin.ext (by simp; omega)
        rw [this]; exact hk'.2)

@[expose] def GoodFamily (n : ℕ) (I : Set (Fin n)) {β : Type} (J : β → Set (Fin n)) : Prop :=
  (∀ b, J b ⊆ I) ∧ (∀ i ∈ I, ∃ b, i ∈ J b) ∧
    (∀ b b', b ≠ b' → ∀ i ∈ J b, ∀ j ∈ J b', i ≠ j ∧ ¬ DAdj n i j) ∧
    (∀ b, IsABlock (J b) ∨ ∃ a, a + 3 ≤ n ∧ J b = blkNodes n a)

theorem family_of_frame (fr : DFrame n m) (hνinj : Function.Injective fr.ν)
    (hν : ∀ k k' : Fin m, DAdj n (fr.ν k) (fr.ν k') → k.val + 1 = k'.val ∨ k'.val + 1 = k.val)
    (I : Set (Fin n)) (hI : I ⊆ Set.range fr.ν) :
    ∃ (β : Type) (_ : Fintype β) (J : β → Set (Fin n)), GoodFamily n I J := by
  classical
  let S : Set (Fin m) := {k | fr.ν k ∈ I}
  refine ⟨↥(blocksOf S), inferInstance, fun b => fr.ν '' nodesOf b.1, ?_, ?_, ?_, ?_⟩
  · rintro b _ ⟨k, hk, rfl⟩
    obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.2
    have := nodesOf_subset (I := S) p
    rw [← hp] at this
    exact this hk
  · intro i hi
    obtain ⟨k, rfl⟩ := hI hi
    have hk : k ∈ S := hi
    refine ⟨⟨blkSet S k.castSucc, mem_blocksOf.mpr ⟨⟨_, rfl⟩, ⟨k, mem_nodesOf_of_mem hk⟩⟩⟩, k,
      mem_nodesOf_of_mem hk, rfl⟩
  · intro b b' hbb'
    obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.2
    obtain ⟨⟨q, hq⟩, -⟩ := mem_blocksOf.mp b'.2
    have : blkSet S p ≠ blkSet S q := fun h => hbb' (Subtype.ext (by rw [hp, hq, h]))
    have := frame_nonadj fr hνinj hν this
    rw [← hp, ← hq] at this
    exact this
  · intro b
    left
    obtain ⟨⟨p, hp⟩, hne⟩ := mem_blocksOf.mp b.2
    rw [hp] at hne
    show IsABlock (fr.ν '' nodesOf b.1)
    rw [hp]
    exact fr.isABlock S p hne


theorem frameId_inj (m : ℕ) : Function.Injective (frameId m).ν := Fin.castSucc_injective m

theorem frameId_adj (m : ℕ) (k k' : Fin m)
    (h : DAdj (m + 1) ((frameId m).ν k) ((frameId m).ν k')) :
    k.val + 1 = k'.val ∨ k'.val + 1 = k.val := by
  simp only [frameId_ν, DAdj, Fin.val_castSucc] at h
  have := k.isLt
  have := k'.isLt
  omega

theorem frameTau_inj (m : ℕ) (hm : 2 ≤ m) : Function.Injective (frameTau m hm).ν := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp only [frameTau] at h'
  have := a.isLt
  have := b.isLt
  split_ifs at h' <;> simp at h' <;> omega

theorem frameTau_adj (m : ℕ) (hm : 2 ≤ m) (k k' : Fin m)
    (h : DAdj (m + 1) ((frameTau m hm).ν k) ((frameTau m hm).ν k')) :
    k.val + 1 = k'.val ∨ k'.val + 1 = k.val := by
  simp only [frameTau, DAdj] at h
  have := k.isLt
  have := k'.isLt
  by_cases ha : k.val + 1 < m <;> by_cases hb : k'.val + 1 < m <;> simp [ha, hb] at h <;> omega


theorem Dgamma_self (x : Fin n ⊕ Fin n) : Dgamma x x = 0 := by
  funext k
  have := two_mul_Dgamma x x k
  simp only [Pi.zero_apply]
  omega

@[expose] def twoBlock (x y : Fin n ⊕ Fin n) (hxy : x ≠ y) (hyx : y ≠ x.swap) (i : Fin n)
    (hd : Dgamma x y = Pi.single i 1) : DBlk n Bool where
  pos := fun b => if b then x else y
  nodes := {i}
  pos_inj := by
    intro a b h
    cases a <;> cases b <;> simp at h ⊢
    · exact absurd h.symm hxy
    · exact absurd h hxy
  pos_swap := by
    have hx : x ≠ x.swap := by rcases x with c | c <;> simp
    have hy : y ≠ y.swap := by rcases y with c | c <;> simp
    have hxy' : x ≠ y.swap := fun e => hyx (by rw [e, Sum.swap_swap])
    intro a b
    cases a <;> cases b <;> simp [hx, hy, hxy', hyx]
  supp := by
    intro u v k hk
    have hk' : k ≠ i := hk
    have h0 : (Pi.single i 1 : Fin n → ℤ) k = 0 := Pi.single_eq_of_ne hk' _
    cases u <;> cases v <;> simp only [Bool.false_eq_true, if_true, if_false]
    · rw [Dgamma_self]; rfl
    · have := Dgamma_neg x y
      rw [this, hd]; simpa using h0
    · rw [hd]; exact h0
    · rw [Dgamma_self]; rfl
  gen := by
    intro j hj
    have : j = i := hj
    subst this
    exact ⟨true, false, by simp, by simpa using hd⟩

theorem twoBlock_isABlock (x y : Fin n ⊕ Fin n) (hxy : x ≠ y) (hyx : y ≠ x.swap) (i : Fin n)
    (hd : Dgamma x y = Pi.single i 1) : IsABlock ({i} : Set (Fin n)) :=
  ⟨Bool, inferInstance, inferInstance, twoBlock x y hxy hyx i hd, rfl, by simp⟩

end Family

section Comb

theorem comb_noFork (m : ℕ) (hm : 3 ≤ m) (I : Set (Fin (m + 1)))
    (h : Fin.last m ∉ I ∨ Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) ∉ I) :
    ∃ (β : Type) (_ : Fintype β) (J : β → Set (Fin (m + 1))), GoodFamily (m + 1) I J := by
  rcases h with h1 | h2
  · refine family_of_frame (frameId m) (frameId_inj m) (frameId_adj m) I ?_
    intro i hi
    have : i ≠ Fin.last m := fun e => h1 (e ▸ hi)
    exact ⟨i.castPred this, Fin.castSucc_castPred i this⟩
  · refine family_of_frame (frameTau m (by omega)) (frameTau_inj m (by omega))
      (frameTau_adj m (by omega)) I ?_
    intro i hi
    by_cases hl : i = Fin.last m
    · refine ⟨⟨m - 1, by omega⟩, ?_⟩
      simp only [frameTau]
      rw [if_neg (by simp; omega)]
      exact hl.symm
    · have hne : i ≠ Fin.last m := hl
      have hk : (i.castPred hne).val + 1 < m := by
        have h3 := i.castPred hne |>.isLt
        by_contra hcon
        apply h2
        have : (i.castPred hne) = ⟨m - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [← this, Fin.castSucc_castPred]
        exact hi
      refine ⟨i.castPred hne, ?_⟩
      simp only [frameTau]
      rw [if_pos hk]
      exact Fin.castSucc_castPred i hne


open Classical in
theorem comb_fork (m : ℕ) (hm : 3 ≤ m) (I : Set (Fin (m + 1))) (h1 : Fin.last m ∈ I)
    (h2 : Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) ∈ I) :
    ∃ (β : Type) (_ : Fintype β) (J : β → Set (Fin (m + 1))), GoodFamily (m + 1) I J := by
  let S : Set (Fin m) := {k | k.castSucc ∈ I}
  let R : Finset (Fin (m + 1)) := blkSet S (Fin.last m)
  have hRne : R.Nonempty := ⟨Fin.last m, self_mem_blkSet _⟩
  let a : Fin (m + 1) := R.min' hRne
  have hmem : ∀ c, c ∈ R ↔ a ≤ c := by
    intro c
    constructor
    · intro hc; exact Finset.min'_le R c hc
    · intro hac
      exact blkSet_convex (Finset.min'_mem R hRne) (self_mem_blkSet _) hac (Fin.le_last c)
  have hm1S : (⟨m - 1, by omega⟩ : Fin m) ∈ S := h2
  have hm1R : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ R := by
    rw [mem_blkSet]
    intro j hj
    have hjne : j.val ≠ m - 1 := fun e => hj (by
      have : j = ⟨m - 1, by omega⟩ := Fin.ext e
      rw [this]; exact hm1S)
    have := j.isLt
    simp only [Fin.val_last]
    constructor <;> intro h <;> omega
  have ham1 : a.val ≤ m - 1 := by
    have := Finset.min'_le R _ hm1R
    simpa [Fin.le_def] using this
  have hbelow : ∀ B ∈ blocksOf S, B ≠ R → ∀ c ∈ B, c.val < a.val := by
    intro B hB hBR c hc
    obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp hB
    have hd : Disjoint B R := by rw [hp]; exact disjoint_blkSet (by rw [← hp]; exact hBR)
    by_contra hcon
    have hac : a ≤ c := by rw [Fin.le_def]; omega
    exact Finset.disjoint_left.mp hd hc ((hmem c).mpr hac)
  have hfr := frameId_ν m
  by_cases hD : a.val + 1 < m
  ·
    refine ⟨Option {b : ↥(blocksOf S) // b.1 ≠ R}, inferInstance, fun o =>
      match o with
      | none => blkNodes (m + 1) a.val
      | some b => (frameId m).ν '' nodesOf b.1.1, ?_, ?_, ?_, ?_⟩
    · intro o
      cases o with
      | none =>
        intro i hi
        have hai : a.val ≤ i.val := hi
        by_cases hl : i = Fin.last m
        · rw [hl]; exact h1
        · have hk : (i.castPred hl) ∈ nodesOf R := by
            refine ⟨(hmem _).mpr ?_, (hmem _).mpr ?_⟩ <;>
              simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred] <;> omega
          have := nodesOf_subset (I := S) (Fin.last m) hk
          have e : (i.castPred hl).castSucc = i := Fin.castSucc_castPred i hl
          have h3 : (i.castPred hl).castSucc ∈ I := this
          rwa [e] at h3
      | some b =>
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.1.2
        have := nodesOf_subset (I := S) p
        rw [← hp] at this
        exact this hk
    · intro i hi
      by_cases hai : a.val ≤ i.val
      · exact ⟨none, hai⟩
      · have hl : i ≠ Fin.last m := fun e => hai (by rw [e]; simp; omega)
        set k : Fin m := i.castPred hl with hk
        have hkS : k ∈ S := by
          show k.castSucc ∈ I
          rw [hk, Fin.castSucc_castPred]; exact hi
        have hB : blkSet S k.castSucc ∈ blocksOf S :=
          mem_blocksOf.mpr ⟨⟨_, rfl⟩, ⟨k, mem_nodesOf_of_mem hkS⟩⟩
        have hBR : blkSet S k.castSucc ≠ R := by
          intro e
          have : k.castSucc ∈ R := by rw [← e]; exact self_mem_blkSet _
          have := (hmem _).mp this
          simp only [Fin.le_def, Fin.val_castSucc] at this
          apply hai
          rw [hk] at this
          simpa using this
        refine ⟨some ⟨⟨_, hB⟩, hBR⟩, k, mem_nodesOf_of_mem hkS, ?_⟩
        rw [hfr, hk, Fin.castSucc_castPred]
    · intro o o' hoo' i hi j hj
      cases o with
      | none =>
        cases o' with
        | none => exact absurd rfl hoo'
        | some b' =>
          obtain ⟨k, hk, rfl⟩ := hj
          have hkc := hbelow _ b'.1.2 b'.2 _ hk.2
          simp only [Fin.val_succ] at hkc
          have hai : a.val ≤ i.val := hi
          have := k.isLt
          simp only [frameId_ν, Fin.val_castSucc, DAdj]
          refine ⟨fun e => ?_, ?_⟩
          · have := congrArg Fin.val e; simp at this; omega
          · have := i.isLt; omega
      | some b =>
        cases o' with
        | none =>
          obtain ⟨k, hk, rfl⟩ := hi
          have hkc := hbelow _ b.1.2 b.2 _ hk.2
          simp only [Fin.val_succ] at hkc
          have hai : a.val ≤ j.val := hj
          have := k.isLt
          simp only [frameId_ν, Fin.val_castSucc, DAdj]
          refine ⟨fun e => ?_, ?_⟩
          · have := congrArg Fin.val e; simp at this; omega
          · have := j.isLt; omega
        | some b' =>
          obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.1.2
          obtain ⟨⟨q, hq⟩, -⟩ := mem_blocksOf.mp b'.1.2
          have hne : blkSet S p ≠ blkSet S q := fun h => hoo' (by
            congr 2
            exact Subtype.ext (Subtype.ext (by rw [hp, hq, h])))
          have := frame_nonadj (frameId m) (frameId_inj m) (frameId_adj m) hne
          rw [← hp, ← hq] at this
          exact this i hi j hj
    · intro o
      cases o with
      | none => exact Or.inr ⟨a.val, by omega, rfl⟩
      | some b =>
        left
        obtain ⟨⟨p, hp⟩, hne⟩ := mem_blocksOf.mp b.1.2
        show IsABlock ((frameId m).ν '' nodesOf b.1.1)
        rw [hp]
        rw [hp] at hne
        exact (frameId m).isABlock S p hne
  ·
    have haeq : a.val = m - 1 := by omega
    let c0 : Fin (m + 1) := Fin.castSucc ⟨m - 1, by omega⟩
    have hc0 : c0.val = m - 1 := rfl
    refine ⟨Bool ⊕ {b : ↥(blocksOf S) // b.1 ≠ R}, inferInstance, fun o =>
      match o with
      | Sum.inl true => {c0}
      | Sum.inl false => {Fin.last m}
      | Sum.inr b => (frameId m).ν '' nodesOf b.1.1, ?_, ?_, ?_, ?_⟩
    · intro o
      rcases o with (_ | _) | b
      · rintro i rfl; exact h1
      · rintro i rfl; exact h2
      · rintro _ ⟨k, hk, rfl⟩
        obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.1.2
        have := nodesOf_subset (I := S) p
        rw [← hp] at this
        exact this hk
    · intro i hi
      by_cases hl : i = Fin.last m
      · exact ⟨Sum.inl false, by rw [hl]; rfl⟩
      · by_cases hc : i = c0
        · exact ⟨Sum.inl true, hc⟩
        · set k : Fin m := i.castPred hl with hk
          have hkS : k ∈ S := by
            show k.castSucc ∈ I
            rw [hk, Fin.castSucc_castPred]; exact hi
          have hB : blkSet S k.castSucc ∈ blocksOf S :=
            mem_blocksOf.mpr ⟨⟨_, rfl⟩, ⟨k, mem_nodesOf_of_mem hkS⟩⟩
          have hBR : blkSet S k.castSucc ≠ R := by
            intro e
            have : k.castSucc ∈ R := by rw [← e]; exact self_mem_blkSet _
            have h5 := (hmem _).mp this
            simp only [Fin.le_def, Fin.val_castSucc] at h5
            apply hc
            apply Fin.ext
            have h6 : i.val = k.val := by rw [hk]; simp
            have := k.isLt
            rw [hc0, h6]; omega
          refine ⟨Sum.inr ⟨⟨_, hB⟩, hBR⟩, k, mem_nodesOf_of_mem hkS, ?_⟩
          rw [hfr, hk, Fin.castSucc_castPred]
    · intro o o' hoo' i hi j hj
      have key : ∀ (b : {b : ↥(blocksOf S) // b.1 ≠ R}) (x : Fin (m + 1)),
          x ∈ (frameId m).ν '' nodesOf b.1.1 → x.val + 2 < m := by
        rintro b x ⟨k, hk, rfl⟩
        have hkc := hbelow _ b.1.2 b.2 _ hk.2
        simp only [Fin.val_succ] at hkc
        simp only [frameId_ν, Fin.val_castSucc]
        omega
      rcases o with (_ | _) | b <;> rcases o' with (_ | _) | b'
      · exact absurd rfl hoo'
      · simp only [Set.mem_singleton_iff] at hi hj
        rw [hi, hj]
        simp only [DAdj, hc0, Fin.val_last]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [hc0, Fin.val_last] at this; omega
        · omega
      · simp only [Set.mem_singleton_iff] at hi
        rw [hi]
        have := key b' j hj
        simp only [DAdj, Fin.val_last]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
        · have := j.isLt; omega
      · simp only [Set.mem_singleton_iff] at hi hj
        rw [hi, hj]
        simp only [DAdj, hc0, Fin.val_last]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [hc0, Fin.val_last] at this; omega
        · omega
      · exact absurd rfl hoo'
      · simp only [Set.mem_singleton_iff] at hi
        rw [hi]
        have := key b' j hj
        simp only [DAdj, hc0]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [hc0] at this; omega
        · have := j.isLt; omega
      · simp only [Set.mem_singleton_iff] at hj
        rw [hj]
        have := key b i hi
        simp only [DAdj, Fin.val_last]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
        · have := i.isLt; omega
      · simp only [Set.mem_singleton_iff] at hj
        rw [hj]
        have := key b i hi
        simp only [DAdj, hc0]
        refine ⟨fun e => ?_, ?_⟩
        · have := congrArg Fin.val e; rw [hc0] at this; omega
        · have := i.isLt; omega
      · obtain ⟨⟨p, hp⟩, -⟩ := mem_blocksOf.mp b.1.2
        obtain ⟨⟨q, hq⟩, -⟩ := mem_blocksOf.mp b'.1.2
        have hne : blkSet S p ≠ blkSet S q := fun h => hoo' (by
          congr 1
          exact Subtype.ext (Subtype.ext (by rw [hp, hq, h])))
        have := frame_nonadj (frameId m) (frameId_inj m) (frameId_adj m) hne
        rw [← hp, ← hq] at this
        exact this i hi j hj
    · intro o
      left
      rcases o with (_ | _) | b
      · exact twoBlock_isABlock (Sum.inl c0) (Sum.inr (Fin.last m))
          (by simp) (by
            simp only [Sum.swap_inl, ne_eq, Sum.inr.injEq]
            intro e
            have := congrArg Fin.val e
            rw [hc0, Fin.val_last] at this
            omega) (Fin.last m) (by
            have := Dgamma_flag (n := m + 1) (by omega)
            convert this using 3 <;> first | rfl | (apply Fin.ext; simp; omega))
      · have hc1 : c0.val + 1 < m + 1 := by rw [hc0]; omega
        exact twoBlock_isABlock (Sum.inl c0) (Sum.inl ⟨c0.val + 1, hc1⟩) (by simp [Fin.ext_iff])
          (by simp) c0 (Dgamma_inl_succ c0 hc1)
      · obtain ⟨⟨p, hp⟩, hne⟩ := mem_blocksOf.mp b.1.2
        show IsABlock ((frameId m).ν '' nodesOf b.1.1)
        rw [hp]
        rw [hp] at hne
        exact (frameId m).isABlock S p hne


theorem comb (m : ℕ) (hm : 3 ≤ m) (I : Set (Fin (m + 1))) :
    ∃ (β : Type) (_ : Fintype β) (J : β → Set (Fin (m + 1))), GoodFamily (m + 1) I J := by
  by_cases h1 : Fin.last m ∈ I
  · by_cases h2 : Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) ∈ I
    · exact comb_fork m hm I h1 h2
    · exact comb_noFork m hm I (Or.inr h2)
  · exact comb_noFork m hm I (Or.inl h1)

end Comb




end P142

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
