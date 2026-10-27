module

public import Certificates.Data.Kernel.Misc.YamakiAut
public import CFSG.Certificates.Kernel.Misc.YamakiS0Sound
public import CFSG.Certificates.Kernel.Misc.YamakiRepFSound

public section

namespace CFSG.KC.YamakiAut

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiAut CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiS0 CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem buildF_foldl (E : Enum) (hs : Array (Array ℕ)) :
    ∀ m : ℕ, (∀ i, 1 ≤ i → i ≤ m → E.parent[i]! < i) →
      let F := (List.range' 1 m).foldl
        (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()]
      F.size = m + 1 ∧ F[0]! = idA () ∧
        ∀ i, 1 ≤ i → i ≤ m → F[i]! = compA F[E.parent[i]!]! hs[E.gen[i]!]!
  | 0, _ => by
    refine ⟨rfl, rfl, fun i h1 h2 => by omega⟩
  | m + 1, hp => by
    intro F
    obtain ⟨s, z, r⟩ := buildF_foldl E hs m fun i h1 h2 => hp i h1 (by omega)
    have hF : F = ((List.range' 1 m).foldl
        (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()]).push
        (compA ((List.range' 1 m).foldl
          (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()])[E.parent[m + 1]!]!
          hs[E.gen[m + 1]!]!) := by
      simp only [F, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [Nat.one_mul, Nat.add_comm 1 m]
    generalize ((List.range' 1 m).foldl
      (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()]) = G at hF s z r
    rw [hF]
    have hpm := hp (m + 1) (by omega) le_rfl
    refine ⟨by simp [s], by rw [push_lt (by omega), z], fun i h1 h2 => ?_⟩
    rcases Nat.lt_or_eq_of_le h2 with h | h
    · have hpi := hp i h1 (by omega)
      have hi1 : i < G.size := by omega
      have hi2 : E.parent[i]! < G.size := by omega
      rw [push_lt hi1, push_lt hi2, r i h1 (by omega)]
    · subst h
      have hi2 : E.parent[m + 1]! < G.size := by omega
      have e : (G.push (compA G[E.parent[m + 1]!]! hs[E.gen[m + 1]!]!))[m + 1]! =
          compA G[E.parent[m + 1]!]! hs[E.gen[m + 1]!]! := by
        rw [← s]
        exact push_eq
      rw [e, push_lt hi2]

theorem buildF_spec (E : Enum) (hs : Array (Array ℕ)) {n : ℕ} (hn : E.elems.size = n + 1)
    (hp : ∀ i, 1 ≤ i → i ≤ n → E.parent[i]! < i) :
    (buildF E hs).size = n + 1 ∧ (buildF E hs)[0]! = idA () ∧
      ∀ i, 1 ≤ i → i ≤ n →
        (buildF E hs)[i]! = compA (buildF E hs)[E.parent[i]!]! hs[E.gen[i]!]! := by
  have e : buildF E hs = (List.range' 1 n).foldl
      (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()] := by
    unfold buildF
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, hn,
      Nat.add_sub_cancel, Nat.div_one, bind_pure]
    exact forIn_foldl _ _ _ _ fun j b => rfl
  rw [e]
  exact buildF_foldl E hs n hp

section Fold

variable {κ : Type} [BEq κ] [LawfulBEq κ] [Hashable κ]

@[expose] def fiStep (acc : Std.HashMap κ ℕ × ℕ) (t : κ) : Std.HashMap κ ℕ × ℕ :=
  (if acc.1.contains t then acc.1 else acc.1.insert t acc.2, acc.2 + 1)

theorem fiFold_spec : ∀ l : List κ,
    (∀ i (hi : i < l.length) j (hj : j < l.length), l[i] = l[j] → i = j) →
      (l.foldl fiStep ((∅ : Std.HashMap κ ℕ), 0)).2 = l.length ∧
      (∀ y, (l.foldl fiStep ((∅ : Std.HashMap κ ℕ), 0)).1.contains y = true ↔ y ∈ l) ∧
      ∀ i (hi : i < l.length), (l.foldl fiStep ((∅ : Std.HashMap κ ℕ), 0)).1[l[i]]? = some i := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton l a ih =>
    intro hd
    have hdl : ∀ i (hi : i < l.length) j (hj : j < l.length), l[i] = l[j] → i = j := by
      intro i hi j hj e
      refine hd i (by simp; omega) j (by simp; omega) ?_
      rw [List.getElem_append_left hi, List.getElem_append_left hj]
      exact e
    obtain ⟨s2, sc, sg⟩ := ih hdl
    have hna : a ∉ l := by
      intro ha
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ha
      have := hd i (by simp; omega) l.length (by simp) (by
        rw [List.getElem_append_left hi, e]
        simp)
      omega
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize l.foldl fiStep ((∅ : Std.HashMap κ ℕ), 0) = S at s2 sc sg ⊢
    have hc : S.1.contains a = false := by
      cases h : S.1.contains a
      · rfl
      · exact absurd ((sc a).1 h) hna
    have hst : fiStep S a = (S.1.insert a S.2, S.2 + 1) := by
      unfold fiStep
      rw [hc]
      rfl
    rw [hst]
    refine ⟨by simp [s2], fun y => ?_, fun i hi => ?_⟩
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, sc]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (rfl | h)
        · exact Or.inr rfl
        · exact Or.inl h
      · rintro (h | rfl)
        · exact Or.inr h
        · exact Or.inl rfl
    · rw [Std.HashMap.getElem?_insert]
      rcases Nat.lt_or_ge i l.length with h | h
      · rw [List.getElem_append_left h]
        have hne : (a == l[i]) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          exact hna (e ▸ List.getElem_mem h)
        rw [hne]
        exact sg i h
      · have hi' : i = l.length := by simp at hi; omega
        subst hi'
        simp [s2]

end Fold

theorem firstIndex_eq (F : Array (Array ℕ)) : firstIndex F = (F.toList.foldl fiStep (∅, 0)).1 := by
  unfold firstIndex
  rw [← Array.foldl_toList]
  rfl

theorem injOK_of_distinct {F : Array (Array ℕ)}
    (hd : ∀ i < F.size, ∀ j < F.size, F[i]! = F[j]! → i = j) : injOK F = true := by
  unfold injOK
  rw [allLt_iff, firstIndex_eq]
  intro i hi
  have hdl : ∀ i (hi : i < F.toList.length) j (hj : j < F.toList.length),
      F.toList[i] = F.toList[j] → i = j := by
    intro i hi j hj e
    simp only [Array.length_toList] at hi hj
    refine hd i hi j hj ?_
    rw [getElem!_pos F i hi, getElem!_pos F j hj]
    simpa using e
  obtain ⟨-, -, sg⟩ := fiFold_spec F.toList hdl
  have e := sg i (by simpa using hi)
  rw [decide_eq_true_eq, getElem!_pos F i hi]
  simpa using e

theorem inj_of_tree {G M : Type*} [Monoid G] [Monoid M] {n k : ℕ} {ψ : ℕ → G} {φ : ℕ → M}
    {s : ℕ → G} {h : ℕ → M} {POS PA PB : ℕ → ℕ}
    (hψ0 : ψ 0 = 1) (hφ0 : φ 0 = 1) (hinj : ∀ a < n, ∀ b < n, ψ a = ψ b → a = b)
    (hsU : ∀ j < k, IsUnit (s j)) (hhU : ∀ j < k, IsUnit (h j))
    (hpos : ∀ i < n, ∀ j < k, POS (i * k + j) < n ∧ ψ (POS (i * k + j)) = ψ i * s j ∧
      φ (POS (i * k + j)) = φ i * h j)
    (htree : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ ψ (i + 1) = ψ (PA i) * s (PB i))
    (hker : ∀ t < n, φ t = 1 → t = 0) :
    ∀ a < n, ∀ b < n, φ a = φ b → a = b := by
  have hφtree : ∀ i < n - 1, φ (i + 1) = φ (PA i) * h (PB i) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := htree i hi
    obtain ⟨p1, p2, p3⟩ := hpos (PA i) (by omega) (PB i) h2
    have e : POS (PA i * k + PB i) = i + 1 := hinj _ p1 _ (by omega) (by rw [p2, h3])
    rw [← e, p3]
  have hU : ∀ t < n, IsUnit (ψ t) ∧ IsUnit (φ t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      cases t with
      | zero =>
        rw [hψ0, hφ0]
        exact ⟨isUnit_one, isUnit_one⟩
      | succ i =>
        obtain ⟨h1, h2, h3⟩ := htree i (by omega)
        obtain ⟨u1, u2⟩ := ih (PA i) (by omega) (by omega)
        rw [h3, hφtree i (by omega)]
        exact ⟨u1.mul (hsU _ h2), u2.mul (hhU _ h2)⟩
  have hcl : ∀ c < n, ∀ a < n, ∃ b < n, ψ b = ψ a * ψ c ∧ φ b = φ a * φ c := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hc a ha
      cases c with
      | zero => exact ⟨a, ha, by rw [hψ0, mul_one], by rw [hφ0, mul_one]⟩
      | succ i =>
        obtain ⟨h1, h2, h3⟩ := htree i (by omega)
        obtain ⟨b', hb', e1, e2⟩ := ih (PA i) (by omega) (by omega) a ha
        obtain ⟨p1, p2, p3⟩ := hpos b' hb' (PB i) h2
        refine ⟨_, p1, ?_, ?_⟩
        · rw [p2, e1, h3, mul_assoc]
        · rw [p3, e2, hφtree i (by omega), mul_assoc]
  intro a ha b hb hab
  classical
  have hf : ∀ c (hc : c ∈ Finset.range n),
      Classical.choose (hcl c (Finset.mem_range.1 hc) a ha) < n ∧
      ψ (Classical.choose (hcl c (Finset.mem_range.1 hc) a ha)) = ψ a * ψ c ∧
      φ (Classical.choose (hcl c (Finset.mem_range.1 hc) a ha)) = φ a * φ c :=
    fun c hc => Classical.choose_spec (hcl c (Finset.mem_range.1 hc) a ha)
  obtain ⟨c, hc, e⟩ := Finset.surj_on_of_inj_on_of_card_le
    (fun c hc => Classical.choose (hcl c (Finset.mem_range.1 hc) a ha))
    (fun c hc => Finset.mem_range.2 (hf c hc).1)
    (fun c₁ c₂ h₁ h₂ e => by
      have e' : ψ a * ψ c₁ = ψ a * ψ c₂ := by rw [← (hf c₁ h₁).2.1, ← (hf c₂ h₂).2.1, e]
      exact hinj _ (Finset.mem_range.1 h₁) _ (Finset.mem_range.1 h₂)
        ((hU a ha).1.mul_left_cancel e'))
    le_rfl b (Finset.mem_range.2 hb)
  have e1 : ψ b = ψ a * ψ c := by rw [e]; exact (hf c hc).2.1
  have e2 : φ b = φ a * φ c := by rw [e]; exact (hf c hc).2.2
  have hc1 : φ c = 1 := (hU a ha).2.mul_left_cancel (by rw [← e2, ← hab, mul_one])
  have hc0 := hker c (Finset.mem_range.1 hc) hc1
  rw [hc0, hψ0, mul_one] at e1
  exact (hinj _ hb _ ha e1).symm

@[expose] noncomputable def encA (m c : ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun i => if i.val < m then nib c i.val else i.val

@[expose] def arrL (m : ℕ) (l : List ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun i => if i.val < m then l.getD i.val 0 else i.val

@[expose] noncomputable def encF (m c : ℕ) : Function.End ℕ := fun p => if p < m then nib c p else p

@[expose] def lF (m : ℕ) (l : List ℕ) : Function.End ℕ := fun p => if p < m then l.getD p 0 else p

theorem nib_lt (c i : ℕ) : nib c i < 16 := Nat.mod_lt _ (by norm_num)

theorem nib_add_zero {x y : ℕ} (hx : x < 16) : nib (x + 16 * y) 0 = x := by
  unfold nib
  change (x + 16 * y) / 16 ^ 0 % 16 = x
  rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem nib_add_succ {x y : ℕ} (hx : x < 16) (i : ℕ) : nib (x + 16 * y) (i + 1) = nib y i := by
  unfold nib
  change (x + 16 * y) / 16 ^ (i + 1) % 16 = y / 16 ^ i % 16
  rw [pow_succ, Nat.mul_comm (16 ^ i) 16, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem compL_cons (x : ℕ) (l : List ℕ) (a : ℕ) :
    compL (x :: l) a = nib a x + 16 * compL l a := rfl

theorem nib_compL : ∀ (l : List ℕ) (a i : ℕ), i < l.length →
    nib (compL l a) i = nib a (l.getD i 0)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: l, a, 0, _ => by rw [compL_cons, nib_add_zero (nib_lt _ _)]; rfl
  | x :: l, a, i + 1, h => by
    rw [compL_cons, nib_add_succ (nib_lt _ _), nib_compL l a i (by simpa using h)]
    rfl

theorem compL_ext : ∀ (l l' : List ℕ) (a b : ℕ), l.length = l'.length →
    (∀ i < l.length, nib a (l.getD i 0) = nib b (l'.getD i 0)) → compL l a = compL l' b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | x :: l, y :: l', a, b, h, hn => by
    rw [compL_cons, compL_cons, compL_ext l l' a b (by simpa using h)
      (fun i hi => hn (i + 1) (by simp; omega))]
    have := hn 0 (by simp)
    simp only [List.getD_cons_zero] at this
    rw [this]

theorem encA_get {m c i : ℕ} (hi : i < 64) : (encA m c)[i]! = if i < m then nib c i else i :=
  getElem!_ofFn_nat _ hi

theorem arrL_get {m : ℕ} {l : List ℕ} {i : ℕ} (hi : i < 64) :
    (arrL m l)[i]! = if i < m then l.getD i 0 else i :=
  getElem!_ofFn_nat _ hi

theorem compA_encA {m : ℕ} {l : List ℕ} (hm : m ≤ 64) (hl : l.length = m)
    (hv : ∀ i < m, l.getD i 0 < m) (a : ℕ) :
    compA (encA m a) (arrL m l) = encA m (compL l a) := by
  refine ext64 (size_compA _ _) (by simp [encA]) fun i hi => ?_
  rw [compA_get _ _ hi, arrL_get hi, encA_get hi]
  by_cases h : i < m
  · rw [if_pos h, if_pos h, encA_get (by have := hv i h; omega), if_pos (hv i h),
      nib_compL l a i (by omega)]
  · rw [if_neg h, if_neg h, encA_get hi, if_neg h]

theorem encF_of_encA {m a b : ℕ} (hm : m ≤ 64) (h : encA m a = encA m b) : encF m a = encF m b := by
  funext p
  unfold encF
  by_cases hp : p < m
  · rw [if_pos hp, if_pos hp]
    have e : (encA m a)[p]! = (encA m b)[p]! := by rw [h]
    rw [encA_get (by omega), encA_get (by omega), if_pos hp, if_pos hp] at e
    exact e
  · rw [if_neg hp, if_neg hp]

theorem encF_mul {m : ℕ} {l : List ℕ} (hl : l.length = m) (hv : ∀ i < m, l.getD i 0 < m)
    (a : ℕ) : encF m (compL l a) = encF m a * lF m l := by
  funext p
  change encF m (compL l a) p = encF m a (lF m l p)
  unfold encF lF
  by_cases hp : p < m
  · rw [if_pos hp, if_pos hp, if_pos (hv p hp), nib_compL l a p (by omega)]
  · rw [if_neg hp, if_neg hp, if_neg hp]

theorem lF_isUnit {m : ℕ} {l li : List ℕ}
    (h : ∀ i < m, l.getD i 0 < m ∧ li.getD i 0 < m ∧ l.getD (li.getD i 0) 0 = i ∧
      li.getD (l.getD i 0) 0 = i) : IsUnit (lF m l) := by
  have h1 : lF m l * lF m li = 1 := by
    funext p
    change lF m l (lF m li p) = p
    unfold lF
    by_cases hp : p < m
    · rw [if_pos hp, if_pos (h p hp).2.1, (h p hp).2.2.1]
    · rw [if_neg hp, if_neg hp]
  have h2 : lF m li * lF m l = 1 := by
    funext p
    change lF m li (lF m l p) = p
    unfold lF
    by_cases hp : p < m
    · rw [if_pos hp, if_pos (h p hp).1, (h p hp).2.2.2]
    · rw [if_neg hp, if_neg hp]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem matrix_isUnit {A B : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : B * A = 1) : IsUnit A :=
  ⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩

theorem invPosK_sound {R : ℕ → ℕ} {n : ℕ} : ∀ {ps : List (ℕ × ℕ)}, invPosK R n ps = true →
    ∀ p ∈ ps, p.1 < n ∧ recPOS R 14 2 (p.1 * 2 + p.2) = 0
  | [], _ => by simp
  | (v, j) :: ps, h => by
    simp only [invPosK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hv, he⟩, hr⟩ := h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hv, he⟩
    · exact invPosK_sound hr p hp

theorem autAt_facts {R RP : ℕ → ℕ} {l0 l1 : List ℕ} {ONEP t : ℕ}
    (h : autAt R RP l0 l1 ONEP t = true) :
    RP (recPOS R 14 2 (t * 2 + 0)) = compL l0 (RP t) ∧
      RP (recPOS R 14 2 (t * 2 + 1)) = compL l1 (RP t) ∧ (RP t = ONEP ↔ t = 0) := by
  unfold autAt at h
  rw [CFSG.KC.YamakiRepF.strictY_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  refine ⟨a, b, ?_⟩
  have c' := beq_iff_eq.1 c
  constructor
  · intro e
    have : Nat.beq (RP t) ONEP = true := Nat.beq_eq.mpr e
    rw [this] at c'
    exact Nat.beq_eq.mp c'.symm
  · intro e
    have : Nat.beq t 0 = true := Nat.beq_eq.mpr e
    rw [this] at c'
    exact Nat.beq_eq.mp c'

variable {R RP : ℕ → ℕ} {l0 l1 lr li0 li1 : List ℕ} {m n ONEP v0 v1 : ℕ} {E : Enum}
  {gs : Array (Array ℕ)}

theorem autAt_of_chunks {L M : ℕ} (h : ∀ q < M, autChunk R RP l0 l1 ONEP n L q = true)
    (hm : n ≤ L * M) : ∀ t < n, autAt R RP l0 l1 ONEP t = true := by
  intro t ht
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hm; omega
  have hq : t / L < M := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; omega)
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 (h _ hq) t (Nat.mul_div_le t L) (by
    have := Nat.lt_div_mul_add (a := t) hL
    rw [Nat.mul_comm] at this
    exact this)
  have hb : Nat.blt t n = true := Nat.blt_eq.mpr ht
  rw [hb, cond_true] at e
  exact e

theorem autOK_of_codes
    (hE : BInvE (fun t => arrN (recX R 14 t)) (recF R 14 0) (recF R 14 1) n E) (hn : 0 < n)
    (h0 : recX R 14 0 = ONE)
    (hB : ∀ i < n - 1, recF R 14 0 i ≤ i ∧ recF R 14 1 i < 2 ∧
      recX R 14 (i + 1) = MULF (recX R 14 (recF R 14 0 i)) (R (12 + recF R 14 1 i)))
    (hlt : ∀ t < n, recX R 14 t < 2 ^ 36)
    (hstep : ∀ i < n * 2, recPOS R 14 2 i < n ∧
      recX R 14 (recPOS R 14 2 i) = MULF (recX R 14 (i / 2)) (R (12 + i % 2)))
    (hgs : gs.size = 2) (hg : ∀ j < 2, gs[j]! = arrN (R (12 + j)))
    (hm : m ≤ 64) (hl0 : l0.length = m) (hl1 : l1.length = m) (hlr : lr.length = m)
    (hv0 : ∀ i < m, l0.getD i 0 < m ∧ li0.getD i 0 < m ∧ l0.getD (li0.getD i 0) 0 = i ∧
      li0.getD (l0.getD i 0) 0 = i)
    (hv1 : ∀ i < m, l1.getD i 0 < m ∧ li1.getD i 0 < m ∧ l1.getD (li1.getD i 0) 0 = i ∧
      li1.getD (l1.getD i 0) 0 = i)
    (hr : ∀ i < m, lr.getD i 0 = i) (hone : ∀ i < m, nib ONEP i = i)
    (hone' : compL lr ONEP = ONEP)
    (hinv : invPosK R n [(v0, 0), (v1, 1)] = true)
    (hc : ∀ t < n, autAt R RP l0 l1 ONEP t = true) :
    autOK E gs #[arrL m l0, arrL m l1] (buildF E #[arrL m l0, arrL m l1]) = true ∧
      ∀ t < n, (buildF E #[arrL m l0, arrL m l1])[t]! = encA m (RP t) := by
  have hE' := hE
  obtain ⟨e1, -, -, e4, e5, -, e7⟩ := hE
  let lj : ℕ → List ℕ := fun j => if j = 0 then l0 else l1
  have hlj : ∀ j < 2, (lj j).length = m ∧ ∀ i < m, (lj j).getD i 0 < m := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨hl0, fun i hi => (hv0 i hi).1⟩
    · exact ⟨hl1, fun i hi => (hv1 i hi).1⟩
  have hsj : ∀ j < 2, (#[arrL m l0, arrL m l1] : Array (Array ℕ))[j]! = arrL m (lj j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rfl
    · rfl
  have hP : ∀ i < n, ∀ j < 2, recPOS R 14 2 (i * 2 + j) < n ∧
      recX R 14 (recPOS R 14 2 (i * 2 + j)) = MULF (recX R 14 i) (R (12 + j)) ∧
      RP (recPOS R 14 2 (i * 2 + j)) = compL (lj j) (RP i) := by
    intro i hi j hj
    obtain ⟨s1, s2⟩ := hstep (i * 2 + j) (by omega)
    have hd : (i * 2 + j) / 2 = i := by omega
    have hm2 : (i * 2 + j) % 2 = j := by omega
    rw [hd, hm2] at s2
    obtain ⟨a, b, -⟩ := autAt_facts (hc i hi)
    refine ⟨s1, s2, ?_⟩
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact a
    · exact b
  have hK : ∀ t < n, (RP t = ONEP ↔ t = 0) := fun t ht => (autAt_facts (hc t ht)).2.2
  have hd : ∀ a < n, ∀ b < n, recX R 14 a = recX R 14 b → a = b := by
    intro a ha b hb e
    have h1 := e7 a ha
    have h2 := e7 b hb
    simp only at h1 h2
    rw [e] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  have hdisc : ∀ i < n - 1, recPOS R 14 2 (recF R 14 0 i * 2 + recF R 14 1 i) = i + 1 := by
    intro i hi
    obtain ⟨b1, b2, b3⟩ := hB i hi
    obtain ⟨p1, p2, -⟩ := hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2
    exact hd _ p1 (i + 1) (by omega) (by rw [p2, b3])
  have hinjP : ∀ a < n, ∀ b < n, encF m (RP a) = encF m (RP b) → a = b := by
    obtain ⟨⟨hv0n, hp0⟩, ⟨hv1n, hp1⟩⟩ : (v0 < n ∧ recPOS R 14 2 (v0 * 2 + 0) = 0) ∧
        (v1 < n ∧ recPOS R 14 2 (v1 * 2 + 1) = 0) :=
      ⟨invPosK_sound hinv (v0, 0) (by simp), invPosK_sound hinv (v1, 1) (by simp)⟩
    refine inj_of_tree (G := Matrix (Fin 6) (Fin 6) (ZMod 2)) (M := Function.End ℕ) (k := 2)
      (ψ := fun t => pkMat 6 (recX R 14 t)) (φ := fun t => encF m (RP t))
      (s := fun j => pkMat 6 (R (12 + j))) (h := fun j => lF m (lj j))
      (POS := recPOS R 14 2) (PA := recF R 14 0) (PB := recF R 14 1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h0, pkMat_ONE]
    · beta_reduce
      have e := (hK 0 hn).2 rfl
      rw [e]
      funext p
      unfold encF
      by_cases hp : p < m
      · rw [if_pos hp, hone p hp]
        rfl
      · rw [if_neg hp]
        rfl
    · intro a ha b hb e
      exact hd a ha b hb (CFSG.KC.Sp62.pkMat_inj (hlt a ha) (hlt b hb) e)
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · obtain ⟨-, p2, -⟩ := hP v0 hv0n 0 (by norm_num)
        rw [hp0, h0] at p2
        refine matrix_isUnit (B := pkMat 6 (recX R 14 v0)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p2, pkMat_ONE]
      · obtain ⟨-, p2, -⟩ := hP v1 hv1n 1 (by norm_num)
        rw [hp1, h0] at p2
        refine matrix_isUnit (B := pkMat 6 (recX R 14 v1)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p2, pkMat_ONE]
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact lF_isUnit hv0
      · exact lF_isUnit hv1
    · intro i hi j hj
      obtain ⟨p1, p2, p3⟩ := hP i hi j hj
      refine ⟨p1, ?_, ?_⟩
      · beta_reduce
        rw [p2, CFSG.KC.Sp62.pkMat_MULF]
      · beta_reduce
        rw [p3, encF_mul (hlj j hj).1 (hlj j hj).2]
    · intro i hi
      obtain ⟨b1, b2, b3⟩ := hB i hi
      refine ⟨b1, b2, ?_⟩
      beta_reduce
      rw [b3, CFSG.KC.Sp62.pkMat_MULF]
    · intro t ht e
      by_contra h0t
      apply h0t
      apply (hK t ht).1
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      obtain ⟨b1, b2, -⟩ := hB i (by omega)
      obtain ⟨-, -, p3⟩ := hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2
      rw [hdisc i (by omega)] at p3
      rw [p3, ← hone']
      refine compL_ext _ _ _ _ (by rw [hlr]; exact (hlj _ b2).1) fun q hq => ?_
      rw [(hlj _ b2).1] at hq
      rw [hr q hq, hone q hq, ← nib_compL _ _ _ (by rw [(hlj _ b2).1]; exact hq), ← p3]
      have := congrFun e q
      change encF m (RP (i + 1)) q = q at this
      unfold encF at this
      rwa [if_pos hq] at this
  have hpar : ∀ i, 1 ≤ i → i ≤ n - 1 → E.parent[i]! < i := by
    intro i h1 h2
    rw [(e5 i (by omega) (by omega)).1]
    have := (hB (i - 1) (by omega)).1
    omega
  obtain ⟨fs, f0, fr⟩ := buildF_spec E #[arrL m l0, arrL m l1] (n := n - 1)
    (by rw [e1]; omega) hpar
  have hF : ∀ t < n, (buildF E #[arrL m l0, arrL m l1])[t]! = encA m (RP t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      cases t with
      | zero =>
        rw [f0, (hK 0 hn).2 rfl]
        refine ext64 size_idA (by simp [encA]) fun i hi => ?_
        rw [idA_get hi, encA_get hi]
        by_cases h : i < m
        · rw [if_pos h, hone i h]
        · rw [if_neg h]
      | succ i =>
        obtain ⟨p1, p2⟩ := e5 (i + 1) ht (by omega)
        obtain ⟨b1, b2, -⟩ := hB i (by omega)
        rw [fr (i + 1) (by omega) (by omega), p1, p2, Nat.add_sub_cancel, hsj _ b2,
          ih _ (by omega) (by omega), compA_encA hm (hlj _ b2).1 (hlj _ b2).2,
          ← (hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2).2.2, hdisc i (by omega)]
  refine ⟨?_, hF⟩
  unfold autOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
  refine ⟨⟨⟨⟨by rw [fs, e1]; omega, ?_⟩, fun i hi => ?_⟩, fun i hi j hj => ?_⟩, ?_⟩
  · rw [Array.getElem?_eq_getElem (by rw [fs]; omega), ← getElem!_pos _ 0 (by rw [fs]; omega), f0]
  · rw [e1] at hi
    by_cases h0i : i = 0
    · exact Or.inl h0i
    · exact Or.inr (fr i (by omega) (by omega))
  · rw [e1] at hi
    rw [hgs] at hj
    have hl : E.lookup (compA E.elems[i]! gs[j]!) = some (recPOS R 14 2 (i * 2 + j)) := by
      obtain ⟨p1, p2, -⟩ := hP i hi j hj
      rw [e4 i hi, hg j hj, arrN_mul, ← p2]
      exact lookup_of_inv hE' p1
    rw [hl]
    simp only [decide_eq_true_eq]
    obtain ⟨p1, -, p3⟩ := hP i hi j hj
    rw [hF _ p1, hF i hi, hsj j hj, compA_encA hm (hlj j hj).1 (hlj j hj).2, p3]
  · apply injOK_of_distinct
    intro a ha b hb e
    rw [fs] at ha hb
    refine hinjP a (by omega) b (by omega) (encF_of_encA hm ?_)
    rw [← hF a (by omega), ← hF b (by omega)]
    exact e

end CFSG.KC.YamakiAut

end
