module

public import Certificates.Data.Kernel.W16Cls
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.W16Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

abbrev PR (P : Nat) (g : Equiv.Perm (Fin 128)) : Prop := PRep 128 8 P g

theorem pr_pc {P Q : Nat} {g h : Equiv.Perm (Fin 128)} (hP : PR P g) (hQ : PR Q h) :
    PR (pc P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem pr_pid : PR pid 1 := prep_pidn (by norm_num) (by norm_num)

theorem pr_unique {P : Nat} {g h : Equiv.Perm (Fin 128)} (hg : PR P g) (hh : PR P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem pr_inj {P Q : Nat} {g : Equiv.Perm (Fin 128)} (hP : PR P g) (hQ : PR Q g)
    (hP0 : P >>> 1024 = 0) (hQ0 : Q >>> 1024 = 0) : P = Q :=
  CFSG.KS.PF.eq_of_fields (n := 128) (w := 8) (by norm_num) hP0 hQ0
    fun i hi => (hP ⟨i, hi⟩).trans (hQ ⟨i, hi⟩).symm

theorem pc_shr (P Q : Nat) : pc P Q >>> 1024 = 0 :=
  CFSG.KS.PF.pcomp_shr (n := 128) (w := 8) P Q (by norm_num) (by norm_num)

section Closure

variable {G : Type*} [Group G]

theorem closure_conj_closed {S X : Set G} (hX : X.Finite) (h : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ ∈ X) :
    ∀ g ∈ Subgroup.closure S, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => intro x hx; simpa using hx
  | mul a b _ _ ha hb =>
    intro x hx
    have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb x hx)
  | inv a _ ha =>
    intro x hx
    have : Finite X := hX.to_subtype
    let f : X → X := fun y => ⟨a * y * a⁻¹, ha y y.2⟩
    have hf : Function.Injective f := fun y z hyz => by
      have := congrArg Subtype.val hyz
      simp only [f, mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x, hx⟩
    have hy' : a * (y : G) * a⁻¹ = x := congrArg Subtype.val hy
    have e : a⁻¹ * x * a⁻¹⁻¹ = y := by rw [← hy']; group
    rw [e]
    exact y.2

theorem closure_mul_closed {S X : Set G} (hX : X.Finite) (h : ∀ s ∈ S, ∀ x ∈ X, x * s ∈ X) :
    ∀ g ∈ Subgroup.closure S, ∀ x ∈ X, x * g ∈ X := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => intro x hx; simpa using hx
  | mul a b _ _ ha hb =>
    intro x hx
    rw [← mul_assoc]
    exact hb _ (ha x hx)
  | inv a _ ha =>
    intro x hx
    have : Finite X := hX.to_subtype
    let f : X → X := fun y => ⟨y * a, ha y y.2⟩
    have hf : Function.Injective f := fun y z hyz => by
      have := congrArg Subtype.val hyz
      simp only [f, mul_left_inj] at this
      exact Subtype.ext this
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x, hx⟩
    have hy' : (y : G) * a = x := congrArg Subtype.val hy
    have e : x * a⁻¹ = y := by rw [← hy']; group
    rw [e]
    exact y.2

end Closure

theorem treeK_spec {ng N : Nat} {E P : Nat → Nat} (h : treeK ng N E P = true) {i : Nat}
    (hi : i < N) (h0 : i ≠ 0) :
    f16 (P i) 0 < i ∧ f16 (P i) 1 < ng ∧ f16 (E (f16 (P i) 0)) (f16 (P i) 1) = i := by
  unfold treeK at h
  have h1 := allN_iff.1 h i hi
  simp only [Bool.or_eq_true, Nat.beq_eq_true_eq, Bool.and_eq_true, Nat.blt_eq] at h1
  rcases h1 with h1 | ⟨⟨h2, h3⟩, h4⟩
  · exact absurd (Nat.eq_of_beq_eq_true h1) h0
  · exact ⟨h2, h3, Nat.eq_of_beq_eq_true h4⟩

theorem ordK_inj {N : Nat} {T O : Nat → Nat} (h : ordK N T O = true) {i j : Nat} (hi : i < N)
    (hj : j < N) (he : T i = T j) : i = j := by
  unfold ordK at h
  rw [Bool.and_eq_true, allN_iff, allN_iff] at h
  obtain ⟨hO, hlt⟩ := h
  have hmono : ∀ m m', m < m' → m' < N → T (O m) < T (O m') := by
    intro m m' hmm' hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      have hs : T (O m') < T (O (m' + 1)) := Nat.blt_eq ▸ hlt m' (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hmm' with h1 | h1
      · exact lt_trans (ih h1 (by omega)) hs
      · rw [h1]; exact hs
  let o : Fin N → Fin N := fun m => ⟨O m, Nat.blt_eq ▸ hO m m.2⟩
  have ho : Function.Injective o := by
    intro m m' hmm'
    have e : O m = O m' := congrArg Fin.val hmm'
    rcases lt_trichotomy (m : Nat) m' with h1 | h1 | h1
    · have := hmono m m' h1 m'.2; rw [e] at this; exact absurd this (lt_irrefl _)
    · exact Fin.ext h1
    · have := hmono m' m h1 m.2; rw [e] at this; exact absurd this (lt_irrefl _)
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 ho) ⟨i, hi⟩
  obtain ⟨m', hm'⟩ := (Finite.injective_iff_surjective.1 ho) ⟨j, hj⟩
  have ei : O m = i := congrArg Fin.val hm
  have ej : O m' = j := congrArg Fin.val hm'
  rcases lt_trichotomy (m : Nat) m' with h1 | h1 | h1
  · have := hmono m m' h1 m'.2; rw [ei, ej, he] at this; exact absurd this (lt_irrefl _)
  · rw [← ei, ← ej, Fin.ext h1]
  · have := hmono m' m h1 m.2; rw [ei, ej, he] at this; exact absurd this (lt_irrefl _)

theorem enum_sound {ng N : Nat} {T E P O : Nat → Nat} {stepP : Nat → Nat → Nat}
    {step : Nat → Equiv.Perm (Fin 128) → Equiv.Perm (Fin 128)} {x0 : Equiv.Perm (Fin 128)}
    {Orb : Set (Equiv.Perm (Fin 128))}
    (hstep : ∀ k < ng, ∀ t x, PR t x → PR (stepP k t) (step k x))
    (hshr : ∀ k < ng, ∀ t, stepP k t >>> 1024 = 0)
    (h0 : PR (T 0) x0) (hT0 : T 0 >>> 1024 = 0)
    (hcl : ∀ i < N, ∀ k < ng, f16 (E i) k < N ∧ stepP k (T i) = T (f16 (E i) k))
    (htree : treeK ng N E P = true) (hord : ordK N T O = true) (hN : 0 < N)
    (hx0 : x0 ∈ Orb) (hOrb : ∀ k < ng, ∀ x ∈ Orb, step k x ∈ Orb)
    (hmin : ∀ X : Set (Equiv.Perm (Fin 128)), X.Finite → x0 ∈ X →
      (∀ k < ng, ∀ x ∈ X, step k x ∈ X) → Orb ⊆ X) :
    (∀ x, x ∈ Orb ↔ ∃ i < N, PR (T i) x) ∧ Nat.card Orb = N ∧ ∀ i < N, T i >>> 1024 = 0 := by
  have hreach : ∀ i < N, (∃ x ∈ Orb, PR (T i) x) ∧ T i >>> 1024 = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hz : i = 0
      · subst hz
        exact ⟨⟨x0, hx0, h0⟩, hT0⟩
      · obtain ⟨hp, hk, he⟩ := treeK_spec htree hi hz
        obtain ⟨⟨x, hx, hpx⟩, -⟩ := ih _ hp (by omega)
        have hc := (hcl (f16 (P i) 0) (by omega) (f16 (P i) 1) hk).2
        rw [he] at hc
        rw [← hc]
        exact ⟨⟨step _ x, hOrb _ hk x hx, hstep _ hk _ _ hpx⟩, hshr _ hk _⟩
  let X : Set (Equiv.Perm (Fin 128)) := {x | ∃ i < N, PR (T i) x}
  have hXf : X.Finite := by
    have : X ⊆ (fun i : Fin N => Classical.choose (hreach i i.2).1) '' Set.univ := by
      rintro x ⟨i, hi, hx⟩
      refine ⟨⟨i, hi⟩, trivial, ?_⟩
      exact pr_unique (Classical.choose_spec (hreach i hi).1).2 hx
    exact (Set.finite_univ.image _).subset this
  have hXc : ∀ k < ng, ∀ x ∈ X, step k x ∈ X := by
    rintro k hk x ⟨i, hi, hx⟩
    obtain ⟨h1, h2⟩ := hcl i hi k hk
    exact ⟨_, h1, h2 ▸ hstep k hk _ _ hx⟩
  have hsub := hmin X hXf ⟨0, hN, h0⟩ hXc
  have hmem : ∀ x, x ∈ Orb ↔ ∃ i < N, PR (T i) x := by
    intro x
    refine ⟨fun hx => hsub hx, ?_⟩
    rintro ⟨i, hi, hx⟩
    obtain ⟨⟨y, hy, hpy⟩, -⟩ := hreach i hi
    rw [pr_unique hx hpy]
    exact hy
  refine ⟨hmem, ?_, fun i hi => (hreach i hi).2⟩
  let g : Fin N → Orb := fun i =>
    ⟨Classical.choose (hreach i i.2).1, (Classical.choose_spec (hreach i i.2).1).1⟩
  have hg : ∀ i : Fin N, PR (T i) (g i) := fun i => (Classical.choose_spec (hreach i i.2).1).2
  have hbij : Function.Bijective g := by
    refine ⟨fun i j hij => ?_, fun x => ?_⟩
    · have e : (g i : Equiv.Perm (Fin 128)) = g j := congrArg Subtype.val hij
      have h1 := hg i
      rw [e] at h1
      exact Fin.ext (ordK_inj hord i.2 j.2
        (pr_inj h1 (hg j) (hreach i i.2).2 (hreach j j.2).2))
    · obtain ⟨i, hi, hx⟩ := (hmem x).1 x.2
      exact ⟨⟨i, hi⟩, Subtype.ext (pr_unique (hg ⟨i, hi⟩) hx)⟩
  rw [← Nat.card_eq_of_bijective g hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem orbK_sound {A AI : Nat → Nat} {a : Fin 2 → Equiv.Perm (Fin 128)}
    (hA : ∀ k : Fin 2, PR (A k) (a k) ∧ PR (AI k) (a k)⁻¹) {N r : Nat} {T E P O : Nat → Nat}
    {R : Equiv.Perm (Fin 128)} (hR : PR r R) (hN : 0 < N)
    (h : orbK A AI N r T E P O = true) :
    (∀ x, (∃ g ∈ Subgroup.closure (Set.range a), x = g * R * g⁻¹) ↔ ∃ i < N, PR (T i) x) ∧
      Nat.card {x | ∃ g ∈ Subgroup.closure (Set.range a), x = g * R * g⁻¹} = N ∧
      ∀ i < N, T i >>> 1024 = 0 := by
  unfold orbK at h
  simp only [Bool.and_eq_true, Nat.beq_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hT0, hr⟩, hcl⟩, htree⟩, hord⟩ := h
  rw [allN_iff] at hcl
  have hT0' : T 0 = r := Nat.eq_of_beq_eq_true hT0
  have key := enum_sound (ng := 2) (T := T) (E := E) (P := P) (O := O) (x0 := R)
    (stepP := fun k t => pc (A k) (pc t (AI k)))
    (step := fun k x => if hk : k < 2 then a ⟨k, hk⟩ * x * (a ⟨k, hk⟩)⁻¹ else x)
    (Orb := {x | ∃ g ∈ Subgroup.closure (Set.range a), x = g * R * g⁻¹})
    (fun k hk t x hx => by
      simp only [hk, ↓reduceDIte]
      rw [mul_assoc]
      exact pr_pc (hA ⟨k, hk⟩).1 (pr_pc hx (hA ⟨k, hk⟩).2))
    (fun k _ t => pc_shr _ _) (by rw [hT0']; exact hR) (by rw [hT0']; exact Nat.eq_of_beq_eq_true hr)
    (fun i hi k hk => by
      have h1 := allN_iff.1 (hcl i hi) k hk
      simp only [Bool.and_eq_true, Nat.blt_eq] at h1
      exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩)
    htree hord hN ⟨1, Subgroup.one_mem _, by simp⟩
    (fun k hk x ⟨g, hg, hx⟩ => by
      simp only [hk, ↓reduceDIte]
      refine ⟨a ⟨k, hk⟩ * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) hg, ?_⟩
      rw [hx]
      group)
    (fun X hXf hR' hX => by
      rintro x ⟨g, hg, rfl⟩
      refine closure_conj_closed hXf ?_ g hg R hR'
      rintro s ⟨k, rfl⟩ y hy
      have := hX k k.2 y hy
      simpa [k.2] using this)
  exact ⟨fun x => key.1 x, key.2.1, key.2.2⟩

theorem sylK_sound {G : Nat → Nat} {ng : Nat} {p : Fin ng → Equiv.Perm (Fin 128)}
    (hG : ∀ k : Fin ng, PR (G k) (p k)) {N : Nat} {L E P O : Nat → Nat} (hN : 0 < N)
    (h : sylK G ng N L E P O = true) :
    (∀ x, x ∈ Subgroup.closure (Set.range p) ↔ ∃ i < N, PR (L i) x) ∧
      Nat.card (Subgroup.closure (Set.range p)) = N ∧ ∀ i < N, L i >>> 1024 = 0 := by
  unfold sylK at h
  simp only [Bool.and_eq_true, Nat.beq_eq_true_eq] at h
  obtain ⟨⟨⟨hL0, hcl⟩, htree⟩, hord⟩ := h
  rw [allN_iff] at hcl
  have hL0' : L 0 = pid := Nat.eq_of_beq_eq_true hL0
  have key := enum_sound (ng := ng) (T := L) (E := E) (P := P) (O := O) (x0 := 1)
    (stepP := fun k t => pc t (G k))
    (step := fun k x => if hk : k < ng then x * p ⟨k, hk⟩ else x)
    (Orb := (Subgroup.closure (Set.range p) : Set (Equiv.Perm (Fin 128))))
    (fun k hk t x hx => by
      simp only [hk, ↓reduceDIte]
      exact pr_pc hx (hG ⟨k, hk⟩))
    (fun k _ t => pc_shr _ _) (by rw [hL0']; exact pr_pid) (by rw [hL0']; decide +kernel)
    (fun i hi k hk => by
      have h1 := allN_iff.1 (hcl i hi) k hk
      simp only [Bool.and_eq_true, Nat.blt_eq] at h1
      exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩)
    htree hord hN (Subgroup.one_mem _)
    (fun k hk x hx => by
      simp only [hk, ↓reduceDIte]
      exact Subgroup.mul_mem _ hx (Subgroup.subset_closure ⟨_, rfl⟩))
    (fun X hXf h1 hX => by
      intro x hx
      have := closure_mul_closed hXf (S := Set.range p) (by
        rintro s ⟨k, rfl⟩ y hy
        have := hX k k.2 y hy
        simpa [k.2] using this) x hx 1 h1
      simpa using this)
  refine ⟨fun x => key.1 x, ?_, key.2.2⟩
  rw [← key.2.1]
  rfl

theorem letters_lt (c : Nat) : ∀ k ∈ letters c, k < 2 := by
  intro k hk
  unfold letters at hk
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hk
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem wordP_sound {A : Nat → Nat} {a : Fin 2 → Equiv.Perm (Fin 128)}
    (hA : ∀ k : Fin 2, PR (A k) (a k)) (c : Nat) :
    ∃ x ∈ Subgroup.closure (Set.range a), PR (wordP A c) x := by
  unfold wordP
  suffices h : ∀ l : List Nat, (∀ k ∈ l, k < 2) → ∀ acc x, x ∈ Subgroup.closure (Set.range a) →
      PR acc x → ∃ y ∈ Subgroup.closure (Set.range a),
        PR (l.foldl (fun acc k => pc (A k) acc) acc) y from
    h _ (letters_lt c) pid 1 (Subgroup.one_mem _) pr_pid
  intro l
  induction l with
  | nil => exact fun _ acc x hx h => ⟨x, hx, h⟩
  | cons k l ih =>
    intro hl acc x hx h
    have hk : k < 2 := hl k (by simp)
    exact ih (fun k' hk' => hl k' (by simp [hk'])) _ (a ⟨k, hk⟩ * x)
      (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) hx) (pr_pc (hA ⟨k, hk⟩) h)

theorem pid_shr : pid >>> 1024 = 0 := by decide +kernel

theorem invCovK_spec {N : Nat} {L C : Nat → Nat} {T : Nat → Nat → Nat} {NC : Nat → Nat}
    (h : invCovK N L C T NC = true) {i : Nat} (hi : i < N) {y : Equiv.Perm (Fin 128)}
    (hy : PR (L i) y) (h1 : y ≠ 1) (h2 : y * y = 1) :
    ∃ j < 9, ∃ idx < NC j, T j idx = L i := by
  unfold invCovK at h
  have h' := allN_iff.1 h i hi
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h'
  rcases h' with (h' | h') | ⟨⟨⟨-, hc⟩, hn⟩, he⟩
  · exact absurd (pr_unique hy ((Nat.eq_of_beq_eq_true h') ▸ pr_pid)) h1
  · have hpp : PR (pc (L i) (L i)) 1 := h2 ▸ pr_pc hy hy
    have e := pr_inj hpp pr_pid (pc_shr _ _) pid_shr
    rw [e] at h'
    simp at h'
  · exact ⟨_, hc, _, hn, Nat.eq_of_beq_eq_true he⟩

end CFSG.KC.W16Cls

end
