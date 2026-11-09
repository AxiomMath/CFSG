module

public import CFSG.Certificates.Kernel.O8.SBClsSound

public section

namespace CFSG.KC.SBRec

open CFSG.EvenSmallLie.OmegaEight.SpBranch CFSG.KC.SBCls MulAction

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ}

@[expose] def Cor (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (N u : ℕ) (p : ℕ × ℕ) : Prop :=
  p.2 < N ∧ p.1 = cconj mul inv p.2 u

variable (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
include Φ h0 hinv

theorem cc {a b : ℕ} (ha : a < N) (hb : b < N) :
    cconj mul inv a b = Φ.f (Φ.g a * Φ.g b * (Φ.g a)⁻¹) := by
  rw [Φ.f_conj h0 (fun c hc => inv_spec hinv hc), Φ.f_g ha, Φ.f_g hb]

theorem mul_lt {a b : ℕ} (ha : a < N) (hb : b < N) : mul a b < N := by
  rw [← Φ.f_g ha, ← Φ.f_g hb, ← Φ.map_mul]
  exact Φ.lt _

include hgens in
theorem cor_step {u o w g : ℕ} (hu : u < N) (hg : g ∈ gens) (h : Cor mul inv N u (o, w)) :
    Cor mul inv N u (cconj mul inv g o, mul g w) := by
  obtain ⟨hw, ho⟩ := h
  simp only at hw ho
  have hgN := hgens g hg
  refine ⟨mul_lt Φ h0 hinv hgN hw, ?_⟩
  simp only
  have hoN : o < N := by rw [ho, cc Φ h0 hinv hw hu]; exact Φ.lt _
  have hm : Φ.g (mul g w) = Φ.g g * Φ.g w := by
    refine Φ.inj ?_
    rw [Φ.map_mul, Φ.f_g hgN, Φ.f_g hw, Φ.f_g (mul_lt Φ h0 hinv hgN hw)]
  rw [cc Φ h0 hinv hgN hoN, cc Φ h0 hinv (mul_lt Φ h0 hinv hgN hw) hu, ho,
    cc Φ h0 hinv hw hu, Φ.g_f, hm]
  congr 1
  group

@[expose] def AddPost (u o : ℕ) (L : List ℕ) (R B : List (ℕ × ℕ))
    (a : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) : Prop :=
  Tracks a.2.2 a.1 ∧ (∀ p ∈ a.1, Cor mul inv N u p) ∧ (a.1.map Prod.fst).Nodup ∧
    (∀ p ∈ R, p ∈ a.1) ∧ (∀ p ∈ B, p ∈ a.2.1) ∧ (∀ p ∈ a.2.1, p ∈ B ∨ p ∈ a.1) ∧
    (∀ g ∈ L, cconj mul inv g o ∈ a.1.map Prod.fst) ∧
    (∀ x ∈ a.1.map Prod.fst, x ∈ R.map Prod.fst ∨ x ∈ a.2.1.map Prod.fst) ∧
    ∃ k, a.1.length = R.length + k ∧ a.2.1.length = B.length + k

include hgens in
theorem fold_post {u o w : ℕ} (hu : u < N) (hc : Cor mul inv N u (o, w)) :
    ∀ (L : List ℕ), (∀ g ∈ L, g ∈ gens) → ∀ (R B : List (ℕ × ℕ)) (M : ℕ), Tracks M R →
      (∀ p ∈ R, Cor mul inv N u p) → (R.map Prod.fst).Nodup →
      AddPost (mul := mul) (inv := inv) (N := N) u o L R B (L.foldl (recAdd mul inv o w) (R, B, M))
  | [], _, R, B, M, hM, hR, hN => ⟨hM, hR, hN, fun _ h => h, fun _ h => h, fun _ h => Or.inl h,
      fun _ h => by simp at h, fun _ h => Or.inl h, 0, rfl, rfl⟩
  | g :: L, hL, R, B, M, hM, hR, hN => by
    have hLg : ∀ g' ∈ L, g' ∈ gens := fun g' h => hL g' (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    by_cases h : M.testBit (cconj mul inv g o) = true
    · have e : recAdd mul inv o w (R, B, M) g = (R, B, M) := by
        unfold recAdd
        simp only [h, if_true]
      rw [e]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, k, hk1, hk2⟩ :=
        fold_post hu hc L hLg R B M hM hR hN
      refine ⟨h1, h2, h3, h4, h5, h6, fun g' hg' => ?_, h8, k, hk1, hk2⟩
      rcases List.mem_cons.1 hg' with rfl | hg'
      · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 ((hM _).1 h)
        exact List.mem_map.2 ⟨p, h4 p hp, hpe⟩
      · exact h7 g' hg'
    · have e : recAdd mul inv o w (R, B, M) g = ((cconj mul inv g o, mul g w) :: R,
          B ++ [(cconj mul inv g o, mul g w)], M ||| 2 ^ cconj mul inv g o) := by
        unfold recAdd
        simp only [h, Bool.false_eq_true, if_false]
      rw [e]
      set v := cconj mul inv g o
      have hM' : Tracks (M ||| 2 ^ v) ((v, mul g w) :: R) := by
        intro x
        rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hM, List.map_cons,
          List.mem_cons, decide_eq_true_eq, eq_comm, or_comm]
      have hR' : ∀ p ∈ (v, mul g w) :: R, Cor mul inv N u p := by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact cor_step Φ h0 hinv hgens hu (hL g List.mem_cons_self) hc
        · exact hR p hp
      have hN' : (((v, mul g w) :: R).map Prod.fst).Nodup := by
        rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hv => h ((hM v).2 hv), hN⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, k, hk1, hk2⟩ :=
        fold_post hu hc L hLg _ (B ++ [(v, mul g w)]) _ hM' hR' hN'
      refine ⟨h1, h2, h3, fun p hp => h4 p (List.mem_cons_of_mem _ hp),
        fun p hp => h5 p (List.mem_append_left _ hp), fun p hp => ?_, fun g' hg' => ?_,
        fun x hx => ?_, k + 1, ?_, ?_⟩
      · rcases h6 p hp with hp' | hp'
        · rcases List.mem_append.1 hp' with hp'' | hp''
          · exact Or.inl hp''
          · rw [List.mem_singleton] at hp''
            exact Or.inr (h4 _ (hp'' ▸ List.mem_cons_self))
        · exact Or.inr hp'
      · rcases List.mem_cons.1 hg' with rfl | hg'
        · exact List.mem_map.2 ⟨_, h4 _ List.mem_cons_self, rfl⟩
        · exact h7 g' hg'
      · rcases h8 x hx with hx' | hx'
        · rw [List.map_cons, List.mem_cons] at hx'
          rcases hx' with rfl | hx'
          · exact Or.inr (List.mem_map.2 ⟨_, h5 _ (List.mem_append_right _ (List.mem_singleton_self _)),
              rfl⟩)
          · exact Or.inl hx'
        · exact Or.inr hx'
      · rw [hk1, List.length_cons]
        omega
      · rw [hk2, List.length_append, List.length_singleton]
        omega

@[expose] def RInv (u : ℕ) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) : Prop :=
  Tracks st.2.2 st.1 ∧ (∀ p ∈ st.1, Cor mul inv N u p) ∧ (st.1.map Prod.fst).Nodup ∧
    (∀ x ∈ st.1.map Prod.fst, x ∈ st.2.1.map Prod.fst ∨
      ∀ g ∈ gens, cconj mul inv g x ∈ st.1.map Prod.fst) ∧
    (∀ p ∈ st.2.1, p ∈ st.1) ∧ st.2.1.length ≤ st.1.length ∧ u ∈ st.1.map Prod.fst

include hgens in
theorem step_inv {u : ℕ} (hu : u < N) {R : List (ℕ × ℕ)} {o w : ℕ} {q : List (ℕ × ℕ)} {M : ℕ}
    (h : RInv (mul := mul) (inv := inv) (N := N) (gens := gens) u (R, (o, w) :: q, M)) :
    RInv (mul := mul) (inv := inv) (N := N) (gens := gens) u (recMStep mul inv gens (R, (o, w) :: q, M)) ∧
      R.length - ((o, w) :: q).length + 1 =
        (recMStep mul inv gens (R, (o, w) :: q, M)).1.length -
          (recMStep mul inv gens (R, (o, w) :: q, M)).2.1.length := by
  obtain ⟨hM, hR, hN, hcl, hQ, hlen, hu'⟩ := h
  rw [recMStep_cons]
  have hc : Cor mul inv N u (o, w) := hR _ (hQ _ List.mem_cons_self)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, k, hk1, hk2⟩ :=
    fold_post Φ h0 hinv hgens hu hc gens (fun _ h => h) R q M hM hR hN
  simp only at hlen ⊢
  refine ⟨⟨h1, h2, h3, fun x hx => ?_, fun p hp => ?_, by rw [hk1, hk2]; simp at hlen; omega, ?_⟩,
    by rw [hk1, hk2]; simp at hlen ⊢; omega⟩
  · rcases h8 x hx with hx' | hx'
    · rcases hcl x hx' with hq | hc'
      · rw [List.map_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Or.inr h7
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
          exact Or.inl (List.mem_map.2 ⟨p, h5 p hp, rfl⟩)
      · refine Or.inr fun g hg => ?_
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 (hc' g hg)
        exact List.mem_map.2 ⟨p, h4 p hp, hpe⟩
    · exact Or.inl hx'
  · rcases h6 p hp with hp' | hp'
    · exact h4 p (hQ p (List.mem_cons_of_mem _ hp'))
    · exact hp'
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hu'
    exact List.mem_map.2 ⟨p, h4 p hp, hpe⟩

include hgens in
theorem run_inv {u : ℕ} (hu : u < N) : ∀ (L : List ℕ) (n : ℕ) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ),
    RInv (mul := mul) (inv := inv) (N := N) (gens := gens) u st →
    (st.2.1 = [] ∨ n ≤ st.1.length - st.2.1.length) →
    RInv (mul := mul) (inv := inv) (N := N) (gens := gens) u
        (L.foldl (fun st _ => recMStep mul inv gens st) st) ∧
      ((L.foldl (fun st _ => recMStep mul inv gens st) st).2.1 = [] ∨
        n + L.length ≤ (L.foldl (fun st _ => recMStep mul inv gens st) st).1.length -
          (L.foldl (fun st _ => recMStep mul inv gens st) st).2.1.length)
  | [], n, st, h, hn => ⟨h, by simpa using hn⟩
  | _ :: L, n, ⟨R, Q, M⟩, h, hn => by
    rw [List.foldl_cons]
    cases Q with
    | nil =>
      have e : recMStep mul inv gens (R, [], M) = (R, [], M) := rfl
      rw [e]
      have := run_inv hu L (n + 1) (R, [], M) h (Or.inl rfl)
      rw [List.length_cons]
      rcases this.2 with h' | h'
      · exact ⟨this.1, Or.inl h'⟩
      · exact ⟨this.1, Or.inr (by omega)⟩
    | cons p q =>
      obtain ⟨o, w⟩ := p
      obtain ⟨hs, hd⟩ := step_inv Φ h0 hinv hgens hu h
      have hn' : n ≤ R.length - ((o, w) :: q).length := by simpa using hn
      have := run_inv hu L (n + 1) _ hs (Or.inr (by omega))
      rw [List.length_cons]
      rcases this.2 with h' | h'
      · exact ⟨this.1, Or.inl h'⟩
      · exact ⟨this.1, Or.inr (by omega)⟩

include hgens in
theorem recM_ok {u : ℕ} (hu : u < N)
    (hsmall : (orbit (ConjAct H) (Φ.g u)).ncard < 130) :
    orbOK mul inv N u (recM mul inv gens u) = true ∧
      orbClosed mul inv gens u (recM mul inv gens u) = true := by
  have h00 : Cor mul inv N u (u, 0) := by
    refine ⟨Φ.pos, ?_⟩
    simp only
    rw [cc Φ h0 hinv Φ.pos hu, ← Φ.f_one h0, Φ.g_f, one_mul, inv_one, mul_one, Φ.f_g hu]
  have hinit : RInv (mul := mul) (inv := inv) (N := N) (gens := gens) u ([(u, 0)], [(u, 0)], 2 ^ u) := by
    refine ⟨fun x => ?_, fun p hp => ?_, by simp, fun x hx => Or.inl (by simpa using hx),
      fun p hp => hp, le_refl _, by simp⟩
    · rw [Nat.testBit_two_pow, decide_eq_true_eq]
      simp [eq_comm]
    · rw [List.mem_singleton] at hp
      rw [hp]
      exact h00
  obtain ⟨⟨hM, hR, hN, hcl, hQ, hlen, hu'⟩, hend⟩ :=
    run_inv Φ h0 hinv hgens hu (List.range 130) 0 _ hinit (Or.inr (Nat.zero_le _))
  have hok : orbOK mul inv N u (recM mul inv gens u) = true := by
    unfold recM orbOK
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨fun p hp => hR p hp, hN⟩
  refine ⟨hok, ?_⟩
  have hle := Φ.length_le_ncard h0 hinv (u := Φ.g u) (O := recM mul inv gens u)
    (by rw [Φ.f_g hu]; exact hok)
  have hQe : ((List.range 130).foldl (fun st _ => recMStep mul inv gens st)
      ([(u, 0)], [(u, 0)], 2 ^ u)).2.1 = [] := by
    rcases hend with h | h
    · exact h
    · exfalso
      rw [List.length_range] at h
      unfold recM at hle
      omega
  rw [hQe] at hcl
  unfold recM orbClosed
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  refine ⟨hu', fun p hp g hg => ?_⟩
  rcases hcl p.1 (List.mem_map_of_mem hp) with h | h
  · simp at h
  · exact h g hg

end CFSG.KC.SBRec

end
