module

public import Certificates.Data.Kernel.G23F48.ConjOrb
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w p : ℕ} {gs : List ℕ} {T : List (ℕ × ℕ × ℕ)}

theorem reachP_spec (h : reachP n w p gs T = true) :
    (T.getD 0 (0, 0, 0)).1 = p ∧ p < n ∧ ∀ i < T.length, (T.getD i (0, 0, 0)).1 < n ∧
      (i = 0 ∨ (T.getD i (0, 0, 0)).2.1 < i ∧ (T.getD i (0, 0, 0)).2.2 < gs.length ∧
        pg w (mask w) (gs.getD (T.getD i (0, 0, 0)).2.2 0)
          (T.getD (T.getD i (0, 0, 0)).2.1 (0, 0, 0)).1 = (T.getD i (0, 0, 0)).1) := by
  unfold reachP at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun i hi => ?_⟩
  have := h3 i hi
  tauto

theorem reach_of_reachP {H : Subgroup (Equiv.Perm (Fin n))} {σ : ℕ → Equiv.Perm (Fin n)}
    (hσ : ∀ s < gs.length, PRep n w (gs.getD s 0) (σ s) ∧ σ s ∈ H) (h : reachP n w p gs T = true)
    (hp : p < n) :
    ∀ i < T.length, ∃ g ∈ H, ((g ⟨p, hp⟩ : Fin n) : ℕ) = (T.getD i (0, 0, 0)).1 := by
  obtain ⟨h1, -, h3⟩ := reachP_spec h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, h0 | ⟨hj, hs, he⟩⟩ := h3 i hi
    · subst h0
      exact ⟨1, H.one_mem, by rw [h1]; rfl⟩
    · obtain ⟨g, hg, hgp⟩ := ih _ hj (by omega)
      refine ⟨σ (T.getD i (0, 0, 0)).2.2 * g, H.mul_mem (hσ _ hs).2 hg, ?_⟩
      rw [Equiv.Perm.mul_apply, ← (hσ _ hs).1 (g ⟨p, hp⟩), hgp, he]

@[expose] noncomputable def pconjW (n w : ℕ) (G GI : List ℕ) : List ℕ → ℕ → ℕ
  | [], x => x
  | s :: ws, x => pconj n w (G.getD s 0) (GI.getD s 0) (pconjW n w G GI ws x)

theorem forceL_eq {α : Type} (y : ℕ) (k : ℕ → α) : forceL y k = k y := by cases y <;> rfl

theorem hasBit_false {M r : ℕ} (h : hasBit M r = false) : M.testBit r = false := by
  have h0 : M &&& 2 ^ r = 0 := by
    have h1 : ¬ 0 < M &&& 1 <<< r := fun hp => by
      have : Nat.blt 0 (M &&& 1 <<< r) = true := by
        rw [Nat.blt_eq]
        exact hp
      exact Bool.false_ne_true (h.symm.trans this)
    rw [Nat.one_shiftLeft] at h1
    omega
  have := congrArg (fun x => x.testBit r) h0
  simpa [Nat.testBit_and, Nat.testBit_two_pow_self] using this

def ConjInv (n w md : ℕ) (G GI : List ℕ) (a b : ℕ) (Vc F B : List (ℕ × ℕ)) (M c : ℕ) : Prop :=
  c = Vc.length ∧
    (∀ v ∈ Vc, ∃ ws : List ℕ, (∀ s ∈ ws, s < G.length) ∧
      v = (pconjW n w G GI ws a, pconjW n w G GI ws b)) ∧
    Vc.Pairwise (fun u v => ckey n w u % md ≠ ckey n w v % md) ∧
    (∀ v ∈ Vc, M.testBit (ckey n w v % md) = true) ∧ (∀ v ∈ F ++ B, v ∈ Vc)

theorem ckids_nil (md : ℕ) (G GI : List ℕ) (v : ℕ × ℕ) (k : List (ℕ × ℕ) → ℕ → ℕ → Bool)
    (B : List (ℕ × ℕ)) (M c : ℕ) : ckids n w md G GI v [] k B M c = k B M c := rfl

theorem ckids_cons (md : ℕ) (G GI : List ℕ) (v : ℕ × ℕ) (s : ℕ) (cs : List ℕ)
    (k : List (ℕ × ℕ) → ℕ → ℕ → Bool) (B : List (ℕ × ℕ)) (M c : ℕ) :
    ckids n w md G GI v (s :: cs) k B M c = (Nat.blt s G.length &&
      forceL (pconj n w (G.getD s 0) (GI.getD s 0) v.1) fun x =>
        forceL (pconj n w (G.getD s 0) (GI.getD s 0) v.2) fun y =>
          forceL (Nat.mod (ckey n w (x, y)) md) fun r =>
            !hasBit M r &&
              forceL (Nat.lor M (Nat.shiftLeft (nat_lit 1) r)) fun M' =>
                ckids n w md G GI v cs k ((x, y) :: B) M' (Nat.succ c)) := rfl

theorem ckids_sound {md : ℕ} {G GI : List ℕ} {a b : ℕ} {v : ℕ × ℕ}
    (hv : ∃ ws : List ℕ, (∀ s ∈ ws, s < G.length) ∧
      v = (pconjW n w G GI ws a, pconjW n w G GI ws b))
    (k : List (ℕ × ℕ) → ℕ → ℕ → Bool) (F : List (ℕ × ℕ)) :
    ∀ (cs : List ℕ) (Vc B : List (ℕ × ℕ)) (M c : ℕ),
      ConjInv n w md G GI a b Vc F B M c → ckids n w md G GI v cs k B M c = true →
      ∃ Vc' B' M' c', ConjInv n w md G GI a b Vc' F B' M' c' ∧ k B' M' c' = true
  | [], Vc, B, M, c, hI, h => ⟨Vc, B, M, c, hI, by rwa [ckids_nil] at h⟩
  | s :: cs, Vc, B, M, c, hI, h => by
    rw [ckids_cons] at h
    simp only [forceL_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hs, hb, h⟩ := h
    have hs' : s < G.length := by rwa [Nat.blt_eq] at hs
    obtain ⟨hc, hW, hP, hM, hFB⟩ := hI
    set x := pconj n w (G.getD s 0) (GI.getD s 0) v.1
    set y := pconj n w (G.getD s 0) (GI.getD s 0) v.2
    have hr : M.testBit (ckey n w (x, y) % md) = false := hasBit_false hb
    refine ckids_sound hv k F cs ((x, y) :: Vc) ((x, y) :: B) _ _ ⟨?_, ?_, ?_, ?_, ?_⟩ h
    · rw [hc]
      rfl
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · obtain ⟨ws, hws, rfl⟩ := hv
        refine ⟨s :: ws, fun t ht => ?_, rfl⟩
        rcases List.mem_cons.1 ht with rfl | ht
        · exact hs'
        · exact hws t ht
      · exact hW u hu
    · refine List.Pairwise.cons (fun u hu e => ?_) hP
      have := hM u hu
      rw [← e, hr] at this
      exact Bool.false_ne_true this
    · intro u hu
      change (M ||| 1 <<< (ckey n w (x, y) % md)).testBit _ = true
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      rcases List.mem_cons.1 hu with rfl | hu
      · simp
      · rw [hM u hu, Bool.true_or]
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact List.mem_cons_of_mem _ (hFB u (List.mem_append_left _ hu))
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hFB u (List.mem_append_right _ hu))

theorem crun_sound {md N : ℕ} {G GI : List ℕ} {a b : ℕ} :
    ∀ (C : List (List ℕ)) (Vc F B : List (ℕ × ℕ)) (M c : ℕ),
      ConjInv n w md G GI a b Vc F B M c → crun n w md N G GI C F B M c = true →
      ∃ V : List (ℕ × ℕ), V.length = N ∧
        (∀ v ∈ V, ∃ ws : List ℕ, (∀ s ∈ ws, s < G.length) ∧
          v = (pconjW n w G GI ws a, pconjW n w G GI ws b)) ∧
        V.Pairwise (fun u v => ckey n w u % md ≠ ckey n w v % md)
  | [], Vc, F, B, M, c, hI, h => by
    have h' : (F.isEmpty && B.isEmpty && Nat.beq c N) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hc, hW, hP, -, -⟩ := hI
    exact ⟨Vc, by rw [← hc]; exact Nat.eq_of_beq_eq_true h'.2, hW, hP⟩
  | cs :: C, Vc, F, B, M, c, hI, h => by
    obtain ⟨hc, hW, hP, hM, hFB⟩ := hI
    cases F with
    | cons v F =>
      have h' : ckids n w md G GI v cs (fun B' M' c' => crun n w md N G GI C F B' M' c') B M c =
          true := h
      obtain ⟨Vc', B', M', c', hI', hk⟩ := ckids_sound (hW v (hFB v (by simp))) _ F cs Vc B M c
        ⟨hc, hW, hP, hM, fun u hu => hFB u (by
          rcases List.mem_append.1 hu with hu | hu
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ hu)
          · exact List.mem_append_right _ hu)⟩ h'
      exact crun_sound C Vc' F B' M' c' hI' hk
    | nil =>
      have h' : List.rec (motive := fun _ => Bool) false
          (fun v F' _ => ckids n w md G GI v cs (fun B' M' c' => crun n w md N G GI C F' B' M' c')
            [] M c) B.reverse = true := h
      cases hB : B.reverse with
      | nil =>
        rw [hB] at h'
        exact absurd h' Bool.false_ne_true
      | cons v F' =>
        rw [hB] at h'
        have hmem : ∀ u ∈ v :: F', u ∈ Vc := fun u hu => hFB u (by
          rw [List.nil_append, ← List.mem_reverse, hB]
          exact hu)
        obtain ⟨Vc', B', M', c', hI', hk⟩ := ckids_sound (hW v (hmem v List.mem_cons_self)) _ F'
          cs Vc [] M c ⟨hc, hW, hP, hM, fun u hu => hmem u (by
            rw [List.append_nil] at hu
            exact List.mem_cons_of_mem _ hu)⟩ h'
        exact crun_sound C Vc' F' B' M' c' hI' hk

theorem conjQ_spec {md : ℕ} {G GI : List ℕ} {a b N : ℕ} {C : List (List ℕ)}
    (h : conjQ n w md G GI a b C N = true) :
    ∃ V : List (ℕ × ℕ), V.length = N ∧
      (∀ v ∈ V, ∃ ws : List ℕ, (∀ s ∈ ws, s < G.length) ∧
        v = (pconjW n w G GI ws a, pconjW n w G GI ws b)) ∧
      V.Pairwise (fun u v => ckey n w u % md ≠ ckey n w v % md) := by
  unfold conjQ at h
  rw [forceL_eq] at h
  refine crun_sound C [(a, b)] [(a, b)] [] _ _ ⟨rfl, fun v hv => ⟨[], by simp, ?_⟩,
    List.pairwise_singleton _ _, fun v hv => ?_, fun v hv => by simpa using hv⟩ h
  · rw [List.mem_singleton.1 hv]
    rfl
  · rw [List.mem_singleton.1 hv]
    change (1 <<< (ckey n w (a, b) % md)).testBit _ = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

end CFSG.KC.G23F48

end
