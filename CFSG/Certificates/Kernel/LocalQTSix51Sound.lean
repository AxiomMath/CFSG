module

public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSixInputs
public import Certificates.Data.Kernel.LocalQT.SixRank

public section

namespace CFSG.KC.LQT.X6

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Unc25K1.Six CFSG.KC.Ord

theorem get_enc (σ : P6) (i : Fin 6) : (R6.enc σ).get i = σ i := by
  fin_cases i <;> rfl

theorem enc_mul (σ τ : P6) : R6.enc (σ * τ) = R6.enc σ * R6.enc τ := by
  change _ = R6.mul _ _
  simp only [R6.mul, get_enc]
  rfl

theorem enc_one : R6.enc 1 = 1 := rfl

theorem enc_inj {σ τ : P6} (h : R6.enc σ = R6.enc τ) : σ = τ :=
  Equiv.ext fun i => by
    have := congrArg (fun x => R6.get x i) h
    simpa only [get_enc] using this

def κ (y : R6) : ℕ := y.a.val + y.b.val * 32 + y.c.val * 1024 + y.d.val * 32768 +
  y.e.val * 1048576 + y.f.val * 33554432

theorem κ_enc (σ : P6) : κ (R6.enc σ) = P.code σ := by
  rw [P.code_fin, Fin.sum_univ_six]
  simp [κ, R6.enc]

variable (hrank : rankOK = true)
include hrank in
theorem rank_inj {σ τ : P6} (h : rank6 (P.code σ) = rank6 (P.code τ)) : σ = τ := by
  rw [rankOK, P.allP_iff] at hrank
  have h1 := P.beq_iff.1 (hrank σ)
  have h2 := P.beq_iff.1 (hrank τ)
  rw [h] at h1
  exact P.code_inj (by norm_num) (h1.symm.trans h2)

theorem inM_eq (m x : ℕ) : inM m x = m.testBit (rank6 x) := P.bit_eq m (rank6 x)

def Inv (st : ℕ × List ℕ) : Prop :=
  (∀ c ∈ st.2, ∃ σ : P6, P.code σ = c) ∧ st.2.Nodup ∧
    ∀ σ : P6, inM st.1 (P.code σ) = true ↔ P.code σ ∈ st.2

@[expose] noncomputable def ins (st : ℕ × List ℕ) (y : ℕ) : ℕ × List ℕ :=
  Bool.rec (motive := fun _ => ℕ × List ℕ)
    (Prod.mk (Nat.lor st.1 (Nat.shiftLeft 1 (rank6 y))) (List.cons y st.2)) st (inM st.1 y)

include hrank in
theorem ins_spec {st : ℕ × List ℕ} (hst : Inv st) (τ : P6) :
    Inv (ins st (P.code τ)) ∧ ∀ c, c ∈ (ins st (P.code τ)).2 ↔ c ∈ st.2 ∨ c = P.code τ := by
  obtain ⟨h1, h2, h3⟩ := hst
  unfold ins
  cases h : inM st.1 (P.code τ)
  · have hn : P.code τ ∉ st.2 := fun hm => by rw [← h3] at hm; rw [hm] at h; exact absurd h (by simp)
    change Inv (_, P.code τ :: st.2) ∧ ∀ c, c ∈ P.code τ :: st.2 ↔ _
    refine ⟨⟨?_, List.nodup_cons.2 ⟨hn, h2⟩, fun σ => ?_⟩, fun c => by simp [or_comm]⟩
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨τ, rfl⟩
      · exact h1 c hc
    · rw [inM_eq, P.lor_eq, Nat.testBit_or, Nat.testBit_two_pow, ← inM_eq, Bool.or_eq_true, h3,
        List.mem_cons, decide_eq_true_iff]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (by rw [rank_inj hrank h.symm])
      · rintro (h | h)
        · exact Or.inr (by rw [P.code_inj (by norm_num) h])
        · exact Or.inl h
  · change Inv st ∧ ∀ c, c ∈ st.2 ↔ _
    have hm : P.code τ ∈ st.2 := (h3 τ).1 h
    refine ⟨⟨h1, h2, h3⟩, fun c => ⟨Or.inl, ?_⟩⟩
    rintro (h | rfl)
    · exact h
    · exact hm

@[expose] noncomputable def innerK (G : List ℕ) (x : ℕ) : ℕ × List ℕ → ℕ × List ℕ :=
  List.rec (motive := fun _ => ℕ × List ℕ → ℕ × List ℕ) (fun st => st)
    (fun g _ ih2 st => ih2 (letP (P.mul 6 x g) fun y => Bool.rec (motive := fun _ => ℕ × List ℕ)
      (Prod.mk (Nat.lor st.1 (Nat.shiftLeft 1 (rank6 y))) (List.cons y st.2)) st (inM st.1 y))) G

theorem letP_eq (y : ℕ) (k : ℕ → ℕ × List ℕ) : letP y k = k y := by cases y <;> rfl

theorem innerK_nil (x : ℕ) (st : ℕ × List ℕ) : innerK [] x st = st := rfl

theorem shl1 (r : ℕ) : Nat.shiftLeft 1 r = 2 ^ r := by
  change 1 <<< r = _
  rw [Nat.one_shiftLeft]

theorem innerK_cons (g : ℕ) (G : List ℕ) (x : ℕ) (st : ℕ × List ℕ) :
    innerK (g :: G) x st = innerK G x (letP (P.mul 6 x g) (ins st)) := rfl

include hrank in
theorem innerK_spec (ρ : P6) : ∀ (Gs : List P6) (st : ℕ × List ℕ), Inv st →
    Inv (innerK (Gs.map P.code) (P.code ρ) st) ∧ ∀ c, c ∈ (innerK (Gs.map P.code) (P.code ρ) st).2 ↔
      c ∈ st.2 ∨ ∃ γ ∈ Gs, c = P.code (ρ * γ)
  | [], st, hst => by
    rw [List.map_nil, innerK_nil]
    exact ⟨hst, fun c => by simp⟩
  | γ :: Gs, st, hst => by
    have e : innerK ((γ :: Gs).map P.code) (P.code ρ) st =
        innerK (Gs.map P.code) (P.code ρ) (ins st (P.code (ρ * γ))) := by
      rw [List.map_cons, innerK_cons, letP_eq, P.code_mul (by norm_num)]
    obtain ⟨hi1, hi2⟩ := ins_spec hrank hst (ρ * γ)
    obtain ⟨hj1, hj2⟩ := innerK_spec ρ Gs _ hi1
    rw [e]
    refine ⟨hj1, fun c => ?_⟩
    rw [hj2, hi2]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem stepK_cons (G : List ℕ) (x : ℕ) (old : List ℕ) (st : ℕ × List ℕ) :
    stepK G (x :: old) st = stepK G old (innerK G x st) := rfl

theorem stepK_nil (G : List ℕ) (st : ℕ × List ℕ) : stepK G [] st = st := rfl

include hrank in
theorem stepK_spec (G : List P6) : ∀ (old : List ℕ), (∀ c ∈ old, ∃ σ : P6, P.code σ = c) →
    ∀ st, Inv st → Inv (stepK (G.map P.code) old st) ∧ ∀ c, c ∈ (stepK (G.map P.code) old st).2 ↔
      c ∈ st.2 ∨ ∃ ρ : P6, P.code ρ ∈ old ∧ ∃ γ ∈ G, c = P.code (ρ * γ)
  | [], _, st, hst => by
    rw [stepK_nil]
    exact ⟨hst, fun c => by simp⟩
  | x :: old, hold, st, hst => by
    obtain ⟨ρ, rfl⟩ := hold x (List.mem_cons_self ..)
    obtain ⟨hi1, hi2⟩ := innerK_spec hrank ρ G st hst
    obtain ⟨hj1, hj2⟩ := stepK_spec G old (fun c hc => hold c (List.mem_cons_of_mem _ hc)) _ hi1
    rw [stepK_cons]
    refine ⟨hj1, fun c => ?_⟩
    rw [hj2, hi2]
    constructor
    · rintro ((h | ⟨γ, hγ, rfl⟩) | ⟨ρ', hρ', γ, hγ, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨ρ, List.mem_cons_self .., γ, hγ, rfl⟩
      · exact Or.inr ⟨ρ', List.mem_cons_of_mem _ hρ', γ, hγ, rfl⟩
    · rintro (h | ⟨ρ', hρ', γ, hγ, rfl⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hρ' with h | h
        · rw [P.code_inj (by norm_num) h]
          exact Or.inl (Or.inr ⟨γ, hγ, rfl⟩)
        · exact Or.inr ⟨ρ', h, γ, hγ, rfl⟩

theorem mem_stepL {R : Type*} [Mul R] [DecidableEq R] (gens L : List R) (y : R) :
    y ∈ stepL gens L ↔ y ∈ L ∨ ∃ x ∈ L, ∃ g ∈ gens, y = x * g := by
  simp only [stepL, List.mem_append, List.mem_dedup, List.mem_filter, List.mem_flatMap,
    List.mem_map, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨⟨x, hx, g, hg, rfl⟩, -⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, g, hg, rfl⟩
  · rintro (h | ⟨x, hx, g, hg, rfl⟩)
    · exact Or.inl h
    · by_cases h : x * g ∈ L
      · exact Or.inl h
      · exact Or.inr ⟨⟨x, hx, g, hg, rfl⟩, h⟩

theorem nodup_stepL {R : Type*} [Mul R] [DecidableEq R] (gens L : List R) (h : L.Nodup) :
    (stepL gens L).Nodup := by
  refine List.nodup_append.2 ⟨h, List.nodup_dedup _, fun a ha b hb => ?_⟩
  rw [List.mem_dedup, List.mem_filter, decide_eq_true_iff] at hb
  rintro rfl
  exact hb.2 ha

theorem one_mem_iterL {R : Type*} [One R] [Mul R] [DecidableEq R] (gens : List R) :
    ∀ n, (1 : R) ∈ iterL gens n
  | 0 => List.mem_singleton_self _
  | n + 1 => (mem_stepL _ _ _).2 (Or.inl (one_mem_iterL gens n))

include hrank in
theorem ballK_spec (G : List P6) : ∀ n,
    Inv (ballK (G.map P.code) n) ∧ (iterL (G.map R6.enc) n).Nodup ∧
      (∀ y ∈ iterL (G.map R6.enc) n, ∃ σ, R6.enc σ = y) ∧
      ∀ σ : P6, P.code σ ∈ (ballK (G.map P.code) n).2 ↔ R6.enc σ ∈ iterL (G.map R6.enc) n
  | 0 => by
    refine ⟨⟨fun c hc => ⟨1, by rw [List.mem_singleton.1 hc]; exact P.code_one.symm⟩,
      List.nodup_singleton _, fun σ => ?_⟩, List.nodup_singleton _, fun y hy => ⟨1, ?_⟩,
      fun σ => ?_⟩
    · change inM (Nat.shiftLeft 1 (rank6 (P.one 6))) (P.code σ) = true ↔ P.code σ ∈ [P.one 6]
      rw [inM_eq, shl1, Nat.testBit_two_pow, decide_eq_true_iff,
        List.mem_singleton, P.code_one]
      exact ⟨fun h => by rw [rank_inj hrank h.symm], fun h => by rw [h]⟩
    · rw [List.mem_singleton.1 hy]
      rfl
    · change P.code σ ∈ [P.one 6] ↔ R6.enc σ ∈ [1]
      rw [List.mem_singleton, List.mem_singleton, P.code_one, P.code_eq_iff (by norm_num),
        ← enc_one]
      exact ⟨fun h => h ▸ rfl, enc_inj⟩
  | n + 1 => by
    obtain ⟨hI, hN, hE, hM⟩ := ballK_spec G n
    obtain ⟨hs1, hs2⟩ := stepK_spec hrank G (ballK (G.map P.code) n).2 hI.1 _ hI
    have hmem : ∀ y, y ∈ iterL (G.map R6.enc) (n + 1) ↔ y ∈ iterL (G.map R6.enc) n ∨
        ∃ x ∈ iterL (G.map R6.enc) n, ∃ g ∈ G.map R6.enc, y = x * g := mem_stepL _ _
    refine ⟨hs1, nodup_stepL _ _ hN, fun y hy => ?_, fun σ => ?_⟩
    · rcases (hmem y).1 hy with h | ⟨x, hx, g, hg, rfl⟩
      · exact hE y h
      · obtain ⟨ρ, rfl⟩ := hE x hx
        obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hg
        exact ⟨ρ * γ, enc_mul ρ γ⟩
    · change P.code σ ∈ (stepK (G.map P.code) (ballK (G.map P.code) n).2
        (ballK (G.map P.code) n)).2 ↔ _
      rw [hs2, hmem, hM]
      constructor
      · rintro (h | ⟨ρ, hρ, γ, hγ, h⟩)
        · exact Or.inl h
        · rw [P.code_inj (by norm_num) h]
          exact Or.inr ⟨_, (hM ρ).1 hρ, _, List.mem_map_of_mem hγ, enc_mul ρ γ⟩
      · rintro (h | ⟨x, hx, g, hg, h⟩)
        · exact Or.inl h
        · obtain ⟨ρ, rfl⟩ := hE x hx
          obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
          rw [← enc_mul] at h
          exact Or.inr ⟨ρ, (hM ρ).2 hx, γ, hγ, by rw [enc_inj h]⟩

include hrank in
theorem length_ballK (G : List P6) (n : ℕ) :
    (ballK (G.map P.code) n).2.length = (iterL (G.map R6.enc) n).length := by
  obtain ⟨hI, hN, hE, hM⟩ := ballK_spec hrank G n
  have hnd : ((iterL (G.map R6.enc) n).map κ).Nodup := by
    refine hN.map_on fun a ha b hb hab => ?_
    obtain ⟨ρ, rfl⟩ := hE a ha
    obtain ⟨ρ', rfl⟩ := hE b hb
    rw [κ_enc, κ_enc] at hab
    rw [P.code_inj (by norm_num) hab]
  have hp := (List.perm_ext_iff_of_nodup hI.2.1 hnd).2 fun c => by
    rw [List.mem_map]
    constructor
    · intro hc
      obtain ⟨ρ, rfl⟩ := hI.1 c hc
      exact ⟨_, (hM ρ).1 hc, κ_enc ρ⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨ρ, rfl⟩ := hE y hy
      rw [κ_enc]
      exact (hM ρ).2 hy
  rw [hp.length_eq, List.length_map]

include hrank in
theorem inM_ballK (G : List P6) (n : ℕ) (σ : P6) :
    inM (ballK (G.map P.code) n).1 (P.code σ) = true ↔ R6.enc σ ∈ iterL (G.map R6.enc) n := by
  obtain ⟨hI, -, -, hM⟩ := ballK_spec hrank G n
  rw [hI.2.2, hM]

include hrank in
theorem closedK_iff (G : List P6) (n : ℕ) :
    closedK (G.map P.code) (ballK (G.map P.code) n) = true ↔
      closedB (G.map R6.enc) (iterL (G.map R6.enc) n) = true := by
  obtain ⟨hI, -, hE, hM⟩ := ballK_spec hrank G n
  rw [closedK, P.allL_iff, closedB, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  simp only [List.all_eq_true, decide_eq_true_iff, List.mem_map]
  constructor
  · intro h
    refine ⟨one_mem_iterL _ n, fun y hy g ⟨γ, hγ, hg⟩ => ?_⟩
    obtain ⟨ρ, rfl⟩ := hE y hy
    have := (P.allL_iff _ _).1 (h _ ((hM ρ).2 hy)) _ (List.mem_map_of_mem hγ)
    rw [P.code_mul (by norm_num), inM_ballK hrank, enc_mul] at this
    rw [← hg]
    exact this
  · rintro ⟨-, h⟩ c hc
    obtain ⟨ρ, rfl⟩ := hI.1 c hc
    rw [P.allL_iff]
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
    rw [P.code_mul (by norm_num), inM_ballK hrank, enc_mul]
    exact h _ ((hM ρ).1 hc) _ ⟨γ, hγ, rfl⟩

include hrank in
theorem conjIn_iff (G : List P6) (n : ℕ) (τ γ : P6) :
    conjIn (R6.enc τ) (iterL (G.map R6.enc) n) (R6.enc γ) = true ↔
      R6.enc (τ * γ * τ⁻¹) ∈ iterL (G.map R6.enc) n := by
  obtain ⟨-, -, hE, -⟩ := ballK_spec hrank G n
  rw [conjIn, List.any_eq_true]
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨ρ, rfl⟩ := hE y hy
    rw [← enc_mul, ← enc_mul] at h
    have h' := enc_inj h
    rw [h', mul_inv_cancel_right]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← enc_mul, ← enc_mul, inv_mul_cancel_right]

include hrank in
theorem s4051k (G0 Ga Gb R : List P6) {n0 na nb m k0 ka kb : ℕ} {C0 Ca Cb CR : List ℕ}
    (h0 : G0.map code = C0) (ha : Ga.map code = Ca) (hb : Gb.map code = Cb)
    (hr : R.map code = CR) (hk : c4051 C0 Ca Cb CR n0 na nb m k0 ka kb = true) :
    let L0 := iterL (G0.map R6.enc) n0
    let La := iterL (Ga.map R6.enc) na
    let Lb := iterL (Gb.map R6.enc) nb
    (L0.length = k0 ∧ La.length = ka ∧ Lb.length = kb ∧ L0.Nodup ∧ La.Nodup ∧ Lb.Nodup)
    ∧ (closedB (G0.map R6.enc) L0 = true ∧ closedB (Ga.map R6.enc) La = true ∧
          closedB (Gb.map R6.enc) Lb = true)
    ∧ (∀ x : P6, Perm.sign x = 1 → R6.enc x ∈ La ∨ R6.enc x ∈ Lb ∨
          ∃ r ∈ R, ∃ d ∈ L0, ∃ e ∈ L0, R6.enc x = d * R6.enc r * e)
    ∧ (∀ x : P6, Perm.sign x = 1 →
          ∀ L ∈ R.map (fun r => iterL ((G0 ++ [r]).map R6.enc) m), R6.enc x ∈ L)
    ∧ (∀ τ : P6, (G0.map R6.enc).all (conjIn (R6.enc τ) L0) = true →
          (Ga.map R6.enc).all (conjIn (R6.enc τ) La) = true ∧
          (Gb.map R6.enc).all (conjIn (R6.enc τ) Lb) = true) := by
  intro L0 La Lb
  subst h0 ha hb hr
  rw [S.code_eq_P] at hk
  simp only [c4051, P.letB_eq, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hk
  rw [P.beq_iff, S.lenL_eq, length_ballK hrank] at k1 k2 k3
  rw [closedK_iff hrank] at k4 k5 k6
  have hn6 : (6 : ℕ) ≤ 32 := by norm_num
  obtain ⟨hI0, hN0, hE0, hM0⟩ := ballK_spec hrank G0 n0
  refine ⟨⟨k1, k2, k3, hN0, (ballK_spec hrank Ga na).2.1, (ballK_spec hrank Gb nb).2.1⟩,
    ⟨k4, k5, k6⟩, ?_, ?_, ?_⟩
  · intro x hx
    have h := (P.allP_iff _).1 k7 x
    rw [P.impB_iff, P.even_code hn6, P.orB_iff, P.orB_iff, inM_ballK hrank, inM_ballK hrank,
      P.anyL_map] at h
    rcases h hx with h | h | ⟨ρ, hρ, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [P.anyL_iff] at h
      obtain ⟨d, hd, h⟩ := h
      obtain ⟨δ, rfl⟩ := hI0.1 d hd
      rw [P.code_inv hn6, P.code_inv hn6, P.code_mul hn6, P.code_mul hn6, inM_ballK hrank] at h
      refine Or.inr (Or.inr ⟨ρ, hρ, _, (hM0 δ).1 hd, _, h, ?_⟩)
      rw [← enc_mul, ← enc_mul]
      congr 1
      group
  · intro x hx L hL
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hL
    have h := (P.allL_map _ _).1 k8 ρ hρ
    have e : List.append (G0.map P.code) [P.code ρ] = (G0 ++ [ρ]).map P.code := by simp
    rw [e, P.allP_iff] at h
    have h2 := h x
    rw [P.impB_iff, P.even_code hn6, inM_ballK hrank] at h2
    exact h2 hx
  · intro τ hτ
    have h := (P.allP_iff _).1 k9 τ
    rw [P.impB_iff, P.andB_iff, P.allL_map, P.allL_map, P.allL_map] at h
    simp only [P.conj_code hn6, inM_ballK hrank] at h
    simp only [List.all_eq_true, List.forall_mem_map] at hτ ⊢
    obtain ⟨ha', hb'⟩ := h fun g hg => (conjIn_iff hrank G0 n0 τ g).1 (hτ g hg)
    exact ⟨fun g hg => (conjIn_iff hrank Ga na τ g).2 (ha' g hg),
      fun g hg => (conjIn_iff hrank Gb nb τ g).2 (hb' g hg)⟩

end CFSG.KC.LQT.X6

end
