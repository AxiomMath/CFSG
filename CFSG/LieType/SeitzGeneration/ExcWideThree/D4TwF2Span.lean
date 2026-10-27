module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain
public import CFSG.Quasithin.Recognition.CertTrialityModel
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxBase
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span

open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain
  CFSG.Quasithin

section Span


noncomputable def transportT {K : Type} [Field K] [Finite K] (h : Nat.card K = 8) :
    K ≃+* GF8 :=
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (GaloisField 2 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h, GaloisField.card 2 3 (by norm_num)]
    norm_num
  (FiniteField.ringEquivOfCardEq hc).trans gf8EquivGaloisField.symm


theorem gf8_aut_frob (τ : GF8 ≃+* GF8) (hτ : τ ≠ 1) :
    (∀ a : GF8, τ a = a ^ 2) ∨ (∀ a : GF8, τ a = a ^ 4) := by
  set x : GF8 := GF8.ofNat' 2 with hxdef
  have hx3 : x ^ 3 = x + 1 := by rw [hxdef]; decide
  have hcub : ∀ y : GF8, y ^ 3 = y + 1 → y = x ∨ y = x ^ 2 ∨ y = x ^ 4 := by
    rw [hxdef]; decide
  have hdec : ∀ a : GF8, ∃ b0 b1 b2 : GF8, (b0 = 0 ∨ b0 = 1) ∧ (b1 = 0 ∨ b1 = 1) ∧
      (b2 = 0 ∨ b2 = 1) ∧ a = b0 + b1 * x + b2 * x ^ 2 := by
    rw [hxdef]; decide
  have hsq : ∀ b0 b1 b2 : GF8, (b0 = 0 ∨ b0 = 1) → (b1 = 0 ∨ b1 = 1) → (b2 = 0 ∨ b2 = 1) →
      (b0 + b1 * x + b2 * x ^ 2) ^ 2 = b0 + b1 * x ^ 2 + b2 * x ^ 4 := by
    rw [hxdef]; decide
  have hq4 : ∀ b0 b1 b2 : GF8, (b0 = 0 ∨ b0 = 1) → (b1 = 0 ∨ b1 = 1) → (b2 = 0 ∨ b2 = 1) →
      (b0 + b1 * x + b2 * x ^ 2) ^ 4 = b0 + b1 * x ^ 4 + b2 * x ^ 8 := by
    rw [hxdef]; decide
  have hτ01 : ∀ b : GF8, (b = 0 ∨ b = 1) → τ b = b := by
    rintro b (rfl | rfl) <;> simp
  have hτform : ∀ a : GF8, ∃ b0 b1 b2 : GF8, (b0 = 0 ∨ b0 = 1) ∧ (b1 = 0 ∨ b1 = 1) ∧
      (b2 = 0 ∨ b2 = 1) ∧ a = b0 + b1 * x + b2 * x ^ 2 ∧
      τ a = b0 + b1 * τ x + b2 * (τ x) ^ 2 := by
    intro a
    obtain ⟨b0, b1, b2, h0, h1, h2, rfl⟩ := hdec a
    refine ⟨b0, b1, b2, h0, h1, h2, rfl, ?_⟩
    rw [map_add, map_add, map_mul, map_mul, map_pow, hτ01 b0 h0, hτ01 b1 h1, hτ01 b2 h2]
  have hτx : (τ x) ^ 3 = τ x + 1 := by
    have := congrArg τ hx3
    simpa [map_pow, map_add, map_one] using this
  rcases hcub _ hτx with h | h | h
  · exfalso
    apply hτ
    ext a
    obtain ⟨b0, b1, b2, h0, h1', h2, rfl, hτa⟩ := hτform a
    rw [hτa, h]
    simp
  · left
    intro a
    obtain ⟨b0, b1, b2, h0, h1', h2, rfl, hτa⟩ := hτform a
    rw [hτa, h, hsq b0 b1 b2 h0 h1' h2]
    ring
  · right
    intro a
    obtain ⟨b0, b1, b2, h0, h1', h2, rfl, hτa⟩ := hτform a
    rw [hτa, h, hq4 b0 b1 b2 h0 h1' h2]
    ring


theorem sigma_gf8 {K : Type} [Field K] [Finite K] (h : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    (∀ a : GF8, (transportT h).symm (a ^ 2) = σ ((transportT h).symm a)) ∨
      (∀ a : GF8, (transportT h).symm (a ^ 4) = σ ((transportT h).symm a)) := by
  set T := transportT h with hT
  have hne : (T.symm.trans (σ.trans T)) ≠ 1 := by
    intro h1
    have hσ1 : σ = 1 := by
      ext k
      have h2 := congrArg (fun e : GF8 ≃+* GF8 => e (T k)) h1
      simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply] at h2
      have h3 : T (σ k) = T k := by simpa using h2
      exact T.injective h3
    rw [hσ1, orderOf_one] at hσ
    norm_num at hσ
  rcases gf8_aut_frob _ hne with h4 | h4
  · left
    intro a
    have := h4 a
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply] at this
    rw [← this]
    simp
  · right
    intro a
    have := h4 a
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply] at this
    rw [← this]
    simp

theorem entries_valid_pos_neg : (∀ n < 4, ∀ k ∈ [1, 2], ∀ e ∈ entries Tag.D4 n k,
      e.1 < 28 ∧ e.2.1 < 28) ∧
    (∀ n < 4, ∀ k ∈ [1, 2], ∀ e ∈ entries Tag.D4 (negI n) k, e.1 < 28 ∧ e.2.1 < 28) := by
  decide +kernel

theorem valid_pos (n : ℕ) (hn : n < 4) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ValidEntries Tag.D4 (entries Tag.D4 n k) := by
  intro e he
  have hd : dim Tag.D4 = 28 := by decide +kernel
  rw [hd]
  exact entries_valid_pos_neg.1 n hn k (by rcases hk with rfl | rfl <;> simp) e he

theorem valid_neg (n : ℕ) (hn : n < 4) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ValidEntries Tag.D4 (entries Tag.D4 (negI n) k) := by
  intro e he
  have hd : dim Tag.D4 = 28 := by decide +kernel
  rw [hd]
  exact entries_valid_pos_neg.2 n hn k (by rcases hk with rfl | rfl <;> simp) e he

theorem valid_neg' (n : ℕ) (hn : n < 4) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ValidEntries Tag.D4 (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image n ⟨n, hn⟩) k) := by
  rw [← negI_eq n hn]
  exact valid_neg n hn k hk

section Gens

variable {K : Type} [Field K] [Finite K]

theorem pcoord_xPar_pos (n : ℕ) (hn : n < 4) (c : K) (v : RootModule Tag.D4 K) (q : ℕ) :
    pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single (⟨n, hn⟩ : Fin Tag.D4.rank) 1) c)
      v) q = xEg n c (fun r => pcoord K v r) q :=
  pcoord_endHom_pos ⟨n, hn⟩ c v q (valid_pos n hn 1 (Or.inl rfl)) (valid_pos n hn 2 (Or.inr rfl))

theorem pcoord_xPar_neg (n : ℕ) (hn : n < 4) (c : K) (v : RootModule Tag.D4 K) (q : ℕ) :
    pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single (⟨n, hn⟩ : Fin Tag.D4.rank) 1) c)
      v) q = yEg n c (fun r => pcoord K v r) q :=
  by
    have h := pcoord_endHom_neg ⟨n, hn⟩ c v q (valid_neg' n hn 1 (Or.inl rfl))
      (valid_neg' n hn 2 (Or.inr rfl))
    rw [h]
    simp only [yEg, negI_eq n hn, Fin.val_mk]

noncomputable def gpos (σ : K ≃+* K) (s : K) : adjointGroup Tag.D4 K :=
  xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) s *
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (σ s) *
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (σ (σ s))

noncomputable def gneg (σ : K ≃+* K) (s : K) : adjointGroup Tag.D4 K :=
  xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) s *
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (σ s) *
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (σ (σ s))

theorem pcoord_gpos (σ : K ≃+* K) (s : K) (u : RootModule Tag.D4 K) (q : ℕ) :
    pcoord K (endHom K (gpos σ s) u) q = tpEg (⇑σ) s (fun r => pcoord K u r) q := by
  have e0 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (Pi.single (nd 0) 1) s) V) r = xEg 0 s (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_pos 0 (by decide) s V r
  have e1 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (Pi.single (nd 1) 1) (σ s)) V) r = xEg 1 (σ s) (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_pos 1 (by decide) (σ s) V r
  have e3 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (Pi.single (nd 3) 1) (σ (σ s))) V) r = xEg 3 (σ (σ s)) (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_pos 3 (by decide) (σ (σ s)) V r
  unfold gpos tpEg
  simp only [map_mul, Module.End.mul_apply]
  rw [e0]
  congr 1
  funext q'
  rw [e1]
  congr 1
  funext r
  rw [e3]

theorem pcoord_gneg (σ : K ≃+* K) (s : K) (u : RootModule Tag.D4 K) (q : ℕ) :
    pcoord K (endHom K (gneg σ s) u) q = tmEg (⇑σ) s (fun r => pcoord K u r) q := by
  have e0 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (-Pi.single (nd 0) 1) s) V) r = yEg 0 s (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_neg 0 (by decide) s V r
  have e1 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (-Pi.single (nd 1) 1) (σ s)) V) r = yEg 1 (σ s) (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_neg 1 (by decide) (σ s) V r
  have e3 : ∀ (V : RootModule Tag.D4 K) (r : ℕ), pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (-Pi.single (nd 3) 1) (σ (σ s))) V) r = yEg 3 (σ (σ s)) (fun t => pcoord K V t) r :=
    fun V r => pcoord_xPar_neg 3 (by decide) (σ (σ s)) V r
  unfold gneg tmEg
  simp only [map_mul, Module.End.mul_apply]
  rw [e0]
  congr 1
  funext q'
  rw [e1]
  congr 1
  funext r
  rw [e3]

theorem gpos_mem {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (s : K) :
    gpos σ s ∈ fixedSubgroup (d4Twist 1 σ) := triple_pos_mem hσ3 s

theorem gneg_mem {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (s : K) :
    gneg σ s ∈ fixedSubgroup (d4Twist 1 σ) := triple_neg_mem hσ3 s

noncomputable def gEl (σ : K ≃+* K) (x x2 : K) : ℕ → adjointGroup Tag.D4 K
  | 0 => xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) 1
  | 1 => xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) 1
  | 2 => gpos σ 1
  | 3 => gneg σ 1
  | 4 => gpos σ x
  | 5 => gneg σ x
  | 6 => gpos σ x2
  | _ => gneg σ x2

theorem gEl_mem {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (x x2 : K) (idx : ℕ) :
    gEl σ x x2 idx ∈ fixedSubgroup (d4Twist 1 σ) := by
  match idx with
  | 0 => exact xPar_e2_mem_fixed hσ3 (map_one σ)
  | 1 => exact xPar_neg_e2_mem_fixed hσ3 (map_one σ)
  | 2 => exact gpos_mem hσ3 1
  | 3 => exact gneg_mem hσ3 1
  | 4 => exact gpos_mem hσ3 x
  | 5 => exact gneg_mem hσ3 x
  | 6 => exact gpos_mem hσ3 x2
  | _ + 7 => exact gneg_mem hσ3 x2

theorem pcoord_gEl {σ : K ≃+* K} (x x2 : K) (idx : ℕ) (u : RootModule Tag.D4 K) (q : ℕ) :
    pcoord K (endHom K (gEl σ x x2 idx) u) q = genR (⇑σ) 1 x x2 idx (fun r => pcoord K u r) q := by
  match idx with
  | 0 => exact pcoord_xPar_pos 2 (by decide) 1 u q
  | 1 => exact pcoord_xPar_neg 2 (by decide) 1 u q
  | 2 => exact pcoord_gpos σ 1 u q
  | 3 => exact pcoord_gneg σ 1 u q
  | 4 => exact pcoord_gpos σ x u q
  | 5 => exact pcoord_gneg σ x u q
  | 6 => exact pcoord_gpos σ x2 u q
  | _ + 7 => exact pcoord_gneg σ x2 u q

end Gens

noncomputable abbrev vTheta (K : Type) [Field K] : RootModule Tag.D4 K := rootVec Tag.D4 K (d4Root 22)

theorem vTheta_eq_posVec (K : Type) [Field K] : vTheta K = posVec Tag.D4 K 26 := by
  unfold vTheta posVec
  simp only [show ¬ (26 < Tag.D4.rank) from by decide, dif_neg, not_false_eq_true]
  rfl

theorem pcoord_vTheta (K : Type) [Field K] (q : ℕ) :
    pcoord K (vTheta K) q = if q = 26 then 1 else 0 := by
  rw [pcoord, vTheta_eq_posVec, posCoord_posVec (by decide)]

@[expose] def validFromB : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | n, st :: rest => decide (st.2 < n) && validFromB (n + 1) rest

def PInv {K : Type} [Field K] [Finite K] (T : K ≃+* GF8) (σ : K ≃+* K)
    (acc : List (ℕ → GF8)) : Prop :=
  ∀ j < acc.length, ∃ r ∈ fixedSubgroup (d4Twist 1 σ),
    (fun q => pcoord K (endHom K r (vTheta K)) q) = fun q => T.symm (acc.getD j eTheta q)

theorem PInv_init {K : Type} [Field K] [Finite K] (T : K ≃+* GF8) (σ : K ≃+* K) :
    PInv T σ [eTheta] := by
  intro j hj
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  refine ⟨1, one_mem _, ?_⟩
  funext q
  rw [map_one, Module.End.one_apply, pcoord_vTheta]
  simp only [eTheta, List.getD_cons_zero]
  by_cases h : q = 26
  · simp [h]
  · simp [h]

theorem PInv_step {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (T : K ≃+* GF8) (φ : GF8 → GF8)
    (hφ : ∀ a : GF8, T.symm (φ a) = σ (T.symm a)) (acc : List (ℕ → GF8)) (pred idx : ℕ)
    (hpred : pred < acc.length) (hinv : PInv T σ acc) :
    PInv T σ (acc ++ [genR φ 1 (GF8.ofNat' 2) (GF8.ofNat' 4) idx (acc.getD pred eTheta)]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j acc.length with hlt | hge
  · obtain ⟨r, hr, hfun⟩ := hinv j hlt
    refine ⟨r, hr, hfun.trans ?_⟩
    funext q
    rw [List.getD_append _ _ _ _ hlt]
  · have hjeq : j = acc.length := by omega
    obtain ⟨rp, hrp, hfunp⟩ := hinv pred hpred
    refine ⟨gEl σ (T.symm (GF8.ofNat' 2)) (T.symm (GF8.ofNat' 4)) idx * rp,
      mul_mem (gEl_mem hσ3 _ _ idx) hrp, ?_⟩
    funext q
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have h0 : j - acc.length = 0 := by omega
    rw [h0, List.getD_cons_zero]
    have key : T.symm (genR φ 1 (GF8.ofNat' 2) (GF8.ofNat' 4) idx (acc.getD pred eTheta) q) =
        genR (⇑σ) 1 (T.symm (GF8.ofNat' 2)) (T.symm (GF8.ofNat' 4)) idx
          (fun r => T.symm (acc.getD pred eTheta r)) q := by
      have h1 := genR_map T.symm.toRingHom φ (⇑σ) (fun a => hφ a) 1 (GF8.ofNat' 2)
        (GF8.ofNat' 4) idx (acc.getD pred eTheta) q
      rw [map_one] at h1
      exact h1
    rw [map_mul, Module.End.mul_apply, pcoord_gEl]
    rw [show (fun r => pcoord K (endHom K rp (vTheta K)) r) =
      fun r => T.symm (acc.getD pred eTheta r) from hfunp]
    rw [key]

theorem PInv_foldl {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (T : K ≃+* GF8) (φ : GF8 → GF8)
    (hφ : ∀ a : GF8, T.symm (φ a) = σ (T.symm a)) :
    ∀ (steps : List (ℕ × ℕ)) (acc : List (ℕ → GF8)) (n : ℕ), acc.length = n →
      validFromB n steps = true → PInv T σ acc →
      PInv T σ (steps.foldl (chainStepG φ) acc)
  | [], acc, n, _, _, h => by simpa using h
  | st :: rest, acc, n, hn, hv, h => by
      simp only [validFromB, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hpred, hrest⟩ := hv
      rw [List.foldl_cons]
      refine PInv_foldl hσ3 T φ hφ rest (chainStepG φ acc st) (n + 1) ?_ hrest ?_
      · simp [chainStepG, hn]
      · exact PInv_step hσ3 T φ hφ acc st.2 st.1 (by omega) h

theorem eq_of_pcoord {K : Type} [Field K] (v w : RootModule Tag.D4 K)
    (h : ∀ q < dim Tag.D4, pcoord K v q = pcoord K w q) : v = w := by
  refine Finsupp.ext fun b => ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  have h' := h p hp
  unfold pcoord posCoord at h'
  simpa [hp] using h'

theorem mem_list_sum {K : Type} [Field K] {M : Type} [AddCommMonoid M] [Module K M]
    (W : Submodule K M) : ∀ l : List M, (∀ x ∈ l, x ∈ W) → l.sum ∈ W
  | [], _ => Submodule.zero_mem W
  | x :: l, h => by
      rw [List.sum_cons]
      exact W.add_mem (h x (by simp)) (mem_list_sum W l (fun y hy => h y (by simp [hy])))

theorem span_top_of_chain {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (T : K ≃+* GF8) (φ : GF8 → GF8)
    (hφ : ∀ a : GF8, T.symm (φ a) = σ (T.symm a))
    (steps : List (ℕ × ℕ)) (cert : List (List GF8))
    (hsteps : validFromB 1 steps = true)
    (hlen : (steps.foldl (chainStepG φ) [eTheta]).length = 28)
    (hcert : ∀ p < 28, ∀ q < 28, (if p = q then (1 : GF8) else 0) =
      ((List.range 28).map fun j => (cert.getD p []).getD j 0 *
        ((steps.foldl (chainStepG φ) [eTheta]).getD j eTheta q)).sum) :
    Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ), x = endHom K r (vTheta K)} = ⊤ := by
  set C := steps.foldl (chainStepG φ) [eTheta] with hC
  have hinv : PInv T σ C := PInv_foldl hσ3 T φ hφ steps [eTheta] 1 rfl hsteps (PInv_init T σ)
  have hex : ∀ j : ℕ, ∃ r : adjointGroup Tag.D4 K, j < 28 →
      (r ∈ fixedSubgroup (d4Twist 1 σ) ∧
        (fun q => pcoord K (endHom K r (vTheta K)) q) = fun q => T.symm (C.getD j eTheta q)) := by
    intro j
    by_cases hj : j < 28
    · obtain ⟨r, hr, he⟩ := hinv j (by rw [hlen]; exact hj)
      exact ⟨r, fun _ => ⟨hr, he⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose rs hrs using hex
  set W := Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ), x = endHom K r (vTheta K)}
    with hW
  have hmem : ∀ j < 28, endHom K (rs j) (vTheta K) ∈ W := fun j hj =>
    Submodule.subset_span ⟨rs j, (hrs j hj).1, rfl⟩
  have hd28 : dim Tag.D4 = 28 := by decide +kernel
  have hposvec : ∀ p < 28, posVec Tag.D4 K p ∈ W := by
    intro p hp
    have hid : posVec Tag.D4 K p =
        ((List.range 28).map fun j => T.symm ((cert.getD p []).getD j 0) •
          endHom K (rs j) (vTheta K)).sum := by
      refine eq_of_pcoord _ _ fun q hq => ?_
      rw [hd28] at hq
      have hdp : p < dim Tag.D4 := by rw [hd28]; exact hp
      show posCoord Tag.D4 K q (posVec Tag.D4 K p) = posCoord Tag.D4 K q _
      rw [posCoord_posVec hdp, map_list_sum]
      have hterm : ∀ j ∈ List.range 28, posCoord Tag.D4 K q
          (T.symm ((cert.getD p []).getD j 0) • endHom K (rs j) (vTheta K)) =
            T.symm ((cert.getD p []).getD j 0) * T.symm (C.getD j eTheta q) := by
        intro j hj
        rw [List.mem_range] at hj
        rw [map_smul, smul_eq_mul]
        congr 1
        exact congrFun (hrs j hj).2 q
      simp only [List.map_map, Function.comp_def]
      rw [List.map_congr_left hterm]
      simp only [← map_mul]
      have hsum : ((List.range 28).map fun a => T.symm ((cert.getD p []).getD a 0 *
          C.getD a eTheta q)).sum = T.symm (((List.range 28).map fun a => (cert.getD p []).getD a 0 *
          C.getD a eTheta q).sum) := by
        rw [map_list_sum, List.map_map]
        rfl
      rw [hsum, ← hcert p hp q hq]
      by_cases h : p = q
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hid]
    refine mem_list_sum W _ fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact W.smul_mem _ (hmem j (List.mem_range.1 hj))
  rw [Submodule.eq_top_iff']
  intro v
  refine Finsupp.induction_linear v (W.zero_mem) (fun f g hf hg => W.add_mem hf hg) ?_
  intro b c
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  have hp28 : p < 28 := by rw [← hd28]; exact hp
  have hsingle : Finsupp.single (posLabel p hp) c = c • posVec Tag.D4 K p := by
    rw [posVec_eq_single hp, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle]
  exact W.smul_mem _ (hposvec p hp28)


theorem validFromB_frob : validFromB 1 stepsFrob = true := by decide +kernel

theorem validFromB_frob2 : validFromB 1 stepsFrob2 = true := by decide +kernel

theorem span_top_K {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (h8 : Nat.card K = 8) (hσ : orderOf σ = 3) :
    Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ), x = endHom K r (vTheta K)} = ⊤ := by
  rcases sigma_gf8 h8 hσ with h | h
  · exact span_top_of_chain hσ3 (transportT h8) frobE h stepsFrob certFrob validFromB_frob
      chainFrob_length certFrob_ok
  · exact span_top_of_chain hσ3 (transportT h8) frob2E h stepsFrob2 certFrob2 validFromB_frob2
      chainFrob2_length certFrob2_ok

end Span

end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span

end
