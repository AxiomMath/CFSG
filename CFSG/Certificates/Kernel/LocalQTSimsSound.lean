module

public import CFSG.Certificates.Kernel.LocalQTTleTSound
public import CFSG.Certificates.Kernel.LocalQTContainsCSound
import all CFSG.Certificates.Kernel.LocalQTChainGSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

@[expose] noncomputable def simsGo (n : ℕ) (S : List ℕ) : List Lvl → List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun prev => P.allL S fun s => P.impB (P.allL prev fun b => Nat.beq (P.img s b) b)
      (Nat.beq s (P.one n)))
    (fun lv C' ih prev => CFSG.KC.Ord.andB
      (P.allL S fun s => P.impB (P.allL prev fun b => Nat.beq (P.img s b) b)
        (P.allL (filtL lv.2.1 fun u => CFSG.KC.Ord.notB (Nat.beq u 0)) fun u =>
          inC n (List.cons lv C') (chainF (List.cons lv C')) (P.mul n s u)))
      (ih (List.cons lv.1 prev)))

theorem simsK_eq (n : ℕ) (C : List Lvl) (S : List ℕ) :
    CFSG.KC.LQT.PH.simsK n C S = simsGo n S C [] := rfl

abbrev Gen (n : ℕ) (S : List ℕ) (prev : List ℕ) : Set (Perm (Fin n)) :=
  {σ | P.code σ ∈ S ∧ ∀ b ∈ prev, P.img (P.code σ) b = b}

theorem memU {U : List ℕ} {j : ℕ} (e : getK U j ≠ 0) :
    getK U j ∈ filtL U fun u => CFSG.KC.Ord.notB (Nat.beq u 0) := by
  rw [filtL_eq', List.mem_filter]
  refine ⟨?_, P.notB_iff.2 fun h0 => e (P.beq_iff.1 h0)⟩
  rw [getK_getD'] at e ⊢
  by_cases hjl : j < U.length
  · rw [List.getD_eq_getElem _ _ hjl]
    exact List.getElem_mem hjl
  · rw [List.getD_eq_default _ _ (by omega)] at e
    exact absurd rfl e

theorem inv_pow_closed {X : Perm (Fin n) → Prop} {x : Perm (Fin n)}
    (h : ∀ σ, X σ → X (x * σ)) : ∀ σ, X σ → X (x⁻¹ * σ) := by
  intro σ hσ
  have hpow : ∀ m : ℕ, X (x ^ m * σ) := by
    intro m
    induction m with
    | zero => rwa [pow_zero, one_mul]
    | succ m ihm =>
      rw [pow_succ', mul_assoc]
      exact h _ ihm
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x),
      pow_orderOf_eq_one]
  rw [e]
  exact hpow _

theorem sims_sound (hn : n ≤ 32) (S : List ℕ) : ∀ {prev : List ℕ} {C : List Lvl},
    ChainP n prev C → simsGo n S C prev = true →
    (∀ lv ∈ C, ∀ j < n, getK lv.2.1 j ≠ 0 → getK lv.2.1 j ∈ S) →
    ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure (Gen n S prev)
  | prev, [], _, h, _, σ => by
    change P.allL S (fun s => P.impB (P.allL prev fun b => Nat.beq (P.img s b) b)
      (Nat.beq s (P.one n))) = true at h
    rw [P.allL_iff] at h
    have hbot : Subgroup.closure (Gen n S prev) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro τ ⟨hτS, hτF⟩
      have := h _ hτS
      rw [P.impB_iff, P.allL_iff, P.beq_iff] at this
      have e := this fun b hb => P.beq_iff.2 (hτF b hb)
      rw [P.code_one] at e
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      exact P.code_inj hn e
    rw [hbot, Subgroup.mem_bot]
    change (sift n [] (P.code σ)).isSome = true ↔ _
    simp only [sift]
    rw [P.code_one]
    by_cases e : σ = 1
    · subst e
      simp
    · rw [if_neg fun h => e (P.code_inj hn h)]
      simp [e]
  | prev, lv :: C, hC, h, hR, σ => by
    change CFSG.KC.Ord.andB (P.allL S fun s => P.impB
        (P.allL prev fun b => Nat.beq (P.img s b) b)
        (P.allL (filtL lv.2.1 fun u => CFSG.KC.Ord.notB (Nat.beq u 0)) fun u =>
          inC n (lv :: C) (chainF (lv :: C)) (P.mul n s u)))
      (simsGo n S C (lv.1 :: prev)) = true at h
    rw [P.andB_iff, P.allL_iff] at h
    obtain ⟨htest, hrest⟩ := h
    have ih := sims_sound hn S hC.2 hrest fun l hl => hR l (List.mem_cons_of_mem _ hl)
    have hCl := chainP_lvOK hC
    have hsub : Subgroup.closure (Gen n S (lv.1 :: prev)) ≤ Subgroup.closure (Gen n S prev) :=
      Subgroup.closure_mono fun τ hτ => ⟨hτ.1, fun b hb => hτ.2 b (List.mem_cons_of_mem _ hb)⟩
    have fwd : ∀ σ, InC n (lv :: C) σ → σ ∈ Subgroup.closure (Gen n S prev) := by
      intro σ hσ
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
      obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code hn hC.1.1 σ hk
      have hτH : τ ∈ Subgroup.closure (Gen n S prev) := Subgroup.subset_closure
        ⟨by rw [hτ]; exact hR lv List.mem_cons_self j hj e,
          fun b hb => by rw [hτ]; exact (hC.1.2.1 j hj e).1 b hb⟩
      have hr : τ⁻¹ * σ ∈ Subgroup.closure (Gen n S prev) :=
        hsub ((ih _).1 (by rw [InC, h']; rfl))
      have := Subgroup.mul_mem _ hτH hr
      rwa [mul_inv_cancel_left] at this
    have gstep : ∀ s ∈ Gen n S prev, ∀ σ, InC n (lv :: C) σ → InC n (lv :: C) (s * σ) := by
      rintro s ⟨hsS, hsF⟩ σ hσ
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
      obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code hn hC.1.1 σ hk
      have ht := htest _ hsS
      rw [P.impB_iff, P.allL_iff] at ht
      have ht2 := ht fun b hb => P.beq_iff.2 (hsF b hb)
      rw [P.allL_iff] at ht2
      have hsτ := ht2 _ (memU e)
      rw [← hτ, P.code_mul hn, inC_iff hn hCl] at hsτ
      obtain ⟨k2, hk2⟩ := Option.isSome_iff_exists.1 hsτ
      obtain ⟨j2, hj2, τ2, hτ2, e2, -, k2', h2', -⟩ := sift_cons_code hn hC.1.1 (s * τ) hk2
      have hρ : InC n C (τ2⁻¹ * (s * τ) * (τ⁻¹ * σ)) := (ih _).2
        (Subgroup.mul_mem _ ((ih _).1 (by rw [InC, h2']; rfl)) ((ih _).1 (by rw [InC, h']; rfl)))
      obtain ⟨k3, hk3⟩ := Option.isSome_iff_exists.1 hρ
      have := sift_mul_rep hn hC hj2 τ2 hτ2 e2 hk3
      have eq : τ2 * (τ2⁻¹ * (s * τ) * (τ⁻¹ * σ)) = s * σ := by group
      rw [eq] at this
      rw [InC, this]
      rfl
    have lclosed : ∀ g ∈ Subgroup.closure (Gen n S prev), ∀ σ, InC n (lv :: C) σ →
        InC n (lv :: C) (g * σ) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => exact gstep x hx
      | one =>
        intro σ hσ
        rwa [one_mul]
      | mul x y _ _ ihx ihy =>
        intro σ hσ
        rw [mul_assoc]
        exact ihx _ (ihy σ hσ)
      | inv x _ ihx => exact inv_pow_closed ihx
    refine ⟨fwd σ, fun hσH => ?_⟩
    obtain ⟨σ0, h0⟩ := exists_sift hn hC 0 (chainF_pos hC)
    have hσ0 : InC n (lv :: C) σ0 := by rw [InC, h0]; rfl
    have := lclosed (σ * σ0⁻¹) (Subgroup.mul_mem _ hσH (Subgroup.inv_mem _ (fwd σ0 hσ0))) σ0 hσ0
    rwa [inv_mul_cancel_right] at this

theorem simsGrp (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n)))
    (hs : CFSG.KC.LQT.PH.simsK n C (List.append (G.map P.code) (CFSG.KC.LQT.PH.allReps C)) =
      true)
    (hw : ∀ σ, InC n C σ → ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.prod = σ) :
    ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G} := by
  have hCP := chainP_of_ok hok hI
  have hR : ∀ lv ∈ C, ∀ j < n, getK lv.2.1 j ≠ 0 →
      getK lv.2.1 j ∈ List.append (G.map P.code) (CFSG.KC.LQT.PH.allReps C) := by
    intro lv hlv j _ e
    refine List.mem_append_right _ ?_
    unfold CFSG.KC.LQT.PH.allReps
    rw [List.mem_flatten]
    exact ⟨_, List.mem_map_of_mem hlv, memU e⟩
  have hS := sims_sound hn _ hCP (by rw [← simsK_eq]; exact hs) hR
  intro σ
  constructor
  · intro hσ
    obtain ⟨l, hl, rfl⟩ := hw σ hσ
    clear hσ
    induction l with
    | nil => exact Subgroup.one_mem _
    | cons a l ih =>
      rw [List.prod_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (hl a List.mem_cons_self))
        (ih fun g hg' => hl g (List.mem_cons_of_mem _ hg'))
  · intro hσ
    refine (hS σ).2 (Subgroup.closure_mono (fun g hg => ?_) hσ)
    exact ⟨List.mem_append_left _ (List.mem_map_of_mem hg), fun b hb => absurd hb List.not_mem_nil⟩

theorem grp_spec (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) (d : ℕ)
    (h1 : ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G})
    (h2 : ∀ σ, InC n C σ → ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ d ∧
      l.prod = σ) :
    (∀ r, r ∈ bfsSet (G.map RN.enc) d ↔ ∃ σ, InC n C σ ∧ RN.enc σ = r) ∧
      (bfsSet (G.map RN.enc) d).size = chainF C ∧
      closedH (G.map RN.enc) (bfsSet (G.map RN.enc) d) = true := by
  have hmem : ∀ r, r ∈ bfsSet (G.map RN.enc) d ↔ ∃ σ, InC n C σ ∧ RN.enc σ = r := by
    intro r
    constructor
    · intro hr
      obtain ⟨σ, hσ, rfl⟩ := bfsSet_sound (rawIsEnc n) G d r hr
      exact ⟨σ, (h1 σ).2 hσ, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨l, hl, hlen, rfl⟩ := h2 σ hσ
      exact mem_bfsSet_prod RN.enc_mul RN.enc_one G d l hl hlen
  refine ⟨hmem, ?_, closedH_of_grp G d (InC n C) hmem ((h1 1).2 (Subgroup.one_mem _))
    fun σ hσ g hg => (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) (Subgroup.subset_closure hg))⟩
  have hY : ∀ x, x ∈ Subgroup.closure {g | g ∈ G} ↔
      RN.enc x ∈ (bfsSet (G.map RN.enc) d).toList := by
    intro x
    rw [Std.HashSet.mem_toList, hmem, ← h1]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨σ, hσ, e⟩ => (RN.enc_inj e) ▸ hσ⟩
  have := card_of_list RN.enc_inj (Subgroup.closure {g | g ∈ G}) _ (toList_nodup _) hY
    (fun r hr => ⟨_, ((hmem r).1 (Std.HashSet.mem_toList.1 hr)).choose_spec.2⟩)
  rw [Std.HashSet.length_toList] at this
  rw [← this, ← card_inC hn hok hI]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (h1 σ).symm)

theorem grpS_sound (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h : CFSG.KC.LQT.PH.grpS n C (chainF C) (G.map P.code) W d = true) :
    (∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G}) ∧
      ∀ σ, InC n C σ → ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ d ∧
        l.prod = σ := by
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  unfold CFSG.KC.LQT.PH.grpS at h
  rw [P.andB_iff, P.andB_iff] at h
  obtain ⟨-, hw, hs⟩ := h
  rw [wordsC_eq] at hw
  have hwords := words_of_inC hn G C W d hw hC
  exact ⟨simsGrp hn hok hI G hs fun σ hσ =>
    let ⟨l, hl, _, e⟩ := hwords σ hσ; ⟨l, hl, e⟩, hwords⟩

theorem grpT_sound (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) {W : List (List (List ℕ))} {k L d : ℕ}
    {T : List (List ℕ)} (h : grpT n C (chainF C) (G.map P.code) W k T L d = true) :
    (∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G}) ∧
      ∀ σ, InC n C σ → ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ d ∧
        l.prod = σ := by
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  unfold grpT at h
  rw [P.andB_iff, P.andB_iff, wordsT_eq] at h
  obtain ⟨-, hw, hs⟩ := h
  have hwords := words_of_inCT hn G T L C W d k hw hC
  exact ⟨simsGrp hn hok hI G hs fun σ hσ =>
    let ⟨l, hl, _, e⟩ := hwords σ hσ; ⟨l, hl, e⟩, hwords⟩

end CFSG.KC.LQT.CM

end
