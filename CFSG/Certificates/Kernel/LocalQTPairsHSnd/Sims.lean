module

public import CFSG.Certificates.Kernel.LocalQTPairsHSnd.ChainW
public import Certificates.Data.Kernel.LocalQT.PairsH

public section

namespace CFSG.KC.LQT.PHSnd

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.KC.LQT.CM

variable {n : ℕ}

private noncomputable def simsGo (n : ℕ) (S : List ℕ) : List Lvl → List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun prev => P.allL S fun s => P.impB (P.allL prev fun b => Nat.beq (P.img s b) b)
      (Nat.beq s (P.one n)))
    (fun lv C' ih prev => CFSG.KC.Ord.andB
      (P.allL S fun s => P.impB (P.allL prev fun b => Nat.beq (P.img s b) b)
        (P.allL (filtL lv.2.1 fun u => CFSG.KC.Ord.notB (Nat.beq u 0)) fun u =>
          inC n (List.cons lv C') (chainF (List.cons lv C')) (P.mul n s u)))
      (ih (List.cons lv.1 prev)))

private theorem simsK_eq_go (n : ℕ) (C : List Lvl) (S : List ℕ) :
    CFSG.KC.LQT.PH.simsK n C S = simsGo n S C [] := rfl

private abbrev Gen (n : ℕ) (S : List ℕ) (prev : List ℕ) : Set (Perm (Fin n)) :=
  {σ | P.code σ ∈ S ∧ ∀ b ∈ prev, P.img (P.code σ) b = b}

private theorem getK_eq_getD : ∀ (l : List ℕ) (i : ℕ), getK l i = l.getD i 0
  | [], _ => rfl
  | x :: t, i => by
    change Bool.rec (motive := fun _ => ℕ) (getK t (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      have e : Nat.beq (i + 1) 0 = false := rfl
      rw [e]
      dsimp only
      rw [getK_eq_getD t, List.getD_cons_succ]
      rfl

private theorem filtL_eq_filter (l : List ℕ) (f : ℕ → Bool) : filtL l f = l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filtL l f) (x :: filtL l f) (f x) = _
    rw [List.filter_cons, ih]
    cases f x <;> rfl

private theorem mem_rep {U : List ℕ} {j : ℕ} (e : getK U j ≠ 0) :
    getK U j ∈ filtL U fun u => CFSG.KC.Ord.notB (Nat.beq u 0) := by
  rw [filtL_eq_filter, List.mem_filter]
  refine ⟨?_, P.notB_iff.2 fun h0 => e (P.beq_iff.1 h0)⟩
  rw [getK_eq_getD] at e ⊢
  by_cases hjl : j < U.length
  · rw [List.getD_eq_getElem _ _ hjl]
    exact List.getElem_mem hjl
  · rw [List.getD_eq_default _ _ (by omega)] at e
    exact absurd rfl e

private theorem lvW_of_chainW : ∀ {prev : List ℕ} {C : List Lvl}, ChainW n prev C →
    ∀ lv ∈ C, LvW n lv
  | _, [], _ => fun _ h => absurd h List.not_mem_nil
  | _, lv :: C, h => fun l hl => by
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h.1
    · exact lvW_of_chainW h.2.2 l hl

private theorem inv_mul_closed {X : Perm (Fin n) → Prop} {x : Perm (Fin n)}
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

private theorem sims_w (hn : n ≤ 32) (S : List ℕ) : ∀ {prev : List ℕ} {C : List Lvl},
    ChainW n prev C → simsGo n S C prev = true →
    (∀ lv ∈ C, ∀ j < n, getK lv.2.1 j ≠ 0 → getK lv.2.1 j ∈ S) →
    (∀ σ, ¬ InC n C σ) ∨ ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure (Gen n S prev)
  | prev, [], _, h, _ => by
    right
    intro σ
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
  | prev, lv :: C, hC, h, hR => by
    change CFSG.KC.Ord.andB (P.allL S fun s => P.impB
        (P.allL prev fun b => Nat.beq (P.img s b) b)
        (P.allL (filtL lv.2.1 fun u => CFSG.KC.Ord.notB (Nat.beq u 0)) fun u =>
          inC n (lv :: C) (chainF (lv :: C)) (P.mul n s u)))
      (simsGo n S C (lv.1 :: prev)) = true at h
    rw [P.andB_iff, P.allL_iff] at h
    obtain ⟨htest, hrest⟩ := h
    have hCl := lvW_of_chainW hC
    rcases sims_w hn S hC.2.2 hrest fun l hl => hR l (List.mem_cons_of_mem _ hl) with hemp | ih
    · left
      intro σ hσ
      obtain ⟨j, hj, τ, hτ, e, h', -⟩ := inC_cons_w hn hC hσ
      exact hemp _ h'
    · by_cases hne : ∃ σ0, InC n (lv :: C) σ0
      · right
        obtain ⟨σ0, hσ0⟩ := hne
        have hsub : Subgroup.closure (Gen n S (lv.1 :: prev)) ≤ Subgroup.closure (Gen n S prev) :=
          Subgroup.closure_mono fun τ hτ => ⟨hτ.1, fun b hb => hτ.2 b (List.mem_cons_of_mem _ hb)⟩
        have fwd : ∀ σ, InC n (lv :: C) σ → σ ∈ Subgroup.closure (Gen n S prev) := by
          intro σ hσ
          obtain ⟨j, hj, τ, hτ, e, h', -⟩ := inC_cons_w hn hC hσ
          have hτH : τ ∈ Subgroup.closure (Gen n S prev) := Subgroup.subset_closure
            ⟨by rw [hτ]; exact hR lv List.mem_cons_self j hj e,
              fun b hb => by rw [hτ]; exact (hC.2.1 j hj e).1 b hb⟩
          have hr : τ⁻¹ * σ ∈ Subgroup.closure (Gen n S prev) := hsub ((ih _).1 h')
          have := Subgroup.mul_mem _ hτH hr
          rwa [mul_inv_cancel_left] at this
        have gstep : ∀ s ∈ Gen n S prev, ∀ σ, InC n (lv :: C) σ → InC n (lv :: C) (s * σ) := by
          rintro s ⟨hsS, hsF⟩ σ hσ
          obtain ⟨j, hj, τ, hτ, e, h', -⟩ := inC_cons_w hn hC hσ
          have ht := htest _ hsS
          rw [P.impB_iff, P.allL_iff] at ht
          have ht2 := ht fun b hb => P.beq_iff.2 (hsF b hb)
          rw [P.allL_iff] at ht2
          have hsτ := ht2 _ (mem_rep e)
          rw [← hτ, P.code_mul hn, inC_iff_w hn hCl] at hsτ
          obtain ⟨j2, hj2, τ2, hτ2, e2, h2', -⟩ := inC_cons_w hn hC hsτ
          have hρ : InC n C (τ2⁻¹ * (s * τ) * (τ⁻¹ * σ)) :=
            (ih _).2 (Subgroup.mul_mem _ ((ih _).1 h2') ((ih _).1 h'))
          have := inC_rep_mul_w hn hC hj2 hτ2 e2 hρ
          have eq : τ2 * (τ2⁻¹ * (s * τ) * (τ⁻¹ * σ)) = s * σ := by group
          rwa [eq] at this
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
          | inv x _ ihx => exact inv_mul_closed ihx
        refine fun σ => ⟨fwd σ, fun hσH => ?_⟩
        have := lclosed (σ * σ0⁻¹) (Subgroup.mul_mem _ hσH (Subgroup.inv_mem _ (fwd σ0 hσ0)))
          σ0 hσ0
        rwa [inv_mul_cancel_right] at this
      · left
        exact not_exists.1 hne

theorem grpC_of_grpS {n : ℕ} (hn : n ≤ 32) {C : List Lvl} {G : List ℕ} {W : List (List (List ℕ))}
    {d : ℕ} (hC : chainOK n C = true) (hG : CFSG.KC.LQT.P.allL G (CFSG.KC.LQT.P.permK n) = true)
    (h : CFSG.KC.LQT.PH.grpS n C (chainF C) G W d = true) : grpC n C (chainF C) G W d = true := by
  unfold CFSG.KC.LQT.PH.grpS at h
  unfold grpC
  rw [P.andB_iff, P.andB_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · cases C with
    | nil =>
      change P.allL G (fun g => inC 0 [] (chainF []) (P.mul 0 (P.one 0) g)) = true
      exact (P.allL_iff _ _).2 fun g _ => rfl
    | cons lv C' => rfl
  · have hCW := chainW_of_ok hn0 hC
    have hLv := lvW_of_chainW hCW
    have hR : ∀ lv ∈ C, ∀ j < n, getK lv.2.1 j ≠ 0 →
        getK lv.2.1 j ∈ List.append G (CFSG.KC.LQT.PH.allReps C) := by
      intro lv hlv j _ e
      refine List.mem_append_right _ ?_
      unfold CFSG.KC.LQT.PH.allReps
      rw [List.mem_flatten]
      exact ⟨_, List.mem_map_of_mem hlv, mem_rep e⟩
    rcases sims_w hn _ hCW (by rw [← simsK_eq_go]; exact h3) hR with hemp | hgrp
    · exact allChain_complete_w hn hCW _ fun σ hσ => absurd hσ (hemp σ)
    · refine allChain_complete_w hn hCW _ fun σ hσ => ?_
      rw [P.allL_iff]
      intro g hg
      obtain ⟨γ, hγ⟩ := P.exists_of_permK ((P.allL_iff _ _).1 hG g hg)
      have hγS : γ ∈ Gen n (List.append G (CFSG.KC.LQT.PH.allReps C)) [] :=
        ⟨by rw [hγ]; exact List.mem_append_left _ hg, fun b hb => absurd hb List.not_mem_nil⟩
      rw [← hγ, P.code_mul hn, inC_iff_w hn hLv]
      exact (hgrp _).2 (Subgroup.mul_mem _ ((hgrp σ).1 hσ) (Subgroup.subset_closure hγS))

end CFSG.KC.LQT.PHSnd

end
