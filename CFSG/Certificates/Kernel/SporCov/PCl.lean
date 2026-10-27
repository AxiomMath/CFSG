module

public import Certificates.Data.Kernel.SporCov.PCl
public import CFSG.Certificates.Kernel.SporCov.Cover
public import CFSG.Certificates.Kernel.SporCov.P3Cover

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape

variable {G : Type} [Group G] {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G}

theorem allLt_iff (f : ℕ → Bool) : ∀ n, allLt n f = true ↔ ∀ j < n, f j = true
  | 0 => by simp [allLt]
  | n + 1 => by
    change (allLt n f && f n) = true ↔ _
    rw [Bool.and_eq_true, allLt_iff f n]
    constructor
    · rintro ⟨h, hn⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h j hj
      · exact hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

theorem _root_.CFSG.StandardType.SporadicShape.SporKRestGenerating.pow {K : Type} [Group K]
    {p : ℕ} {v : K} (h : SporKRestGenerating p v) (a : ℕ) : SporKRestGenerating p (v ^ a) := by
  intro Y hY hc
  refine h Y hY fun g hg => hc g ?_
  have e : (g⁻¹ * v * g) ^ a = g⁻¹ * v ^ a * g := by
    have := conj_pow (a := g⁻¹) (b := v) (i := a)
    rwa [inv_inv] at this
  rw [← e]
  exact Y.pow_mem hg a

theorem chW_mem {L : ℕ → Bool} : ∀ {w : List ℕ}, chW L w = true → ∀ l ∈ w, L l = true
  | [], _, _, hl => absurd hl List.not_mem_nil
  | c :: w, h, l, hl => by
    rw [chW_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h.1
    · exact chW_mem h.2 l hl

namespace Model

variable (hM : Model L E ev)
include hM

theorem mem_expC_of {S : Subgroup G} {M : List (List ℕ)} :
    ∀ {c : List ℕ}, (∀ k ∈ c, ev (nthW M k) ∈ S) → ev (expC M c) ∈ S
  | [], _ => by
    rw [expC_nil, hM.nil]
    exact S.one_mem
  | k :: c, h => by
    rw [expC_cons, hM.append]
    exact S.mul_mem (mem_expC_of fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
      (h k List.mem_cons_self)

theorem generating_of_pcl [Finite G] {p : ℕ} (hp : p.Prime) {g₁ g₂ t : List ℕ}
    (hS₀ : IsPGroup p (Subgroup.closure ({ev g₁, ev g₂} : Set G)))
    (hg₁ : chW L g₁ = true) (hg₂ : chW L g₂ = true) (ht : chW L t = true)
    {M Y H Yc : List (List ℕ)} {K : List ℕ} {nL nE : ℕ}
    (hH : pgH E L g₁ g₂ M nL Y nE = true) (hE : ∀ e < nE, pgE E L t H Y Yc M e = true)
    (hL : ∀ j < nL, pgL E M Y K nE j = true) {R C : List (List ℕ)} {nR : ℕ}
    (hs : stH L R nR = true) (hst : ∀ k < nR, stOK E M C R k = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) :
    ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSS⟩ := hS₀.exists_le_sylow
  set S₀ := Subgroup.closure ({ev g₁, ev g₂} : Set G)
  unfold pgH at hH
  simp only [Bool.and_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨hM2, hY2⟩, hMc⟩, hYc⟩, e₁⟩, e₂⟩ := hH
  have hMl := (lenLe_iff _ _).1 hM2
  have oM := chW_nthW hMc
  have oY := chW_nthW hYc
  have hinv : ∀ j < nL, ev (nthW M (2 * j + 1)) = (ev (nthW M (2 * j)))⁻¹ := by
    intro j hj
    have h := hL j hj
    unfold pgL at h
    rw [Bool.and_eq_true] at h
    have f := hM.eq (chW_append_of (oM _) (oM _)) (chW_nil L) h.1
    rw [hM.append, hM.nil, mul_eq_one_iff_eq_inv] at f
    exact f
  have hlow : ∀ k < 4, ev (nthW M k) ∈ S₀ := by
    have h0 : ev (nthW M 0) ∈ S₀ := by
      rw [hM.eq (oM 0) hg₁ e₁]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 : ev (nthW M 2) ∈ S₀ := by
      rw [hM.eq (oM 2) hg₂ e₂]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    intro k hk
    by_cases hkn : k < 2 * nL
    · interval_cases k
      · exact h0
      · rw [hinv 0 (by omega)]
        exact S₀.inv_mem h0
      · exact h2
      · rw [hinv 1 (by omega)]
        exact S₀.inv_mem h2
    · rw [nthW_ge M k (by omega), hM.nil]
      exact S₀.one_mem
  have hent : ∀ e < nE, ev (nthW Y e) ∈ (S : Subgroup G) ∧
      (ev (nthW H e))⁻¹ * ev t * ev (nthW H e) = ev (nthW Y e) := by
    intro e he
    have h := hE e he
    unfold pgE at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨oH, hc⟩, hcodes⟩, hy⟩ := h
    refine ⟨hSS ?_, ?_⟩
    · rw [hM.eq (oY e) (chW_expC hMc _) hy]
      exact hM.mem_expC_of fun k hk => hlow k (Nat.le_of_ble_eq_true (chW_mem hcodes k hk))
    · rw [mul_assoc, hM.conj ht oH (oY e) hc, ← mul_assoc, inv_mul_cancel, one_mul]
  set T : Set G := {z | ∃ j, j < nL ∧ 2 ≤ j ∧ z = ev (nthW M (2 * j))}
  have hT : ∀ z ∈ T, ∃ g : G, ∃ y ∈ (S : Subgroup G), g⁻¹ * ev t * g = y ∧
      z ∈ Subgroup.centralizer ({y} : Set G) := by
    rintro z ⟨j, hj, h2, rfl⟩
    have h := hL j hj
    unfold pgL at h
    have hb : Nat.blt j 2 = false := Bool.eq_false_iff.2 fun e => by
      have := Nat.le_of_ble_eq_true e
      omega
    rw [hb, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨-, hK, hc⟩ := h
    obtain ⟨hyS, hy⟩ := hent _ (Nat.le_of_ble_eq_true hK)
    exact ⟨_, _, hyS, hy,
      Subgroup.mem_centralizer_singleton_iff.2 (hM.comm (oM _) (oY _) hc)⟩
  set U := Subgroup.closure ((S : Set G) ∪ T)
  have hlet : ∀ k, ev (nthW M k) ∈ U := by
    intro k
    by_cases hk : k < 2 * nL
    swap
    · rw [nthW_ge M k (by omega), hM.nil]
      exact U.one_mem
    have heven : ∀ j < nL, ev (nthW M (2 * j)) ∈ U := by
      intro j hj
      by_cases h2 : j < 2
      · exact Subgroup.subset_closure (Or.inl (hSS (hlow _ (by omega))))
      · exact Subgroup.subset_closure (Or.inr ⟨j, hj, by omega, rfl⟩)
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact heven j (by omega)
    · rw [hinv j (by omega)]
      exact U.inv_mem (heven j (by omega))
  have hgen : U = ⊤ := htop U (hM.mem_of_stages hlet hMc hs hst)
  intro y hy
  exact ggSporKRest_generating_of_closure hp S hy T hT hgen

theorem generating_of_pclOK [Finite G] {p : ℕ} (hp : p.Prime) {g₁ g₂ t : List ℕ}
    (hS₀ : IsPGroup p (Subgroup.closure ({ev g₁, ev g₂} : Set G)))
    (hg₁ : chW L g₁ = true) (hg₂ : chW L g₂ = true) {nL nE nR : ℕ}
    {M Y H Yc C R : List (List ℕ)} {K : List ℕ}
    (h : pclOK E L nL nE nR g₁ g₂ t M Y H Yc C R K = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) :
    chW L t = true ∧ ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  unfold pclOK at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨hH, hE⟩, hL⟩, hs⟩, hst⟩, ht⟩ := h
  exact ⟨ht, hM.generating_of_pcl hp hS₀ hg₁ hg₂ ht hH hE hL hs hst htop⟩

theorem cover_of_p3c [Finite G] {p : ℕ} (hp : p.Prime) (hval : (Nat.card G).factorization p = 3)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {e₁ e₂ nL nE nR : ℕ}
    {g₁ g₂ z t gz : List ℕ} {M Y H Yc C R : List (List ℕ)} {K : List ℕ}
    (h : p3cOK E L p e₁ e₂ nL nE nR g₁ g₂ z t gz M Y H Yc C R K = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) : SporKRestCover p G := by
  unfold p3cOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h3, hpcl⟩, ogz⟩, hcj⟩ := h
  obtain ⟨o₁, o₂, oz, -⟩ := hM.p3OK_facts h3
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK hp (hM.p3Rel h3).isPGroup o₁ o₂ hpcl htop
  exact hM.cover_of_p3_center hp hval hc h3 fun y hy =>
    hgen y ((isConj_of_conj (hM.conj ot ogz oz hcj)).trans hy)

theorem cover_of_p3l [Finite G] {p : ℕ} (hp : p.Prime) (hval : (Nat.card G).factorization p = 3)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {e₁ e₂ nL nE nR : ℕ}
    {g₁ g₂ z t : List ℕ} {M Y H Yc C R : List (List ℕ)} {K A : List ℕ} {W : List (List ℕ)}
    (h : p3lOK E L p e₁ e₂ nL nE nR g₁ g₂ z t M Y H Yc C R K A W = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) : SporKRestCover p G := by
  unfold p3lOK at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨h3, hpcl⟩, hl⟩ := h
  obtain ⟨o₁, o₂, oz, hne, -⟩ := hM.p3OK_facts h3
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK hp (hM.p3Rel h3).isPGroup o₁ o₂ hpcl htop
  have hline : ∀ i ≤ p, ∀ y, IsConj (ev (lnW g₁ g₂ p i)) y → SporKRestGenerating p y := by
    intro i hi y hy
    obtain ⟨oW, hcj⟩ := hl i (by omega)
    have oln : chW L (lnW g₁ g₂ p i) = true := by
      unfold lnW
      cases Nat.blt i p
      · exact o₂
      · exact chW_append_of (chW_repW o₂ i) o₁
    have hconj := isConj_of_conj (hM.conj (chW_repW ot _) oW oln hcj)
    rw [hM.repW_eq] at hconj
    obtain ⟨c, rfl⟩ := isConj_iff.1 (hconj.trans hy)
    rw [← conj_pow]
    exact (hgen _ (isConj_iff.2 ⟨c, rfl⟩)).pow _
  have hlt : ∀ i < p, ev (lnW g₁ g₂ p i) = ev g₁ * ev g₂ ^ i := by
    intro i hi
    have e : Nat.blt i p = true := by simp [hi]
    unfold lnW
    rw [e, cond_true, hM.append, hM.repW_eq]
  have hp' : ev (lnW g₁ g₂ p p) = ev g₂ := by
    have e : Nat.blt p p = false :=
      Bool.eq_false_iff.2 fun h => absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self p)
    unfold lnW
    rw [e, cond_false]
  refine (hM.p3Rel h3).sporKRest_cover hp hval (hM.ne_one hc oz hne) (Or.inr ⟨?_, ?_⟩)
  · intro y hy
    rw [← hp'] at hy
    exact hline p le_rfl y hy
  · intro i hi y hy
    rw [← hlt i hi] at hy
    exact hline i hi.le y hy

end Model

end CFSG.KD.SporCov

end
