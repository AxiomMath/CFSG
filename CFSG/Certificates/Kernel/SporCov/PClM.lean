module

public import Certificates.Data.Kernel.SporCov.PClM
public import CFSG.Certificates.Kernel.SporCov.PCl

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape

variable {G : Type} [Group G] {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G}

namespace Model

variable (hM : Model L E ev)
include hM

theorem generating_of_pclM [Finite G] {p : ℕ} (hp : p.Prime) {gs : List (List ℕ)} {m : ℕ}
    (hS₀ : IsPGroup p (Subgroup.closure {x : G | ∃ j < m, x = ev (nthW gs j)}))
    (hgs : chA L gs = true) {t : List ℕ} (ht : chW L t = true)
    {M Y H Yc : List (List ℕ)} {K : List ℕ} {nL nE : ℕ}
    (hH : pgHm E L gs m M nL Y nE = true) (hE : ∀ e < nE, pgEm E L t H Y Yc M m e = true)
    (hL : ∀ j < nL, pgLm E M Y K m nE j = true) {R C : List (List ℕ)} {nR : ℕ}
    (hs : stH L R nR = true) (hst : ∀ k < nR, stOK E M C R k = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) :
    ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSS⟩ := hS₀.exists_le_sylow
  set S₀ := Subgroup.closure {x : G | ∃ j < m, x = ev (nthW gs j)}
  unfold pgHm at hH
  simp only [Bool.and_eq_true, allLt_iff] at hH
  obtain ⟨⟨⟨⟨hM2, hY2⟩, hMc⟩, hYc⟩, hg⟩ := hH
  have hMl := (lenLe_iff _ _).1 hM2
  have oM := chW_nthW hMc
  have oY := chW_nthW hYc
  have hinv : ∀ j < nL, ev (nthW M (2 * j + 1)) = (ev (nthW M (2 * j)))⁻¹ := by
    intro j hj
    have h := hL j hj
    unfold pgLm at h
    rw [Bool.and_eq_true] at h
    have f := hM.eq (chW_append_of (oM _) (oM _)) (chW_nil L) h.1
    rw [hM.append, hM.nil, mul_eq_one_iff_eq_inv] at f
    exact f
  have heven : ∀ j < m, ev (nthW M (2 * j)) ∈ S₀ := by
    intro j hj
    rw [hM.eq (oM _) (chW_nthW hgs j) (hg j hj)]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hlow : ∀ k < 2 * m, ev (nthW M k) ∈ S₀ := by
    intro k hk
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact heven j (by omega)
    · by_cases hj : j < nL
      · rw [hinv j hj]
        exact S₀.inv_mem (heven j (by omega))
      · rw [nthW_ge M _ (by omega), hM.nil]
        exact S₀.one_mem
  have hent : ∀ e < nE, ev (nthW Y e) ∈ (S : Subgroup G) ∧
      (ev (nthW H e))⁻¹ * ev t * ev (nthW H e) = ev (nthW Y e) := by
    intro e he
    have h := hE e he
    unfold pgEm at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨oH, hc⟩, hcodes⟩, hy⟩ := h
    refine ⟨hSS ?_, ?_⟩
    · rw [hM.eq (oY e) (chW_expC hMc _) hy]
      exact hM.mem_expC_of fun k hk => hlow k (Nat.le_of_ble_eq_true (chW_mem hcodes k hk))
    · rw [mul_assoc, hM.conj ht oH (oY e) hc, ← mul_assoc, inv_mul_cancel, one_mul]
  set T : Set G := {z | ∃ j, j < nL ∧ m ≤ j ∧ z = ev (nthW M (2 * j))}
  have hT : ∀ z ∈ T, ∃ g : G, ∃ y ∈ (S : Subgroup G), g⁻¹ * ev t * g = y ∧
      z ∈ Subgroup.centralizer ({y} : Set G) := by
    rintro z ⟨j, hj, hm, rfl⟩
    have h := hL j hj
    unfold pgLm at h
    have hb : Nat.blt j m = false := Bool.eq_false_iff.2 fun e => by
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
    have hev : ∀ j < nL, ev (nthW M (2 * j)) ∈ U := by
      intro j hj
      by_cases hm : j < m
      · exact Subgroup.subset_closure (Or.inl (hSS (heven j hm)))
      · exact Subgroup.subset_closure (Or.inr ⟨j, hj, by omega, rfl⟩)
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact hev j (by omega)
    · rw [hinv j (by omega)]
      exact U.inv_mem (hev j (by omega))
  have hgen : U = ⊤ := htop U (hM.mem_of_stages hlet hMc hs hst)
  intro y hy
  exact ggSporKRest_generating_of_closure hp S hy T hT hgen

theorem generating_of_pclMOK [Finite G] {p : ℕ} (hp : p.Prime) {gs : List (List ℕ)} {m : ℕ}
    (hS₀ : IsPGroup p (Subgroup.closure {x : G | ∃ j < m, x = ev (nthW gs j)}))
    (hgs : chA L gs = true) {nL nE nR : ℕ} {t : List ℕ} {M Y H Yc C R : List (List ℕ)}
    {K : List ℕ} (h : pclMOK E L gs m nL nE nR t M Y H Yc C R K = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) :
    chW L t = true ∧ ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  unfold pclMOK at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨hH, hE⟩, hL⟩, hs⟩, hst⟩, ht⟩ := h
  exact ⟨ht, hM.generating_of_pclM hp hS₀ hgs ht hH hE hL hs hst htop⟩

end Model

end CFSG.KD.SporCov

end
