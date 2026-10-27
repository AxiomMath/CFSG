module

public import Certificates.Data.Kernel.L34QEightK
public import CFSG.Certificates.Kernel.FootePkSound
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

namespace CFSG.Certificates.Kernel.L34QEightK

open CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.FootePk CFSG.Sporadic.Schreier
open CFSG.GH74.KGroups.L34 Certificates.Data.L34QEight CFSG.RankThree.PartTwo.KFacts.L34Max
open CFSG.KS.PK

theorem pkp_prodV (w : List (VP 21)) : pkp (prodV w) = pkpW w := by
  induction w with
  | nil => exact pkp_oneV 21
  | cons a w ih => rw [prodV, List.foldr_cons, ← prodV, pkp_mulV, ih, pkpW_cons]

theorem pkp_n0aV : pkp n0aV = n0a := by
  rw [n0aV, pkp_prodV, gV, pkpW_codesW, n0a, ofPAB, tab_eq]

theorem pkp_n0bV : pkp n0bV = n0b := by
  rw [n0bV, pkp_prodV, gV, pkpW_codesW, n0b, ofPAB, tab_eq]

theorem qV_map : qV.map pkp = qList := by
  simp only [qV, qList, List.map_cons, List.map_nil, pkp_mulV, pkp_powV, pkp_oneV, q1V, q2V,
    pkp_n0aV, pkp_n0bV, tab_eq, q1, q2]

theorem eqV_eq_decide (a b : VP 21) : eqV a b = decide (pkp a = pkp b) :=
  (decide_eq_eqV a b).symm

def IsP (s : Nat) (σ : Equiv.Perm (Fin 21)) : Prop := ∀ i : Fin 21, fd 5 s i = (σ i : Nat)

theorem wd21 : wd 21 = 5 := by decide

theorem isP_vp (v : VP 21) : IsP v.1.1 (pkp v) := by
  intro i
  rw [pkp_apply, wd21]

theorem isP_vp_inv (v : VP 21) : IsP v.1.2 (pkp v)⁻¹ := by
  intro i
  have h : (((pkp v)⁻¹ i : Fin 21) : Nat) = fd (wd 21) v.1.2 i := rfl
  rw [h, wd21]

theorem fdS_eq (x i : Nat) : fdS x i = fd 5 x i := by
  have h : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  rw [fdS, h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, fd]

theorem mulN_eq (s t : Nat) : mulN s t = enc 5 (fun i => fd 5 s (fd 5 t i)) 21 := by
  simp only [mulN, fdS_eq]
  rfl

theorem fd_mulN (s t : Nat) {i : Nat} (hi : i < 21) : fd 5 (mulN s t) i = fd 5 s (fd 5 t i) := by
  rw [mulN_eq]
  exact fd_enc (fun j _ => fd_lt _ _ _) hi

theorem isP_mulN {s t : Nat} {σ τ : Equiv.Perm (Fin 21)} (hs : IsP s σ) (ht : IsP t τ) :
    IsP (mulN s t) (σ * τ) := by
  intro i
  rw [fd_mulN _ _ i.2, ht i, hs (τ i)]
  rfl

theorem fd_oneN {i : Nat} (hi : i < 21) : fd 5 oneN i = i :=
  fd_enc (fun j hj => by norm_num; omega) hi

theorem isP_oneN : IsP oneN 1 := fun i => fd_oneN i.2

theorem eq_one_of {s : Nat} {σ : Equiv.Perm (Fin 21)} (hs : IsP s σ) (h : (s == oneN) = true) :
    σ = 1 := by
  rw [beq_iff_eq] at h
  ext i
  rw [← hs i, h, fd_oneN i.2]
  rfl

theorem orderIs_three {σ : Equiv.Perm (Fin 21)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    orderIs σ 3 = true := by
  rw [orderIs_iff _ (by norm_num)]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 h1

theorem orderIs_false {g : Equiv.Perm (Fin 21)} {m : Nat} (h : g ^ m ≠ 1) :
    orderIs g m = false := by
  simp [orderIs, h]

def IsF (f : Nat → Nat) (σ : Equiv.Perm (Fin 21)) : Prop := ∀ i : Fin 21, f i = (σ i : Nat)

theorem isF_of_isP {s : Nat} {σ : Equiv.Perm (Fin 21)} (hs : IsP s σ) : IsF (fdS s) σ := by
  intro i
  rw [fdS_eq]
  exact hs i

theorem isF_comp {f g : Nat → Nat} {σ τ : Equiv.Perm (Fin 21)} (hf : IsF f σ) (hg : IsF g τ) :
    IsF (fun i => f (g i)) (σ * τ) := by
  intro i
  change f (g i) = _
  rw [hg i, hf (τ i)]
  rfl

theorem eq_one_of_all {f : Nat → Nat} {σ : Equiv.Perm (Fin 21)} (hf : IsF f σ)
    (h : ((List.range 21).all fun i => f i == i) = true) : σ = 1 := by
  ext i
  have e := List.all_eq_true.1 h i (List.mem_range.2 i.2)
  rw [beq_iff_eq, hf i] at e
  exact e

theorem ne_one_of_all {f : Nat → Nat} {σ : Equiv.Perm (Fin 21)} (hf : IsF f σ)
    (h : (!(List.range 21).all fun i => f i == i) = true) : σ ≠ 1 := by
  intro hσ
  rw [Bool.not_eq_true', Bool.eq_false_iff] at h
  apply h
  rw [List.all_eq_true]
  intro i hi
  have e := hf ⟨i, List.mem_range.1 hi⟩
  rw [hσ] at e
  rw [beq_iff_eq, e]
  rfl

theorem getD_mem_or {α : Type*} (l : List α) (m : Nat) (d : α) : l.getD m d ∈ l ∨ l.getD m d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[m]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

theorem qN_spec (m : Nat) : ∃ q ∈ qList,
    IsP ((qV.map fun q => (q.1.1, q.1.2)).getD m (oneN, oneN)).1 q ∧
    IsP ((qV.map fun q => (q.1.1, q.1.2)).getD m (oneN, oneN)).2 q⁻¹ := by
  rcases getD_mem_or (qV.map fun q => (q.1.1, q.1.2)) m (oneN, oneN) with h | h
  · obtain ⟨v, hv, he⟩ := List.mem_map.1 h
    rw [← he]
    refine ⟨pkp v, ?_, isP_vp v, isP_vp_inv v⟩
    rw [← qV_map]
    exact List.mem_map_of_mem hv
  · rw [h]
    refine ⟨1, ?_, isP_oneN, ?_⟩
    · exact List.mem_map.2 ⟨1, List.mem_cons_self, tab_eq 1⟩
    · rw [inv_one]
      exact isP_oneN

theorem isF_ap3 {p₁ p₂ p₃ : Nat} {α β γ : Equiv.Perm (Fin 21)} (h₁ : IsP p₁ α) (h₂ : IsP p₂ β)
    (h₃ : IsP p₃ γ) : IsF (ap3 p₁ p₂ p₃) (α * (β * γ)) := by
  have e := isF_comp (isF_of_isP h₁) (isF_comp (isF_of_isP h₂) (isF_of_isP h₃))
  exact e

theorem cjK_spec {x xi : Nat} {σ : Equiv.Perm (Fin 21)} (hx : IsP x σ) (hxi : IsP xi σ⁻¹)
    (k : Nat) {κ : Nat → Nat → Nat → Bool}
    (h : cjK (qV.map fun q => (q.1.1, q.1.2)) x xi k κ = true) :
    ∃ c ∈ conjs qList σ, ∃ p₁ p₂ p₃, IsF (ap3 p₁ p₂ p₃) c ∧ κ p₁ p₂ p₃ = true := by
  unfold cjK at h
  by_cases h0 : k = 0
  · rw [if_pos h0] at h
    have e := isF_ap3 isP_oneN isP_oneN isP_oneN
    rw [one_mul, one_mul] at e
    exact ⟨1, List.mem_cons_self, _, _, _, e, h⟩
  rw [if_neg h0, forceD_eq, forceD_eq] at h
  obtain ⟨q, hq, h1, h2⟩ := qN_spec ((k - 1) / 2)
  by_cases h3 : (k - 1) % 2 = 0
  · rw [if_pos h3] at h
    refine ⟨tab (q * σ * q⁻¹), List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨q, hq, ?_⟩),
      _, _, _, ?_, h⟩
    · exact List.mem_cons_self
    · rw [tab_eq, mul_assoc]
      exact isF_ap3 h1 hx h2
  · rw [if_neg h3] at h
    refine ⟨tab (q * σ⁻¹ * q⁻¹), List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨q, hq, ?_⟩),
      _, _, _, ?_, h⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [tab_eq, mul_assoc]
      exact isF_ap3 h1 hxi h2

theorem tripN_sound {x xi : Nat} {σ : Equiv.Perm (Fin 21)} (hx : IsP x σ) (hxi : IsP xi σ⁻¹)
    {t : Nat × Nat × Nat} (h : tripN (qV.map fun q => (q.1.1, q.1.2)) x xi t = true) :
    wordOK qList σ = true := by
  rw [tripN] at h
  obtain ⟨a, ha, a₁, a₂, a₃, hA, h⟩ := cjK_spec hx hxi t.1 h
  beta_reduce at h
  obtain ⟨b, hb, b₁, b₂, b₃, hB, h⟩ := cjK_spec hx hxi t.2.1 h
  beta_reduce at h
  obtain ⟨c, hc, c₁, c₂, c₃, hC, h⟩ := cjK_spec hx hxi t.2.2 h
  beta_reduce at h
  rw [Bool.and_eq_true] at h
  have hy : IsF (yN x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃) (σ * (a * (b * c))) := by
    have e := isF_comp (isF_of_isP hx) (isF_comp hA (isF_comp hB hC))
    exact e
  rw [← mul_assoc, ← mul_assoc] at hy
  have h3 : (σ * a * b * c) ^ 3 = 1 := by
    have e := eq_one_of_all (isF_comp hy (isF_comp hy hy)) h.1
    rw [← e, pow_succ, pow_succ, pow_one, mul_assoc]
  have h1 := ne_one_of_all hy h.2
  rw [wordOK, List.any_eq_true]
  refine ⟨a, ha, ?_⟩
  rw [List.any_eq_true]
  refine ⟨b, hb, ?_⟩
  rw [List.any_eq_true]
  exact ⟨c, hc, orderIs_three h3 h1⟩

theorem testN_sound {x xi : Nat} {σ : Equiv.Perm (Fin 21)} (hx : IsP x σ) (hxi : IsP xi σ⁻¹)
    (h : testN (qV.map fun q => (q.1.1, q.1.2)) x xi = true) :
    (!(orderIs σ 5 || orderIs σ 7) || wordOK qList σ) = true := by
  rw [testN, forceD_eq, forceD_eq, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h1 | ⟨h5, h7⟩) | h
  · have e := eq_one_of hx h1
    have o5 : orderIs σ 5 = false := by
      rw [Bool.eq_false_iff, ne_eq, orderIs_iff _ (by norm_num), e, orderOf_one]
      omega
    have o7 : orderIs σ 7 = false := by
      rw [Bool.eq_false_iff, ne_eq, orderIs_iff _ (by norm_num), e, orderOf_one]
      omega
    rw [o5, o7]
    rfl
  · have f := isF_of_isP hx
    have f5 : IsF (p5N x) (σ * (σ * (σ * (σ * σ)))) := by
      have e := isF_comp f (isF_comp f (isF_comp f (isF_comp f f)))
      exact e
    have f7 : IsF (p7N x) (σ * (σ * (σ * (σ * (σ * (σ * σ)))))) := by
      have e := isF_comp f (isF_comp f f5)
      exact e
    have e5 := ne_one_of_all f5 h5
    have e7 := ne_one_of_all f7 h7
    have p5 : σ ^ 5 = σ * (σ * (σ * (σ * σ))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have p7 : σ ^ 7 = σ * (σ * (σ * (σ * (σ * (σ * σ))))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← p5] at e5
    rw [← p7] at e7
    rw [orderIs_false e5, orderIs_false e7]
    rfl
  · obtain ⟨t, -, ht⟩ := List.any_eq_true.1 h
    rw [tripN_sound hx hxi ht, Bool.or_true]

theorem qClosed_of_qClosedV (h : qClosedV = true) : qClosed = true := by
  rw [qClosedV, forceL_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hd, hm⟩, hi⟩ := h
  rw [qClosed, ← qV_map, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.nodup_iff_injective_get]
    intro i j hij
    rw [List.all_eq_true] at hd
    have h1 := List.all_eq_true.1 (hd i.1 (List.mem_range.2 (by simpa using i.2))) j.1
      (List.mem_range.2 (by simpa using j.2))
    rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', eqV_eq_decide,
      decide_eq_false_iff_not] at h1
    rcases h1 with h1 | h1
    · exact Fin.ext h1
    · exfalso
      apply h1
      simp only [List.get_eq_getElem, List.getElem_map] at hij
      rw [List.getD_eq_getElem _ _ (by simpa using i.2), List.getD_eq_getElem _ _ (by simpa using j.2)]
      exact hij
  · rw [List.all_eq_true] at hm ⊢
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    obtain ⟨d, hd, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 (hm a' ha') b' hb')
    rw [eqV_eq_decide, decide_eq_true_eq, pkp_mulV] at he
    rw [List.contains_iff_mem, he]
    exact List.mem_map_of_mem hd
  · rw [List.all_eq_true] at hi ⊢
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, he⟩ := List.any_eq_true.1 (hi a' ha')
    rw [eqV_eq_decide, decide_eq_true_eq, pkp_invV] at he
    rw [List.contains_iff_mem, he]
    exact List.mem_map_of_mem hd

theorem isP_prodN (w : List (VP 21)) : IsP (prodN w) (pkpW w) := by
  induction w with
  | nil =>
    rw [prodN, List.foldr_nil, pkpW_nil]
    exact isP_oneN
  | cons a w ih =>
    rw [prodN, List.foldr_cons, ← prodN, stepN, forceD_eq, pkpW_cons]
    exact isP_mulN (isP_vp a) ih

theorem closureCheck_of_blocks (h : ∀ j < ((transL QP21).headD []).length, closureBlock j = true) :
    closureCheck = true := by
  rw [closureCheck]
  apply elemsT_all_of_blocks QP21 (by decide)
  intro j hj
  have hj' := h j hj
  rw [closureBlock, forceL_eq, forceLL_eq, List.all_eq_true] at hj'
  rw [List.all_eq_true]
  intro w hw
  have hi := isP_prodN (invW w)
  rw [pkpW_invW] at hi
  exact testN_sound (isP_prodN w) hi (hj' w hw)

end CFSG.Certificates.Kernel.L34QEightK

end
