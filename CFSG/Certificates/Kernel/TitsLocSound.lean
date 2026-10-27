module

public import Certificates.Data.Kernel.TitsLocK
public import CFSG.Certificates.Kernel.TwoF4LieSound
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KC.TitsLocSound

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsLocK CFSG.KC.TwoF4LieSound
  CFSG.KC.EnumSound

@[expose] def a1Cnt (w : List ℕ) : ℕ := w.countP fun c => decide (c / 2 = 2)

theorem shiftRight_one (c : ℕ) : Nat.shiftRight c 1 = c / 2 := by
  have h := Nat.shiftRight_eq_div_pow c 1
  rw [pow_one] at h
  exact h

theorem wordDe_sound : ∀ (w : List ℕ) (e : Bool), wordDe w e = true →
    CodesOK w ∧ (e = true ↔ Even (a1Cnt w))
  | [], e, h => by
    have he : e = true := h
    exact ⟨fun c hc => absurd hc (List.not_mem_nil), by simp [a1Cnt, he]⟩
  | c :: w, e, h => by
    change bAnd(Nat.ble 2 c, bAnd(Nat.blt c 10, wordDe w
      (bIf(Nat.beq (Nat.shiftRight c 1) 2, bIf(e, false, true), e)))) = true at h
    simp only [bAnd_eq', Bool.and_eq_true] at h
    obtain ⟨h2, h10, hw⟩ := h
    have hc2 : 2 ≤ c := Nat.le_of_ble_eq_true h2
    have hc10 : c + 1 ≤ 10 := Nat.le_of_ble_eq_true h10
    have codes (hw' : CodesOK w) : CodesOK (c :: w) := fun c' hc' => by
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨hc2, by omega⟩
      · exact hw' c' hc'
    cases hb : Nat.beq (Nat.shiftRight c 1) 2
    · rw [hb] at hw
      have ih := wordDe_sound w e hw
      have hne : ¬ c / 2 = 2 := by
        intro h'
        rw [shiftRight_one, h'] at hb
        exact absurd hb (by decide)
      have hcnt : a1Cnt (c :: w) = a1Cnt w := by simp [a1Cnt, List.countP_cons, hne]
      exact ⟨codes ih.1, by rw [hcnt]; exact ih.2⟩
    · rw [hb] at hw
      have ih := wordDe_sound w (bIf(e, false, true)) hw
      have heq : c / 2 = 2 := by
        rw [← shiftRight_one]
        exact Nat.eq_of_beq_eq_true hb
      have hcnt : a1Cnt (c :: w) = a1Cnt w + 1 := by simp [a1Cnt, List.countP_cons, heq]
      refine ⟨codes ih.1, ?_⟩
      rw [hcnt, Nat.even_add_one]
      cases e
      · exact ⟨fun h => absurd h (by decide), fun h => absurd (ih.2.1 rfl) h⟩
      · exact ⟨fun _ hn => absurd (ih.2.2 hn) (by decide), fun _ => rfl⟩

theorem wordD_sound {w : List ℕ} (h : wordD w = true) : CodesOK w ∧ Even (a1Cnt w) :=
  have h' := wordDe_sound w true h
  ⟨h'.1, h'.2.1 rfl⟩

section Parity

variable {A D : Subgroup Pm} {g : ℕ → Pm}

theorem mul_mem_iff_two (hidx : (D.subgroupOf A).index = 2) {a b : Pm} (ha : a ∈ A)
    (hb : b ∈ A) : a * b ∈ D ↔ (a ∈ D ↔ b ∈ D) := by
  have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using h

theorem wordP_mem_of_even (hidx : (D.subgroupOf A).index = 2) (hA : ∀ h < 4, g h ∈ A)
    (hD : ∀ h < 4, h ≠ 1 → g h ∈ D) {w : List ℕ} (hw : CodesOK w) (he : Even (a1Cnt w)) :
    wordP g w ∈ D := by
  have hlet : ∀ c, 2 ≤ c → c < 10 → letP g c ∈ A ∧ (letP g c ∈ D ↔ g (c / 2 - 1) ∈ D) := by
    intro c hc hc'
    have h4 : c / 2 - 1 < 4 := by omega
    unfold letP
    split_ifs
    · exact ⟨hA _ h4, Iff.rfl⟩
    · exact ⟨A.inv_mem (hA _ h4), inv_mem_iff⟩
  by_cases h1 : g 1 ∈ D
  · unfold wordP
    refine Subgroup.list_prod_mem (K := D) ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    have hc' := hw c hc
    refine (hlet c hc'.1 hc'.2).2.2 ?_
    by_cases e : c / 2 - 1 = 1
    · rw [e]
      exact h1
    · exact hD _ (by omega) e
  · have main : ∀ w : List ℕ, CodesOK w → wordP g w ∈ A ∧ (wordP g w ∈ D ↔ Even (a1Cnt w)) := by
      intro w
      induction w with
      | nil => intro _; simp [wordP, a1Cnt]
      | cons c w ih =>
        intro hw
        have hc := hw c List.mem_cons_self
        obtain ⟨ihA, ihD⟩ := ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
        obtain ⟨lA, lD⟩ := hlet c hc.1 hc.2
        have lD' : letP g c ∈ D ↔ ¬ c / 2 = 2 := by
          rw [lD]
          by_cases hc2 : c / 2 = 2
          · have e : c / 2 - 1 = 1 := by omega
            rw [e]
            exact ⟨fun h => absurd h h1, fun h => absurd hc2 h⟩
          · exact ⟨fun _ => hc2, fun _ => hD _ (by omega) (by omega)⟩
        have e : wordP g (c :: w) = letP g c * wordP g w := by simp [wordP]
        rw [e, mul_mem_iff_two hidx lA ihA, lD', ihD]
        refine ⟨A.mul_mem lA ihA, ?_⟩
        by_cases hc2 : c / 2 = 2
        · have hcnt : a1Cnt (c :: w) = a1Cnt w + 1 := by simp [a1Cnt, List.countP_cons, hc2]
          rw [hcnt, Nat.even_add_one]
          simp [hc2]
        · have hcnt : a1Cnt (c :: w) = a1Cnt w := by simp [a1Cnt, List.countP_cons, hc2]
          rw [hcnt]
          simp [hc2]
    exact ((main w hw).2).2 he

end Parity

theorem pairK_sound {F FI A B lp : ℕ → ℕ} {base r : List ℕ}
    (h : pairK F FI A B lp base r = true) :
    wordD (r.drop 8) = true ∧ rowF F FI A B lp base (r.take 4 ++ r.drop 8) = true ∧
      rowF F FI A B lp base (r.drop 4) = true := by
  unfold pairK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem pchK_sound {F FI A B lp : ℕ → ℕ} {base : List ℕ} {z₀ z₁ e₀ e₁ : ℕ}
    {R : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ → Prop} :
    ∀ (L : List (List ℕ)) (ia ja ib jb : ℕ),
      (∀ r ∈ L, pairK F FI A B lp base r = true →
        R (r.getD 2 0, r.getD 3 0, r.getD 6 0, r.getD 7 0)
          (r.getD 0 0, r.getD 1 0, r.getD 4 0, r.getD 5 0)) →
      pchK F FI A B lp base z₀ z₁ e₀ e₁ L ia ja ib jb = true →
      Relation.ReflTransGen R (ia, ja, ib, jb) (z₀, z₁, e₀, e₁)
  | [], ia, ja, ib, jb, _, h => by
    change bAnd(Nat.beq ia z₀, bAnd(Nat.beq ja z₁, bAnd(Nat.beq ib e₀, Nat.beq jb e₁))) = true
      at h
    simp only [bAnd_eq', Bool.and_eq_true, beq_iff] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact Relation.ReflTransGen.refl
  | r :: L, ia, ja, ib, jb, hR, h => by
    change bAnd(Nat.beq (r.getD 2 0) ia, bAnd(Nat.beq (r.getD 3 0) ja,
      bAnd(Nat.beq (r.getD 6 0) ib, bAnd(Nat.beq (r.getD 7 0) jb,
      bAnd(pairK F FI A B lp base r, pchK F FI A B lp base z₀ z₁ e₀ e₁ L (r.getD 0 0)
        (r.getD 1 0) (r.getD 4 0) (r.getD 5 0)))))) = true at h
    simp only [bAnd_eq', Bool.and_eq_true, beq_iff] at h
    obtain ⟨h2, h3, h6, h7, hp, hL⟩ := h
    have hstep := hR r List.mem_cons_self hp
    rw [h2, h3, h6, h7] at hstep
    exact Relation.ReflTransGen.head hstep
      (pchK_sound L _ _ _ _ (fun r' hr' => hR r' (List.mem_cons_of_mem _ hr')) hL)

theorem onL0_cases {lp : ℕ → ℕ} {p : ℕ} (h : onL0 lp p = true) :
    p = lp 0 ∨ p = lp 1 ∨ p = lp 2 := by
  unfold onL0 at h
  cases e0 : Nat.beq p (lp 0)
  · rw [e0] at h
    cases e1 : Nat.beq p (lp 1)
    · rw [e1] at h
      exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e1))
  · exact Or.inl (Nat.eq_of_beq_eq_true e0)

theorem uK_sound {F FI A B lp : ℕ → ℕ} {g : ℕ → Pm} {base u : List ℕ} {Z : ℕ} {z a b : Pm}
    (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) (hw : CodesOK (u.drop 3))
    (hZ : PR Z z) (ha : PR (A (u.getD 1 0)) a) (hb : PR (B (u.getD 2 0)) b)
    (h : uK F FI A B lp base Z u = true) :
    (wordP g (u.drop 3) 0 : ℕ) = u.headD 0 ∧
      (wordP g (u.drop 3) * z * (wordP g (u.drop 3))⁻¹) 0 = 0 ∧
      (∀ p : Fin 1755, onL0 lp p = true →
        onL0 lp ((wordP g (u.drop 3) * z * (wordP g (u.drop 3))⁻¹) p) = true) ∧
      (∀ p : Fin 1755, (p : ℕ) ∈ base →
        (wordP g (u.drop 3) * z * (wordP g (u.drop 3))⁻¹) p = (a * b) p) := by
  unfold uK stabS at h
  simp only [strictB_eq', bAnd_eq', Bool.and_eq_true, beq_iff, List.all_eq_true] at h
  obtain ⟨h0, ⟨hs0, hs1, hs2, hs3⟩, hbase⟩ := h
  have key : ∀ x : Fin 1755, conjPt F FI Z (u.drop 3) x =
      ((wordP g (u.drop 3) * z * (wordP g (u.drop 3))⁻¹) x : ℕ) := by
    intro x
    unfold conjPt
    rw [wInv_eq hF hFI _ hw x, gp_eq hZ, wPt_eq hF hFI _ hw]
    simp only [Equiv.Perm.mul_apply]
  refine ⟨(wPt_eq hF hFI _ hw 0).symm.trans h0, Fin.ext (by rw [← key 0]; exact hs0), ?_, ?_⟩
  · intro p hp
    rcases onL0_cases hp with e | e | e
    · rw [← key p, e]
      exact hs1
    · rw [← key p, e]
      exact hs2
    · rw [← key p, e]
      exact hs3
  · intro p hp
    refine Fin.ext ?_
    rw [← key p, hbase p hp, gp_eq hb, gp_eq ha]
    simp only [Equiv.Perm.mul_apply]

theorem endK_sound {A B lp : ℕ → ℕ} {e : List ℕ} (h : endK A B lp e = true) :
    gp (A (e.getD 0 0)) (gp (B (e.getD 1 0)) (e.getD 2 0)) ≠ e.getD 2 0 ∧
      onLine lp 0 (e.getD 3 0) = true ∧ onLine lp (e.getD 2 0) (e.getD 3 0) = true := by
  unfold endK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e' => ?_, h2, h3⟩
  rw [e', Nat.beq_refl] at h1
  exact absurd h1 (by decide)

theorem locK_sound {F FI A B lp : ℕ → ℕ} {base : List ℕ} {Z : ℕ} {r₀ r₁ : List ℕ}
    {U : List (List ℕ)} {P : List (List (List ℕ))} {E : List (List ℕ)} {i₀ : ℕ}
    (h : locK F FI A B lp base Z r₀ r₁ U P E i₀ = true) :
    ∀ k (hk : k < U.length), uK F FI A B lp base Z U[k] = true ∧
      endK A B lp (E.getD (i₀ + k) []) = true ∧
      pchK F FI A B lp base (r₀.headD 0) (r₀.tail.headD 0) ((E.getD (i₀ + k) []).headD 0)
        ((E.getD (i₀ + k) []).getD 1 0) (P.getD (i₀ + k) []) (U[k].getD 1 0) (U[k].getD 2 0)
        (r₁.headD 0) (r₁.tail.headD 0) = true := by
  intro k hk
  unfold locK at h
  have := (allL_iff U i₀).1 h k hk
  simpa only [bAnd_eq', Bool.and_eq_true] using this

theorem fixK_sound {T C : ℕ} {U : List (List ℕ)} {t c : Pm} (hT : PR T t) (hC : PR C c)
    (h : fixK T C U = true) (p : Fin 1755) (hp : t p = p) :
    p = 0 ∨ p = c 0 ∨ p = c (c 0) ∨ ∃ u ∈ U, u.headD 0 = p := by
  unfold fixK at h
  have h1 := PK.allN_iff.1 h p p.2
  have hc0 : gp C (nat_lit 0) = (c 0 : ℕ) := gp_eq hC 0
  have hcc : gp C (gp C (nat_lit 0)) = (c (c 0) : ℕ) := by
    rw [hc0]
    exact gp_eq hC (c 0)
  rw [gp_eq hT p, hp, Nat.beq_refl, hcc, hc0] at h1
  cases e0 : Nat.beq (p : ℕ) (nat_lit 0)
  · rw [e0] at h1
    cases e1 : Nat.beq (p : ℕ) (c 0 : ℕ)
    · rw [e1] at h1
      cases e2 : Nat.beq (p : ℕ) (c (c 0) : ℕ)
      · rw [e2] at h1
        have h1' : List.any U (fun u => Nat.beq (u.headD 0) p) = true := h1
        obtain ⟨u, hu, hb⟩ := List.any_eq_true.1 h1'
        exact Or.inr (Or.inr (Or.inr ⟨u, hu, Nat.eq_of_beq_eq_true hb⟩))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext (Nat.eq_of_beq_eq_true e2))))
    · exact Or.inr (Or.inl (Fin.ext (Nat.eq_of_beq_eq_true e1)))
  · exact Or.inl (Fin.ext (Nat.eq_of_beq_eq_true e0))

theorem qK_sound {F FI lp : ℕ → ℕ} {g : ℕ → Pm} {Z T C : ℕ} {w : List ℕ} {z t c : Pm}
    (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) (hZ : PR Z z)
    (hT : PR T t) (hC : PR C c) (h : qK F FI lp Z T C w = true) :
    CodesOK w ∧ Even (a1Cnt w) ∧ stabS lp (gp (wN F FI w)) = true ∧
      wordP g w * wordP g w = z ∧ wordP g w * t = t * wordP g w ∧
      wordP g w * (c * (z * (c * c))) = c * (z * (c * c)) * wordP g w := by
  unfold qK at h
  simp only [strictB_eq', bAnd_eq', Bool.and_eq_true, beq_iff] at h
  obtain ⟨hd, hs, h1, h2, h3⟩ := h
  obtain ⟨hc, he⟩ := wordD_sound hd
  have hQ := wN_prep hF hFI w hc
  have hZ₁ := prep_mul hC (prep_mul hZ (prep_mul hC hC))
  refine ⟨hc, he, hs, prep_unique (prep_mul hQ hQ) (by rw [h1]; exact hZ),
    prep_unique (prep_mul hQ hT) (by rw [h2]; exact prep_mul hT hQ),
    prep_unique (prep_mul hQ hZ₁) (by rw [h3]; exact prep_mul hZ₁ hQ)⟩

end CFSG.KC.TitsLocSound

end
