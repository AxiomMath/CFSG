module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank

variable {G : Type*} [Group G]

@[expose] def pPart (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (p n : ℕ) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ a ^ (p ^ n) = 1}
  one_mem' := ⟨A.one_mem, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    rw [(show Commute a b from hA a ha b hb).mul_pow, ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨A.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem pPart_le (A : Subgroup G) (hA) (p n : ℕ) : pPart A hA p n ≤ A := fun _ h => h.1

theorem pPart_conj (A : Subgroup G) (hA) (p n : ℕ) {g : G}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) {a : G} (ha : a ∈ pPart A hA p n) :
    g * a * g⁻¹ ∈ pPart A hA p n := by
  refine ⟨hg a ha.1, ?_⟩
  rw [conj_pow, ha.2, mul_one, mul_inv_cancel]

theorem pPart_isPGroup (A : Subgroup G) (hA) (p n : ℕ) : IsPGroup p (pPart A hA p n) :=
  fun x => ⟨n, Subtype.ext x.2.2⟩

theorem mem_pPart_of_orderOf {A : Subgroup G} {hA} {p n : ℕ} (hn : 1 ≤ n) {a : G} (ha : a ∈ A)
    (hao : orderOf a = p) : a ∈ pPart A hA p n := by
  refine ⟨ha, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ', pow_mul, ← hao, pow_orderOf_eq_one, one_pow]

theorem comm_of_card_le_two {N : Subgroup G} [Finite N] (hN : Nat.card N ≤ 2) {x y : G}
    (hx : x ∈ N) (hyx : y * x * y⁻¹ ∈ N) : y * x = x * y := by
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, one_mul]
  by_contra hne
  have hw1 : y * x * y⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [this, h]; group
  have hwx : y * x * y⁻¹ ≠ x := by
    intro h
    apply hne
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h]
  have hsub : ({1, x, y * x * y⁻¹} : Set G) ⊆ (N : Set G) := by
    rintro _ (rfl | rfl | rfl)
    · exact N.one_mem
    · exact hx
    · exact hyx
  have h3 : ({1, x, y * x * y⁻¹} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hwx.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hw1⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at hle
  have : Nat.card (N : Set G) = Nat.card N := rfl
  omega

theorem not_dvd_sub_pow {p q a b : ℕ}
    (hpq : (p = 11 ∧ q = 7 ∧ a ≤ 2) ∨ ((p = 23 ∨ p = 31 ∨ p = 37) ∧ q = 7 ∧ a ≤ 1) ∨
      ((p = 5 ∨ p = 7 ∨ p = 29 ∨ p = 43) ∧ q = 11 ∧ a ≤ 1))
    (hba : b < a) : ¬ (q : ℤ) ∣ ((p ^ a : ℕ) : ℤ) - ((p ^ b : ℕ) : ℤ) := by
  rcases hpq with ⟨rfl, rfl, ha⟩ | ⟨hp, rfl, ha⟩ | ⟨hp, rfl, ha⟩
  · interval_cases a <;> interval_cases b <;> decide
  · rcases hp with rfl | rfl | rfl <;> interval_cases a <;> interval_cases b <;> decide
  · rcases hp with rfl | rfl | rfl | rfl <;> interval_cases a <;> interval_cases b <;> decide

theorem theta_central_core [Finite G] {z c : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hco : orderOf c = 3) (hcz : c * z = z * c) (Kg : Subgroup G)
    (hK : ∀ k ∈ Kg, k * c = c * k → ∃ e : Bool, ∃ i < 3, k = (if e then z else 1) * c ^ i)
    (hP : ∀ S : Subgroup G,
      S ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) →
      (∀ l ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G),
        ∀ s ∈ S, l * s * l⁻¹ ∈ S) →
      Group.IsSolvable S → S ≤ Kg)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43)
    (hsq : ∀ p : ℕ, (p = 5 ∨ p = 7 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43) →
      ¬ p ^ 2 ∣ Nat.card G)
    (h114 : ¬ 11 ^ 4 ∣ Nat.card G)
    (h7 : z ∈ Subgroup.closure {g | g ∈ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ∧ orderOf g = 7})
    (h11 : z ∈ Subgroup.closure {g | g ∈ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ∧ orderOf g = 11})
    (H3 : ∀ (N : Subgroup G) (t : G), t ^ 2 = 1 → t ≠ 1 → (∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ n ∈ N, t * n = n * t → n = 1 ∨ n = t) →
      ∃ A : Subgroup G, A ≤ N ∧ (∀ g : G, (∀ n ∈ N, g * n * g⁻¹ ∈ N) → ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
        Odd (Nat.card A) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.relIndex N ≤ 2)
    (H4 : ∀ (P : Subgroup G) (w : G) (q : ℕ), q.Prime → orderOf w = q →
      (∀ x ∈ P, w * x * w⁻¹ ∈ P) →
      (∀ B : Subgroup G, B ≤ P → B ≠ P → ¬ (q : ℤ) ∣ (Nat.card P : ℤ) - (Nat.card B : ℤ)) →
      ∀ x ∈ P, w * x = x * w) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G)) ≤
      Subgroup.center (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set L := Subgroup.centralizer ({z} : Set G) ⊓ C with hL
  set N := thetaOf c with hN
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hcz.symm
  have hcomm : ∀ n ∈ N, n * z = z * n → n = 1 ∨ n = z :=
    fun n hn h => theta_comm_core hz hco hcz Kg hK hP hn h
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz) hz1
  obtain ⟨A, hAN, hAchar, hAodd, hAab, hArel⟩ := H3 N z (by rw [sq]; exact hz) hz1
    (fun n hn => thetaOf_conj hzC hn) (fun n hn h => hcomm n hn h.symm)
  have hAz : ∀ a ∈ A, a * z = z * a → a = 1 := by
    intro a ha h
    rcases hcomm a (hAN ha) h with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at ha
      have h2 : 2 ∣ Nat.card A := hzo ▸ Subgroup.orderOf_dvd_natCard A ha
      exact (Nat.not_even_iff_odd.2 hAodd) (even_iff_two_dvd.2 h2)
  have hLA : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A :=
    fun l hl => hAchar l (fun n hn => thetaOf_conj (Subgroup.mem_inf.1 hl).2 hn)
  have hAbot : A = ⊥ := by
    by_contra hne
    have hcard1 : Nat.card A ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hcard1
    have : Fact p.Prime := ⟨hp⟩
    have hAG : Nat.card A ∣ Nat.card G := Subgroup.card_subgroup_dvd_card A
    have hpG : p ∣ Nat.card G := hpA.trans hAG
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hAodd) (even_iff_two_dvd.2 hpA)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact thetaOf_not_three_dvd c (hpA.trans (Subgroup.card_dvd_of_le hAN))
    set P := pPart A hAab p (Nat.card G) with hPdef
    have hPA : P ≤ A := pPart_le A hAab p _
    have hPp : IsPGroup p P := pPart_isPGroup A hAab p _
    obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpA
    have hx0' : orderOf (x0 : G) = p := by rw [Subgroup.orderOf_coe]; exact hx0
    have hx0P : (x0 : G) ∈ P := mem_pPart_of_orderOf Nat.card_pos x0.2 hx0'
    have hx01 : (x0 : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx0'
      exact hp.one_lt.ne' hx0'.symm
    have hPL : ∀ x ∈ P, x ∈ L → x = 1 := by
      intro x hx hxL
      exact hAz x (hPA hx) (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hxL).1)
    have hLP : ∀ l ∈ L, ∀ x ∈ P, l * x * l⁻¹ ∈ P :=
      fun l hl x hx => pPart_conj A hAab p _ (hLA l hl) hx
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 hPp)
    have hPG : p ^ a ∣ Nat.card G := ha ▸ Subgroup.card_subgroup_dvd_card P
    have ha1 : 1 ≤ a := by
      by_contra h0
      have : a = 0 := by omega
      rw [this, pow_zero] at ha
      exact hx01 (by
        have := (Subgroup.card_eq_one.1 ha)
        have hx' : (x0 : G) ∈ (⊥ : Subgroup G) := this ▸ hx0P
        exact Subgroup.mem_bot.1 hx')
    have hcase : ∃ q : ℕ, (q = 7 ∨ q = 11) ∧
        ((p = 11 ∧ q = 7 ∧ a ≤ 2) ∨ ((p = 23 ∨ p = 31 ∨ p = 37) ∧ q = 7 ∧ a ≤ 1) ∨
          ((p = 5 ∨ p = 7 ∨ p = 29 ∨ p = 43) ∧ q = 11 ∧ a ≤ 1)) := by
      have hsmall : ∀ p' : ℕ, (p' = 5 ∨ p' = 7 ∨ p' = 23 ∨ p' = 29 ∨ p' = 31 ∨ p' = 37 ∨ p' = 43) →
          p' = p → a ≤ 1 := by
        rintro p' hp' rfl
        by_contra h2
        exact hsq p' hp' ((pow_dvd_pow p' (by omega : 2 ≤ a)).trans hPG)
      rcases hprimes p hp hpG with h | h | h | h | h | h | h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · exact ⟨11, Or.inr rfl, Or.inr (Or.inr ⟨Or.inl h, rfl, hsmall p (Or.inl h) rfl⟩)⟩
      · exact ⟨11, Or.inr rfl, Or.inr (Or.inr ⟨Or.inr (Or.inl h), rfl,
          hsmall p (Or.inr (Or.inl h)) rfl⟩)⟩
      ·
        subst h
        refine ⟨7, Or.inl rfl, Or.inl ⟨rfl, rfl, ?_⟩⟩
        by_contra h3
        have ha3 : a = 3 := by
          by_contra h4
          exact h114 ((pow_dvd_pow 11 (by omega : 4 ≤ a)).trans hPG)
        obtain ⟨y, ⟨hyL, hyo⟩⟩ : ∃ y, y ∈ L ∧ orderOf y = 11 := by
          by_contra hno
          push Not at hno
          have hempty : {g | g ∈ L ∧ orderOf g = 11} = (∅ : Set G) := by
            ext g; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            exact fun ⟨h1, h2⟩ => hno g h1 h2
          rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at h11
          exact hz1 h11
        have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) := by
          rw [Subgroup.zpowers_le]
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · exact fun hx => hLP y hyL x hx
          · intro hx
            have := hLP y⁻¹ (L.inv_mem hyL) _ hx
            simpa [mul_assoc] using this
        have hyp : IsPGroup 11 (Subgroup.zpowers y) := by
          refine IsPGroup.of_card (n := 1) ?_
          rw [Nat.card_zpowers, hyo, pow_one]
        have hsup := IsPGroup.to_sup_of_normal_left' hPp hyp hyN
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hsup
        have hmG : 11 ^ m ∣ Nat.card G := hm ▸ Subgroup.card_subgroup_dvd_card _
        have hm3 : m ≤ 3 := by
          by_contra h4
          exact h114 ((pow_dvd_pow 11 (by omega : 4 ≤ m)).trans hmG)
        have heq : P ⊔ Subgroup.zpowers y = P := by
          apply le_antisymm _ le_sup_left
          apply (Subgroup.eq_of_le_of_card_ge le_sup_left _).ge
          rw [hm, ha, ha3]
          exact Nat.pow_le_pow_right (by norm_num) hm3
        have hyP : y ∈ P := heq ▸ (le_sup_right : Subgroup.zpowers y ≤ _) (Subgroup.mem_zpowers y)
        have := hPL y hyP hyL
        rw [this, orderOf_one] at hyo
        exact absurd hyo (by norm_num)
      · exact ⟨7, Or.inl rfl, Or.inr (Or.inl ⟨Or.inl h, rfl,
          hsmall p (Or.inr (Or.inr (Or.inl h))) rfl⟩)⟩
      · exact ⟨11, Or.inr rfl, Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl h)), rfl,
          hsmall p (Or.inr (Or.inr (Or.inr (Or.inl h)))) rfl⟩)⟩
      · exact ⟨7, Or.inl rfl, Or.inr (Or.inl ⟨Or.inr (Or.inl h), rfl,
          hsmall p (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) rfl⟩)⟩
      · exact ⟨7, Or.inl rfl, Or.inr (Or.inl ⟨Or.inr (Or.inr h), rfl,
          hsmall p (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) rfl⟩)⟩
      · exact ⟨11, Or.inr rfl, Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr h)), rfl,
          hsmall p (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) rfl⟩)⟩
    obtain ⟨q, hq, hpq⟩ := hcase
    have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
    have hcop : ∀ B : Subgroup G, B ≤ P → B ≠ P →
        ¬ (q : ℤ) ∣ (Nat.card P : ℤ) - (Nat.card B : ℤ) := by
      intro B hBP hBne
      have hBp : IsPGroup p B := hPp.to_le hBP
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hBp
      have hdvd : p ^ b ∣ p ^ a := hb ▸ ha ▸ Subgroup.card_dvd_of_le hBP
      have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
      have hba' : b < a := by
        refine lt_of_le_of_ne hba ?_
        rintro rfl
        exact hBne (Subgroup.eq_of_le_of_card_ge hBP (by rw [ha, hb]))
      rw [ha, hb]
      exact not_dvd_sub_pow hpq hba'
    have hcent : ∀ w ∈ L, orderOf w = q → ∀ x ∈ P, w * x = x * w :=
      fun w hw hwo => H4 P w q hqp hwo (hLP w hw) hcop
    have hzP : ∀ x ∈ P, z * x = x * z := by
      have hsub : {g | g ∈ L ∧ orderOf g = q} ⊆ (Subgroup.centralizer (P : Set G) : Set G) := by
        rintro w ⟨hw, hwo⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hcent w hw hwo x hx).symm
      have hzc : z ∈ Subgroup.centralizer (P : Set G) := by
        rcases hq with rfl | rfl
        · exact (Subgroup.closure_le _).2 hsub h7
        · exact (Subgroup.closure_le _).2 hsub h11
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.1 hzc) x hx).symm
    exact hx01 (hAz _ (hPA hx0P) (hzP _ hx0P).symm)
  have hN2 : Nat.card N ≤ 2 := by
    have := hArel
    rwa [hAbot, Subgroup.relIndex_bot_left] at this
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hxN : (x : G) ∈ N := ⟨x, hx, rfl⟩
  have hyN : (y : G) * x * (y : G)⁻¹ ∈ N := thetaOf_conj y.2 hxN
  exact Subtype.ext (comm_of_card_le_two hN2 hxN hyN)

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
