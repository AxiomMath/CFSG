module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDefs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def CSimpleType (X : Type) [Group X] : Prop :=
  Blueprint.OddLieType X ∨ (∃ n : ℕ, 7 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    Blueprint.LieModel X .PSL 3 2 2

theorem CSimpleType.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : CSimpleType X) : CSimpleType X' := by
  rcases h with ⟨t, n, p, f, hp, hp2, hadm, hm⟩ | ⟨n, hn, ⟨f⟩⟩ | h
  · exact Or.inl ⟨t, n, p, f, hp, hp2, hadm, Blueprint.LieModel.of_mulEquiv e hm⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr (Blueprint.LieModel.of_mulEquiv e h))

theorem cSimpleType_of_typC {T : Type} [Group T] (h : TypC T) :
    CSimpleType (T ⧸ Open.fusionZStar T) := by
  rcases h with h | ⟨n, hn, -, -, ⟨f⟩⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨n, hn, ⟨(Sol78.coreQuotientCenterEquiv T).symm.trans f⟩⟩)
  · exact Or.inr (Or.inr (Blueprint.LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv T) h))

theorem card_eq_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : Blueprint.LieModel X t n p f) {N : ℕ}
    (hN : lieOrderNumerator t n (p ^ f) = N * lieOrderDivisor t n (p ^ f))
    (hd : 0 < lieOrderDivisor t n (p ^ f)) : Nat.card X = N := by
  obtain ⟨-, hord, -⟩ := hO X t n p f hadm hX
  rw [hN] at hord
  exact Nat.eq_of_mul_eq_mul_right hd hord

theorem card_eq_of_lieModel_L34 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : Blueprint.LieModel X .PSL 3 2 2) : Nat.card X = 20160 :=
  card_eq_of_lieModel hO hX.admissible hX (by decide) (by decide)

theorem prime_mem_of_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ {l : List (ℕ × ℕ)}, (∀ x ∈ l, x.1.Prime) → p ∣ (l.map fun x => x.1 ^ x.2).prod →
      ∃ x ∈ l, p = x.1
  | [], _, h => absurd (Nat.le_of_dvd one_pos (by simpa using h)) (by have := hp.two_le; omega)
  | x :: l, hl, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact ⟨x, List.mem_cons_self .., (Nat.prime_dvd_prime_iff_eq hp
        (hl x List.mem_cons_self ..)).mp (hp.dvd_of_dvd_pow h)⟩
    · obtain ⟨y, hy, rfl⟩ :=
        prime_mem_of_dvd_prod hp (fun y hy => hl y (List.mem_cons_of_mem _ hy)) h
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

theorem factorial_div_two_ne {N n : ℕ} (hn : 7 ≤ n) (h11 : ¬ 11 ∣ N)
    (hs : N ≠ 2520 ∧ N ≠ 20160 ∧ N ≠ 181440 ∧ N ≠ 1814400) : n.factorial / 2 ≠ N := by
  intro h
  rcases (by omega : n ≤ 10 ∨ 11 ≤ n) with hle | hge
  · interval_cases n <;> simp [Nat.factorial] at h <;> omega
  · apply h11
    rw [← h]
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h11' : 11 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hge
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hk] at h11'
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h11')

theorem not_cSimpleType_of_card (hO : LieOrderFormulasInput) {X : Type} [Group X] {N : ℕ}
    (hX : Nat.card X = N) (h11 : ¬ 11 ∣ N)
    (hs : N ≠ 2520 ∧ N ≠ 20160 ∧ N ≠ 181440 ∧ N ≠ 1814400)
    (hodd : ∀ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 → StatedLieAdmissible t n p f →
      Blueprint.LieModel X t n p f → False) : ¬ CSimpleType X := by
  rintro (⟨t, n, p, f, -, hp2, hadm, hm⟩ | ⟨n, hn, ⟨e⟩⟩ | h)
  · exact hodd t n p f hp2 hadm hm
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc := Nat.card_congr e.toEquiv
    rw [hX, nat_card_alternatingGroup, Nat.card_fin] at hc
    exact factorial_div_two_ne hn h11 hs hc.symm
  · exact hs.2.1 ((card_eq_of_lieModel_L34 hO h).symm.trans hX).symm

theorem prime_dvd_sp62 {p : ℕ} (hp : p.Prime) (h : p ∣ 1451520) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  obtain ⟨x, hx, rfl⟩ := prime_mem_of_dvd_prod hp (l := [(2, 9), (3, 4), (5, 1), (7, 1)])
    (by decide) (by simpa using h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem prime_dvd_tits {p : ℕ} (hp : p.Prime) (h : p ∣ 17971200) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
  obtain ⟨x, hx, rfl⟩ := prime_mem_of_dvd_prod hp (l := [(2, 11), (3, 3), (5, 2), (13, 1)])
    (by decide) (by simpa using h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem prime_dvd_f42 {p : ℕ} (hp : p.Prime) (h : p ∣ 3311126603366400) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 := by
  obtain ⟨x, hx, rfl⟩ := prime_mem_of_dvd_prod hp
    (l := [(2, 24), (3, 6), (5, 2), (7, 2), (13, 1), (17, 1)]) (by decide) (by simpa using h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lieModel_odd_card_ne_sp62 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 1451520 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 1451520 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 1451520 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_sp62 hp hpd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem lieModel_odd_card_ne_tits (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 17971200 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 17971200 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 17971200 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_tits hp hpd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem lieModel_odd_card_ne_f42 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 3311126603366400 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 3311126603366400 :=
    hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 3311126603366400 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_f42 hp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem not_cSimpleType_of_card_sp62 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : Nat.card X = 1451520) : ¬ CSimpleType X :=
  not_cSimpleType_of_card hO hX (by decide) (by decide)
    fun _ _ _ _ hp2 hadm hm => lieModel_odd_card_ne_sp62 hO hp2 hadm hm hX

theorem not_cSimpleType_of_card_tits (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : Nat.card X = 17971200) : ¬ CSimpleType X :=
  not_cSimpleType_of_card hO hX (by decide) (by decide)
    fun _ _ _ _ hp2 hadm hm => lieModel_odd_card_ne_tits hO hp2 hadm hm hX

theorem not_cSimpleType_of_card_f42 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : Nat.card X = 3311126603366400) : ¬ CSimpleType X :=
  not_cSimpleType_of_card hO hX (by decide) (by decide)
    fun _ _ _ _ hp2 hadm hm => lieModel_odd_card_ne_f42 hO hp2 hadm hm hX

end CFSG.ComponentClassification.GS82PumpInputs
