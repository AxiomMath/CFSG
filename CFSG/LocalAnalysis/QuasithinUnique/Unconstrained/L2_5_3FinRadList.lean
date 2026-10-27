module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRad
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadListCheck
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Sporadic.Schreier

section Main

variable {X ι : Type} [Group X] [Finite X] [DecidableEq ι]

omit [Finite X] [DecidableEq ι] in
theorem ListModel.enc_pow (M : ListModel X ι) (x : X) (n : ℕ) :
    M.enc (x ^ n) = lpow M.mul M.one (M.enc x) n := by
  induction n with
  | zero => rw [pow_zero, M.enc_one]; rfl
  | succ n ih => rw [pow_succ', M.enc_mul, ih]; rfl

omit [Finite X] [DecidableEq ι] in
theorem ListModel.enc_mem (M : ListModel X ι) (x : X) : M.enc x ∈ M.elems :=
  (M.mem_elems _).2 ⟨x, rfl⟩

theorem radData_of_listModel (M : ListModel X ι) (hsimple : IsSimpleGroup X) {m : ℕ} (hm : Odd m)
    (hm1 : 1 < m) (hcard : Nat.card X = 16 * m) (invs ord4 : List ι)
    (hinvs : ∀ t, t ∈ invs ↔ t ∈ M.elems ∧ t ≠ M.one ∧ M.mul t t = M.one)
    (hord4 : ∀ u, u ∈ ord4 ↔
      u ∈ M.elems ∧ lpow M.mul M.one u 4 = M.one ∧ lpow M.mul M.one u 2 ≠ M.one)
    (hcenter : CenterOK M.mul M.one M.elems)
    (hodd : OddOK M.mul M.one m M.elems invs ord4)
    (hquat : QuatAll M.mul M.one M.elems invs)
    (hcore : CoreAll M.mul M.one M.inv M.elems invs) :
    RadData X := by
  have hmulself : ∀ x : X, M.mul (M.enc x) (M.enc x) = M.enc (x * x) := fun x =>
    (M.enc_mul x x).symm
  have hone_ne : ∀ x : X, x ≠ 1 → M.enc x ≠ M.one := fun x hx h =>
    hx (M.inj (h.trans M.enc_one.symm))
  have hinv_mem : ∀ t : X, t ≠ 1 → t * t = 1 → M.enc t ∈ invs := fun t ht1 htt =>
    (hinvs _).2 ⟨M.enc_mem t, hone_ne t ht1, by rw [hmulself, htt, M.enc_one]⟩
  refine ⟨?_, hsimple, ⟨m, hm, hm1, hcard⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    by_contra hz1
    rcases hcenter (M.enc z) (M.enc_mem z) with h | ⟨x', hx', hne⟩
    · exact hz1 (M.inj (h.trans M.enc_one.symm))
    · obtain ⟨x, rfl⟩ := (M.mem_elems _).1 hx'
      apply hne
      rw [← M.enc_mul, ← M.enc_mul, hz x]
  ·
    intro x hx1 hxo u hux hu4
    by_contra hu2
    have hxm : x ^ m = 1 := by
      have hdvd : orderOf x ∣ 16 * m := hcard ▸ orderOf_dvd_natCard x
      have hcop : Nat.Coprime (orderOf x) 16 := by
        have := Nat.Coprime.pow_right 4 (Odd.coprime_two_right hxo)
        simpa using this
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)
    have hxpow : lpow M.mul M.one (M.enc x) m = M.one := by
      rw [← M.enc_pow, hxm, M.enc_one]
    obtain ⟨h1, -⟩ := hodd (M.enc x) (M.enc_mem x) (hone_ne x hx1) hxpow
    have hu4' : u ^ 4 = 1 := by rw [pow_four_eq']; exact hu4
    have hu2' : u ^ 2 ≠ 1 := by rw [pow_two]; exact hu2
    have hmemu : M.enc u ∈ ord4 := (hord4 _).2 ⟨M.enc_mem u, by
      rw [← M.enc_pow, hu4', M.enc_one], by
      rw [← M.enc_pow]
      intro h
      exact hu2' (M.inj (h.trans M.enc_one.symm))⟩
    apply h1 (M.enc u) hmemu
    rw [← M.enc_mul, ← M.enc_mul, hux]
  ·
    intro x hx1 hxo t s ht1 hs1 hts htt hss hcts htx hsx
    have hxm : x ^ m = 1 := by
      have hdvd : orderOf x ∣ 16 * m := hcard ▸ orderOf_dvd_natCard x
      have hcop : Nat.Coprime (orderOf x) 16 := by
        have := Nat.Coprime.pow_right 4 (Odd.coprime_two_right hxo)
        simpa using this
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)
    have hxpow : lpow M.mul M.one (M.enc x) m = M.one := by
      rw [← M.enc_pow, hxm, M.enc_one]
    obtain ⟨-, h2⟩ := hodd (M.enc x) (M.enc_mem x) (hone_ne x hx1) hxpow
    refine h2 (M.enc t) (List.mem_filter.2 ⟨hinv_mem t ht1 htt, ?_⟩) (M.enc s)
      (List.mem_filter.2 ⟨hinv_mem s hs1 hss, ?_⟩) (fun h => hts (M.inj h)) ?_
    · rw [decide_eq_true_eq, ← M.enc_mul, ← M.enc_mul, htx]
    · rw [decide_eq_true_eq, ← M.enc_mul, ← M.enc_mul, hsx]
    · rw [← M.enc_mul, ← M.enc_mul, hcts]
  ·
    intro t hto
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [hto, pow_two] at this
      exact this
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hto
      omega
    obtain ⟨hne, -⟩ := hquat (M.enc t) (hinv_mem t ht1 htt)
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    rw [List.mem_filter, decide_eq_true_eq] at hy
    obtain ⟨y', rfl⟩ := (M.mem_elems _).1 hy.1
    exact ⟨y', M.inj (by rw [← M.enc_mul]at hy; exact hy.2)⟩
  ·
    intro t hto y y' hy hy'
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [hto, pow_two] at this
      exact this
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hto
      omega
    obtain ⟨-, hclos, -⟩ := hquat (M.enc t) (hinv_mem t ht1 htt)
    have hsq : ∀ z : X, z * z = t → M.enc z ∈ M.elems.filter
        (fun y => decide (M.mul y y = M.enc t)) := fun z hz =>
      List.mem_filter.2 ⟨M.enc_mem z, by rw [decide_eq_true_eq, ← M.enc_mul, hz]⟩
    rcases hclos (M.enc y) (hsq y hy) (M.enc y') (hsq y' hy') with h | h | h
    · left
      exact M.inj (by rw [M.enc_mul, M.enc_one]; exact h)
    · right; left
      exact M.inj (by rw [M.enc_mul]; exact h)
    · right; right
      exact M.inj (by simp only [M.enc_mul]; exact h)
  ·
    intro t hto
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [hto, pow_two] at this
      exact this
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hto
      omega
    obtain ⟨-, -, hnodup, hlen⟩ := hquat (M.enc t) (hinv_mem t ht1 htt)
    rw [card_eq_length (fun y : X => y = 1 ∨ y = t ∨ y * y = t) M.enc M.inj
      (M.one :: M.enc t :: M.elems.filter fun y => decide (M.mul y y = M.enc t)) hnodup ?_]
    · exact hlen
    · intro b
      constructor
      · intro hb
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hb
        rcases hb with rfl | rfl | ⟨hbe, hbb⟩
        · exact ⟨1, Or.inl rfl, M.enc_one⟩
        · exact ⟨t, Or.inr (Or.inl rfl), rfl⟩
        · obtain ⟨a, rfl⟩ := (M.mem_elems _).1 hbe
          exact ⟨a, Or.inr (Or.inr (M.inj (by rw [M.enc_mul]; exact hbb))), rfl⟩
      · rintro ⟨a, ha, rfl⟩
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
        rcases ha with rfl | rfl | ha
        · exact Or.inl M.enc_one
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨M.enc_mem a, by rw [← M.enc_mul, ha]⟩)
  ·
    intro t hto c hct hnc
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [hto, pow_two] at this
      exact this
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hto
      omega
    have hcC : M.enc c ∈ M.elems.filter (fun c' => decide (M.mul c' (M.enc t) = M.mul (M.enc t) c')) :=
      List.mem_filter.2 ⟨M.enc_mem c, by rw [decide_eq_true_eq, ← M.enc_mul, ← M.enc_mul, hct]⟩
    rcases hcore (M.enc t) (hinv_mem t ht1 htt) (M.enc c) hcC with h | ⟨w', hw', hw16⟩
    · exfalso
      apply hnc
      rcases h with h | h | h
      · exact Or.inl (M.inj (h.trans M.enc_one.symm))
      · exact Or.inr (Or.inl (M.inj h))
      · exact Or.inr (Or.inr (M.inj (by rw [M.enc_mul]; exact h)))
    · rw [List.mem_filter, decide_eq_true_eq] at hw'
      obtain ⟨w, rfl⟩ := (M.mem_elems _).1 hw'.1
      refine ⟨w, M.inj (by rw [M.enc_mul, M.enc_mul]; exact hw'.2), fun h => hw16 ?_⟩
      have := congrArg M.enc h
      rw [M.enc_pow, M.enc_one] at this
      simpa [M.enc_mul, M.enc_inv] using this

omit [Finite X] in
theorem radData_of_listModel_equiv {Y : Type} [Group Y] [Finite Y] (M : ListModel X ι)
    (e : Y ≃* X) (hsimple : IsSimpleGroup Y) {m : ℕ} (hm : Odd m) (hm1 : 1 < m)
    (hcard : Nat.card Y = 16 * m) (invs ord4 : List ι)
    (hinvs : ∀ t, t ∈ invs ↔ t ∈ M.elems ∧ t ≠ M.one ∧ M.mul t t = M.one)
    (hord4 : ∀ u, u ∈ ord4 ↔
      u ∈ M.elems ∧ lpow M.mul M.one u 4 = M.one ∧ lpow M.mul M.one u 2 ≠ M.one)
    (hcenter : CenterOK M.mul M.one M.elems)
    (hodd : OddOK M.mul M.one m M.elems invs ord4)
    (hquat : QuatAll M.mul M.one M.elems invs)
    (hcore : CoreAll M.mul M.one M.inv M.elems invs) : RadData Y :=
  radData_of_listModel (M.ofMulEquiv e) hsimple hm hm1 hcard invs ord4 hinvs hord4 hcenter hodd
    hquat hcore

end Main

end CFSG.QuasithinUnique.Fin253
