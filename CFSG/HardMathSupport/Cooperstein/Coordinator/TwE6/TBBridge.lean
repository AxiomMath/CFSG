module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.DigitFold

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator

@[expose] def cart (i k : Fin Tag.F4.rank) : ℤ := Tag.F4.cartan i k

@[expose] def cartLit : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  ![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]]

theorem cart_eq : ∀ i k : Fin Tag.F4.rank, cart i k = cartLit i k := by
  decide +kernel

theorem cart_omega : ∀ i s : Fin Tag.F4.rank, ∑ k, cart i k * F4Exc.f4Omega s k =
    if i = s then 1 else 0 := by
  decide +kernel

@[expose] def twOf (c : TwN) : Fin Tag.F4.rank := c

@[expose] def rv (s : Fin Tag.F4.rank) : Fin Tag.F4.rank := twOf (twNode s)

@[expose] def twU (x : Fin Tag.F4.rank → ℤ) (c : TwN) : ℤ := ∑ k, cart (rv (twOf c)) k * x k

theorem rv_rv (s : Fin Tag.F4.rank) : rv (rv s) = s :=
  Fin.ext (by have : s.val < 4 := s.2; simp only [rv, twNode, twOf]; omega)

theorem twA_sub_cartan (f : ℕ) (c : TwN) (i : Fin Tag.F4.rank) :
    twA f c (twNode i) - cart (rv (twOf c)) i =
      if c.val = 1 ∧ i.val = 1 then 1 - 2 ^ f else 0 := by
  rw [cart_eq]
  obtain ⟨c, hc⟩ := c
  obtain ⟨i, hi⟩ := i
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
    have : c < 4 := hc
    omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have : i < 4 := hi
    omega
  by_cases h : c = 1 ∧ i = 1
  · obtain ⟨rfl, rfl⟩ := h
    show -(1 + 2 ^ f : ℤ) - (-2) = _
    simp only [and_self, ite_true]
    ring
  · have hn : ¬ (c = 1 ∧ i = 1) := h
    simp only [hn, ite_false]
    rcases hc' with rfl | rfl | rfl | rfl <;> rcases hi' with rfl | rfl | rfl | rfl <;>
      first | exact absurd ⟨rfl, rfl⟩ h | rfl

theorem twRefl_twU {f : ℕ} {m : ℤ} (hm : m ∣ 2 ^ f - 1) (i : Fin Tag.F4.rank)
    (x : Fin Tag.F4.rank → ℤ) (c : TwN) :
    m ∣ twRefl f (twNode i) (twU x) c - twU (reflect .F4 i x) c := by
  have e1 : twU (reflect .F4 i x) c = twU x c -
      cart (rv (twOf c)) i * ∑ j, cart i j * x j := by
    simp [twU, reflect, cart, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have e2 : twU x (twNode i) = ∑ j, cart i j * x j := by
    show ∑ k, cart (rv (rv i)) k * x k = _
    rw [rv_rv]
  have e3 : twRefl f (twNode i) (twU x) c - twU (reflect .F4 i x) c =
      -(twA f c (twNode i) - cart (rv (twOf c)) i) * ∑ j, cart i j * x j := by
    unfold twRefl
    rw [e1, e2]; ring
  rw [e3, twA_sub_cartan]
  split_ifs
  · exact Dvd.dvd.mul_right (by rw [neg_sub]; exact hm) _
  · simp

theorem twAct_twU {f : ℕ} {m : ℤ} (hm : m ∣ 2 ^ f - 1) (l : List (Fin Tag.F4.rank))
    (e : TwN → ℤ) (x : Fin Tag.F4.rank → ℤ) (h : ∀ c, m ∣ e c - twU x c) :
    ∀ c, m ∣ twAct f (twWd l) e c - twU (l.foldr (reflect .F4) x) c := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro c
    have hx : twAct f (twWd (i :: l)) e = twRefl f (twNode i) (twAct f (twWd l) e) := rfl
    rw [hx, List.foldr_cons]
    set E := twAct f (twWd l) e
    set x' := l.foldr (reflect .F4) x
    have key : twRefl f (twNode i) E c - twU (reflect .F4 i x') c =
        ((E c - twU x' c) - twA f c (twNode i) * (E (twNode i) - twU x' (twNode i))) +
          (twRefl f (twNode i) (twU x') c - twU (reflect .F4 i x') c) := by
      unfold twRefl; ring
    rw [key]
    exact dvd_add (dvd_sub (ih c) (Dvd.dvd.mul_left (ih _) _)) (twRefl_twU hm i x' c)

theorem reflect_cart (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) :
    reflect .F4 i v = v - (∑ k, cart i k * v k) • Pi.single i 1 := rfl

theorem cart_sum_lin (i : Fin Tag.F4.rank) (p q : ℤ) (x z : Fin Tag.F4.rank → ℤ) :
    ∑ k, cart i k * (p • x - q • z) k =
      p * ∑ k, cart i k * x k - q * ∑ k, cart i k * z k := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring

theorem reflect_lin (i : Fin Tag.F4.rank) (p q : ℤ) (x z : Fin Tag.F4.rank → ℤ) :
    reflect .F4 i (p • x - q • z) = p • reflect .F4 i x - q • reflect .F4 i z := by
  funext j
  rw [reflect_cart, reflect_cart, reflect_cart, cart_sum_lin]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem foldr_reflect_lin (l : List (Fin Tag.F4.rank)) (p q : ℤ) (x z : Fin Tag.F4.rank → ℤ) :
    l.foldr (reflect .F4) (p • x - q • z) =
      p • l.foldr (reflect .F4) x - q • l.foldr (reflect .F4) z := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, reflect_lin]

theorem twU_sub (x y : Fin Tag.F4.rank → ℤ) (c : TwN) : twU (x - y) c = twU x c - twU y c := by
  simp only [twU, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem twU_start (f : ℕ) {m : ℤ} (hm : m ∣ 2 ^ f - 1) (s : Fin Tag.F4.rank) (p : ℤ)
    (lam : TwN → ℤ) (hlam : ∀ c, m ∣ lam c - p * (if c = twNode s then 1 else 0)) (b : ℕ)
    (c : TwN) :
    m ∣ (lam c - 2 ^ b * twRoot f (twNode s) c) -
      twU (p • F4Exc.f4Omega s - (2 : ℤ) ^ b • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) c := by
  have e1 : twU (p • F4Exc.f4Omega s - (2 : ℤ) ^ b • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) c =
      p * (if rv (twOf c) = s then 1 else 0) - 2 ^ b * cart (rv (twOf c)) s := by
    rw [twU, cart_sum_lin, cart_omega]
    simp [Pi.single_apply]
  have e2 : (if rv (twOf c) = s then (1 : ℤ) else 0) = if c = twNode s then 1 else 0 := by
    have : rv (twOf c) = s ↔ c = twNode s := by
      have hc4 : c.val < 4 := c.2
      have hs4 : s.val < 4 := s.2
      constructor
      · intro h
        have h' : 3 - c.val = s.val := Fin.ext_iff.1 h
        exact Fin.ext (show c.val = 3 - s.val by omega)
      · intro h
        have h' : c.val = 3 - s.val := Fin.ext_iff.1 h
        exact Fin.ext (show 3 - c.val = s.val by omega)
    simp only [this]
  have e3 : (lam c - 2 ^ b * twRoot f (twNode s) c) -
      twU (p • F4Exc.f4Omega s - (2 : ℤ) ^ b • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) c =
      (lam c - p * (if c = twNode s then 1 else 0)) -
        2 ^ b * (twA f c (twNode s) - cart (rv (twOf c)) s) := by
    rw [e1, e2]; unfold twRoot; ring
  rw [e3, twA_sub_cartan]
  refine dvd_sub (hlam c) (Dvd.dvd.mul_left ?_ _)
  split_ifs
  · rw [← neg_sub]; exact dvd_neg.2 hm
  · simp

theorem dvd_of_dvd_twU {m : ℤ} (z : Fin Tag.F4.rank → ℤ) (h : ∀ c, m ∣ twU z c)
    (k : Fin Tag.F4.rank) : m ∣ z k := by
  have e2 : ∀ i, twU z (twNode i) = ∑ j, cart i j * z j := fun i => by
    show ∑ k, cart (rv (rv i)) k * z k = _
    rw [rv_rv]
  have e : z k = ∑ i, F4Exc.f4Omega i k * twU z (twNode i) := by
    simp only [e2]
    calc z k = ∑ j, (if k = j then (1 : ℤ) else 0) * z j := by simp
      _ = ∑ j, (∑ i, F4Exc.f4Omega i k * cart i j) * z j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (∑ i, F4Exc.f4Omega i k * cart i j) = _ from F4Exc.f4Omega_mul_cartan k j]
      _ = ∑ i, F4Exc.f4Omega i k * ∑ j, cart i j * z j := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (h _) _

section Certs


theorem wF_smul (s : Fin Tag.F4.rank) (i : ℕ) (x : Fin Tag.F4.rank → ℤ) :
    F4Exc.wF s i • x = (F4Exc.gamWord s i).foldr (reflect .F4) x := by
  simp only [F4Exc.wF, CurtisExc.wordProd_smul']

theorem uF_smul (s : Fin Tag.F4.rank) (j : ℕ) (x : Fin Tag.F4.rank → ℤ) :
    F4Exc.uF s j • x = (F4Exc.uWord s j).foldr (reflect .F4) x := by
  simp only [F4Exc.uF, CurtisExc.wordProd_smul']

theorem twV_dvd {f : ℕ} {m : ℤ} (hm : m ∣ 2 ^ f - 1) (s : Fin Tag.F4.rank) (p : ℤ)
    (lam : TwN → ℤ) (hlam : ∀ c, m ∣ lam c - p * (if c = twNode s then 1 else 0)) (b : ℕ)
    (i : Fin 12) (j : Fin 8) (c : TwN) :
    m ∣ twV f s lam b i j c -
      twU (p • (F4Exc.wF s i • (F4Exc.uF s j • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ b • (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))) c := by
  have h1 := twAct_twU hm (F4Exc.uWord s j) _
    (p • F4Exc.f4Omega s - (2 : ℤ) ^ b • (Pi.single s 1 : Fin Tag.F4.rank → ℤ))
    (twU_start f hm s p lam hlam b)
  have h2 := twAct_twU hm (F4Exc.gamWord s i) _ _ h1
  have hfix : (F4Exc.uWord s j).foldr (reflect .F4) (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ) =
      Pi.single s 1 := by
    rw [← uF_smul]; exact (F4Exc.family_props s).1 j
  have e : (F4Exc.gamWord s i).foldr (reflect .F4) ((F4Exc.uWord s j).foldr (reflect .F4)
      (p • F4Exc.f4Omega s - (2 : ℤ) ^ b • (Pi.single s 1 : Fin Tag.F4.rank → ℤ))) =
      p • (F4Exc.wF s i • (F4Exc.uF s j • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ b • (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) := by
    rw [foldr_reflect_lin, foldr_reflect_lin, hfix, wF_smul, wF_smul, uF_smul]
  rw [e] at h2
  exact h2 c

theorem twExistsDigit_holds : TwExistsDigit := by
  intro f s hf hs J' hJ' hc
  obtain ⟨dg, hdg, hsep⟩ := F4Exc.exists_digit_fold hs hf J' hJ' hc
  refine ⟨dg, hdg, fun i i' hii j j' hdiv => ?_⟩
  refine hsep i i' hii j j' fun k => ?_
  have hm : ((((2 ^ f - 1 : ℕ)) : ℤ)) ∣ 2 ^ f - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; exact dvd_rfl
  set a : ℤ := ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) with ha
  have hlam : ∀ c : TwN, (((2 ^ f - 1 : ℕ)) : ℤ) ∣
      (if c = twNode s then a else 0) - a * (if c = twNode s then 1 else 0) := by
    intro c; split_ifs <;> simp
  have hz : ∀ c : TwN, (((2 ^ f - 1 : ℕ)) : ℤ) ∣ twU (
      (a • (F4Exc.wF s i • (F4Exc.uF s j • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ dg • (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))) -
      (a • (F4Exc.wF s i' • (F4Exc.uF s j' • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ dg • (F4Exc.wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)))) c := by
    intro c
    rw [twU_sub]
    have e1 := twV_dvd hm s a _ hlam dg i j c
    have e2 := twV_dvd hm s a _ hlam dg i' j' c
    have := dvd_sub (hdiv c) (dvd_sub e1 e2)
    convert this using 1
    ring
  have := dvd_of_dvd_twU _ hz k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

end Certs

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
