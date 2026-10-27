module

public import CFSG.ClassicalInvolution.Solomon73.SqrtFusion
public import CFSG.ClassicalInvolution.Solomon73.YamakiEnum
public import CFSG.ClassicalInvolution.Solomon73.YamakiModel
public import Certificates.Certificate550801

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

theorem countLt_eq_nat_card (n : ℕ) (p : ℕ → Bool) :
    countLt n p = Nat.card {i : Fin n // p i.val = true} := by
  have h1 : countLt n p = Nat.count (fun i => p i = true) n := by
    simp only [countLt, Nat.count, Bool.decide_eq_true]
  have h2 : Nat.count (fun i => p i = true) n = Nat.card {k : ℕ // k < n ∧ p k = true} :=
    (Nat.count_eq_card_fintype _ n).trans
      (@Fintype.card_eq_nat_card _ (Nat.CountSet.fintype (fun i => p i = true) n))
  rw [h1, h2]
  exact Nat.card_congr
    { toFun := fun k => ⟨⟨k.1, k.2.1⟩, k.2.2⟩
      invFun := fun i => ⟨i.1.val, i.1.2, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem mulEquiv_mem_center {P Q : Type*} [Group P] [Group Q] (φ : P ≃* Q) {z : P}
    (hz : z ∈ Subgroup.center P) : φ z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro q
  have h := congrArg φ (hz (φ.symm q))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

section Enum

variable {E : Enum} {gs : Array (Array ℕ)} {s : ℕ → StatedSp 3 (ZMod 2)}
  {L : Subgroup (StatedSp 3 (ZMod 2))}

theorem exists_equiv_fin_of_enumOK (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) :
    ∃ f : Fin E.elems.size ≃ ↥L, ∀ i, code (f i : StatedSp 3 (ZMod 2)) = E.elems[i.val]! := by
  subst hL
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  have hnodup : ∀ i < E.elems.size, E.lookup E.elems[i]! = some i := by
    simp only [enumOK, Bool.and_eq_true] at h
    simpa only [nodupOK, allLt_iff, decide_eq_true_eq] using h.2
  choose e he hec using exists_mem_closure_of_treeOK hgs htree
  have hbij : Function.Bijective fun i : Fin E.elems.size =>
      (⟨e i i.2, he i i.2⟩ : Subgroup.closure (s '' Set.Iio gs.size)) := by
    constructor
    · intro i j hij
      have hv : e i i.2 = e j j.2 := congrArg Subtype.val hij
      have hc : E.elems[i.val]! = E.elems[j.val]! := by
        rw [← hec i i.2, ← hec j j.2, hv]
      have h1 := hnodup i i.2
      rw [hc, hnodup j j.2] at h1
      exact Fin.ext (Option.some.inj h1).symm
    · intro x
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs h x.2)
      obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
      exact ⟨⟨k, hks⟩, Subtype.ext (code_injective ((hec k hks).trans hke))⟩
  exact ⟨Equiv.ofBijective _ hbij, fun i => hec i i.2⟩

theorem nat_card_subtype_eq_countLt (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) (p : Array ℕ → Bool) :
    Nat.card {x : ↥L // p (code x) = true} = countLt E.elems.size fun i => p E.elems[i]! := by
  obtain ⟨f, hf⟩ := exists_equiv_fin_of_enumOK hL hgs h
  rw [countLt_eq_nat_card]
  refine Nat.card_congr (Equiv.subtypeEquiv f fun i => ?_).symm
  rw [hf i]

theorem nat_card_sq_eq_sqCount (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) (x : ↥L) :
    Nat.card {y : ↥L // y ^ 2 = x} = sqCount E (code x) := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)).trans
    (nat_card_subtype_eq_countLt hL hgs h fun t => decide (compA t t = code x))
  show y ^ 2 = x ↔ decide (compA (code (y : StatedSp 3 (ZMod 2)))
    (code (y : StatedSp 3 (ZMod 2))) = code (x : StatedSp 3 (ZMod 2))) = true
  rw [decide_eq_true_iff, ← code_mul, ← Subgroup.coe_mul, ← pow_two]
  exact ⟨fun hy => by rw [hy], fun hy => Subtype.ext (code_injective hy)⟩

theorem commute_of_commOK (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) {a : Array ℕ} (hc : commOK gs a = true)
    {y : StatedSp 3 (ZMod 2)} (hy : code y = a) {x : StatedSp 3 (ZMod 2)} (hx : x ∈ L) :
    x * y = y * x := by
  subst hL
  have hgen : ∀ j < gs.size, s j * y = y * s j := by
    intro j hj
    simp only [commOK, allLt_iff, decide_eq_true_eq] at hc
    apply code_injective
    rw [code_mul, code_mul, hy, ← hgs j hj]
    exact (hc j hj).symm
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact hgen j hj
  | one => rw [one_mul, mul_one]
  | mul x z _ _ hx hz => exact Commute.mul_left hx hz
  | inv x _ hx => exact Commute.inv_left hx

theorem code_eq_of_centerOK (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) {a b : Array ℕ}
    (hc : centerOK E gs a b = true) {x : StatedSp 3 (ZMod 2)} (hx : x ∈ L)
    (hxs : ∀ j < gs.size, x * s j = s j * x) :
    code x = idA () ∨ code x = a ∨ code x = b ∨ code x = compA a b := by
  subst hL
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs h hx)
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  have hcomm : commOK gs E.elems[k]! = true := by
    simp only [commOK, allLt_iff, decide_eq_true_eq]
    intro j hj
    rw [hke, hgs j hj, ← code_mul, ← code_mul, hxs j hj]
  simp only [centerOK, allLt_iff] at hc
  have hk' := hc k hks
  rw [hcomm, hke] at hk'
  simpa only [Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] using hk'

end Enum

section Checks

theorem enumS0_ok_holds : enumOK (enumS0 ()) (gS0 ()) = true :=
  Certificates.certificate550801.1

theorem sqCount_one_holds : sqCount (enumS0 ()) (idA ()) = 144 :=
  Certificates.certificate550801.2.1

theorem sqCount_alpha_holds : sqCount (enumS0 ()) (genA ())[5]! = 0 :=
  Certificates.certificate550801.2.2.1

theorem sqCount_pi12_holds : sqCount (enumS0 ()) (genA ())[4]! = 48 :=
  Certificates.certificate550801.2.2.2.1

theorem sqCount_pi3_holds : sqCount (enumS0 ()) (compA (genA ())[5]! (genA ())[4]!) = 32 :=
  Certificates.certificate550801.2.2.2.2.1

theorem commOK_alpha_holds : commOK (gS0 ()) (genA ())[5]! = true :=
  Certificates.certificate550801.2.2.2.2.2.1

theorem commOK_pi12_holds : commOK (gS0 ()) (genA ())[4]! = true :=
  Certificates.certificate550801.2.2.2.2.2.2.1

theorem centerOK_S0_holds : centerOK (enumS0 ()) (gS0 ()) (genA ())[5]! (genA ())[4]! = true :=
  Certificates.certificate550801.2.2.2.2.2.2.2

end Checks

theorem size_gS0 : (gS0 ()).size = 9 := by
  simp only [gS0, Array.size_ofFn]

section Model

@[expose] def s0Gen (j : ℕ) : StatedSp 3 (ZMod 2) := if h : j < 12 then yamakiSp ⟨j, h⟩ else 1

theorem gS0_get : ∀ j < (gS0 ()).size, (gS0 ())[j]! = code (s0Gen j) := by
  intro j hj
  rw [size_gS0] at hj
  have h12 : j < 12 := by omega
  rw [s0Gen, dif_pos h12, code_yamakiSp]
  simp only [gS0]
  rw [getElem!_ofFn_nat _ hj]

theorem S0_eq_closure : S0 = Subgroup.closure (s0Gen '' Set.Iio (gS0 ()).size) := by
  rw [size_gS0, S0]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Iio]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, by omega, by rw [s0Gen, dif_pos i.2]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, show j ≤ 8 by omega, by rw [s0Gen, dif_pos (show j < 12 by omega)]⟩

private theorem code_alpha : code alpha = (genA ())[5]! := code_yamakiSp 5

private theorem code_pi12 : code pi12 = (genA ())[4]! := code_yamakiSp 4

private theorem code_pi3 : code pi3 = compA (genA ())[5]! (genA ())[4]! := by
  rw [pi3, code_mul, code_alpha, code_pi12]

end Model

section S0

theorem nat_card_sqrt_S0 (x : ↥S0) :
    Nat.card {y : ↥S0 // y ^ 2 = x} = sqCount (enumS0 ()) (code x) :=
  nat_card_sq_eq_sqCount S0_eq_closure gS0_get enumS0_ok_holds x

theorem nat_card_sqrt_one : Nat.card {s : ↥S0 // s ^ 2 = 1} = 144 := by
  rw [nat_card_sqrt_S0]
  show sqCount (enumS0 ()) (code 1) = 144
  rw [code_one]
  exact sqCount_one_holds

theorem nat_card_sqrt_alpha : Nat.card {s : ↥S0 // s ^ 2 = ⟨alpha, alpha_mem_S0⟩} = 0 := by
  rw [nat_card_sqrt_S0]
  show sqCount (enumS0 ()) (code alpha) = 0
  rw [code_alpha]
  exact sqCount_alpha_holds

theorem nat_card_sqrt_pi12 : Nat.card {s : ↥S0 // s ^ 2 = ⟨pi12, pi12_mem_S0⟩} = 48 := by
  rw [nat_card_sqrt_S0]
  show sqCount (enumS0 ()) (code pi12) = 48
  rw [code_pi12]
  exact sqCount_pi12_holds

theorem nat_card_sqrt_pi3 : Nat.card {s : ↥S0 // s ^ 2 = ⟨pi3, pi3_mem_S0⟩} = 32 := by
  rw [nat_card_sqrt_S0]
  show sqCount (enumS0 ()) (code pi3) = 32
  rw [code_pi3]
  exact sqCount_pi3_holds

theorem commute_alpha {h : StatedSp 3 (ZMod 2)} (hh : h ∈ S0) : h * alpha = alpha * h :=
  commute_of_commOK S0_eq_closure gS0_get commOK_alpha_holds code_alpha hh

theorem commute_pi12 {h : StatedSp 3 (ZMod 2)} (hh : h ∈ S0) : h * pi12 = pi12 * h :=
  commute_of_commOK S0_eq_closure gS0_get commOK_pi12_holds code_pi12 hh

theorem commute_pi3 {h : StatedSp 3 (ZMod 2)} (hh : h ∈ S0) : h * pi3 = pi3 * h := by
  rw [pi3]
  exact Commute.mul_right (commute_alpha hh) (commute_pi12 hh)

theorem eq_of_mem_center_S0 :
    ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3 := by
  intro g hg hc
  have hgen : ∀ j < (gS0 ()).size, g * s0Gen j = s0Gen j * g := fun j hj =>
    hc _ (by rw [S0_eq_closure]; exact Subgroup.subset_closure ⟨j, hj, rfl⟩)
  rcases code_eq_of_centerOK S0_eq_closure gS0_get enumS0_ok_holds centerOK_S0_holds hg hgen
    with h | h | h | h
  · exact Or.inl (code_injective (h.trans code_one.symm))
  · exact Or.inr (Or.inl (code_injective (h.trans code_alpha.symm)))
  · exact Or.inr (Or.inr (Or.inl (code_injective (h.trans code_pi12.symm))))
  · exact Or.inr (Or.inr (Or.inr (code_injective (h.trans code_pi3.symm))))

theorem mem_center_S0_iff (g : ↥S0) :
    g ∈ Subgroup.center ↥S0 ↔ (g : StatedSp 3 (ZMod 2)) = 1 ∨ (g : StatedSp 3 (ZMod 2)) = alpha ∨
      (g : StatedSp 3 (ZMod 2)) = pi12 ∨ (g : StatedSp 3 (ZMod 2)) = pi3 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hg
    refine eq_of_mem_center_S0 g g.2 fun h hh => ?_
    have e := congrArg Subtype.val (hg ⟨h, hh⟩)
    simp only [Subgroup.coe_mul] at e
    exact e.symm
  · intro hg h
    apply Subtype.ext
    show (h : StatedSp 3 (ZMod 2)) * g = g * h
    rcases hg with hg | hg | hg | hg <;> rw [hg]
    · rw [one_mul, mul_one]
    · exact commute_alpha h.2
    · exact commute_pi12 h.2
    · exact commute_pi3 h.2

theorem alpha_mem_center_S0 : (⟨alpha, alpha_mem_S0⟩ : ↥S0) ∈ Subgroup.center ↥S0 :=
  (mem_center_S0_iff _).mpr (Or.inr (Or.inl rfl))

theorem pi12_mem_center_S0 : (⟨pi12, pi12_mem_S0⟩ : ↥S0) ∈ Subgroup.center ↥S0 :=
  (mem_center_S0_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem pi3_mem_center_S0 : (⟨pi3, pi3_mem_S0⟩ : ↥S0) ∈ Subgroup.center ↥S0 :=
  (mem_center_S0_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem mem_center_S0_cases {c : ↥S0} (hc : c ∈ Subgroup.center ↥S0) :
    (c = 1 ∧ Nat.card {s : ↥S0 // s ^ 2 = c} = 144) ∨
      (c = ⟨alpha, alpha_mem_S0⟩ ∧ Nat.card {s : ↥S0 // s ^ 2 = c} = 0) ∨
      (c = ⟨pi12, pi12_mem_S0⟩ ∧ Nat.card {s : ↥S0 // s ^ 2 = c} = 48) ∨
      (c = ⟨pi3, pi3_mem_S0⟩ ∧ Nat.card {s : ↥S0 // s ^ 2 = c} = 32) := by
  rcases (mem_center_S0_iff c).mp hc with h | h | h | h
  · obtain rfl : c = 1 := Subtype.ext h
    exact Or.inl ⟨rfl, nat_card_sqrt_one⟩
  · obtain rfl : c = ⟨alpha, alpha_mem_S0⟩ := Subtype.ext h
    exact Or.inr (Or.inl ⟨rfl, nat_card_sqrt_alpha⟩)
  · obtain rfl : c = ⟨pi12, pi12_mem_S0⟩ := Subtype.ext h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, nat_card_sqrt_pi12⟩))
  · obtain rfl : c = ⟨pi3, pi3_mem_S0⟩ := Subtype.ext h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, nat_card_sqrt_pi3⟩))

theorem eq_of_nat_card_sqrt_eq {a b : ↥S0} (ha : a ∈ Subgroup.center ↥S0)
    (hb : b ∈ Subgroup.center ↥S0)
    (h : Nat.card {s : ↥S0 // s ^ 2 = a} = Nat.card {s : ↥S0 // s ^ 2 = b}) : a = b := by
  rcases mem_center_S0_cases ha with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
  rcases mem_center_S0_cases hb with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
  first
  | (rw [h1, h2] at h; omega)
  | rfl

theorem alpha_ne_pi12 : (⟨alpha, alpha_mem_S0⟩ : ↥S0) ≠ ⟨pi12, pi12_mem_S0⟩ := by
  intro h
  have e := nat_card_sqrt_alpha
  rw [h, nat_card_sqrt_pi12] at e
  omega

theorem alpha_ne_pi3 : (⟨alpha, alpha_mem_S0⟩ : ↥S0) ≠ ⟨pi3, pi3_mem_S0⟩ := by
  intro h
  have e := nat_card_sqrt_alpha
  rw [h, nat_card_sqrt_pi3] at e
  omega

theorem pi12_ne_pi3 : (⟨pi12, pi12_mem_S0⟩ : ↥S0) ≠ ⟨pi3, pi3_mem_S0⟩ := by
  intro h
  have e := nat_card_sqrt_pi12
  rw [h, nat_card_sqrt_pi3] at e
  omega

theorem mulEquiv_S0_apply_of_mem_center (φ : ↥S0 ≃* ↥S0) {z : ↥S0}
    (hz : z ∈ Subgroup.center ↥S0) : φ z = z :=
  (eq_of_nat_card_sqrt_eq hz (mulEquiv_mem_center φ hz) (nat_card_sq_congr φ z)).symm

theorem mulEquiv_S0_alpha (φ : ↥S0 ≃* ↥S0) : φ ⟨alpha, alpha_mem_S0⟩ = ⟨alpha, alpha_mem_S0⟩ :=
  mulEquiv_S0_apply_of_mem_center φ alpha_mem_center_S0

end S0

section Restrict

variable {G : Type*} [Group G]

@[expose] def mulEquivS0OfLe {K : Subgroup (StatedSp 3 (ZMod 2))} (hK : S0 ≤ K)
    {H P : Subgroup G} (θ : ↥H ≃* ↥K) (hPH : P ≤ H)
    (hθP : ∀ x (hx : x ∈ H), x ∈ P ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) :
    ↥P ≃* ↥S0 where
  toFun t := ⟨θ ⟨t, hPH t.2⟩, (hθP t (hPH t.2)).mp t.2⟩
  invFun s := ⟨θ.symm ⟨s, hK s.2⟩, (hθP _ (θ.symm ⟨s, hK s.2⟩).2).mpr (by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact s.2)⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  map_mul' a b := by
    apply Subtype.ext
    show ((θ ⟨(a * b : ↥P), hPH (a * b).2⟩ : ↥K) : StatedSp 3 (ZMod 2)) =
      ((θ ⟨a, hPH a.2⟩ * θ ⟨b, hPH b.2⟩ : ↥K) : StatedSp 3 (ZMod 2))
    have e : (⟨(a * b : ↥P), hPH (a * b).2⟩ : ↥H) = ⟨a, hPH a.2⟩ * ⟨b, hPH b.2⟩ :=
      Subtype.ext rfl
    rw [e, map_mul]

@[simp] theorem coe_mulEquivS0OfLe_apply {K : Subgroup (StatedSp 3 (ZMod 2))} (hK : S0 ≤ K)
    {H P : Subgroup G} (θ : ↥H ≃* ↥K) (hPH : P ≤ H)
    (hθP : ∀ x (hx : x ∈ H), x ∈ P ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) (t : ↥P) :
    ((mulEquivS0OfLe hK θ hPH hθP t : ↥S0) : StatedSp 3 (ZMod 2)) = θ ⟨t, hPH t.2⟩ :=
  rfl

@[simp] theorem coe_mulEquivS0OfLe_symm_apply {K : Subgroup (StatedSp 3 (ZMod 2))}
    (hK : S0 ≤ K) {H P : Subgroup G} (θ : ↥H ≃* ↥K) (hPH : P ≤ H)
    (hθP : ∀ x (hx : x ∈ H), x ∈ P ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) (s : ↥S0) :
    (((mulEquivS0OfLe hK θ hPH hθP).symm s : ↥P) : G) = θ.symm ⟨s, hK s.2⟩ :=
  rfl

end Restrict

section Sylow

variable {G : Type*} [Group G]

theorem eq_of_isConj_of_mem_center [Finite G] (T : Sylow 2 G) (φ : ↥(T : Subgroup G) ≃* ↥S0)
    {x y : G} (hxT : x ∈ (T : Subgroup G)) (hx : ∀ t ∈ (T : Subgroup G), t * x = x * t)
    (hyT : y ∈ (T : Subgroup G)) (hy : ∀ t ∈ (T : Subgroup G), t * y = y * t)
    (hxy : IsConj x y) : x = y := by
  have hcx : x ∈ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr hx
  have hcy : y ∈ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr hy
  have hzx : (⟨x, hxT⟩ : ↥(T : Subgroup G)) ∈ Subgroup.center ↥(T : Subgroup G) :=
    Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hx t t.2)
  have hzy : (⟨y, hyT⟩ : ↥(T : Subgroup G)) ∈ Subgroup.center ↥(T : Subgroup G) :=
    Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hy t t.2)
  have hcount : Nat.card {s : ↥S0 // s ^ 2 = φ ⟨x, hxT⟩} =
      Nat.card {s : ↥S0 // s ^ 2 = φ ⟨y, hyT⟩} :=
    (nat_card_sq_congr φ ⟨x, hxT⟩).symm.trans <|
      (nat_card_sq_subtype (T : Subgroup G) ⟨x, hxT⟩).symm.trans <|
        (nat_card_sq_eq_of_isConj T hcx hcy hxy).trans <|
          (nat_card_sq_subtype (T : Subgroup G) ⟨y, hyT⟩).trans (nat_card_sq_congr φ ⟨y, hyT⟩)
  have e := eq_of_nat_card_sqrt_eq (mulEquiv_mem_center φ hzx) (mulEquiv_mem_center φ hzy) hcount
  exact congrArg Subtype.val (φ.injective e)

theorem not_isConj_symm_of_mem_center [Finite G] (T : Sylow 2 G)
    (φ : ↥(T : Subgroup G) ≃* ↥S0) {a b : ↥S0} (ha : a ∈ Subgroup.center ↥S0)
    (hb : b ∈ Subgroup.center ↥S0) (hab : a ≠ b) : ¬ IsConj (φ.symm a : G) (φ.symm b : G) := by
  intro h
  have hza := mulEquiv_mem_center φ.symm ha
  have hzb := mulEquiv_mem_center φ.symm hb
  rw [Subgroup.mem_center_iff] at hza hzb
  exact hab (φ.symm.injective (Subtype.ext (eq_of_isConj_of_mem_center T φ (φ.symm a).2
    (fun t ht => congrArg Subtype.val (hza ⟨t, ht⟩)) (φ.symm b).2
    (fun t ht => congrArg Subtype.val (hzb ⟨t, ht⟩)) h)))

theorem not_isConj_symm_of_le [Finite G] (T : Sylow 2 G) {K : Subgroup (StatedSp 3 (ZMod 2))}
    (hK : S0 ≤ K) {H : Subgroup G} (θ : ↥H ≃* ↥K) (hTH : (T : Subgroup G) ≤ H)
    (hθT : ∀ x (hx : x ∈ H),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0)
    {a b : ↥S0} (ha : a ∈ Subgroup.center ↥S0) (hb : b ∈ Subgroup.center ↥S0) (hab : a ≠ b) :
    ¬ IsConj (θ.symm ⟨a, hK a.2⟩ : G) (θ.symm ⟨b, hK b.2⟩ : G) :=
  not_isConj_symm_of_mem_center T (mulEquivS0OfLe hK θ hTH hθT) ha hb hab

theorem not_isConj_symm_alpha_pi12 [Finite G] (T : Sylow 2 G)
    {K : Subgroup (StatedSp 3 (ZMod 2))} (hK : S0 ≤ K) {H : Subgroup G} (θ : ↥H ≃* ↥K)
    (hTH : (T : Subgroup G) ≤ H)
    (hθT : ∀ x (hx : x ∈ H),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) :
    ¬ IsConj (θ.symm ⟨alpha, hK alpha_mem_S0⟩ : G) (θ.symm ⟨pi12, hK pi12_mem_S0⟩ : G) :=
  not_isConj_symm_of_le T hK θ hTH hθT alpha_mem_center_S0 pi12_mem_center_S0 alpha_ne_pi12

theorem not_isConj_symm_alpha_pi3 [Finite G] (T : Sylow 2 G)
    {K : Subgroup (StatedSp 3 (ZMod 2))} (hK : S0 ≤ K) {H : Subgroup G} (θ : ↥H ≃* ↥K)
    (hTH : (T : Subgroup G) ≤ H)
    (hθT : ∀ x (hx : x ∈ H),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) :
    ¬ IsConj (θ.symm ⟨alpha, hK alpha_mem_S0⟩ : G) (θ.symm ⟨pi3, hK pi3_mem_S0⟩ : G) :=
  not_isConj_symm_of_le T hK θ hTH hθT alpha_mem_center_S0 pi3_mem_center_S0 alpha_ne_pi3

theorem not_isConj_symm_pi12_pi3 [Finite G] (T : Sylow 2 G)
    {K : Subgroup (StatedSp 3 (ZMod 2))} (hK : S0 ≤ K) {H : Subgroup G} (θ : ↥H ≃* ↥K)
    (hTH : (T : Subgroup G) ≤ H)
    (hθT : ∀ x (hx : x ∈ H),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥K) : StatedSp 3 (ZMod 2)) ∈ S0) :
    ¬ IsConj (θ.symm ⟨pi12, hK pi12_mem_S0⟩ : G) (θ.symm ⟨pi3, hK pi3_mem_S0⟩ : G) :=
  not_isConj_symm_of_le T hK θ hTH hθT pi12_mem_center_S0 pi3_mem_center_S0 pi12_ne_pi3

theorem not_isConj_hhat_symm_pi12_pi3 [Finite G] (T : Sylow 2 G) {H : Subgroup G}
    (θ : ↥H ≃* ↥Hhat) (hTH : (T : Subgroup G) ≤ H)
    (hθT : ∀ x (hx : x ∈ H),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0) :
    ¬ IsConj (θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : G)
      (θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ : G) :=
  not_isConj_symm_pi12_pi3 T S0_le_Hhat θ hTH hθT

end Sylow

end CFSG.ClassicalInvolution.Solomon73.Yamaki
