module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def E7ThreeRow : Prop :=
  ∀ (X : Type) [Group X], Blueprint.LieModel X .E7 0 3 1 →
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃*
        Blueprint.Multiplier.generic .E7 0 3 1 × Blueprint.Multiplier.exceptional .E7 0 3 1)

private lemma eq_one_of_sq_eq_one_of_odd_natCard {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {z : G} (hz : z ^ 2 = 1) : z = 1 := by
  have h2 : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    have hdiv : orderOf z ∣ Nat.card G := orderOf_dvd_natCard z
    rw [h] at hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)

private lemma sq_eq_one_zmod_of_dvd_two {a : ℕ} (ha : a ∣ 2) (z : Multiplicative (ZMod a)) :
    z ^ 2 = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp ha with rfl | rfl
  · exact Subsingleton.elim _ _
  · revert z; decide

private lemma eq_one_zmod_of_sq_eq_one_odd {e : ℕ} (he : Odd e)
    {z : Multiplicative (ZMod e)} (hz : z ^ 2 = 1) : z = 1 := by
  have hodd : Odd (Nat.card (Multiplicative (ZMod e))) := by
    show Odd (Nat.card (ZMod e))
    rw [Nat.card_zmod]
    exact he
  exact eq_one_of_sq_eq_one_of_odd_natCard hodd hz

private lemma eq_of_orderOf_eq_two_zmod {g : ℕ} [NeZero g] {a b : Multiplicative (ZMod g)}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have hd : 2 ∣ Fintype.card (Multiplicative (ZMod g)) := by
    rw [← ha]
    simpa using orderOf_dvd_natCard a
  have hcount := IsCyclic.card_orderOf_eq_totient (α := Multiplicative (ZMod g)) (d := 2) hd
  rw [Nat.totient_two] at hcount
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcount
  have ha' : a ∈ Finset.univ.filter (fun x : Multiplicative (ZMod g) => orderOf x = 2) := by
    simp [ha]
  have hb' : b ∈ Finset.univ.filter (fun x : Multiplicative (ZMod g) => orderOf x = 2) := by
    simp [hb]
  rw [hc, Finset.mem_singleton] at ha' hb'
  rw [ha', hb']

private lemma orderOf_eq_two_of_sq_eq_one_of_ne_one {G : Type*} [Group G] {a : G}
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) : orderOf a = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr ha) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1
  · exact h

private lemma prod_eq_one_of_sq_eq_one {M N : Type*} [Group M] [Group N]
    (hM : ∀ z : M, z ^ 2 = 1 → z = 1) (hN : ∀ z : N, z ^ 2 = 1 → z = 1)
    {z : M × N} (hz : z ^ 2 = 1) : z = 1 :=
  Prod.ext (hM z.1 (by simpa using congrArg Prod.fst hz))
    (hN z.2 (by simpa using congrArg Prod.snd hz))

private lemma sq_eq_one_of_orders {a₁ a₂ b₁ b₂ : ℕ}
    (h : a₁ ∣ 2 ∧ a₂ ∣ 2 ∧ b₁ ∣ 2 ∧ b₂ ∣ 2)
    (z : (Multiplicative (ZMod a₁) × Multiplicative (ZMod a₂)) ×
         (Multiplicative (ZMod b₁) × Multiplicative (ZMod b₂))) : z ^ 2 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp only [map_pow, Prod.fst_one, Prod.snd_one]
  · exact sq_eq_one_zmod_of_dvd_two h1 _
  · exact sq_eq_one_zmod_of_dvd_two h2 _
  · exact sq_eq_one_zmod_of_dvd_two h3 _
  · exact sq_eq_one_zmod_of_dvd_two h4 _

private lemma eq_mk_one_of_sq_eq_one_fst_zmod {g e₁ e₂ : ℕ} (hodd : Odd (e₁ * e₂))
    {z : (Multiplicative (ZMod g) × Multiplicative (ZMod 1)) ×
         (Multiplicative (ZMod e₁) × Multiplicative (ZMod e₂))}
    (hz : z ^ 2 = 1) : z = ((z.1.1, 1), 1) := by
  have hzE : z.2 = 1 :=
    prod_eq_one_of_sq_eq_one
      (fun w hw => eq_one_zmod_of_sq_eq_one_odd (Nat.odd_mul.mp hodd).1 hw)
      (fun w hw => eq_one_zmod_of_sq_eq_one_odd (Nat.odd_mul.mp hodd).2 hw)
      (by simpa using congrArg Prod.snd hz)
  have hzB : z.1.2 = 1 := Subsingleton.elim _ _
  rw [show z = ((z.1.1, z.1.2), z.2) from rfl, hzB, hzE]

private lemma unique_of_prod {X : Type} [Group X] {g e₁ e₂ : ℕ} [NeZero g]
    (hodd : Odd (e₁ * e₂))
    (e : griessHopfMultiplier X ≃*
      (Multiplicative (ZMod g) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod e₁) × Multiplicative (ZMod e₂))) :
    ∀ x y : griessHopfMultiplier X, orderOf x = 2 → orderOf y = 2 → x = y := by
  intro x y hx hy
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hex2 : e x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hey2 : e y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hxshape := eq_mk_one_of_sq_eq_one_fst_zmod hodd hex2
  have hyshape := eq_mk_one_of_sq_eq_one_fst_zmod hodd hey2
  have hxne1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; omega
  have hyne1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy; omega
  have hexne : e x ≠ 1 := fun h => hxne1 (e.injective (by rw [h, map_one]))
  have heyne : e y ≠ 1 := fun h => hyne1 (e.injective (by rw [h, map_one]))
  have ha1 : (e x).1.1 ≠ 1 := fun h => hexne (by rw [hxshape, h]; rfl)
  have hb1 : (e y).1.1 ≠ 1 := fun h => heyne (by rw [hyshape, h]; rfl)
  have ha2 : (e x).1.1 ^ 2 = 1 := by
    simpa using congrArg (fun w => w.1.1) hex2
  have hb2 : (e y).1.1 ^ 2 = 1 := by
    simpa using congrArg (fun w => w.1.1) hey2
  have haa : (e x).1.1 = (e y).1.1 :=
    eq_of_orderOf_eq_two_zmod (orderOf_eq_two_of_sq_eq_one_of_ne_one ha2 ha1)
      (orderOf_eq_two_of_sq_eq_one_of_ne_one hb2 hb1)
  exact e.injective (by rw [hxshape, hyshape, haa])

theorem unique_involution_of_psl_psu
    (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    {τ : StatedLieTag} {m k : ℕ} (hτ : τ = .PSL ∨ τ = .PSU) (hm : 0 < m)
    (hX : Blueprint.LieModel X τ (2 * m) 3 k) :
    ∀ x y : griessHopfMultiplier X, orderOf x = 2 → orderOf y = 2 → x = y := by
  have hm' : 2 * m ≠ 0 := by omega
  obtain ⟨-, ⟨e⟩⟩ := hGA X τ (2 * m) 3 k
    (ComponentClassification.HarrisLit.models_lieModel_of_lieModel_of_ne_zero hm' hX)
  rcases hτ with rfl | rfl
  · haveI : NeZero (Blueprint.Multiplier.genericOrders .PSL (2 * m) 3 k).1 := by
      rw [show Blueprint.Multiplier.genericOrders .PSL (2 * m) 3 k =
        (Nat.gcd (2 * m) (3 ^ k - 1), 1) from rfl]
      exact ⟨(Nat.gcd_pos_of_pos_left (m := 2 * m) (3 ^ k - 1) (by omega)).ne'⟩
    exact unique_of_prod (e := e)
      (ComponentClassification.HarrisLit.odd_exceptionalOrders_psl (p := 3) (by norm_num))
  · haveI : NeZero (Blueprint.Multiplier.genericOrders .PSU (2 * m) 3 k).1 := by
      rw [show Blueprint.Multiplier.genericOrders .PSU (2 * m) 3 k =
        (Nat.gcd (2 * m) (3 ^ k + 1), 1) from rfl]
      exact ⟨(Nat.gcd_pos_of_pos_left (m := 2 * m) (3 ^ k + 1) (by omega)).ne'⟩
    exact unique_of_prod (e := e)
      (ComponentClassification.HarrisLit.odd_exceptionalOrders_psu (p := 3) (by norm_num))

private lemma genericOrders_PSp (n : ℕ) :
    Blueprint.Multiplier.genericOrders .PSp n 3 1 = (2, 1) := rfl

private lemma exceptionalOrders_PSp (n : ℕ) :
    Blueprint.Multiplier.exceptionalOrders .PSp n 3 1 = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders; split <;> first | decide | simp_all

private lemma genericOrders_POmegaPlus_four :
    Blueprint.Multiplier.genericOrders .POmegaPlus 4 3 1 = (2, 2) := rfl

private lemma genericOrders_POmegaPlus_six :
    Blueprint.Multiplier.genericOrders .POmegaPlus 6 3 1 = (2, 2) := rfl

private lemma exceptionalOrders_POmegaPlus_four :
    Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 3 1 = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders; split <;> first | decide | simp_all

private lemma exceptionalOrders_POmegaPlus_six :
    Blueprint.Multiplier.exceptionalOrders .POmegaPlus 6 3 1 = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders; split <;> first | decide | simp_all

private lemma genericOrders_E7 :
    Blueprint.Multiplier.genericOrders .E7 0 3 1 = (2, 1) := rfl

private lemma exceptionalOrders_E7 :
    Blueprint.Multiplier.exceptionalOrders .E7 0 3 1 = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders; split <;> first | decide | simp_all

theorem sq_eq_one_of_shape (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE7 : E7ThreeRow) {Q : Type} [Group Q] {τ : StatedLieTag} {n : ℕ}
    (hm : Blueprint.LieModel Q τ n 3 1)
    (hτ : (τ = .PSp ∧ 2 ≤ n) ∨ (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7) :
    ∀ m : griessHopfMultiplier Q, m ^ 2 = 1 := by
  rcases hτ with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl
  · obtain ⟨-, ⟨e⟩⟩ := hGA Q .PSp n 3 1
      (ComponentClassification.HarrisLit.models_lieModel_of_lieModel_of_ne_zero
        (by omega : n ≠ 0) hm)
    intro m
    have hm2 : (e m) ^ 2 = 1 := by
      refine sq_eq_one_of_orders ?_ (e m)
      rw [genericOrders_PSp n, exceptionalOrders_PSp n]
      norm_num
    exact e.injective (by rw [map_pow, hm2, map_one])
  · rcases hn with rfl | rfl
    · obtain ⟨-, ⟨e⟩⟩ := hGA Q .POmegaPlus 4 3 1
        (ComponentClassification.HarrisLit.models_lieModel_of_lieModel_of_ne_zero
          (by omega : (4 : ℕ) ≠ 0) hm)
      intro m
      have hm2 : (e m) ^ 2 = 1 := by
        refine sq_eq_one_of_orders ?_ (e m)
        rw [genericOrders_POmegaPlus_four, exceptionalOrders_POmegaPlus_four]
        norm_num
      exact e.injective (by rw [map_pow, hm2, map_one])
    · obtain ⟨-, ⟨e⟩⟩ := hGA Q .POmegaPlus 6 3 1
        (ComponentClassification.HarrisLit.models_lieModel_of_lieModel_of_ne_zero
          (by omega : (6 : ℕ) ≠ 0) hm)
      intro m
      have hm2 : (e m) ^ 2 = 1 := by
        refine sq_eq_one_of_orders ?_ (e m)
        rw [genericOrders_POmegaPlus_six, exceptionalOrders_POmegaPlus_six]
        norm_num
      exact e.injective (by rw [map_pow, hm2, map_one])
  · have hn0 : n = 0 := by
      rcases hm with ⟨hcl, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact absurd hcl (by decide)
      · exact h0
      · exact h0
      · exact h0
    obtain ⟨-, ⟨e⟩⟩ := hE7 Q (hn0 ▸ hm)
    intro m
    have hm2 : (e m) ^ 2 = 1 := by
      refine sq_eq_one_of_orders ?_ (e m)
      rw [genericOrders_E7, exceptionalOrders_E7]
      norm_num
    exact e.injective (by rw [map_pow, hm2, map_one])

end CFSG.OddStandard.HigherRank.F3.Ident
