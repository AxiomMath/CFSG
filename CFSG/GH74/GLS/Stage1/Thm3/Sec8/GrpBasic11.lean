module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

namespace DihedralPres

section Presentation

variable {Q : Type*} [Group Q] {n : ℕ} [NeZero n] {ρ σ : Q}

@[expose] def zmodPow (ρ : Q) (n : ℕ) (i : ZMod n) : Q := ρ ^ i.val

omit [NeZero n] in
theorem zmodPow_zero : zmodPow ρ n 0 = 1 := by
  simp [zmodPow]

theorem zmodPow_add (hρ : ρ ^ n = 1) (i j : ZMod n) :
    zmodPow ρ n (i + j) = zmodPow ρ n i * zmodPow ρ n j := by
  unfold zmodPow
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hρ, pow_add]

theorem zmodPow_neg (hρ : ρ ^ n = 1) (i : ZMod n) : zmodPow ρ n (-i) = (zmodPow ρ n i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← zmodPow_add hρ, neg_add_cancel, zmodPow_zero]

omit [NeZero n] in
theorem zmodPow_one (hρ : ρ ^ n = 1) : zmodPow ρ n 1 = ρ := by
  unfold zmodPow
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hρ, pow_one]

theorem pow_mul_comm_σ (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹) (k : ℕ) :
    ρ ^ k * σ = σ * (ρ ^ k)⁻¹ := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h1 : σ * ρ ^ k * σ = (ρ ^ k)⁻¹ := by
    have := map_pow (MulAut.conj σ) ρ k
    simp only [MulAut.conj_apply, hc, inv_pow] at this
    rwa [hσi] at this
  calc ρ ^ k * σ = (σ * σ) * ρ ^ k * σ := by rw [hσ, one_mul]
    _ = σ * (σ * ρ ^ k * σ) := by group
    _ = σ * (ρ ^ k)⁻¹ := by rw [h1]

theorem zmodPow_mul_comm_σ (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (i : ZMod n) : zmodPow ρ n i * σ = σ * zmodPow ρ n (-i) := by
  rw [zmodPow_neg hρ]
  exact pow_mul_comm_σ hσ hc _

@[expose] def dihedralHom (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹) :
    DihedralGroup n →* Q :=
  MonoidHom.mk' (fun x => match x with
    | DihedralGroup.r i => zmodPow ρ n i
    | DihedralGroup.sr i => σ * zmodPow ρ n i) (by
    intro a b
    rcases a with i | i <;> rcases b with j | j
    · rw [DihedralGroup.r_mul_r]
      exact zmodPow_add hρ i j
    · rw [DihedralGroup.r_mul_sr]
      show σ * zmodPow ρ n (j - i) = zmodPow ρ n i * (σ * zmodPow ρ n j)
      rw [← mul_assoc, zmodPow_mul_comm_σ hρ hσ hc, mul_assoc, ← zmodPow_add hρ,
        show -i + j = j - i by abel]
    · rw [DihedralGroup.sr_mul_r]
      show σ * zmodPow ρ n (i + j) = σ * zmodPow ρ n i * zmodPow ρ n j
      rw [mul_assoc, ← zmodPow_add hρ]
    · rw [DihedralGroup.sr_mul_sr]
      show zmodPow ρ n (j - i) = σ * zmodPow ρ n i * (σ * zmodPow ρ n j)
      calc zmodPow ρ n (j - i) = (σ * σ) * zmodPow ρ n (-i + j) := by
            rw [hσ, one_mul, show -i + j = j - i by abel]
        _ = σ * (σ * zmodPow ρ n (-i)) * zmodPow ρ n j := by
            rw [zmodPow_add hρ]; group
        _ = σ * (zmodPow ρ n i * σ) * zmodPow ρ n j := by
            rw [zmodPow_mul_comm_σ hρ hσ hc]
        _ = σ * zmodPow ρ n i * (σ * zmodPow ρ n j) := by group)

@[simp] theorem dihedralHom_r (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (i : ZMod n) : dihedralHom hρ hσ hc (DihedralGroup.r i) = zmodPow ρ n i := rfl

@[simp] theorem dihedralHom_sr (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (i : ZMod n) : dihedralHom hρ hσ hc (DihedralGroup.sr i) = σ * zmodPow ρ n i := rfl

theorem dihedral_mulEquiv (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hgen : closure {ρ, σ} = ⊤) (hcard : Nat.card Q = 2 * n) :
    Nonempty (DihedralGroup n ≃* Q) := by
  have hfin : Finite Q :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact mul_ne_zero two_ne_zero (NeZero.ne n))
  have hsurj : Function.Surjective (dihedralHom hρ hσ hc) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨DihedralGroup.r 1, by rw [dihedralHom_r, zmodPow_one hρ]⟩
    · exact ⟨DihedralGroup.sr 0, by rw [dihedralHom_sr, zmodPow_zero, mul_one]⟩
  have hbij : Function.Bijective (dihedralHom hρ hσ hc) :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, DihedralGroup.nat_card])
  exact ⟨MulEquiv.ofBijective _ hbij⟩

end Presentation

theorem dihedral3_mulEquiv_perm : Nonempty (DihedralGroup 3 ≃* Equiv.Perm (Fin 3)) := by
  refine dihedral_mulEquiv (ρ := finRotate 3) (σ := Equiv.swap (0 : Fin 3) 1) ?_ ?_ ?_ ?_ ?_
  · decide
  · exact Equiv.swap_mul_self _ _
  · decide
  · have := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 3)
      (isCycle_finRotate (n := 1)) (support_finRotate (n := 1)) 0
    have h0 : (finRotate 3) 0 = 1 := by decide
    rwa [h0] at this
  · rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]

section Quotient

variable {G : Type*} [Group G]

theorem eq_top_of_le_map {X : Subgroup G} (S : Subgroup ↥X) (hS : X ≤ S.map X.subtype) : S = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hS y.2
  have : z = y := Subtype.ext hzy
  rwa [this] at hz

theorem card_mul_card_quotient {X K : Subgroup G} (hKX : K ≤ X) :
    Nat.card ↥K * Nat.card (↥X ⧸ K.subgroupOf X) = Nat.card ↥X := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf X)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv] at h1

theorem quotient_dihedral_mulEquiv {X K : Subgroup G} [hK : (K.subgroupOf X).Normal] {n : ℕ} [NeZero n]
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) (han : a ^ n ∈ K) (hb2 : b * b = 1)
    (hab : b * a * b⁻¹ = a⁻¹)
    (hgen : ∀ S : Subgroup ↥X, (⟨a, ha⟩ : ↥X) ∈ S → (⟨b, hb⟩ : ↥X) ∈ S → K.subgroupOf X ≤ S →
      S = ⊤)
    (hcard : Nat.card (↥X ⧸ K.subgroupOf X) = 2 * n) :
    Nonempty (DihedralGroup n ≃* (↥X ⧸ K.subgroupOf X)) := by
  refine dihedral_mulEquiv (ρ := (QuotientGroup.mk ⟨a, ha⟩ : ↥X ⧸ K.subgroupOf X))
    (σ := (QuotientGroup.mk ⟨b, hb⟩ : ↥X ⧸ K.subgroupOf X)) ?_ ?_ ?_ ?_ hcard
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact han
  · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show b * b ∈ K
    rw [hb2]
    exact one_mem K
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hab
  · set C : Subgroup (↥X ⧸ K.subgroupOf X) :=
      closure {(QuotientGroup.mk ⟨a, ha⟩ : ↥X ⧸ K.subgroupOf X), QuotientGroup.mk ⟨b, hb⟩} with hC
    have hS : C.comap (QuotientGroup.mk' (K.subgroupOf X)) = ⊤ := by
      apply hgen
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · intro x hx
        show QuotientGroup.mk' (K.subgroupOf X) x ∈ C
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
        exact one_mem _
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have : x ∈ C.comap (QuotientGroup.mk' (K.subgroupOf X)) := by rw [hS]; trivial
    exact this

end Quotient

end DihedralPres

namespace SigmaDihedral

section Concrete

variable {G : Type*} [Group G]

theorem mul_self_ne_one {h : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1)) : h * h ≠ 1 := by
  intro h1
  have h2 : h ^ 2 = 1 := by rw [pow_two]; exact h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 3 ^ 1 ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ne_one_of_inv {h t : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1)) (hth : t * h * t⁻¹ = h⁻¹) :
    t ≠ 1 := by
  intro h1
  rw [h1] at hth
  apply mul_self_ne_one hord
  have : h = h⁻¹ := by simpa using hth
  exact mul_eq_one_iff_eq_inv.2 this

theorem zpowers_inf_zpowers_eq_bot {h t : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1))
    (ht2 : t * t = 1) (hth : t * h * t⁻¹ = h⁻¹) : zpowers h ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases (mem_zpowers_of_sq' ht2).1 hx.2 with h1 | h1
  · rw [h1]
    exact one_mem _
  · exfalso
    have hth' : t ∈ zpowers h := h1 ▸ hx.1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hth'
    have hcomm : h * t = t * h := by
      rw [← hi]
      exact ((Commute.refl h).zpow_right i).eq
    have e1 : t * h * t⁻¹ = h := by
      rw [← hcomm]
      group
    rw [e1] at hth
    exact mul_self_ne_one hord (mul_eq_one_iff_eq_inv.2 hth)

theorem card_zpowers_sup_zpowers {h t : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1))
    (ht2 : t * t = 1) (hth : t * h * t⁻¹ = h⁻¹) :
    Nat.card ↥(zpowers h ⊔ zpowers t) = 2 * 3 ^ (m + 1) := by
  have h1 := card_sup_mul_card_inf' (A := zpowers h) (B := zpowers t)
    (zpowers_t_le_normalizer ht2 hth)
  rw [zpowers_inf_zpowers_eq_bot hord ht2 hth, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    Nat.card_zpowers, hord,
    orderOf_eq_prime (by rw [pow_two]; exact ht2) (ne_one_of_inv hord hth)] at h1
  omega

theorem card_zpowers_pow_three {h : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1)) :
    Nat.card ↥(zpowers (h ^ 3)) = 3 ^ m := by
  rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hord]; exact dvd_pow_self 3 (by omega)),
    hord, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem mem_normalizer_zpowers_pow {h g : G}
    (hg : g * h * g⁻¹ = h ∨ g * h * g⁻¹ = h⁻¹) (k : ℕ) :
    g ∈ normalizer ((zpowers (h ^ k) : Subgroup G) : Set G) := by
  have key : ∀ g : G, (g * h * g⁻¹ = h ∨ g * h * g⁻¹ = h⁻¹) →
      ∀ x ∈ zpowers (h ^ k), g * x * g⁻¹ ∈ zpowers (h ^ k) := by
    intro g hg x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 : g * (h ^ k) ^ i * g⁻¹ = ((g * h * g⁻¹) ^ k) ^ i := by
      simp
    rw [h1]
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i
    · rw [hg, inv_pow]
      exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers _)) i
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have hg' : g⁻¹ * h * g⁻¹⁻¹ = h ∨ g⁻¹ * h * g⁻¹⁻¹ = h⁻¹ := by
    rw [inv_inv]
    rcases hg with hg | hg
    · left
      calc g⁻¹ * h * g = g⁻¹ * (g * h * g⁻¹) * g := by rw [hg]
        _ = h := by group
    · right
      have h2 : g⁻¹ * h⁻¹ * g = h := by
        calc g⁻¹ * h⁻¹ * g = g⁻¹ * (g * h * g⁻¹) * g := by rw [hg]
          _ = h := by group
      calc g⁻¹ * h * g = (g⁻¹ * h⁻¹ * g)⁻¹ := by group
        _ = h⁻¹ := by rw [h2]
  have h3 := key g⁻¹ hg' _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h3

theorem card_zpowers_sup_zpowers_klein {t w : G} (ht2 : t * t = 1) (hw2 : w * w = 1)
    (htw : t * w = w * t) (ht1 : t ≠ 1) (hw1 : w ≠ 1) (hwt : w ≠ t) :
    Nat.card ↥(zpowers t ⊔ zpowers w) = 4 := by
  have hc : ∀ a ∈ zpowers t, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute t w from htw) i j).eq
  have h1 := card_sup_mul_card_inf' (A := zpowers t) (B := zpowers w) (le_normalizer_of_commute' hc)
  have hbot : zpowers t ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases (mem_zpowers_of_sq' ht2).1 hx.1 with h2 | h2
    · rw [h2]
      exact one_mem _
    · exfalso
      rcases (mem_zpowers_of_sq' hw2).1 hx.2 with h3 | h3
      · exact ht1 (h2.symm.trans h3)
      · exact hwt (h3.symm.trans h2)
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1,
    orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1] at h1
  omega

theorem card_zpowers_sup_klein {h t w : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1))
    (ht2 : t * t = 1) (hw2 : w * w = 1) (hth : t * h * t⁻¹ = h⁻¹) (hwh : w * h = h * w)
    (htw : t * w = w * t) (hw1 : w ≠ 1) (hwt : w ≠ t)
    (hint : ∀ x ∈ zpowers h, x ∈ zpowers t ⊔ zpowers w → x = 1) :
    Nat.card ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)) = 4 * 3 ^ (m + 1) := by
  have hnorm : zpowers t ⊔ zpowers w ≤ normalizer ((zpowers h : Subgroup G) : Set G) := by
    apply sup_le
    · exact zpowers_t_le_normalizer ht2 hth
    · apply le_normalizer_of_commute'
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute h w from hwh.symm) i j).eq
  have h1 := card_sup_mul_card_inf' (A := zpowers h) (B := zpowers t ⊔ zpowers w) hnorm
  have hbot : zpowers h ⊓ (zpowers t ⊔ zpowers w) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).2 (hint x hx.1 hx.2)
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord,
    card_zpowers_sup_zpowers_klein ht2 hw2 htw (ne_one_of_inv hord hth) hw1 hwt] at h1
  omega

end Concrete

section TwoPower

theorem dvd_sq_sub_one_of_dvd_pow_two_pow_sub_one {m e : ℕ} {j : ℤ}
    (hj : ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j ^ (2 ^ e) - 1) : ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j ^ 2 - 1 := by
  have : NeZero (3 ^ (m + 1)) := ⟨by positivity⟩
  have h1 : ((j : ZMod (3 ^ (m + 1))) ^ (2 ^ e)) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ (2 ^ e) - 1) (3 ^ (m + 1))).2 hj
    push_cast at this
    exact sub_eq_zero.1 this
  let x : (ZMod (3 ^ (m + 1)))ˣ := Units.ofPowEqOne _ (2 ^ e) h1 (by positivity)
  have hx : x ^ (2 ^ e) = 1 := Units.pow_ofPowEqOne h1 (by positivity)
  have hx2 : x ^ (Nat.totient (3 ^ (m + 1))) = 1 := ZMod.pow_totient x
  have hg : x ^ (Nat.gcd (2 ^ e) (Nat.totient (3 ^ (m + 1)))) = 1 := pow_gcd_eq_one.2 ⟨hx, hx2⟩
  have htot : Nat.totient (3 ^ (m + 1)) = 3 ^ m * 2 := by
    rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
    simp
  have hcop : Nat.Coprime (3 ^ m) (2 ^ e) := Nat.Coprime.pow m e (by norm_num)
  have hgd : Nat.gcd (2 ^ e) (Nat.totient (3 ^ (m + 1))) ∣ 2 := by
    rw [htot, Nat.Coprime.gcd_mul_left_cancel_right 2 hcop]
    exact Nat.gcd_dvd_right _ _
  have hx3 : x ^ 2 = 1 := by
    have := orderOf_dvd_of_pow_eq_one hg
    exact orderOf_dvd_iff_pow_eq_one.1 (this.trans hgd)
  have h2 : ((j : ZMod (3 ^ (m + 1))) ^ 2) = 1 := by
    have := congrArg (fun y : (ZMod (3 ^ (m + 1)))ˣ => (y : ZMod (3 ^ (m + 1)))) hx3
    simpa [x, Units.val_ofPowEqOne] using this
  have h3 : (((j ^ 2 - 1 : ℤ)) : ZMod (3 ^ (m + 1))) = 0 := by
    push_cast
    rw [h2, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ 2 - 1) (3 ^ (m + 1))).1 h3

theorem dvd_sub_one_or_add_one_of_dvd_sq_sub_one {m : ℕ} {j : ℤ}
    (hj : ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j ^ 2 - 1) :
    ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j - 1 ∨ ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j + 1 := by
  have hmul : ((3 ^ (m + 1) : ℕ) : ℤ) ∣ (j - 1) * (j + 1) := by
    have : j ^ 2 - 1 = (j - 1) * (j + 1) := by ring
    rwa [this] at hj
  have hcast : ((3 ^ (m + 1) : ℕ) : ℤ) = (3 : ℤ) ^ (m + 1) := by push_cast; ring
  rw [hcast] at hmul ⊢
  by_cases h3 : (3 : ℤ) ∣ j + 1
  · right
    have h3' : ¬ (3 : ℤ) ∣ j - 1 := by
      intro h
      have : (3 : ℤ) ∣ (j + 1) - (j - 1) := dvd_sub h3 h
      norm_num at this
    have hcop : IsCoprime ((3 : ℤ) ^ (m + 1)) (j - 1) :=
      IsCoprime.pow_left (Int.prime_three.irreducible.coprime_iff_not_dvd.2 h3')
    exact hcop.dvd_of_dvd_mul_left hmul
  · left
    have hcop : IsCoprime ((3 : ℤ) ^ (m + 1)) (j + 1) :=
      IsCoprime.pow_left (Int.prime_three.irreducible.coprime_iff_not_dvd.2 h3)
    exact hcop.dvd_of_dvd_mul_right hmul

variable {G : Type*} [Group G]

theorem conj_pow_eq_zpow {h d : G} {j : ℤ} (hj : d * h * d⁻¹ = h ^ j) (k : ℕ) :
    d ^ k * h * (d ^ k)⁻¹ = h ^ (j ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc d ^ (k + 1) * h * (d ^ (k + 1))⁻¹ = d * (d ^ k * h * (d ^ k)⁻¹) * d⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = d * h ^ (j ^ k) * d⁻¹ := by rw [ih]
      _ = (d * h * d⁻¹) ^ (j ^ k) := by simp
      _ = (h ^ j) ^ (j ^ k) := by rw [hj]
      _ = h ^ (j ^ (k + 1)) := by rw [← zpow_mul, pow_succ']

end TwoPower

end SigmaDihedral

theorem exists_sigma3 {G : Type*} [Group G] {h t : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1))
    (ht2 : t * t = 1) (hth : t * h * t⁻¹ = h⁻¹) :
    ∃ _ : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ zpowers t)).Normal,
      Nonempty ((↥(zpowers h ⊔ zpowers t) ⧸ (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ zpowers t)) ≃*
        Equiv.Perm (Fin 3)) := by
  have hhX : h ∈ zpowers h ⊔ zpowers t := Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  have htX : t ∈ zpowers h ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hKX : zpowers (h ^ 3) ≤ zpowers h ⊔ zpowers t := by
    rw [zpowers_le]
    exact pow_mem hhX 3
  have hNn : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ zpowers t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    apply sup_le
    · rw [zpowers_le]
      exact SigmaDihedral.mem_normalizer_zpowers_pow (Or.inl (by group)) 3
    · rw [zpowers_le]
      exact SigmaDihedral.mem_normalizer_zpowers_pow (Or.inr hth) 3
  refine ⟨hNn, ?_⟩
  have hq : Nat.card (↥(zpowers h ⊔ zpowers t) ⧸
      (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ zpowers t)) = 2 * 3 := by
    have h1 := DihedralPres.card_mul_card_quotient hKX
    rw [SigmaDihedral.card_zpowers_pow_three hord,
      SigmaDihedral.card_zpowers_sup_zpowers hord ht2 hth] at h1
    have hpos : 0 < 3 ^ m := by positivity
    have : 3 ^ m * Nat.card (↥(zpowers h ⊔ zpowers t) ⧸
        (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ zpowers t)) = 3 ^ m * (2 * 3) := by
      rw [h1, pow_succ]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨e₁⟩ := DihedralPres.quotient_dihedral_mulEquiv (n := 3) (a := h) (b := t) hhX htX
    (Subgroup.mem_zpowers _) ht2 hth (by
      intro S hh ht _
      apply DihedralPres.eq_top_of_le_map
      apply sup_le
      · rw [zpowers_le]
        exact ⟨_, hh, rfl⟩
      · rw [zpowers_le]
        exact ⟨_, ht, rfl⟩) hq
  obtain ⟨e₂⟩ := DihedralPres.dihedral3_mulEquiv_perm
  exact ⟨e₁.symm.trans e₂⟩

theorem exists_dihedral12 {G : Type*} [Group G] {h t w : G} {m : ℕ} (hord : orderOf h = 3 ^ (m + 1))
    (ht2 : t * t = 1) (hw2 : w * w = 1) (hth : t * h * t⁻¹ = h⁻¹) (hwh : w * h = h * w)
    (htw : t * w = w * t) (hw1 : w ≠ 1) (hwt : w ≠ t)
    (hint : ∀ x ∈ zpowers h, x ∈ zpowers t ⊔ zpowers w → x = 1) :
    ∃ _ : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w))).Normal,
      Nonempty ((↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)) ⧸
        (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w))) ≃*
          DihedralGroup 6) := by
  have hhX : h ∈ zpowers h ⊔ (zpowers t ⊔ zpowers w) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  have htX : t ∈ zpowers h ⊔ (zpowers t ⊔ zpowers w) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hwX : w ∈ zpowers h ⊔ (zpowers t ⊔ zpowers w) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hKX : zpowers (h ^ 3) ≤ zpowers h ⊔ (zpowers t ⊔ zpowers w) := by
    rw [zpowers_le]
    exact pow_mem hhX 3
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hNn : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    apply sup_le
    · rw [zpowers_le]
      exact SigmaDihedral.mem_normalizer_zpowers_pow (Or.inl (by group)) 3
    · apply sup_le
      · rw [zpowers_le]
        exact SigmaDihedral.mem_normalizer_zpowers_pow (Or.inr hth) 3
      · rw [zpowers_le]
        refine SigmaDihedral.mem_normalizer_zpowers_pow (Or.inl ?_) 3
        calc w * h * w⁻¹ = h * w * w⁻¹ := by rw [hwh]
          _ = h := by group
  refine ⟨hNn, ?_⟩
  have hq : Nat.card (↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)) ⧸
      (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w))) = 2 * 6 := by
    have h1 := DihedralPres.card_mul_card_quotient hKX
    rw [SigmaDihedral.card_zpowers_pow_three hord,
      SigmaDihedral.card_zpowers_sup_klein hord ht2 hw2 hth hwh htw hw1 hwt hint] at h1
    have hpos : 0 < 3 ^ m := by positivity
    have : 3 ^ m * Nat.card (↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)) ⧸
        (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w))) = 3 ^ m * (2 * 6) := by
      rw [h1, pow_succ]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hcomm : Commute h w := hwh.symm
  have hh3 : h ^ 3 ∈ zpowers (h ^ 3) := Subgroup.mem_zpowers _
  obtain ⟨e₁⟩ := DihedralPres.quotient_dihedral_mulEquiv (n := 6) (a := h * w) (b := t)
    (mul_mem hhX hwX) htX (by
      have h6 : (h * w) ^ 6 = (h ^ 3) ^ 2 := by
        have hw6 : w ^ 6 = 1 := by
          have : w ^ 2 = 1 := by rw [pow_two]; exact hw2
          calc w ^ 6 = (w ^ 2) ^ 3 := by rw [← pow_mul]
            _ = 1 := by rw [this, one_pow]
        rw [hcomm.mul_pow, hw6, mul_one, ← pow_mul]
      rw [h6]
      exact pow_mem hh3 2) ht2 (by
      have htw' : t * w * t⁻¹ = w := by
        rw [htw]
        group
      calc t * (h * w) * t⁻¹ = (t * h * t⁻¹) * (t * w * t⁻¹) := by group
        _ = h⁻¹ * w := by rw [hth, htw']
        _ = (h * w)⁻¹ := by
          rw [mul_inv_rev, hwi]
          exact hcomm.inv_left.eq) (by
      intro S hhw ht hK
      have hw3 : (⟨w, hwX⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w))) ∈ S := by
        have h1 : (⟨h ^ 3, hKX hh3⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w))) ∈
            (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ (zpowers t ⊔ zpowers w)) := hh3
        have h2 := mul_mem (inv_mem (hK h1)) (pow_mem hhw 3)
        have e : (⟨h ^ 3, hKX hh3⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)))⁻¹ *
            (⟨h * w, mul_mem hhX hwX⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w))) ^ 3 = ⟨w, hwX⟩ := by
          apply Subtype.ext
          show (h ^ 3)⁻¹ * (h * w) ^ 3 = w
          have hw3' : w ^ 3 = w := by rw [pow_succ, pow_two, hw2, one_mul]
          rw [hcomm.mul_pow, hw3']
          group
        rwa [e] at h2
      have hh : (⟨h, hhX⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w))) ∈ S := by
        have e : (⟨h * w, mul_mem hhX hwX⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w))) *
            (⟨w, hwX⟩ : ↥(zpowers h ⊔ (zpowers t ⊔ zpowers w)))⁻¹ = ⟨h, hhX⟩ := by
          apply Subtype.ext
          show h * w * w⁻¹ = h
          group
        rw [← e]
        exact mul_mem hhw (inv_mem hw3)
      apply DihedralPres.eq_top_of_le_map
      apply sup_le
      · rw [zpowers_le]
        exact ⟨_, hh, rfl⟩
      · apply sup_le
        · rw [zpowers_le]
          exact ⟨_, ht, rfl⟩
        · rw [zpowers_le]
          exact ⟨_, hw3, rfl⟩) hq
  exact ⟨e₁.symm⟩

theorem normalizing_two_power_inv {G : Type*} [Group G] {h d : G} {m e : ℕ}
    (hord : orderOf h = 3 ^ (m + 1)) (hd : d ^ (2 ^ e) = 1) (hn : d * h * d⁻¹ ∈ zpowers h) :
    d * h * d⁻¹ = h ∨ d * h * d⁻¹ = h⁻¹ := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hj' : d * h * d⁻¹ = h ^ j := hj.symm
  have h1 : h ^ (j ^ (2 ^ e)) = h := by
    have := SigmaDihedral.conj_pow_eq_zpow hj' (2 ^ e)
    rwa [hd, inv_one, mul_one, one_mul, eq_comm] at this
  have h2 : ((3 ^ (m + 1) : ℕ) : ℤ) ∣ j ^ (2 ^ e) - 1 := by
    rw [← hord]
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  rcases SigmaDihedral.dvd_sub_one_or_add_one_of_dvd_sq_sub_one
      (SigmaDihedral.dvd_sq_sub_one_of_dvd_pow_two_pow_sub_one h2) with h3 | h3
  · left
    rw [hj']
    rw [← hord] at h3
    have := orderOf_dvd_iff_zpow_eq_one.1 h3
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at this
    exact this
  · right
    rw [hj']
    rw [← hord] at h3
    have := orderOf_dvd_iff_zpow_eq_one.1 h3
    rw [zpow_add, zpow_one] at this
    exact eq_inv_of_mul_eq_one_left this

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
