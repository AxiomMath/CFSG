module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

@[expose] def socleSeries (D : Subgroup (MulAut V)) : ℕ → Subgroup V
  | 0 => ⊥
  | j + 1 =>
    { carrier := {x | ∀ d ∈ D, d x * x⁻¹ ∈ socleSeries D j}
      one_mem' := fun d _ => by simp [(socleSeries D j).one_mem]
      mul_mem' := fun {a b} ha hb d hd => by
        have e : d (a * b) * (a * b)⁻¹ = (d a * a⁻¹) * (d b * b⁻¹) := by
          rw [map_mul, mul_inv]
          exact mul_mul_mul_comm _ _ _ _
        rw [e]
        exact (socleSeries D j).mul_mem (ha d hd) (hb d hd)
      inv_mem' := fun {a} ha d hd => by
        have e : d a⁻¹ * a⁻¹⁻¹ = (d a * a⁻¹)⁻¹ := by
          rw [map_inv, mul_inv, inv_inv]
        rw [e]
        exact (socleSeries D j).inv_mem (ha d hd) }

theorem mem_socleSeries_succ {D : Subgroup (MulAut V)} {j : ℕ} {x : V} :
    x ∈ socleSeries D (j + 1) ↔ ∀ d ∈ D, d x * x⁻¹ ∈ socleSeries D j := Iff.rfl

theorem socleSeries_le_succ (D : Subgroup (MulAut V)) (j : ℕ) :
    socleSeries D j ≤ socleSeries D (j + 1) := by
  induction j with
  | zero => exact bot_le
  | succ j ih =>
    intro x hx
    exact fun d hd => ih (hx d hd)

theorem socleSeries_one (D : Subgroup (MulAut V)) : socleSeries D 1 = fixV D := by
  ext x
  rw [mem_fixV]
  show (∀ d ∈ D, d x * x⁻¹ ∈ socleSeries D 0) ↔ _
  simp [socleSeries, mul_inv_eq_one]

theorem mem_stabSub_socleSeries {D : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ d ∈ D, g * d = d * g) (j : ℕ) : g ∈ stabSub (socleSeries D j) := by
  induction j with
  | zero =>
    intro u
    simp [socleSeries]
  | succ j ih =>
    intro u
    rw [mem_socleSeries_succ, mem_socleSeries_succ]
    have key : ∀ d ∈ D, d (g u) * (g u)⁻¹ = g (d u * u⁻¹) := by
      intro d hd
      have h1 : d (g u) = g (d u) := (DFunLike.congr_fun (hg d hd) u).symm
      rw [map_mul, map_inv, h1]
    constructor
    · intro h d hd
      have h' : g (d u * u⁻¹) ∈ socleSeries D j := by
        rw [← key d hd]
        exact h d hd
      exact (mem_stabSub.1 ih (d u * u⁻¹)).1 h'
    · intro h d hd
      rw [key d hd]
      exact (mem_stabSub.1 ih (d u * u⁻¹)).2 (h d hd)

theorem exists_fixed_mod_of_ne_top [Finite V] {D : Subgroup (MulAut V)} {S : Subgroup V}
    (hV : ∀ v : V, v ^ 2 = 1) (hD2 : ∀ d ∈ D, d * d = 1) (hDS : ∀ d ∈ D, d ∈ stabSub S)
    (hS : S ≠ ⊤) : ∃ x : V, x ∉ S ∧ ∀ d ∈ D, d x * x⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ S := by
    by_contra h
    push Not at h
    exact hS ((Subgroup.eq_top_iff' S).2 fun x => h x)
  have hw1 : (QuotientGroup.mk v : V ⧸ S) ≠ 1 := fun h => hv ((QuotientGroup.eq_one_iff v).1 h)
  have hw2 : (QuotientGroup.mk v : V ⧸ S) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]
  have hord : orderOf (QuotientGroup.mk v : V ⧸ S) = 2 := orderOf_eq_prime hw2 hw1
  have hdvd : 2 ∣ Nat.card (V ⧸ S) := by
    have := orderOf_dvd_natCard (QuotientGroup.mk v : V ⧸ S)
    rwa [hord] at this
  have hsqY : ∀ w : ↥(autQuot D S), w ^ 2 = 1 := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.1 hφ
    refine Subtype.ext ?_
    have hg2 : g ^ 2 = 1 := Subtype.ext (by
      show (g : MulAut V) ^ 2 = 1
      rw [sq]
      exact hD2 _ hg)
    show (quotHom S g) ^ 2 = (1 : MulAut (V ⧸ S))
    rw [← map_pow, hg2, map_one]
  have hY : IsPGroup 2 ↥(autQuot D S) := isPGroup_two_of_sq_eq_one hsqY
  have hmod := card_modEq_card_fixV hY
  have hfix : 2 ∣ Nat.card (fixV (autQuot D S)) := by
    have h0 : Nat.card (V ⧸ S) ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.2 hdvd
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans h0)
  have hne1 : fixV (autQuot D S) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hfix
    omega
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hxD : ∀ d ∈ D, d x * x⁻¹ ∈ S := fun d hd => mk_mem_fixV_autQuot.1 hq d hd (hDS d hd)
  have hxS : x ∉ S := fun h => hq1 (Subtype.ext ((QuotientGroup.eq_one_iff x).2 h))
  exact ⟨x, hxS, hxD⟩

theorem socleSeries_card_two_mul_le [Finite V] {H K : Subgroup V} (h : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le h
  have hK : 0 < Nat.card K := Nat.card_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge h (hc.trans (mul_one _)).le)
  calc 2 * Nat.card H ≤ c * Nat.card H := Nat.mul_le_mul_right _ (by omega)
    _ = Nat.card K := by rw [hc, Nat.mul_comm]

theorem socleSeries_lt_succ [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {D : Subgroup (MulAut V)}
    (hD2 : ∀ d ∈ D, d * d = 1) (hDc : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (j : ℕ)
    (hne : socleSeries D j ≠ ⊤) : socleSeries D j < socleSeries D (j + 1) := by
  have hDS : ∀ d ∈ D, d ∈ stabSub (socleSeries D j) :=
    fun d hd => mem_stabSub_socleSeries (hDc d hd) j
  obtain ⟨x, hxS, hxD⟩ := exists_fixed_mod_of_ne_top hV hD2 hDS hne
  exact lt_of_le_of_ne (socleSeries_le_succ D j) fun h =>
    hxS (by rw [h]; exact mem_socleSeries_succ.2 hxD)

theorem exists_socleSeries_eq_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {D : Subgroup (MulAut V)}
    (hD2 : ∀ d ∈ D, d * d = 1) (hDc : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) :
    ∃ t, socleSeries D t = ⊤ := by
  by_contra hne
  push Not at hne
  have hgrow : ∀ j : ℕ, 2 ^ j ≤ Nat.card (socleSeries D j) := by
    intro j
    induction j with
    | zero => simp [socleSeries]
    | succ j ih =>
      have h2 := socleSeries_card_two_mul_le (socleSeries_le_succ D j)
        (socleSeries_lt_succ hV hD2 hDc j (hne j)).ne
      rw [pow_succ]
      omega
  have hle : Nat.card (socleSeries D (Nat.card V)) ≤ Nat.card V :=
    (Subgroup.card_le_of_le le_top).trans (le_of_eq Subgroup.card_top)
  have hlt : Nat.card V < 2 ^ Nat.card V := Nat.lt_two_pow_self
  have := hgrow (Nat.card V)
  omega

end CFSG.LocalAnalysis.RankThreeUC
