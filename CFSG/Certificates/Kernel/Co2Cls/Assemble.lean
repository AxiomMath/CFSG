module

public import CFSG.Certificates.Kernel.Co2Cls.Units
public import CFSG.Certificates.Kernel.Co2Cls.Glue

public section

namespace CFSG.KC.Co2Cls

open Subgroup

theorem card_cent_conj {G : Type*} [Group G] (H : Subgroup G) {a y : G}
    (hy : ∃ h ∈ H, h * a = y * h) :
    Nat.card (H ⊓ centralizer {y} : Subgroup G) = Nat.card (H ⊓ centralizer {a} : Subgroup G) := by
  obtain ⟨h, hh, e⟩ := hy
  have ey : y = h * a * h⁻¹ := by rw [e]; group
  subst ey
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨h⁻¹ * x * h, by
        obtain ⟨x1, x2⟩ := Subgroup.mem_inf.1 x.2
        have hx := mem_centralizer_singleton_iff.1 x2
        refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) x1) hh,
          mem_centralizer_singleton_iff.2 ?_⟩
        calc h⁻¹ * x * h * a = h⁻¹ * (x * (h * a * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * a * h⁻¹) * x) * h := by rw [hx]
          _ = a * (h⁻¹ * x * h) := by group⟩
      invFun := fun x => ⟨h * x * h⁻¹, by
        obtain ⟨x1, x2⟩ := Subgroup.mem_inf.1 x.2
        have hx := mem_centralizer_singleton_iff.1 x2
        refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hh x1) (H.inv_mem hh),
          mem_centralizer_singleton_iff.2 ?_⟩
        calc h * x * h⁻¹ * (h * a * h⁻¹) = h * (x * a) * h⁻¹ := by group
          _ = h * (a * x) * h⁻¹ := by rw [hx]
          _ = h * a * h⁻¹ * (h * x * h⁻¹) := by group⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }

variable {M : Type*} [Monoid M] [Finite M] {S : Submonoid M}

variable (hS : ∀ x ∈ S, IsUnit x)
include hS

theorem exists_conj_unit {u : Mˣ} {y : M} (hy : ∃ g ∈ S, g * (u : M) = y * g) :
    ∃ v : Mˣ, (v : M) = y ∧ Nat.card (unitsIn S ⊓ centralizer {v} : Subgroup Mˣ) =
      Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ) := by
  obtain ⟨g, hg, e⟩ := hy
  obtain ⟨w, hw, hwg, -⟩ := exists_unitsIn hS hg
  refine ⟨w * u * w⁻¹, ?_, card_cent_conj (unitsIn S) ⟨w, hw, by group⟩⟩
  rw [Units.val_mul, Units.val_mul, hwg, e, mul_assoc, ← hwg, Units.mul_inv, mul_one]

theorem two_pow_dvd_sub {P : Submonoid M} (hPS : P ≤ S) (hP : ∀ x ∈ P, x ^ 32 = 1) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card P) (u : Mˣ) (hc : ∀ x ∈ P, x * (u : M) = u * x) :
    2 ^ k ∣ Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ) := by
  have hPu : ∀ x ∈ P, IsUnit x := fun x hx => hS x (hPS hx)
  have hQ : unitsIn P ≤ unitsIn S ⊓ centralizer {u} := fun v hv =>
    ⟨hPS hv, mem_centralizer_singleton_iff.2 (Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hc _ hv))⟩
  have hp : IsPGroup 2 (unitsIn P) := fun x => ⟨5, by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    simpa using hP _ x.2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hp
  have hke : k ≤ e := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by
    rw [← he, card_unitsIn hPu]
    exact hk)
  calc 2 ^ k ∣ 2 ^ e := pow_dvd_pow 2 hke
    _ = Nat.card (unitsIn P) := he.symm
    _ ∣ _ := card_dvd_of_le hQ

theorem two_pow_dvd_orb {T : Submonoid M} (hTS : T ≤ S) (hT : ∀ x ∈ T, x ^ 32 = 1) {t : ℕ}
    (hTc : 2 ^ t ≤ Nat.card T) {u : Mˣ} {y : M} (hy : ∃ g ∈ S, g * (u : M) = y * g)
    (O : ℕ → M) (hO0 : O 0 = y) {m s : ℕ} (hO : ∀ g ∈ T, ∃ b < m, O b * g = g * O 0)
    (hms : m * 2 ^ s = 2 ^ t) :
    2 ^ s ∣ Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ) := by
  classical
  obtain ⟨v, hv, hcard⟩ := exists_conj_unit hS hy
  rw [← hcard]
  let O' : ℕ → Mˣ := fun b => if h : IsUnit (O b) then h.unit else 1
  refine two_pow_dvd (H := unitsIn S) (T := unitsIn T) (fun x hx => hTS hx) (fun x hx => ?_) ?_ v
    O' (fun g hg => ?_) hms
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hT _ hx
  · rw [card_unitsIn fun x hx => hS x (hTS hx)]
    exact hTc
  · obtain ⟨b, hb, e⟩ := hO _ hg
    rw [hO0] at e
    have hOb : O b = ((g * v * g⁻¹ : Mˣ) : M) := by
      rw [Units.val_mul, Units.val_mul, hv, ← e, mul_assoc, Units.mul_inv, mul_one]
    have hu : IsUnit (O b) := hOb ▸ Units.isUnit _
    refine ⟨b, hb, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, hv]
    simp only [O', dif_pos hu, IsUnit.unit_spec]
    exact e

theorem dvd_of_orderOf_mem {u : Mˣ} {y w : M} (hy : ∃ g ∈ S, g * (u : M) = y * g) (hw : w ∈ S)
    (hc : w * y = y * w) {p : ℕ} (ho : orderOf w = p) :
    p ∣ Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ) := by
  obtain ⟨v, hv, hcard⟩ := exists_conj_unit hS hy
  obtain ⟨w', hw', hwv, hwo⟩ := exists_unitsIn hS hw
  rw [← hcard]
  refine dvd_of_orderOf (unitsIn S) hw' (Units.ext ?_) (by rw [hwo, ho])
  rw [Units.val_mul, Units.val_mul, hv, hwv]
  exact hc

theorem nine_dvd_mem {u : Mˣ} {y U V : M} (hy : ∃ g ∈ S, g * (u : M) = y * g) (hU : U ∈ S)
    (hV : V ∈ S) (hUy : U * y = y * U) (hVy : V * y = y * V) (hUV : U * V = V * U)
    (oU : orderOf U = 3) (oV : orderOf V = 3) (h1 : V ≠ U) (h2 : V ≠ U * U) :
    9 ∣ Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ) := by
  obtain ⟨v, hv, hcard⟩ := exists_conj_unit hS hy
  obtain ⟨U', hU', hUv, hUo⟩ := exists_unitsIn hS hU
  obtain ⟨V', hV', hVv, hVo⟩ := exists_unitsIn hS hV
  rw [← hcard]
  refine nine_dvd (unitsIn S) hU' hV' (Units.ext ?_) (Units.ext ?_) (Units.ext ?_)
    (by rw [hUo, oU]) (by rw [hVo, oV]) (fun e => h1 ?_) (fun e => h2 ?_)
  · rw [Units.val_mul, Units.val_mul, hv, hUv]
    exact hUy
  · rw [Units.val_mul, Units.val_mul, hv, hVv]
    exact hVy
  · rw [Units.val_mul, Units.val_mul, hUv, hVv]
    exact hUV
  · rw [← hUv, ← hVv, e]
  · rw [← hUv, ← hVv, e, Units.val_mul]

theorem class_of {a : M} (ha : a ∈ S) {N c : ℕ}
    (hN : N ≤ Nat.card {y : M // ∃ g ∈ S, g * a = y * g})
    (hc : ∀ u : Mˣ, (u : M) = a → c ∣ Nat.card (unitsIn S ⊓ centralizer {u} : Subgroup Mˣ))
    (hH : N * c = Nat.card S) :
    Nat.card {y : M // ∃ g ∈ S, g * a = y * g} = N ∧
      Nat.card {g : M // g ∈ S ∧ g * a = a * g} = c := by
  obtain ⟨u, -, hu, -⟩ := exists_unitsIn hS ha
  have e1 := card_conj_unitsIn hS u
  have e2 := card_cent_unitsIn hS u
  rw [hu] at e1 e2
  rw [← e1, ← e2]
  refine class_card (unitsIn S) ⟨1, (unitsIn S).one_mem, by rw [one_mul, mul_one]⟩ ?_ (hc u hu) ?_
  · rw [e1]
    exact hN
  · rw [card_unitsIn hS]
    exact hH

theorem class_of_central {a : M} (hc : ∀ g ∈ S, g * a = a * g) :
    Nat.card {y : M // ∃ g ∈ S, g * a = y * g} = 1 ∧
      Nat.card {g : M // g ∈ S ∧ g * a = a * g} = Nat.card S := by
  refine ⟨Nat.card_eq_one_iff_unique.2 ⟨⟨fun x z => ?_⟩, ⟨⟨a, 1, S.one_mem, by
    rw [one_mul, mul_one]⟩⟩⟩, Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      ⟨fun h => h.1, fun h => ⟨h, hc g h⟩⟩)⟩
  have hx : x.1 = a := by
    obtain ⟨g, hg, e⟩ := x.2
    exact (hS g hg).mul_left_inj.1 (e.symm.trans (hc g hg))
  have hz : z.1 = a := by
    obtain ⟨g, hg, e⟩ := z.2
    exact (hS g hg).mul_left_inj.1 (e.symm.trans (hc g hg))
  exact Subtype.ext (hx.trans hz.symm)

end CFSG.KC.Co2Cls

end
