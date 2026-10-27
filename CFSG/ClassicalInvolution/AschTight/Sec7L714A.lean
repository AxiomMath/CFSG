module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64E
public import CFSG.ClassicalInvolution.AschTight.Sec71Basic
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyC
public import CFSG.ClassicalInvolution.AschTight.Sec7L76B

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isUniqueInvolution_zpowers {u : G} {k : ℕ} (hu : orderOf u = 2 ^ (k + 1)) :
    IsUniqueInvolution (Subgroup.zpowers u) (u ^ 2 ^ k) where
  mem := Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  ne_one := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hu] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  sq := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
  unique := by
    intro y hy hy2
    obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : u ^ (2 * c) = 1 := by
      rw [two_mul, zpow_add]; exact hy2
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hu] at h2
    have h3 : ((2 : ℤ) ^ k) ∣ c := by
      have e : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * 2 ^ k := by push_cast; ring
      rw [e] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    obtain ⟨m, rfl⟩ := h3
    have e : u ^ ((2 : ℤ) ^ k * m) = (u ^ 2 ^ k) ^ m := by
      rw [zpow_mul]; norm_cast
    rw [e]
    have hsq : u ^ 2 ^ k * u ^ 2 ^ k = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl (Sec71.zpow_eq_one_of_even hsq hm)
    · exact Or.inr (Sec71.zpow_eq_self_of_odd hsq hm)

theorem closure_pair_eq_sup (a b : G) :
    Subgroup.closure {a, b} = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union]

theorem exists_decomp_of_mem_sup_OCW [Finite G] {W L : Subgroup G} (hW2 : IsPGroup 2 W) {g : G}
    (hgL : g ∈ L) (hg : g ∈ W ⊔ OCW W) : ∃ o ∈ L ⊓ OCW W, ∃ w ∈ L ⊓ W, g = o * w := by
  have hXW : W ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_OCW W)
  have hg' : g ∈ ((W ⊔ OCW W : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXW] at hg'
  obtain ⟨w, hw, x, hx, rfl⟩ := hg'
  have hxw : w * x = x * w := (Subgroup.mem_centralizer_iff.mp (oddCoreOf_le_self _ hx)) w hw
  have hodd : Odd (orderOf x) :=
    (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  obtain ⟨n, hn⟩ := (hW2.to_le (Subgroup.zpowers_le.mpr hw)).exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hc : Commute w x := hxw
  have hpow : (w * x) ^ orderOf x = w ^ orderOf x := by
    rw [hc.mul_pow, pow_orderOf_eq_one, mul_one]
  have hz : Subgroup.zpowers (w ^ ((orderOf x : ℕ) : ℤ)) = Subgroup.zpowers w :=
    Sec71.zpowers_zpow_eq_of_odd hn (by exact_mod_cast hodd)
  have hwL : w ∈ L := by
    have h1 : w ∈ Subgroup.zpowers (w ^ ((orderOf x : ℕ) : ℤ)) := hz ▸ Subgroup.mem_zpowers w
    rw [zpow_natCast, ← hpow] at h1
    exact (Subgroup.zpowers_le.mpr (L.pow_mem hgL _)) h1
  have hxL : x ∈ L := by
    have e : x = w⁻¹ * (w * x) := by group
    rw [e]
    exact L.mul_mem (L.inv_mem hwL) hgL
  exact ⟨x, ⟨hxL, hx⟩, w, ⟨hwL, hw⟩, hxw⟩

theorem inf_OCW_le_oddCoreOf [Finite G] {W L : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : L ⊓ OCW W ≤ oddCoreOf L := by
  refine Sec6Gen.le_oddCoreOf_of_normal inf_le_left (fun g hg => ?_) ?_
  · exact mem_normalizer_inf (Subgroup.le_normalizer hg) (normalizer_le_normalizer_OCW W (hLW hg))
  · exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.card_dvd_of_le inf_le_right)

theorem comm_mem_centralizer {U : Subgroup G} {a g : G} (haU : ∀ w ∈ U, a * w * a⁻¹ = w)
    (hgN : g ∈ Subgroup.normalizer (U : Set G)) :
    a * g * a⁻¹ * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : g⁻¹ * w * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) w).mp hw
    rwa [inv_inv] at this
  have h1 : a⁻¹ * (g⁻¹ * w * g) * a = g⁻¹ * w * g := by
    have := haU _ hw'
    calc a⁻¹ * (g⁻¹ * w * g) * a = a⁻¹ * (a * (g⁻¹ * w * g) * a⁻¹) * a := by rw [this]
      _ = g⁻¹ * w * g := by group
  have haw : a * w = w * a := by
    have := haU w hw
    calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [this]
  calc w * (a * g * a⁻¹ * g⁻¹) = a * g * (g⁻¹ * w * g) * a⁻¹ * g⁻¹ := by
        rw [show a * g * (g⁻¹ * w * g) * a⁻¹ * g⁻¹ = a * w * g * a⁻¹ * g⁻¹ by group, haw]
        group
    _ = a * g * (a⁻¹ * (g⁻¹ * w * g) * a) * a⁻¹ * g⁻¹ := by rw [h1]
    _ = (a * g * a⁻¹ * g⁻¹) * w := by group

theorem comm_mem_of_decomp {L U O : Subgroup G} (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hOU : O ⊓ U = ⊥) (hOC : O ≤ Subgroup.centralizer (U : Set G))
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hLO : L ≤ Subgroup.normalizer (O : Set G))
    (hdec : ∀ g ∈ L, g ∈ Subgroup.centralizer (U : Set G) → ∃ o ∈ O, ∃ w ∈ U, g = o * w)
    {a g b₂ : G} (haU : ∀ w ∈ U, a * w * a⁻¹ = w)
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haO : a ∈ Subgroup.normalizer (O : Set G))
    (hab : a * b₂ * a⁻¹ = b₂) (hgL : g ∈ L) (hb₂L : b₂ ∈ L)
    (hb₂fp : ∀ w ∈ U, b₂ * w * b₂⁻¹ = w → w = 1)
    (hc₁ : g * b₂ * g⁻¹ * b₂ ∈ Subgroup.centralizer (U : Set G)) :
    a * g * a⁻¹ * g⁻¹ ∈ O := by
  have hb₂N := hLU hb₂L
  have hdL : a * g * a⁻¹ * g⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp haL g).mp hgL) (L.inv_mem hgL)
  obtain ⟨od, hod, wd, hwd, hd⟩ := hdec _ hdL (comm_mem_centralizer haU (hLU hgL))
  obtain ⟨oc, hoc, wc, hwc, hc⟩ := hdec _
    (L.mul_mem (L.mul_mem (L.mul_mem hgL hb₂L) (L.inv_mem hgL)) hb₂L) hc₁
  have hkey : a * (g * b₂ * g⁻¹ * b₂) * a⁻¹ =
      (a * g * a⁻¹ * g⁻¹) * (g * b₂ * g⁻¹ * b₂) * (b₂⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * b₂) := by
    calc a * (g * b₂ * g⁻¹ * b₂) * a⁻¹
        = (a * g * a⁻¹) * (a * b₂ * a⁻¹) * (a * g * a⁻¹)⁻¹ * (a * b₂ * a⁻¹) := by group
      _ = (a * g * a⁻¹) * b₂ * (a * g * a⁻¹)⁻¹ * b₂ := by rw [hab]
      _ = (a * g * a⁻¹ * g⁻¹) * (g * b₂ * g⁻¹ * b₂) * (b₂⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * b₂) := by
          group
  have hOW : ∀ o ∈ O, ∀ w ∈ U, o * w = w * o := fun o ho w hw =>
    (Subgroup.mem_centralizer_iff.mp (hOC ho) w hw).symm
  have hx1 : b₂⁻¹ * wd⁻¹ * b₂ ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb₂N) wd⁻¹).mp (U.inv_mem hwd)
    rwa [inv_inv] at this
  have hy1 : b₂⁻¹ * od⁻¹ * b₂ ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLO hb₂L)) od⁻¹).mp
      (O.inv_mem hod)
    rwa [inv_inv] at this
  have haoc : a * oc * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp haO oc).mp hoc
  have hw3 : wd * wc * (b₂⁻¹ * wd⁻¹ * b₂) ∈ U := U.mul_mem (U.mul_mem hwd hwc) hx1
  have heq : (a * oc * a⁻¹) * wc =
      (od * oc * (b₂⁻¹ * od⁻¹ * b₂)) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) := by
    have hL' : a * (g * b₂ * g⁻¹ * b₂) * a⁻¹ = (a * oc * a⁻¹) * wc := by
      rw [hc, show a * (oc * wc) * a⁻¹ = (a * oc * a⁻¹) * (a * wc * a⁻¹) by group,
        haU wc hwc]
    rw [← hL', hkey, hd, hc]
    calc od * wd * (oc * wc) * (b₂⁻¹ * (od * wd)⁻¹ * b₂)
        = od * (wd * oc) * wc * (b₂⁻¹ * wd⁻¹ * b₂) * (b₂⁻¹ * od⁻¹ * b₂) := by group
      _ = od * (oc * wd) * wc * (b₂⁻¹ * wd⁻¹ * b₂) * (b₂⁻¹ * od⁻¹ * b₂) := by
          rw [← hOW oc hoc wd hwd]
      _ = od * oc * ((wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * (b₂⁻¹ * od⁻¹ * b₂)) := by group
      _ = od * oc * ((b₂⁻¹ * od⁻¹ * b₂) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂))) := by
          rw [hOW _ hy1 _ hw3]
      _ = od * oc * (b₂⁻¹ * od⁻¹ * b₂) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) := by group
  have hO' : od * oc * (b₂⁻¹ * od⁻¹ * b₂) ∈ O := O.mul_mem (O.mul_mem hod hoc) hy1
  have h1 : (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * (a * oc * a⁻¹) =
      (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by
    calc (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * (a * oc * a⁻¹)
        = (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * ((a * oc * a⁻¹) * wc) * wc⁻¹ := by group
      _ = (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by rw [heq]; group
  have h2 : (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ ∈ O ⊓ U :=
    ⟨h1 ▸ O.mul_mem (O.inv_mem hO') haoc, U.mul_mem hw3 (U.inv_mem hwc)⟩
  rw [hOU, Subgroup.mem_bot] at h2
  have h3 : wd * (b₂⁻¹ * wd⁻¹ * b₂) = 1 := by
    have hc' : wc * (b₂⁻¹ * wd⁻¹ * b₂) = (b₂⁻¹ * wd⁻¹ * b₂) * wc := hUab _ hwc _ hx1
    calc wd * (b₂⁻¹ * wd⁻¹ * b₂) = (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by
          rw [mul_assoc wd wc, hc']; group
      _ = 1 := h2
  have h4 : b₂ * wd * b₂⁻¹ = wd := by
    have h5 : b₂⁻¹ * wd⁻¹ * b₂ = wd⁻¹ := eq_inv_of_mul_eq_one_right h3
    calc b₂ * wd * b₂⁻¹ = (b₂ * wd⁻¹ * b₂⁻¹)⁻¹ := by group
      _ = (b₂ * (b₂⁻¹ * wd⁻¹ * b₂) * b₂⁻¹)⁻¹ := by rw [h5]
      _ = wd := by group
  rw [hd, hb₂fp wd hwd h4, mul_one]
  exact hod

theorem comm_mem_oddCoreOf_of_closure [Finite G] {L : Subgroup G} {S : Set G}
    (hL : L = Subgroup.closure S) {a : G} (h : ∀ g ∈ S, ⁅a, g⁆ ∈ oddCoreOf L) :
    ∀ l ∈ L, ⁅a, l⁆ ∈ oddCoreOf L := by
  have hLO : ∀ l ∈ L, l ∈ Subgroup.normalizer (oddCoreOf L : Set G) := fun l hl =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hl)
  intro l hl
  rw [hL] at hl
  induction hl using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxL : x ∈ L := hL ▸ hx
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (oddCoreOf L).mul_mem ihx ((Subgroup.mem_normalizer_iff.mp (hLO x hxL) _).mp ihy)
  | inv x hx ihx =>
    have hxL : x ∈ L := hL ▸ hx
    have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLO x⁻¹ (L.inv_mem hxL)) _).mp
      ((oddCoreOf L).inv_mem ihx)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
