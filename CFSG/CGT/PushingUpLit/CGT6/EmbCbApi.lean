module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbDefs
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAw
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

structure CbData (Y : Subgroup (MulAut V)) (t : MulAut V) (m : ℕ) (X : Subgroup (MulAut V)) where
  θ : ↥X ≃* alternatingGroup (Fin (m + 2))
  a : Fin (m + 2)
  b : Fin (m + 2)
  hn : ∀ x ∈ X, t * x * t⁻¹ ∈ X
  hab : a ≠ b
  hstab : (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (m + 2) {a, b}
  hnat : IsNatSectionWith (altAct (m + 2)) θ (commV X) ⊥
  hconj : ∀ (x : MulAut V) (hx : x ∈ X),
    (θ ⟨t * x * t⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
      Equiv.swap a b * (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap a b)⁻¹
  w : Fin (m + 2) → V
  hwmem : ∀ p, w p ∈ commV X ∧ w p ≠ 1
  hwinj : Function.Injective w
  hwact : ∀ (x : MulAut V) (hx : x ∈ X) (p : Fin (m + 2)),
    x (w p) = w ((θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) p)
  hwspan : Subgroup.closure (Set.range w) = commV X
  hwuniq : ∀ (p : Fin (m + 2)) (u : V), u ∈ commV X →
    (∀ (x : MulAut V) (hx : x ∈ X), (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) p = p → x u = u) →
    u = 1 ∨ u = w p
  hw4 : ∀ p q p' q' : Fin (m + 2), p ≠ q → p ≠ p' → p ≠ q' → q ≠ p' → q ≠ q' → p' ≠ q' →
    w p * w q * w p' * w q' ≠ 1
  htw : ∀ p, t (w p) = w (Equiv.swap a b p)

private theorem cba_inv_conj_mem {g : MulAut V} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ y ∈ X, g⁻¹ * y * g ∈ X := by
  let φ : ↥X → ↥X := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h : g * (x : MulAut V) * g⁻¹ = g * (y : MulAut V) * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h)
  intro y hy
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hφ ⟨y, hy⟩
  have h : g * (x : MulAut V) * g⁻¹ = y := congrArg Subtype.val hx
  have h' : g⁻¹ * y * g = x := by rw [← h]; group
  rw [h']
  exact x.2

private theorem cba_mem_zpowers_sq {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) {z : G}
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · left
    have : x = 1 := orderOf_eq_one_iff.mp h1
    rw [this, one_zpow]
  · have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rw [← zpow_mod_orderOf, h1]
    rcases hk with hk | hk
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

private theorem cba_card_sup_of_inf_eq_bot {G : Type*} [CommGroup G] {A B : Subgroup G}
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥A × ↥B => (⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    simp only [Subtype.mk.injEq] at hab
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
    rw [h, Subgroup.mem_bot] at h2
    have h3 : a = a' := (inv_mul_eq_one.mp h2).symm
    have h4 : b' = b := mul_inv_eq_one.mp (by rw [← h1, h2])
    subst h3
    subst h4
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem CbAlg.nonempty_data (hm : 7 ≤ m) (hodd : Odd m) (hX : CbAlg Y t m X) :
    Nonempty (CbData Y t m X) := by
  obtain ⟨θ, a, b, hn, hab, hstab, hnat, hconj⟩ := hX.alt
  obtain ⟨w, hwmem, hwinj, hwact, hwspan, hwuniq, hw4⟩ :=
    exists_wfam (hodd.add_even even_two) (by omega : 7 ≤ m + 2) θ hnat
  have htw : ∀ p, t (w p) = w (Equiv.swap a b p) := fun p =>
    wfam_apply_normalizer θ hwmem hwact hwuniq hn (cba_inv_conj_mem hn) hconj p
  exact ⟨⟨θ, a, b, hn, hab, hstab, hnat, hconj, w, hwmem, hwinj, hwact, hwspan, hwuniq, hw4,
    htw⟩⟩

namespace CbData

variable (D : CbData Y t m X)

omit [Finite V] in
include D in
theorem split (hm : 7 ≤ m) (hodd : Odd m) : commV X ⊔ fixV X = ⊤ ∧ commV X ⊓ fixV X = ⊥ :=
  ⟨commV_sup_fixV_of_natural (hodd.add_even even_two) (by omega) D.θ D.hnat,
    commV_inf_fixV_of_natural (hodd.add_even even_two) (by omega) D.θ D.hnat⟩

omit [Finite V] in
theorem w_sq (hV : ∀ v : V, v ^ 2 = 1) (p : Fin (m + 2)) : D.w p * D.w p = 1 := by
  rw [← pow_two]
  exact hV _

theorem fixV_invariant {g : MulAut V} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {u : V} (hu : u ∈ fixV X) :
    g u ∈ fixV X := by
  intro y hy
  have h1 : (g⁻¹ * y * g) u = u := hu _ (cba_inv_conj_mem hg y hy)
  calc y (g u) = (g * (g⁻¹ * y * g)) u := by rw [show g * (g⁻¹ * y * g) = y * g by group]; rfl
    _ = g ((g⁻¹ * y * g) u) := rfl
    _ = g u := by rw [h1]

theorem commV_zpowers (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (ht2 : t ^ 2 = 1) :
    commV (Subgroup.zpowers t) =
        Subgroup.zpowers (D.w D.a * D.w D.b) ⊔ (commV (Subgroup.zpowers t) ⊓ fixV X) ∧
      Subgroup.zpowers (D.w D.a * D.w D.b) ⊓ fixV X = ⊥ := by
  have hinv : ∀ p, (D.w p)⁻¹ = D.w p := fun p => inv_eq_of_mul_eq_one_right (D.w_sq hV p)
  obtain ⟨hsup, hinf⟩ := D.split hm hodd
  have hg0W : D.w D.a * D.w D.b ∈ commV X :=
    mul_mem (D.hwmem D.a).1 (D.hwmem D.b).1
  have hdisj : Subgroup.zpowers (D.w D.a * D.w D.b) ⊓ fixV X = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    have h : v ∈ commV X ⊓ fixV X := ⟨Subgroup.zpowers_le.mpr hg0W hv.1, hv.2⟩
    rwa [hinf] at h
  have hgen : D.w D.a * D.w D.b ∈ commV (Subgroup.zpowers t) := by
    have h6 : t (D.w D.a) * (D.w D.a)⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, D.w D.a, rfl⟩
    rw [D.htw, Equiv.swap_apply_left, hinv, mul_comm] at h6
    exact h6
  have hkey : ∀ e ∈ commV X, t e * e⁻¹ ∈ Subgroup.zpowers (D.w D.a * D.w D.b) := by
    intro e he
    rw [← D.hwspan] at he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [D.htw]
      by_cases i1 : i = D.a
      · subst i1
        rw [Equiv.swap_apply_left, hinv, mul_comm]
        exact Subgroup.mem_zpowers _
      by_cases i2 : i = D.b
      · subst i2
        rw [Equiv.swap_apply_right, hinv]
        exact Subgroup.mem_zpowers _
      · rw [Equiv.swap_apply_of_ne_of_ne i1 i2, mul_inv_cancel]
        exact one_mem _
    | one => simp
    | mul a b _ _ ha hb =>
      have h : t (a * b) * (a * b)⁻¹ = (t a * a⁻¹) * (t b * b⁻¹) := by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _
      rw [h]
      exact mul_mem ha hb
    | inv a _ ha =>
      have h : t a⁻¹ * (a⁻¹)⁻¹ = (t a * a⁻¹)⁻¹ := by simp [map_inv, mul_comm]
      rw [h]
      exact inv_mem ha
  refine ⟨le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hgen) inf_le_left), hdisj⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨z, hz, v, rfl⟩
  rcases cba_mem_zpowers_sq ht2 hz with h3 | h3
  · rw [h3]
    simp
  · rw [h3]
    have hv : v ∈ commV X ⊔ fixV X := by rw [hsup]; trivial
    obtain ⟨e, he, f, hf, rfl⟩ := Subgroup.mem_sup.mp hv
    have h5 : t (e * f) * (e * f)⁻¹ = (t e * e⁻¹) * (t f * f⁻¹) := by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [h5]
    refine Subgroup.mul_mem_sup (hkey e he) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, f, rfl⟩
    · exact mul_mem (fixV_invariant D.hn hf) (inv_mem hf)

include D in
theorem card_commV_zpowers (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m)
    (ht2 : t ^ 2 = 1) :
    Nat.card ↥(commV (Subgroup.zpowers t)) =
      2 * Nat.card ↥(commV (Subgroup.zpowers t) ⊓ fixV X) := by
  obtain ⟨hsplit, hdisj⟩ := D.commV_zpowers hV hm hodd ht2
  have hinv : ∀ p, (D.w p)⁻¹ = D.w p := fun p => inv_eq_of_mul_eq_one_right (D.w_sq hV p)
  have hAB : Subgroup.zpowers (D.w D.a * D.w D.b) ⊓
      (commV (Subgroup.zpowers t) ⊓ fixV X) = ⊥ :=
    eq_bot_iff.mpr (hdisj ▸ inf_le_inf_left _ inf_le_right)
  have hg1 : D.w D.a * D.w D.b ≠ 1 := by
    intro h
    rw [mul_eq_one_iff_eq_inv, hinv] at h
    exact D.hab (D.hwinj h)
  have hord : orderOf (D.w D.a * D.w D.b) = 2 := orderOf_eq_prime (hV _) hg1
  conv_lhs => rw [hsplit]
  rw [cba_card_sup_of_inf_eq_bot hAB, Nat.card_zpowers, hord]

end CbData

end CFSG.CGT.PushingUpLit.CGT6
