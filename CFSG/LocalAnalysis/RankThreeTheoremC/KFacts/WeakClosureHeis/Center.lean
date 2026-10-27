module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup

theorem exists_central_order_p_not_mem {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {Q Q₀ Q₁ : Subgroup X} (h : HeisShape p Q Q₀ Q₁) {S : Subgroup X} (hSQ : S ≤ Q)
    (hS : Nat.card (S ⊓ centralizer (S : Set X) : Subgroup X) ≤ p) :
    ∃ u ∈ Q, u ^ p = 1 ∧ (∀ q ∈ Q, u * q = q * u) ∧ u ∉ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ0ne : Nat.card Q₀ ≠ 1 := fun h1 => h.ne_bot (Subgroup.card_eq_one.mp h1)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.left_pgrp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hQ0ne (by rw [hk, pow_zero])
  have hdvd : p ∣ Nat.card Q₀ := by
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (g : X) = p := (Subgroup.orderOf_coe g).trans hg
  have hzQ0 : Subgroup.zpowers (g : X) ≤ Q₀ := Subgroup.zpowers_le.mpr g.2
  have hcardZ : Nat.card (Subgroup.zpowers (g : X)) = p := by
    rw [Nat.card_zpowers, hord]
  have hw1 : ∀ w ∈ heisZ Q₁, w ∈ Q₁ := fun w hw =>
    (Subgroup.mem_inf.mp (show w ∈ Q₁ ⊓ centralizer (Q₁ : Set X) from hw)).1
  have hzp : ∀ a ∈ Subgroup.zpowers (g : X), a ^ p = 1 := fun a ha =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers ha).trans (dvd_of_eq hord))
  have hcenQ0 : ∀ a ∈ Subgroup.zpowers (g : X), ∀ q ∈ Q, a * q = q * a := fun a ha q hq =>
    h.commute_left (hzQ0 ha) hq
  have hcenZ : ∀ w ∈ heisZ Q₁, ∀ q ∈ Q, w * q = q * w := by
    intro w hw
    have hw' : w ∈ Q₁ ⊓ centralizer (Q₁ : Set X) := hw
    have hwQ1 : w ∈ Q₁ := (Subgroup.mem_inf.mp hw').1
    have hwC : ∀ y ∈ Q₁, y * w = w * y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw').2
    have hle : Q ≤ centralizer ({w} : Set X) := by
      rw [← h.sup]
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (h.comm x hx w hwQ1).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (hwC x hx).symm
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp (hle hq) w (Set.mem_singleton w)
  have hcomm : ∀ a ∈ Subgroup.zpowers (g : X), ∀ w ∈ heisZ Q₁, Commute a w := fun a ha w hw =>
    h.comm a (hzQ0 ha) w (hw1 w hw)
  have hxQ : ∀ a ∈ Subgroup.zpowers (g : X), ∀ w ∈ heisZ Q₁, a * w ∈ Q := fun a ha w hw =>
    h.mul_mem (hzQ0 ha) (hw1 w hw)
  have hxp : ∀ a ∈ Subgroup.zpowers (g : X), ∀ w ∈ heisZ Q₁, (a * w) ^ p = 1 := fun a ha w hw => by
    rw [(hcomm a ha w hw).mul_pow, hzp a ha, h.exp w (hw1 w hw), one_mul]
  have hxc : ∀ a ∈ Subgroup.zpowers (g : X), ∀ w ∈ heisZ Q₁, ∀ q ∈ Q,
      a * w * q = q * (a * w) := fun a ha w hw q hq => by
    have h1 : Commute a q := hcenQ0 a ha q hq
    have h2 : Commute w q := hcenZ w hw q hq
    exact (h1.mul_left h2).eq
  by_contra hcon
  have H : ∀ u ∈ Q, u ^ p = 1 → (∀ q ∈ Q, u * q = q * u) → u ∈ S := by
    intro u hu hup hc
    by_contra hnot
    exact hcon ⟨u, hu, hup, hc, hnot⟩
  have hxT : ∀ a ∈ Subgroup.zpowers (g : X), ∀ w ∈ heisZ Q₁,
      a * w ∈ (S ⊓ centralizer (S : Set X) : Subgroup X) := by
    intro a ha w hw
    refine Subgroup.mem_inf.mpr ⟨H _ (hxQ a ha w hw) (hxp a ha w hw)
      (fun q hq => hxc a ha w hw q hq), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hxc a ha w hw s (hSQ hs)).symm
  have hinj : Function.Injective (fun x : ↥(Subgroup.zpowers (g : X)) × ↥(heisZ Q₁) =>
      (⟨x.1.1 * x.2.1, hxT x.1.1 x.1.2 x.2.1 x.2.2⟩ :
        ↥(S ⊓ centralizer (S : Set X) : Subgroup X))) := by
    rintro ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ ⟨⟨a', ha'⟩, ⟨w', hw'⟩⟩ hxy
    have hprod : a * w = a' * w' := congrArg Subtype.val hxy
    have hkey : a'⁻¹ * a = w' * w⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * w) * w⁻¹ := by group
        _ = a'⁻¹ * (a' * w') * w⁻¹ := by rw [hprod]
        _ = w' * w⁻¹ := by group
    have hQ0mem : a'⁻¹ * a ∈ Q₀ := Q₀.mul_mem (Q₀.inv_mem (hzQ0 ha')) (hzQ0 ha)
    have hQ1mem : w' * w⁻¹ ∈ Q₁ := Q₁.mul_mem (hw1 w' hw') (Q₁.inv_mem (hw1 w hw))
    have hbot : a'⁻¹ * a ∈ Q₀ ⊓ Q₁ :=
      Subgroup.mem_inf.mpr ⟨hQ0mem, by rw [hkey]; exact hQ1mem⟩
    rw [h.disj, Subgroup.mem_bot] at hbot
    have hea : a' = a := inv_mul_eq_one.mp hbot
    have hew : w' = w := mul_inv_eq_one.mp (by rw [← hkey]; exact hbot)
    subst hea
    subst hew
    rfl
  have hle : Nat.card ↥(Subgroup.zpowers (g : X)) * Nat.card ↥(heisZ Q₁) ≤
      Nat.card ↥(S ⊓ centralizer (S : Set X) : Subgroup X) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  rw [hcardZ, h.card_heisZ] at hle
  have h2 := hp.two_le
  have h3 : p * p ≤ p := le_trans hle hS
  have h4 : p * 2 ≤ p * p := Nat.mul_le_mul (le_refl p) h2
  have h5 : p * 2 ≤ p := le_trans h4 h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
