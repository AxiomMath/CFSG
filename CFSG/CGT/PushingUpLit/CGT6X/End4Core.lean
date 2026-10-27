module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3

variable {V : Type} [CommGroup V]

theorem card_commV_le_of_conj [Finite V] {A B : Subgroup (MulAut V)} (x : MulAut V)
    (hB : ∀ b ∈ B, ∃ a ∈ A, b = x * a * x⁻¹) : Nat.card (commV B) ≤ Nat.card (commV A) := by
  have hmap : ∀ v ∈ commV B, x⁻¹ v ∈ commV A := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨y, hy, u, rfl⟩ := hw
      obtain ⟨a, ha, rfl⟩ := hB y hy
      have h1 : x⁻¹ ((x * a * x⁻¹) u * u⁻¹) = a (x⁻¹ u) * (x⁻¹ u)⁻¹ := by
        simp [map_mul, map_inv, MulAut.mul_apply]
      rw [h1]
      exact Subgroup.subset_closure ⟨a, ha, x⁻¹ u, rfl⟩
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  refine Nat.card_le_card_of_injective (fun v : commV B => (⟨x⁻¹ v, hmap v v.2⟩ : commV A)) ?_
  intro v w h
  have h1 : x⁻¹ (v : V) = x⁻¹ (w : V) := congrArg Subtype.val h
  exact Subtype.ext (x⁻¹.injective h1)

variable [Finite V]

theorem end411_core (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hSQ : SimpleQuot Y)
    (hgen : CommGen Y) {t : MulAut V} (ht2 : t ^ 2 = 1) (htY : ∀ y ∈ Y, t * y = y * t)
    {M : Type*} [Group M] (ρ : M →* MulAut V) (γ : M → M) (O : Subgroup M) (hYO : Y = O.map ρ)
    (hγ : ∀ m, t * ρ m * t⁻¹ = ρ (γ m)) {α δ ω : M} {n : ℕ} (hn : Odd n) (hα : α ∈ O)
    (hδ : ∀ o ∈ O, δ * o = o * δ) (hγδ : γ δ = δ⁻¹) (hαn : α ^ n = 1) (hδn : δ ^ n = 1)
    (hrel : (ω * α * ω⁻¹) ^ 2 = α * δ⁻¹) : ρ δ = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, a = ρ α := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ρ δ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = ρ ω := ⟨_, rfl⟩
  have han : a ^ n = 1 := by rw [ha, ← map_pow, hαn, map_one]
  have hdn : d ^ n = 1 := by rw [hd, ← map_pow, hδn, map_one]
  obtain ⟨b, hb⟩ : ∃ b, b = x * a * x⁻¹ := ⟨_, rfl⟩
  have hbn : b ^ n = 1 := by rw [hb, conj_pow, han]; simp
  have hb2 : b ^ 2 = a * d⁻¹ := by
    have h1 := congrArg ρ hrel
    rw [map_pow, map_mul, map_mul, map_inv, map_mul, map_inv, ← ha, ← hd, ← hx] at h1
    rwa [hb]
  have haY : a ∈ Y := by rw [hYO, ha]; exact ⟨α, hα, rfl⟩
  have hdY : ∀ y ∈ Y, d * y = y * d := by
    intro y hy
    rw [hYO] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    rw [hd, ← map_mul, ← map_mul, hδ o ho]
  have htd : t * d * t⁻¹ = d⁻¹ := by rw [hd, hγ, hγδ, map_inv]
  have hbAD : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    obtain ⟨m, rfl⟩ := hn
    have h1 : b = (b ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hbn, one_mul]
    rw [h1, hb2]
    exact pow_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
      (inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))) _
  have haBD : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    have h1 : a = b ^ 2 * d := by rw [hb2]; group
    rw [h1]
    exact mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)) 2)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hdAB : d ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    have h1 : d = (b ^ 2)⁻¹ * a := by rw [hb2]; group
    rw [h1]
    exact mul_mem (inv_mem (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) 2))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hAD : Subgroup.zpowers a ⊔ Subgroup.zpowers d = Subgroup.zpowers b ⊔ Subgroup.zpowers d :=
    le_antisymm (sup_le (Subgroup.zpowers_le.2 haBD) le_sup_right)
      (sup_le (Subgroup.zpowers_le.2 hbAD) le_sup_right)
  have hAB : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    sup_le le_sup_left (Subgroup.zpowers_le.2 hdAB)
  have hAodd : Odd (Nat.card (Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one han)
  have hDodd : Odd (Nat.card (Subgroup.zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one hdn)
  have hU : commV (Subgroup.zpowers a) ≤ commV Y := commV_mono (Subgroup.zpowers_le.2 haY)
  have hDtriv : ∀ u ∈ commV Y, d u = u :=
    ms_three hgen hdY (ms_odd hV hSQ htY ht2 hdY hn hdn htd)
  have hDU : ∀ e ∈ Subgroup.zpowers d, ∀ u ∈ commV Y, e u = u := by
    let F : Subgroup (MulAut V) :=
      { carrier := {g | ∀ u ∈ commV Y, g u = u}
        one_mem' := fun u _ => rfl
        mul_mem' := fun {g₁ g₂} h₁ h₂ u hu => by
          show g₁ (g₂ u) = u
          rw [h₂ u hu, h₁ u hu]
        inv_mem' := fun {g} h u hu => by
          calc g⁻¹ u = g⁻¹ (g u) := by rw [h u hu]
            _ = u := MulAut.inv_apply_self V g u }
    have hdF : d ∈ F := hDtriv
    exact fun e he => Subgroup.zpowers_le.2 hdF he
  have hcard : Nat.card (commV (Subgroup.zpowers b)) ≤ Nat.card (commV (Subgroup.zpowers a)) := by
    refine card_commV_le_of_conj x fun c hc => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ⟨a ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k, by rw [hb, conj_zpow]⟩
  have hbot := weyl_alt1 hV hAodd hDodd hAD hAB hU hDU hcard
  have hmem : d ∈ (⊥ : Subgroup (MulAut V)) := by
    rw [← hbot]
    exact Subgroup.mem_zpowers d
  rw [← hd]
  exact Subgroup.mem_bot.1 hmem

end CFSG.CGT.PushingUpLit.CGT6X.End4
