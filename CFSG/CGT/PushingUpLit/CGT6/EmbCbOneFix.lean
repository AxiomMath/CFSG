module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneTrans
import CFSG.CGT.PushingUpLit.CGT6.EmbCbPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

theorem cbo_exists_conj_of_inv {Γ : Type*} [Group Γ] {c₀ q : Γ} (hq : c₀ * q * c₀⁻¹ = q⁻¹)
    (hodd : Odd (orderOf q)) : ∃ r : Γ, r ∈ Subgroup.zpowers q ∧ r * c₀ * r⁻¹ = c₀ * q := by
  obtain ⟨e, he⟩ := hodd
  have hqd : q ^ (2 * e + 1) = 1 := by rw [← he]; exact pow_orderOf_eq_one q
  have hqe : c₀ * q ^ e * c₀⁻¹ = (q⁻¹) ^ e := by rw [← conj_pow, hq]
  have hqj : c₀ * (q ^ e)⁻¹ * c₀⁻¹ = q ^ e := by
    have : c₀ * (q ^ e)⁻¹ * c₀⁻¹ = (c₀ * q ^ e * c₀⁻¹)⁻¹ := by group
    rw [this, hqe, inv_pow, inv_inv]
  refine ⟨q ^ e, Subgroup.pow_mem _ (Subgroup.mem_zpowers q) e, ?_⟩
  have h2 : q ^ e * q ^ e = q⁻¹ := by
    rw [← pow_add, ← two_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hqd)
  calc q ^ e * c₀ * (q ^ e)⁻¹ = q ^ e * (c₀ * (q ^ e)⁻¹ * c₀⁻¹) * c₀ := by group
    _ = q ^ e * q ^ e * c₀ := by rw [hqj]
    _ = q⁻¹ * c₀ := by rw [h2]
    _ = c₀ * q := by
      have : c₀ * q = (c₀ * q * c₀⁻¹) * c₀ := by group
      rw [this, hq]

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

namespace OneCfg

variable {G T : Subgroup (MulAut V)} (c : OneCfg G T Y t m X) (D : CbData Y t m X)

include c in
theorem exists_conj_of_transposition {c₁ : MulAut V} (hc₁G : c₁ ∈ G) (hc₁2 : c₁ ^ 2 = 1)
    (hn : ∀ x ∈ X, c₁ * x * c₁⁻¹ ∈ X) {p q : Fin (m + 2)} (hpq : p ≠ q)
    (hσ : ∀ (x : MulAut V) (hx : x ∈ X),
      (D.θ ⟨c₁ * x * c₁⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
        Equiv.swap p q * (D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap p q)⁻¹) :
    ∃ n : MulAut V, n ∈ G ∧ (∀ x ∈ X, n * x * n⁻¹ ∈ X) ∧ c₁ = n * t * n⁻¹ := by
  classical
  have hm : 7 ≤ m := c.hm
  obtain ⟨τ, hτa, hτb⟩ := cbp_exists_alt_pair (by omega : 4 ≤ m + 2) D.hab hpq
  set x₂ : MulAut V := (D.θ.symm τ : MulAut V) with hx₂
  have hx₂X : x₂ ∈ X := (D.θ.symm τ).2
  have hθx₂ : D.θ ⟨x₂, hx₂X⟩ = τ := by
    have : (⟨x₂, hx₂X⟩ : ↥X) = D.θ.symm τ := Subtype.ext rfl
    rw [this, D.θ.apply_symm_apply]
  have hx₂G : x₂ ∈ G := c.X_le_G hx₂X
  set c₂ : MulAut V := x₂⁻¹ * c₁ * x₂ with hc₂
  have hc₂G : c₂ ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hx₂G) hc₁G) hx₂G
  have hc₂2 : c₂ ^ 2 = 1 := by
    have h1 : c₁ * c₁ = 1 := by rw [← pow_two]; exact hc₁2
    rw [hc₂, pow_two]
    calc x₂⁻¹ * c₁ * x₂ * (x₂⁻¹ * c₁ * x₂) = x₂⁻¹ * (c₁ * c₁) * x₂ := by group
      _ = 1 := by rw [h1]; group
  have hn₂ : ∀ y ∈ X, c₂ * y * c₂⁻¹ ∈ X := by
    intro y hy
    have : c₂ * y * c₂⁻¹ = x₂⁻¹ * (c₁ * (x₂ * y * x₂⁻¹) * c₁⁻¹) * x₂ := by rw [hc₂]; group
    rw [this]
    exact X.mul_mem (X.mul_mem (X.inv_mem hx₂X) (hn _ (X.mul_mem (X.mul_mem hx₂X hy)
      (X.inv_mem hx₂X)))) hx₂X
  have hτs : (τ : Equiv.Perm (Fin (m + 2)))⁻¹ * Equiv.swap p q * (τ : Equiv.Perm (Fin (m + 2))) =
      Equiv.swap D.a D.b := by
    have h1 := Equiv.swap_apply_apply (τ : Equiv.Perm (Fin (m + 2))) D.a D.b
    rw [hτa, hτb] at h1
    rw [h1]
    group
  have hind : ∀ (y : MulAut V) (hy : y ∈ X),
      (D.θ ⟨c₂ * y * c₂⁻¹, hn₂ y hy⟩ : Equiv.Perm (Fin (m + 2))) =
        Equiv.swap D.a D.b * (D.θ ⟨y, hy⟩ : Equiv.Perm (Fin (m + 2))) *
          (Equiv.swap D.a D.b)⁻¹ := by
    intro y hy
    have hy' : x₂ * y * x₂⁻¹ ∈ X := X.mul_mem (X.mul_mem hx₂X hy) (X.inv_mem hx₂X)
    have h1 := hσ _ hy'
    have e1 : (D.θ ⟨x₂ * y * x₂⁻¹, hy'⟩ : Equiv.Perm (Fin (m + 2))) =
        (τ : Equiv.Perm (Fin (m + 2))) * (D.θ ⟨y, hy⟩ : Equiv.Perm (Fin (m + 2))) *
          (τ : Equiv.Perm (Fin (m + 2)))⁻¹ := by
      have h3 : (⟨x₂ * y * x₂⁻¹, hy'⟩ : ↥X) = ⟨x₂, hx₂X⟩ * ⟨y, hy⟩ * ⟨x₂, hx₂X⟩⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv, hθx₂]
      rfl
    have e2 : (D.θ ⟨c₂ * y * c₂⁻¹, hn₂ y hy⟩ : Equiv.Perm (Fin (m + 2))) =
        (τ : Equiv.Perm (Fin (m + 2)))⁻¹ *
          (D.θ ⟨c₁ * (x₂ * y * x₂⁻¹) * c₁⁻¹, hn _ hy'⟩ : Equiv.Perm (Fin (m + 2))) *
          (τ : Equiv.Perm (Fin (m + 2))) := by
      have h2 : (⟨c₂ * y * c₂⁻¹, hn₂ y hy⟩ : ↥X) =
          ⟨x₂, hx₂X⟩⁻¹ * ⟨c₁ * (x₂ * y * x₂⁻¹) * c₁⁻¹, hn _ hy'⟩ * ⟨x₂, hx₂X⟩ := by
        apply Subtype.ext
        show c₂ * y * c₂⁻¹ = x₂⁻¹ * (c₁ * (x₂ * y * x₂⁻¹) * c₁⁻¹) * x₂
        rw [hc₂]; group
      rw [h2, map_mul, map_mul, map_inv, hθx₂]
      rfl
    rw [e2, h1, e1, ← hτs]
    group
  have hcent : ∀ y ∈ X, c₂ * y * c₂⁻¹ = t * y * t⁻¹ := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ X := D.hn y hy
    have h1 : (⟨c₂ * y * c₂⁻¹, hn₂ y hy⟩ : ↥X) = ⟨t * y * t⁻¹, hty⟩ := by
      apply D.θ.injective
      apply Subtype.ext
      rw [hind y hy, D.hconj y hy]
    exact congrArg Subtype.val h1
  set q₀ : MulAut V := t⁻¹ * c₂ with hq₀
  have hq₀G : q₀ ∈ G := G.mul_mem (G.inv_mem c.htG) hc₂G
  have hq₀X : q₀ ∈ Subgroup.centralizer (X : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hcent y hy
    calc y * q₀ = t⁻¹ * (t * y * t⁻¹) * c₂ := by rw [hq₀]; group
      _ = t⁻¹ * (c₂ * y * c₂⁻¹) * c₂ := by rw [h1]
      _ = q₀ * y := by rw [hq₀]; group
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact c.ht2)
  have hinv : t * q₀ * t⁻¹ = q₀⁻¹ := by
    have h1 : c₂ * c₂ = 1 := by rw [← pow_two]; exact hc₂2
    have h2 : c₂ = t * q₀ := by rw [hq₀]; group
    rw [h2] at h1
    have h3 : t * q₀ * t = q₀⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← h1]; group)
    rw [htt]
    exact h3
  have hodd : Odd (orderOf q₀) := by
    have hQ := c.cfg.odd_card_centralizer c.hm c.hodd c.hY c.X_le_G c.hX.toCbAlg
    have hmem : q₀ ∈ G ⊓ Subgroup.centralizer (X : Set (MulAut V)) := ⟨hq₀G, hq₀X⟩
    have hd : orderOf (⟨q₀, hmem⟩ : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V)))) ∣
        Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V))) := orderOf_dvd_natCard _
    have hd' : orderOf q₀ ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V))) := by
      rw [← Subgroup.orderOf_coe (⟨q₀, hmem⟩ : ↥(G ⊓ Subgroup.centralizer (X : Set _)))] at hd
      exact hd
    exact Odd.of_dvd_nat hQ hd'
  obtain ⟨r, hr, hrt⟩ := cbo_exists_conj_of_inv hinv hodd
  have hrQ : r ∈ G ⊓ Subgroup.centralizer (X : Set (MulAut V)) :=
    (Subgroup.zpowers_le (H := G ⊓ Subgroup.centralizer (X : Set (MulAut V)))).mpr ⟨hq₀G, hq₀X⟩ hr
  have hrc : ∀ y ∈ X, r * y = y * r := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hrQ.2 y hy).symm
  refine ⟨x₂ * r, G.mul_mem hx₂G hrQ.1, ?_, ?_⟩
  · intro y hy
    have h1 : x₂ * r * y * (x₂ * r)⁻¹ = x₂ * y * x₂⁻¹ := by
      have : r * y * r⁻¹ = y := by rw [hrc y hy]; group
      calc x₂ * r * y * (x₂ * r)⁻¹ = x₂ * (r * y * r⁻¹) * x₂⁻¹ := by group
        _ = x₂ * y * x₂⁻¹ := by rw [this]
    rw [h1]
    exact X.mul_mem (X.mul_mem hx₂X hy) (X.inv_mem hx₂X)
  · have h1 : c₂ = r * t * r⁻¹ := by
      rw [hrt, hq₀]; group
    calc c₁ = x₂ * c₂ * x₂⁻¹ := by rw [hc₂]; group
      _ = x₂ * r * t * (x₂ * r)⁻¹ := by rw [h1]; group

include c in
theorem normalizes_X_of_conj_normalizes {h : MulAut V} (hG : h ∈ G)
    (hn : ∀ x ∈ X, (h * t * h⁻¹) * x * (h * t * h⁻¹)⁻¹ ∈ X) :
    ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  have hc₁G : h * t * h⁻¹ ∈ G := G.mul_mem (G.mul_mem hG c.htG) (G.inv_mem hG)
  have hc₁2 : (h * t * h⁻¹) ^ 2 = 1 := by rw [conj_pow, c.ht2]; group
  obtain ⟨p, q, hpq, hσ⟩ := c.induces_transposition D hG hn
  obtain ⟨n, hnG, hnX, hnt⟩ := c.exists_conj_of_transposition D hc₁G hc₁2 hn hpq hσ
  have hcomm : (n⁻¹ * h) * t = t * (n⁻¹ * h) := by
    have : n⁻¹ * (h * t * h⁻¹) * n = t := by rw [hnt]; group
    calc (n⁻¹ * h) * t = n⁻¹ * (h * t * h⁻¹) * n * (n⁻¹ * h) := by group
      _ = t * (n⁻¹ * h) := by rw [this]
  have h1 := c.normalizes_X_of_comm (G.mul_mem (G.inv_mem hnG) hG) hcomm
  intro x hx
  have h2 : h * x * h⁻¹ = n * ((n⁻¹ * h) * x * (n⁻¹ * h)⁻¹) * n⁻¹ := by group
  rw [h2]
  exact hnX _ (h1 x hx)

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
