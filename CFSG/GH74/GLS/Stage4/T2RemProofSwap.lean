module

public import CFSG.GH74.GLS.Stage4.T2Cent
public import CFSG.GH74.GLS.Stage4.T2Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest.Rem.Swap

variable {G : Type} [Group G]

theorem exists_mem_notMem_finset [Finite G] (P : Subgroup G) (s : Finset G)
    (h : s.card < Nat.card ↥P) : ∃ k ∈ P, k ∉ s := by
  obtain ⟨e, he, hes⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := (s : Set G))
    (t := (P : Set G)) (by rwa [Set.ncard_coe_finset, ← Nat.card_coe_set_eq])
  exact ⟨e, he, by simpa using hes⟩

def swapNorm (t k : G) : G := k * (t * k * t⁻¹)

theorem swapNorm_mul {t : G} {K₁ K₂ : Subgroup G} (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {k k' : G} (hk : k ∈ K₁) (hk' : k' ∈ K₁) :
    swapNorm t (k * k') = swapNorm t k * swapNorm t k' := by
  have h : k' * (t * k * t⁻¹) = (t * k * t⁻¹) * k' := hcomm k' hk' _ (hswap k hk)
  unfold swapNorm
  calc k * k' * (t * (k * k') * t⁻¹) = k * (k' * (t * k * t⁻¹)) * (t * k' * t⁻¹) := by group
    _ = k * ((t * k * t⁻¹) * k') * (t * k' * t⁻¹) := by rw [h]
    _ = k * (t * k * t⁻¹) * (k' * (t * k' * t⁻¹)) := by group

theorem swapNorm_mem_sup {t : G} {K₁ K₂ : Subgroup G} (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂)
    {k : G} (hk : k ∈ K₁) : swapNorm t k ∈ K₁ ⊔ K₂ :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (hswap k hk))

theorem swapNorm_commute {t : G} {K₁ K₂ : Subgroup G} (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (htt : t * t = 1) (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {k : G} (hk : k ∈ K₁) :
    swapNorm t k * t = t * swapNorm t k := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h : k * (t * k * t⁻¹) = (t * k * t⁻¹) * k := hcomm k hk _ (hswap k hk)
  unfold swapNorm
  calc k * (t * k * t⁻¹) * t = (t * k * t⁻¹ * k) * t := by rw [h]
    _ = t * (k * (t * k * t⁻¹)) := by rw [ht]; group

theorem swapNorm_commute_z {z t : G} {K₁ K₂ : Subgroup G} (hz₁ : z ∈ K₁) (hz₂ : z ∈ K₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {k : G}
    (hk : k ∈ K₁) : z * swapNorm t k = swapNorm t k * z := by
  have h1 : k * z = z * k := hcomm k hk z hz₂
  have h2 : z * (t * k * t⁻¹) = (t * k * t⁻¹) * z := hcomm z hz₁ _ (hswap k hk)
  unfold swapNorm
  calc z * (k * (t * k * t⁻¹)) = (z * k) * (t * k * t⁻¹) := by group
    _ = (k * z) * (t * k * t⁻¹) := by rw [h1]
    _ = k * (z * (t * k * t⁻¹)) := by group
    _ = k * ((t * k * t⁻¹) * z) := by rw [h2]
    _ = k * (t * k * t⁻¹) * z := by group

theorem swapNorm_one (t : G) : swapNorm t 1 = 1 := by simp [swapNorm]

theorem swapNorm_z {z t : G} (hz : z * z = 1) (htz : t * z = z * t) : swapNorm t z = 1 := by
  have h : t * z * t⁻¹ = z := by rw [htz]; group
  unfold swapNorm
  rw [h]
  exact hz

theorem swapNorm_eq_one_iff {z t : G} {K₁ K₂ : Subgroup G} (hz : z * z = 1)
    (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z) (htz : t * z = z * t)
    (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {k : G} (hk : k ∈ K₁) :
    swapNorm t k = 1 ↔ k = 1 ∨ k = z := by
  constructor
  · intro h
    have hk2 : k ∈ K₂ := by
      have e : k = (t * k * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [e]
      exact K₂.inv_mem (hswap k hk)
    exact t2C_zpowers_cases hz (hinter ⟨hk, hk2⟩)
  · rintro (h | h)
    · rw [h]
      exact swapNorm_one t
    · rw [h]
      exact swapNorm_z hz htz

theorem swapNorm_ne_z {z t : G} {K₁ K₂ : Subgroup G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hz₂ : z ∈ K₂) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z) (htz : t * z = z * t)
    (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {k : G} (hk : k ∈ K₁) : swapNorm t k ≠ z := by
  intro h
  have hk2 : k ∈ K₂ := by
    have e : k = z * (t * k * t⁻¹)⁻¹ := eq_mul_inv_of_mul_eq h
    rw [e]
    exact K₂.mul_mem hz₂ (K₂.inv_mem (hswap k hk))
  have h1 : swapNorm t k = 1 := (swapNorm_eq_one_iff hz hinter htz hswap hk).2
    (t2C_zpowers_cases hz (hinter ⟨hk, hk2⟩))
  exact hz1 (h.symm.trans h1)

theorem isPGroup_sup_conj_zpowers [Finite G] {t : G} {K₁ K₂ : Subgroup G}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (htt : t * t = 1)
    (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) {P : Subgroup G} (hPK : P ≤ K₁) (hP2 : IsPGroup 2 ↥P) :
    IsPGroup 2 ↥((P ⊔ P.map (MulAut.conj t).toMonoidHom) ⊔ Subgroup.zpowers t) := by
  set P' : Subgroup G := P.map (MulAut.conj t).toMonoidHom with hP'
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmemP' : ∀ y ∈ P, t * y * t⁻¹ ∈ P' := fun y hy => ⟨y, hy, rfl⟩
  have hP'mem : ∀ x ∈ P', ∃ y ∈ P, x = t * y * t⁻¹ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  have hP'K : P' ≤ K₂ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hP'mem x hx
    exact hswap y (hPK hy)
  have hcPP' : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x := fun x hx y hy => hcomm x (hPK hx) y (hP'K hy)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hP2
  have hPexp : ∀ p ∈ P, p ^ (2 ^ a) = 1 := by
    intro p hp
    have h := Subgroup.orderOf_dvd_natCard P hp
    rw [ha] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have hP'exp : ∀ x ∈ P', x ^ (2 ^ a) = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hP'mem x hx
    rw [conj_pow, hPexp y hy, mul_one, mul_inv_cancel]
  set Q : Subgroup G := P ⊔ P' with hQ
  have hQexp : ∀ w ∈ Q, w ^ (2 ^ a) = 1 := by
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_comm hcPP' w).1 hw
    have hxy : Commute x y := hcPP' x hx y hy
    rw [hxy.mul_pow, hPexp x hx, hP'exp y hy, mul_one]
  have hn : ∀ w ∈ Q, t * w * t⁻¹ ∈ Q := by
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_comm hcPP' w).1 hw
    obtain ⟨y', hy', rfl⟩ := hP'mem y hy
    have e : t * (x * (t * y' * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * y' := by
      rw [ht]
      calc t * (x * (t * y' * t)) * t = t * x * t * y' * (t * t) := by group
        _ = t * x * t * y' := by rw [htt, mul_one]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hmemP' x hx)) (Subgroup.mem_sup_left hy')
  have hn' : ∀ w ∈ Q, t⁻¹ * w * t ∈ Q := by
    intro w hw
    have h := hn w hw
    rw [ht] at h ⊢
    exact h
  have hs : t * t ∈ Q := by
    rw [htt]
    exact Q.one_mem
  intro g
  refine ⟨a + 1, ?_⟩
  apply Subtype.ext
  have h := t2S_pow_of_ext hn hn' hs hQexp g.2
  have e : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  rw [e]
  simpa using h

end CFSG.GH74.GLS.Stage4.Rest.Rem.Swap

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

open Swap

theorem swap_contradiction {G : Type} [Group G] [Finite G] {z t : G} {K₁ K₂ : Subgroup G}
    (hz : z * z = 1) (hz1 : z ≠ 1) (hz₁ : z ∈ K₁) (hz₂ : z ∈ K₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z)
    (htt : t * t = 1) (htz : t * z = z * t)
    (hswap : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂)
    (P : Subgroup G) (hPK : P ≤ K₁) (hzP : z ∈ P) (hP2 : IsPGroup 2 ↥P) (hP8 : 8 ≤ Nat.card ↥P)
    (hL : ∀ W : Subgroup G, IsPGroup 2 ↥W → t ∈ W → W ≤ K₁ ⊔ K₂ ⊔ Subgroup.zpowers t →
      ∃ U : Finset G, U.card ≤ 4 ∧ ∀ x ∈ W, x ∈ K₁ ⊔ K₂ → x * t = t * x → x ∈ U) : False := by
  classical
  obtain ⟨k₁, hk₁P, hk₁⟩ := exists_mem_notMem_finset P ({1, z} : Finset G)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨k₂, hk₂P, hk₂⟩ := exists_mem_notMem_finset P ({1, z, k₁, k₁ * z} : Finset G)
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk₁ hk₂
  obtain ⟨hk₁1, hk₁z⟩ := hk₁
  obtain ⟨hk₂1, hk₂z, hk₂k₁, hk₂k₁z⟩ := hk₂
  have hk₁K : k₁ ∈ K₁ := hPK hk₁P
  have hk₂K : k₂ ∈ K₁ := hPK hk₂P
  have hnorm1 : ∀ k ∈ K₁, swapNorm t k = 1 ↔ k = 1 ∨ k = z := fun k hk =>
    swapNorm_eq_one_iff hz hinter htz hswap hk
  have hnez : ∀ k ∈ K₁, swapNorm t k ≠ z := fun k hk =>
    swapNorm_ne_z hz hz1 hz₂ hinter htz hswap hk
  have ha1 : swapNorm t k₁ ≠ 1 := fun h => by
    rcases (hnorm1 k₁ hk₁K).1 h with h | h
    exacts [hk₁1 h, hk₁z h]
  have hb1 : swapNorm t k₂ ≠ 1 := fun h => by
    rcases (hnorm1 k₂ hk₂K).1 h with h | h
    exacts [hk₂1 h, hk₂z h]
  have haz : swapNorm t k₁ ≠ z := hnez k₁ hk₁K
  have hbz : swapNorm t k₂ ≠ z := hnez k₂ hk₂K
  have hmK : k₁⁻¹ * k₂ ∈ K₁ := K₁.mul_mem (K₁.inv_mem hk₁K) hk₂K
  have hbm : swapNorm t k₂ = swapNorm t k₁ * swapNorm t (k₁⁻¹ * k₂) := by
    rw [← swapNorm_mul hcomm hswap hk₁K hmK, mul_inv_cancel_left]
  have hzcomm : z * swapNorm t k₁ = swapNorm t k₁ * z :=
    swapNorm_commute_z hz₁ hz₂ hcomm hswap hk₁K
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hab : swapNorm t k₁ ≠ swapNorm t k₂ := by
    intro h
    have h1 : swapNorm t (k₁⁻¹ * k₂) = 1 := by
      have e : swapNorm t k₁ * swapNorm t (k₁⁻¹ * k₂) = swapNorm t k₁ * 1 := by
        rw [← hbm, mul_one]
        exact h.symm
      exact mul_left_cancel e
    rcases (hnorm1 _ hmK).1 h1 with h2 | h2
    · exact hk₂k₁ (inv_mul_eq_one.1 h2).symm
    · exact hk₂k₁z (inv_mul_eq_iff_eq_mul.1 h2)
  have habz : z * swapNorm t k₁ ≠ swapNorm t k₂ := by
    intro h
    have h1 : swapNorm t (k₁⁻¹ * k₂) = z := by
      have e : swapNorm t k₁ * swapNorm t (k₁⁻¹ * k₂) = swapNorm t k₁ * z := by
        rw [← hbm, ← hzcomm]
        exact h.symm
      exact mul_left_cancel e
    exact hnez _ hmK h1
  have d01 : (1 : G) ≠ z := fun h => hz1 h.symm
  have d02 : (1 : G) ≠ swapNorm t k₁ := fun h => ha1 h.symm
  have d03 : (1 : G) ≠ z * swapNorm t k₁ := fun h =>
    haz ((eq_inv_of_mul_eq_one_right h.symm).trans hzinv)
  have d04 : (1 : G) ≠ swapNorm t k₂ := fun h => hb1 h.symm
  have d12 : z ≠ swapNorm t k₁ := fun h => haz h.symm
  have d13 : z ≠ z * swapNorm t k₁ := fun h =>
    ha1 (mul_left_cancel (a := z) (by rw [mul_one]; exact h.symm))
  have d14 : z ≠ swapNorm t k₂ := fun h => hbz h.symm
  have d23 : swapNorm t k₁ ≠ z * swapNorm t k₁ := fun h =>
    hz1 (mul_right_cancel (b := swapNorm t k₁) (by rw [one_mul]; exact h.symm))
  set P' : Subgroup G := P.map (MulAut.conj t).toMonoidHom with hP'
  have hmemP' : ∀ y ∈ P, t * y * t⁻¹ ∈ P' := fun y hy => ⟨y, hy, rfl⟩
  have hP'K : P' ≤ K₂ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hswap y (hPK hy)
  set W : Subgroup G := (P ⊔ P') ⊔ Subgroup.zpowers t with hW
  have hWp : IsPGroup 2 ↥W := isPGroup_sup_conj_zpowers hcomm htt hswap hPK hP2
  have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hWle : W ≤ K₁ ⊔ K₂ ⊔ Subgroup.zpowers t := sup_le_sup (sup_le_sup hPK hP'K) le_rfl
  have hzW : z ∈ W := Subgroup.mem_sup_left (Subgroup.mem_sup_left hzP)
  have hφW : ∀ k ∈ P, swapNorm t k ∈ W := fun k hk =>
    W.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hmemP' k hk)))
  obtain ⟨U, hU4, hU⟩ := hL W hWp htW hWle
  have hsub : ({1, z, swapNorm t k₁, z * swapNorm t k₁, swapNorm t k₂} : Finset G) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    · exact hU 1 W.one_mem (Subgroup.one_mem _) (by rw [one_mul, mul_one])
    · exact hU z hzW (Subgroup.mem_sup_left hz₁) htz.symm
    · exact hU _ (hφW k₁ hk₁P) (swapNorm_mem_sup hswap hk₁K)
        (swapNorm_commute hcomm htt hswap hk₁K)
    · refine hU _ (W.mul_mem hzW (hφW k₁ hk₁P))
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hz₁) (swapNorm_mem_sup hswap hk₁K)) ?_
      calc z * swapNorm t k₁ * t = z * (swapNorm t k₁ * t) := by rw [mul_assoc]
        _ = z * (t * swapNorm t k₁) := by rw [swapNorm_commute hcomm htt hswap hk₁K]
        _ = (z * t) * swapNorm t k₁ := by rw [mul_assoc]
        _ = (t * z) * swapNorm t k₁ := by rw [htz]
        _ = t * (z * swapNorm t k₁) := by rw [mul_assoc]
    · exact hU _ (hφW k₂ hk₂P) (swapNorm_mem_sup hswap hk₂K)
        (swapNorm_commute hcomm htt hswap hk₂K)
  have hcard : ({1, z, swapNorm t k₁, z * swapNorm t k₁, swapNorm t k₂} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [d01, d02, d03, d04]),
      Finset.card_insert_of_notMem (by simp [d12, d13, d14]),
      Finset.card_insert_of_notMem (by simp [d23, hab]),
      Finset.card_insert_of_notMem (by simp [habz]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  omega

end CFSG.GH74.GLS.Stage4.Rest.Rem
