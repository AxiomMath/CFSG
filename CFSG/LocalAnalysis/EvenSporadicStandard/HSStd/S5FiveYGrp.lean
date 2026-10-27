module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveGood

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup

section Commuting

variable {G : Type*} [Group G] {H K : Subgroup G}

theorem commute_subtype (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (m : ↥H) (n : ↥K) :
    Commute (H.subtype m) (K.subtype n) :=
  hc m m.2 n n.2

theorem sup_eq_range_noncommCoprod (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    H ⊔ K = (MonoidHom.noncommCoprod H.subtype K.subtype (commute_subtype hc)).range := by
  apply le_antisymm
  · refine sup_le (fun h hh => ⟨(⟨h, hh⟩, 1), ?_⟩) (fun k hk => ⟨(1, ⟨k, hk⟩), ?_⟩)
    · simp [MonoidHom.noncommCoprod_apply]
    · simp [MonoidHom.noncommCoprod_apply]
  · rintro _ ⟨⟨h, k⟩, rfl⟩
    rw [MonoidHom.noncommCoprod_apply]
    exact mul_mem (mem_sup_left h.2) (mem_sup_right k.2)

theorem mem_sup_of_commute (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [sup_eq_range_noncommCoprod hc] at hx
  obtain ⟨⟨h, k⟩, rfl⟩ := hx
  exact ⟨h, h.2, k, k.2, by simp [MonoidHom.noncommCoprod_apply]⟩

theorem card_sup_of_commute (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  set Φ := MonoidHom.noncommCoprod H.subtype K.subtype (commute_subtype hc) with hΦ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨h, k⟩ hhk
    have hhk' : (h : G) * (k : G) = 1 := by simpa [hΦ, MonoidHom.noncommCoprod_apply] using hhk
    have hk : ((k : K) : G) = ((h : H) : G)⁻¹ := eq_inv_of_mul_eq_one_right hhk'
    have hmem : ((h : H) : G) ∈ H ⊓ K := ⟨h.2, by
      have := K.inv_mem k.2
      rwa [hk, inv_inv] at this⟩
    rw [hd, mem_bot] at hmem
    have hh : h = 1 := Subtype.ext hmem
    have hk1 : k = 1 := Subtype.ext (by rw [hk, hmem, inv_one]; rfl)
    rw [hh, hk1]
    rfl
  rw [sup_eq_range_noncommCoprod hc, ← hΦ, ← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofInjective Φ hinj).symm

end Commuting

section Centralizers

variable {X : Type*} [Group X]

theorem conj_comm_iff (g x c : X) :
    c * (g * x * g⁻¹) = g * x * g⁻¹ * c ↔ (g⁻¹ * c * g) * x = x * (g⁻¹ * c * g) := by
  constructor
  · intro h
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · intro h
    have := congrArg (fun z => g * z * g⁻¹) h
    simpa [mul_assoc] using this

theorem card_centralizer_conj (g x : X) :
    Nat.card ↥(centralizer ({g * x * g⁻¹} : Set X)) = Nat.card ↥(centralizer ({x} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * (c : X) * g, ?_⟩
      invFun := fun c => ⟨g * (c : X) * g⁻¹, ?_⟩
      left_inv := fun c => ?_
      right_inv := fun c => ?_ }
  · exact mem_centralizer_singleton_iff.2
      ((conj_comm_iff g x c).1 (mem_centralizer_singleton_iff.1 c.2))
  · rw [mem_centralizer_singleton_iff, conj_comm_iff]
    have := mem_centralizer_singleton_iff.1 c.2
    simpa [mul_assoc] using this
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])

theorem card_inf_centralizer_conj (M : Subgroup X) {g : X} (hg : g ∈ M) (x : X) :
    Nat.card ↥(M ⊓ centralizer ({g * x * g⁻¹} : Set X)) =
      Nat.card ↥(M ⊓ centralizer ({x} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * (c : X) * g, M.mul_mem (M.mul_mem (M.inv_mem hg) c.2.1) hg, ?_⟩
      invFun := fun c => ⟨g * (c : X) * g⁻¹, M.mul_mem (M.mul_mem hg c.2.1) (M.inv_mem hg), ?_⟩
      left_inv := fun c => ?_
      right_inv := fun c => ?_ }
  · exact mem_centralizer_singleton_iff.2
      ((conj_comm_iff g x c).1 (mem_centralizer_singleton_iff.1 c.2.2))
  · refine mem_centralizer_singleton_iff.2 ?_
    rw [conj_comm_iff]
    have := mem_centralizer_singleton_iff.1 c.2.2
    simpa [mul_assoc] using this
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])

theorem card_centralizer_subtype (P : Subgroup X) (x : ↥P) :
    Nat.card ↥(centralizer ({x} : Set ↥P)) = Nat.card ↥(P ⊓ centralizer ({(x : X)} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨(c.1 : X), c.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))⟩
      invFun := fun c => ⟨⟨c.1, c.2.1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 c.2.2))⟩
      left_inv := fun c => rfl
      right_inv := fun c => rfl }

theorem map_subtype_centralizer (P : Subgroup X) (x : ↥P) :
    (centralizer ({x} : Set ↥P)).map P.subtype = P ⊓ centralizer ({(x : X)} : Set X) := by
  ext z
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, congrArg Subtype.val ha⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subtype.ext h, rfl⟩

theorem map_conj_inf_centralizer (M : Subgroup X) {g : X} (hg : g ∈ M) (x : X) :
    (M ⊓ centralizer ({g * x * g⁻¹} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      M ⊓ centralizer ({x} : Set X) := by
  ext z
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨c, ⟨hcM, hcC⟩, rfl⟩
    exact ⟨M.mul_mem (M.mul_mem (M.inv_mem hg) hcM) hg, (conj_comm_iff g x c).1 hcC⟩
  · rintro ⟨hzM, hzC⟩
    refine ⟨g * z * g⁻¹, ⟨M.mul_mem (M.mul_mem hg hzM) (M.inv_mem hg), ?_⟩, by group⟩
    rw [conj_comm_iff]
    simpa [mul_assoc] using hzC

theorem map_centralizer_equiv {Y : Type*} [Group Y] (φ : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map φ.toMonoidHom = centralizer ({φ x} : Set Y) := by
  ext y
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, ha]
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hy

end Centralizers

section Involutions

variable {G : Type*} [Group G]

theorem zpow_involution {x : G} (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hsq : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  have hk : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hsq]
    simp
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h]
    simp
  · right
    rw [hk, h]
    simp

theorem mem_zpowers_involution {x : G} (hx : x * x = 1) {a : G} (ha : a ∈ zpowers x) :
    a = 1 ∨ a = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  exact zpow_involution hx k

theorem exists_conj_of_odd_order {x x' : G} (hx : x * x = 1) (hx' : x' * x' = 1)
    (hodd : Odd (orderOf (x⁻¹ * x'))) : ∃ c : G, c * x * c⁻¹ = x' := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  set o := x⁻¹ * x' with ho
  have hx'o : x' = x * o := by rw [ho]; group
  have hxox : x * o * x⁻¹ = o⁻¹ := by
    have h1 : x * o * (x * o) = 1 := by rw [← hx'o]; exact hx'
    have h2 : x * o * x * o = 1 := by simpa [mul_assoc] using h1
    have h3 : x * o * x = o⁻¹ := mul_eq_one_iff_eq_inv.1 h2
    rwa [hxi]
  have hpow : ∀ n : ℕ, x * o ^ n * x⁻¹ = (o⁻¹) ^ n := fun n => by
    have := map_pow (MulAut.conj x) o n
    simpa [MulAut.conj_apply, hxox] using this
  obtain ⟨k, hk⟩ := hodd
  have hom : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  set p := o ^ (k + 1) with hp
  have hpp : p * p = o := by
    rw [hp, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hom, one_mul]
  have hxp : x * p * x⁻¹ = p⁻¹ := by rw [hp, hpow, inv_pow]
  have h3 : x * p = p⁻¹ * x := by
    have := congrArg (· * x) hxp
    simpa [mul_assoc] using this
  have h4 : x * o = o⁻¹ * x := by
    have := congrArg (· * x) hxox
    simpa [mul_assoc] using this
  refine ⟨p⁻¹, ?_⟩
  calc p⁻¹ * x * p⁻¹⁻¹ = p⁻¹ * (x * p) := by rw [inv_inv, mul_assoc]
    _ = p⁻¹ * (p⁻¹ * x) := by rw [h3]
    _ = (p * p)⁻¹ * x := by rw [mul_inv_rev, mul_assoc]
    _ = o⁻¹ * x := by rw [hpp]
    _ = x' := by rw [← h4, hx'o]

end Involutions

section OddCore

variable {K : Type} [Group K] [Finite K]

theorem exists_conj_of_mk_conj {x x' : K} (hx : x * x = 1) (hx' : x' * x' = 1)
    (h : ∃ c : K ⧸ CFSG.oddCore K, c * QuotientGroup.mk x * c⁻¹ = QuotientGroup.mk x') :
    ∃ g : K, g * x * g⁻¹ = x' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c
  set x'' := g₀ * x * g₀⁻¹ with hx''
  have hx''2 : x'' * x'' = 1 := by
    rw [hx'']
    calc g₀ * x * g₀⁻¹ * (g₀ * x * g₀⁻¹) = g₀ * (x * x) * g₀⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hmk : (QuotientGroup.mk x'' : K ⧸ CFSG.oddCore K) = QuotientGroup.mk x' := by
    rw [← hc, hx'']
    simp
  have hmem : x'⁻¹ * x'' ∈ CFSG.oddCore K := QuotientGroup.eq.1 hmk.symm
  have hodd : Odd (orderOf (x'⁻¹ * x'')) :=
    Odd.of_dvd_nat odd_card_oddCore' (Subgroup.orderOf_dvd_natCard _ hmem)
  obtain ⟨d, hd⟩ := exists_conj_of_odd_order hx' hx''2 hodd
  refine ⟨d⁻¹ * g₀, ?_⟩
  calc d⁻¹ * g₀ * x * (d⁻¹ * g₀)⁻¹ = d⁻¹ * (g₀ * x * g₀⁻¹) * d := by group
    _ = d⁻¹ * x'' * d := by rw [hx'']
    _ = d⁻¹ * (d * x' * d⁻¹) * d := by rw [hd]
    _ = x' := by group

end OddCore

end CFSG.EvenSporadicStandard.HSStd.FiveY
