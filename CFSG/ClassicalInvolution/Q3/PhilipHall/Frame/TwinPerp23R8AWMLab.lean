module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

section Label

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)

theorem injOn_of_label (hn : 5 ≤ n) {R₀ : Subgroup G} (hR₀ : R₀ ≤ pSpan P) (h8 : Nat.card R₀ = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (R₀.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) {l₁ l₂ : G} (h₁ : l₁ ∈ R₀)
    (h₂ : l₂ ∈ R₀) (he : I.φ ⟨l₁, hR₀ h₁⟩ = I.φ ⟨l₂, hR₀ h₂⟩) : l₁ = l₂ := by
  let f : ↥(R₀.subgroupOf (pSpan P)) → ↥(AE.memBar α h b) := fun x =>
    ⟨I.φ x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥(R₀.subgroupOf (pSpan P)) ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar hn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀).toEquiv, h8]
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  have := @hinj ⟨⟨l₁, hR₀ h₁⟩, Subgroup.mem_subgroupOf.mpr h₁⟩
    ⟨⟨l₂, hR₀ h₂⟩, Subgroup.mem_subgroupOf.mpr h₂⟩ (Subtype.ext he)
  exact congrArg (fun x : ↥(R₀.subgroupOf (pSpan P)) => ((x : ↥(pSpan P)) : G)) this

theorem map_eq_zBar_of_label (hn : 5 ≤ n) {R₀ : Subgroup G} (hR₀ : R₀ ≤ pSpan P)
    (h8 : Nat.card R₀ = 8) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (R₀.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) {u : G}
    (hu : IsUniqueInvolution R₀ u) : I.φ ⟨u, hR₀ hu.mem⟩ = AE.zBar α h := by
  have hmem : I.φ ⟨u, hR₀ hu.mem⟩ ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨⟨u, hR₀ hu.mem⟩, Subgroup.mem_subgroupOf.mpr hu.mem, rfl⟩
  have hsq : I.φ ⟨u, hR₀ hu.mem⟩ * I.φ ⟨u, hR₀ hu.mem⟩ = 1 := by
    rw [← map_mul, ← map_one I.φ]
    congr 1
    exact Subtype.ext hu.sq
  rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
  · exfalso
    apply hu.ne_one
    have : I.φ ⟨u, hR₀ hu.mem⟩ = I.φ ⟨1, hR₀ R₀.one_mem⟩ := by
      rw [h1]
      exact (map_one I.φ).symm
    exact injOn_of_label I hn hR₀ h8 hlab hu.mem R₀.one_mem this
  · exact h1

theorem map_oddCore_eq_bot (hn : 5 ≤ n) {J : Subgroup G} (hJ : J ≤ pSpan P)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (J.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b)
    (hodd : Odd (Nat.card ↥(oddCoreOf J))) :
    ((oddCoreOf J).subgroupOf (pSpan P)).map I.φ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  have hyO : (y : G) ∈ oddCoreOf J := Subgroup.mem_subgroupOf.mp hy
  have hyJ : (y : G) ∈ J := (oddCoreOf_le_self J) hyO
  have hx : I.φ y ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hyJ, rfl⟩
  have h8 : I.φ y ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥(AE.memBar α h b)) (x := ⟨I.φ y, hx⟩)
    rw [AE.natCard_memBar hn] at this
    exact congrArg Subtype.val this
  have hm : I.φ y ^ Nat.card ↥(oddCoreOf J) = 1 := by
    have h1 : (y : G) ^ Nat.card ↥(oddCoreOf J) = 1 := by
      have := pow_card_eq_one' (G := ↥(oddCoreOf J)) (x := ⟨y, hyO⟩)
      exact congrArg Subtype.val this
    have h2 : y ^ Nat.card ↥(oddCoreOf J) = 1 := Subtype.ext h1
    rw [← map_pow, h2, map_one]
  have hcop : Nat.Coprime (Nat.card ↥(oddCoreOf J)) 8 := by
    have : Nat.Coprime (Nat.card ↥(oddCoreOf J)) 2 := Nat.coprime_two_right.mpr hodd
    exact Nat.Coprime.pow_right 3 this
  have h3 := Nat.eq_one_of_dvd_coprimes hcop.symm (orderOf_dvd_of_pow_eq_one h8)
    (orderOf_dvd_of_pow_eq_one hm)
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp h3

theorem map_eq_of_le_sup_oddCore (hn : 5 ≤ n) {J R₀ : Subgroup G} (hJ : J ≤ pSpan P) (hR₀J : R₀ ≤ J)
    (hsup : J ≤ R₀ ⊔ oddCoreOf J) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (J.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b)
    (hodd : Odd (Nat.card ↥(oddCoreOf J))) :
    (R₀.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b := by
  refine le_antisymm ?_ ?_
  · rw [← hlab]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hR₀J (Subgroup.mem_subgroupOf.mp hx))
  · rw [← hlab]
    have hOJ : oddCoreOf J ≤ pSpan P := (oddCoreOf_le_self J).trans hJ
    have h1 : J.subgroupOf (pSpan P) ≤ R₀.subgroupOf (pSpan P) ⊔ (oddCoreOf J).subgroupOf (pSpan P) := by
      rw [← Subgroup.subgroupOf_sup (hR₀J.trans hJ) hOJ]
      exact fun x hx => Subgroup.mem_subgroupOf.mpr (hsup (Subgroup.mem_subgroupOf.mp hx))
    refine (Subgroup.map_mono h1).trans ?_
    rw [Subgroup.map_sup, map_oddCore_eq_bot I hn hJ hlab hodd, sup_bot_eq]

end Label

section Central

variable {H A : Type*} [Group H] [Group A]

theorem comm_of_pow_three_of_central_ker (f : H →* A) (hker : f.ker ≤ Subgroup.center H) {x t : H} {k : ℕ}
    (ht : t * t = 1) (hx : x ^ 3 ^ k = 1) (h : f x * f t = f t * f x) : x * t = t * x := by
  set c := t⁻¹ * (x * t * x⁻¹) with hc
  have hcker : c ∈ f.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, map_mul, map_mul, map_inv, h]
    group
  have hcc : ∀ y : H, y * c = c * y := fun y => Subgroup.mem_center_iff.mp (hker hcker) y
  have hxt : x * t * x⁻¹ = t * c := by rw [hc]; group
  have hpow : ∀ m : ℕ, x ^ m * t * (x ^ m)⁻¹ = t * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x ^ (m + 1) * t * (x ^ (m + 1))⁻¹ = x * (x ^ m * t * (x ^ m)⁻¹) * x⁻¹ := by
            rw [pow_succ']
            group
        _ = (x * t * x⁻¹) * (x * c ^ m * x⁻¹) := by rw [ih]; group
        _ = t * c ^ (m + 1) := by
            rw [hxt, show x * c ^ m * x⁻¹ = c ^ m by
              rw [(Commute.pow_right (show Commute x c from hcc x) m).eq]; group, pow_succ', mul_assoc]
  have hc2 : c * c = 1 := by
    have h1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht]; group
    rw [hxt] at h1
    have h2 : t * c * (t * c) = (t * t) * (c * c) := by
      calc t * c * (t * c) = t * (c * t) * c := by group
        _ = t * (t * c) * c := by rw [hcc t]
        _ = (t * t) * (c * c) := by group
    rw [h2, ht, one_mul] at h1
    exact h1
  have hc3 : c ^ 3 ^ k = 1 := by
    have := hpow (3 ^ k)
    rw [hx, one_mul, inv_one, mul_one] at this
    exact mul_left_cancel (this.symm.trans (mul_one t).symm)
  have hc1 : c = 1 := by
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hj, pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul] at hc3
    exact hc3
  rw [hc1] at hxt
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [hxt, mul_one]

theorem false_of_odd_pow_of_image (f : H →* A) {c : H} {m : ℕ} (hm : Odd m) (hc : c ^ m = 1)
    (h2 : f c * f c = 1) (h1 : f c ≠ 1) : False := by
  apply h1
  obtain ⟨j, rfl⟩ := hm
  have : f c ^ (2 * j + 1) = 1 := by rw [← map_pow, hc, map_one]
  rwa [pow_succ, pow_mul, pow_two, h2, one_pow, one_mul] at this

end Central

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM
