module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped Pointwise

section Words

variable {T : Type} [Group T]

@[expose] def wd (y c c' : T) (i j l : ℤ) : T := y ^ i * c ^ j * c' ^ l

theorem wd_mul {y c c' : T} (hyc : Commute y c) (hyc' : Commute y c') (hcc' : Commute c c')
    (i j l i' j' l' : ℤ) :
    wd y c c' i j l * wd y c c' i' j' l' = wd y c c' (i + i') (j + j') (l + l') := by
  unfold wd
  have e1 : c' ^ l * y ^ i' = y ^ i' * c' ^ l := (hyc'.symm.zpow_zpow l i').eq
  have e2 : c' ^ l * c ^ j' = c ^ j' * c' ^ l := (hcc'.symm.zpow_zpow l j').eq
  have e3 : c ^ j * y ^ i' = y ^ i' * c ^ j := (hyc.symm.zpow_zpow j i').eq
  calc y ^ i * c ^ j * c' ^ l * (y ^ i' * c ^ j' * c' ^ l')
      = y ^ i * c ^ j * (c' ^ l * y ^ i') * c ^ j' * c' ^ l' := by simp only [mul_assoc]
    _ = y ^ i * c ^ j * (y ^ i' * c' ^ l) * c ^ j' * c' ^ l' := by rw [e1]
    _ = y ^ i * (c ^ j * y ^ i') * c' ^ l * c ^ j' * c' ^ l' := by simp only [mul_assoc]
    _ = y ^ i * (y ^ i' * c ^ j) * c' ^ l * c ^ j' * c' ^ l' := by rw [e3]
    _ = y ^ i * y ^ i' * c ^ j * (c' ^ l * c ^ j') * c' ^ l' := by simp only [mul_assoc]
    _ = y ^ i * y ^ i' * c ^ j * (c ^ j' * c' ^ l) * c' ^ l' := by rw [e2]
    _ = y ^ (i + i') * c ^ (j + j') * c' ^ (l + l') := by
      rw [zpow_add, zpow_add, zpow_add]; simp only [mul_assoc]

theorem wd_zero (y c c' : T) : wd y c c' 0 0 0 = 1 := by simp [wd]

theorem wd_mod {y c c' : T} (hy : y ^ 3 = 1) (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1) (i j l : ℤ) :
    wd y c c' i j l = wd y c c' (i % 3) (j % 3) (l % 3) := by
  unfold wd
  rw [zpow_eq_zpow_emod' i hy, zpow_eq_zpow_emod' j hc, zpow_eq_zpow_emod' l hc']
  simp

theorem mem_closure_wd {y c c' : T} (hyc : Commute y c) (hyc' : Commute y c')
    (hcc' : Commute c c') {x : T} (hx : x ∈ closure ({y, c, c'} : Set T)) :
    ∃ i j l : ℤ, x = wd y c c' i j l := by
  let S : Subgroup T :=
    { carrier := {x | ∃ i j l : ℤ, x = wd y c c' i j l}
      mul_mem' := by
        rintro _ _ ⟨i, j, l, rfl⟩ ⟨i', j', l', rfl⟩
        exact ⟨i + i', j + j', l + l', wd_mul hyc hyc' hcc' i j l i' j' l'⟩
      one_mem' := ⟨0, 0, 0, (wd_zero y c c').symm⟩
      inv_mem' := by
        rintro _ ⟨i, j, l, rfl⟩
        refine ⟨-i, -j, -l, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [wd_mul hyc hyc' hcc']
        simp [wd] }
  have hle : closure ({y, c, c'} : Set T) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]; exact ⟨1, 0, 0, by simp [wd]⟩
    · rw [h]; exact ⟨0, 1, 0, by simp [wd]⟩
    · rw [h]; exact ⟨0, 0, 1, by simp [wd]⟩
  exact hle hx

theorem wd_mem_closure {y c c' : T} (i j l : ℤ) : wd y c c' i j l ∈ closure ({y, c, c'} : Set T) := by
  unfold wd
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _)
    (Subgroup.zpow_mem _ ?_ _)) (Subgroup.zpow_mem _ ?_ _)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem wd_inj {y c c' : T} (hyc : Commute y c) (hyc' : Commute y c') (hcc' : Commute c c')
    (hy : y ^ 3 = 1) (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1)
    (hcard : Nat.card ↥(closure ({y, c, c'} : Set T)) = 27) (i j l i' j' l' : ℤ)
    (h : wd y c c' i j l = wd y c c' i' j' l') :
    i % 3 = i' % 3 ∧ j % 3 = j' % 3 ∧ l % 3 = l' % 3 := by
  haveI : Finite ↥(closure ({y, c, c'} : Set T)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcast : ∀ n : ℤ, (((n % 3).toNat : ℕ) : ℤ) = n % 3 := fun n =>
    Int.toNat_of_nonneg (by omega)
  let g : Fin 3 × Fin 3 × Fin 3 → ↥(closure ({y, c, c'} : Set T)) := fun p =>
    ⟨wd y c c' (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ), wd_mem_closure _ _ _⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨i, j, l, rfl⟩ := mem_closure_wd hyc hyc' hcc' hx
    refine ⟨(⟨(i % 3).toNat, by omega⟩, ⟨(j % 3).toNat, by omega⟩, ⟨(l % 3).toNat, by omega⟩), ?_⟩
    apply Subtype.ext
    show wd y c c' (((i % 3).toNat : ℕ) : ℤ) (((j % 3).toNat : ℕ) : ℤ) (((l % 3).toNat : ℕ) : ℤ) =
      wd y c c' i j l
    simp only [hcast]
    exact (wd_mod hy hc hc' i j l).symm
  have hbij : Function.Bijective g := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨hsurj, ?_⟩
    rw [hcard]
    simp [Nat.card_eq_fintype_card]
  have key : g (⟨(i % 3).toNat, by omega⟩, ⟨(j % 3).toNat, by omega⟩, ⟨(l % 3).toNat, by omega⟩) =
      g (⟨(i' % 3).toNat, by omega⟩, ⟨(j' % 3).toNat, by omega⟩, ⟨(l' % 3).toNat, by omega⟩) := by
    apply Subtype.ext
    show wd y c c' (((i % 3).toNat : ℕ) : ℤ) (((j % 3).toNat : ℕ) : ℤ) (((l % 3).toNat : ℕ) : ℤ) =
      wd y c c' (((i' % 3).toNat : ℕ) : ℤ) (((j' % 3).toNat : ℕ) : ℤ) (((l' % 3).toNat : ℕ) : ℤ)
    simp only [hcast]
    rw [← wd_mod hy hc hc' i j l, ← wd_mod hy hc hc' i' j' l']
    exact h
  have := hbij.1 key
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  omega

end Words

section Apply

variable {T : Type} [Group T]

theorem wd_inv {y c c' : T} (hyc : Commute y c) (hyc' : Commute y c') (hcc' : Commute c c')
    (i j l : ℤ) : (wd y c c' i j l)⁻¹ = wd y c c' (-i) (-j) (-l) := by
  apply inv_eq_of_mul_eq_one_right
  rw [wd_mul hyc hyc' hcc']
  simp [wd]

theorem wd_conj_t {t y c c' : T} (ht2 : t * t = 1) (hyt : y * t = t * y)
    (hc' : t * c * t⁻¹ = c') (hcc' : Commute c c') (i j l : ℤ) :
    t * wd y c c' i j l * t⁻¹ = wd y c c' i l j := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have e1 : t * y * t⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]; exact hyt.symm
  have e3 : t * c' * t⁻¹ = c := by
    rw [← hc', ht']
    calc t * (t * c * t) * t = (t * t) * c * (t * t) := by group
      _ = c := by rw [ht2]; group
  have e4 : c' ^ j * c ^ l = c ^ l * c' ^ j := (hcc'.symm.zpow_zpow j l).eq
  unfold wd
  calc t * (y ^ i * c ^ j * c' ^ l) * t⁻¹
      = (t * y ^ i * t⁻¹) * (t * c ^ j * t⁻¹) * (t * c' ^ l * t⁻¹) := by group
    _ = (t * y * t⁻¹) ^ i * (t * c * t⁻¹) ^ j * (t * c' * t⁻¹) ^ l := by
      rw [conj_zpow, conj_zpow, conj_zpow]
    _ = y ^ i * c' ^ j * c ^ l := by rw [e1, hc', e3]
    _ = y ^ i * (c' ^ j * c ^ l) := by rw [mul_assoc]
    _ = y ^ i * c ^ l * c' ^ j := by rw [e4, ← mul_assoc]

theorem wd_conj_k {k y c c' : T} (hyk : y * k = k * y) (hkc : k * c * k⁻¹ = c⁻¹)
    (hkc' : k * c' = c' * k) (i j l : ℤ) :
    k * wd y c c' i j l * k⁻¹ = wd y c c' i (-j) l := by
  have e1 : k * y * k⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]; exact hyk.symm
  have e3 : k * c' * k⁻¹ = c' := by
    rw [mul_inv_eq_iff_eq_mul]; exact hkc'
  unfold wd
  calc k * (y ^ i * c ^ j * c' ^ l) * k⁻¹
      = (k * y ^ i * k⁻¹) * (k * c ^ j * k⁻¹) * (k * c' ^ l * k⁻¹) := by group
    _ = (k * y * k⁻¹) ^ i * (k * c * k⁻¹) ^ j * (k * c' * k⁻¹) ^ l := by
      rw [conj_zpow, conj_zpow, conj_zpow]
    _ = y ^ i * (c⁻¹) ^ j * c' ^ l := by rw [e1, hkc, e3]
    _ = y ^ i * c ^ (-j) * c' ^ l := by rw [inv_zpow']

theorem E27_inf_ker {X : Type} [Group X] (κ : T →* X) {t y c c' k : T} (ht2 : t * t = 1)
    (hyt : y * t = t * y) (hc' : t * c * t⁻¹ = c')
    (A F : Subgroup T) [A.Normal] (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hker : κ.ker ≤ F ⊔ A) (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f)
    (hFdisj : ∀ f ∈ F, f ∈ A → f = 1) (hF2 : IsPGroup 2 F)
    (hy : y ^ 3 = 1) (hc : c ^ 3 = 1) (hyc : Commute y c) (hyc' : Commute y c')
    (hcc' : Commute c c') (hyk : y * k = k * y) (hkc : k * c * k⁻¹ = c⁻¹)
    (hkc' : k * c' = c' * k)
    (h27 : Nat.card ↥(closure ({y, c, c'} : Set T)) = 27) :
    ∀ x ∈ closure ({y, c, c'} : Set T), κ x = 1 → x = 1 := by
  have hc'3 : c' ^ 3 = 1 := by
    rw [← hc', conj_pow, hc]; group
  have hinj := wd_inj hyc hyc' hcc' hy hc hc'3 h27
  have hcoord : ∀ i j l : ℤ, wd y c c' i j l ∈ A → i % 3 = 0 ∧ (l + j) % 3 = 0 := by
    intro i j l hw
    have h1 := hinv _ hw
    rw [wd_conj_t ht2 hyt hc' hcc', wd_inv hyc hyc' hcc'] at h1
    have h2 := hinj i l j (-i) (-j) (-l) h1
    omega
  intro x hx hkx
  obtain ⟨i, j, l, rfl⟩ := mem_closure_wd hyc hyc' hcc' hx
  have hxker : wd y c c' i j l ∈ κ.ker := hkx
  have hx3 : (wd y c c' i j l) ^ 3 = 1 := by
    rw [pow_three, wd_mul hyc hyc' hcc', wd_mul hyc hyc' hcc', wd_mod hy hc hc'3]
    have e1 : (i + (i + i)) % 3 = 0 := by omega
    have e2 : (j + (j + j)) % 3 = 0 := by omega
    have e3 : (l + (l + l)) % 3 = 0 := by omega
    rw [e1, e2, e3, wd_zero]
  have hxFA : wd y c c' i j l ∈ F ⊔ A := hker hxker
  have hset := Subgroup.mul_normal F A
  have hx' : wd y c c' i j l ∈ (F : Set T) * (A : Set T) := by
    rw [← hset]; exact hxFA
  obtain ⟨f, hf, a, ha, hfa0⟩ := hx'
  have hfa : f * a = wd y c c' i j l := hfa0
  have hcomm : Commute f a := hFA f hf a ha
  have h3 : (f * a) ^ 3 = 1 := by rw [hfa]; exact hx3
  rw [hcomm.mul_pow] at h3
  have hf3A : f ^ 3 ∈ A := by
    have : f ^ 3 = (a ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this]
    exact A.inv_mem (A.pow_mem ha 3)
  have hf3 : f ^ 3 = 1 := hFdisj (f ^ 3) (F.pow_mem hf 3) hf3A
  have hf1 : f = 1 := by
    obtain ⟨n, hn⟩ := hF2 ⟨f, hf⟩
    have hn' : f ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h4 := pow_gcd_eq_one.2 ⟨hf3, hn'⟩
    have hg : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
    rwa [hg, pow_one] at h4
  have hxA : wd y c c' i j l ∈ A := by
    rw [← hfa, hf1, one_mul]; exact ha
  obtain ⟨hi, hlj⟩ := hcoord i j l hxA
  have hkxA : k * wd y c c' i j l * k⁻¹ ∈ A := ‹A.Normal›.conj_mem _ hxA k
  rw [wd_conj_k hyk hkc hkc'] at hkxA
  obtain ⟨-, hlj'⟩ := hcoord i (-j) l hkxA
  have hj : j % 3 = 0 := by omega
  have hl : l % 3 = 0 := by omega
  rw [wd_mod hy hc hc'3, hi, hj, hl, wd_zero]

theorem sigmaConfig_of_lift {X : Type} [Group X] (κ : T →* X) {t y c k : T} (ht2 : t * t = 1)
    (hyt : y * t = t * y) (A F : Subgroup T) [A.Normal] (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hker : κ.ker ≤ F ⊔ A) (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f)
    (hFdisj : ∀ f ∈ F, f ∈ A → f = 1) (hF2 : IsPGroup 2 F)
    (hy3 : orderOf y = 3) (hc3 : orderOf c = 3) (hk2 : k * k = 1)
    (hyc : y * c = c * y) (hyc' : y * (t * c * t⁻¹) = (t * c * t⁻¹) * y)
    (hcc' : c * (t * c * t⁻¹) = (t * c * t⁻¹) * c) (hyk : y * k = k * y)
    (h27 : Nat.card ↥(closure ({y, c, t * c * t⁻¹} : Set T)) = 27)
    (hkc : k * c * k⁻¹ = c⁻¹) (hkc' : k * (t * c * t⁻¹) = (t * c * t⁻¹) * k)
    (hkk' : k * (t * k * t⁻¹) = (t * k * t⁻¹) * k)
    (hyL : κ y ∈ centralizerDerived (κ t)) :
    SigmaConfig (κ t) (κ y) (κ c) (κ k) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hy' : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hc' : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc3] at this
  have hE := E27_inf_ker κ ht2 hyt rfl A F hinv hker hFA hFdisj hF2 hy' hc' hyc hyc' hcc' hyk hkc
    hkc' h27
  have hy1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy3; omega
  have hc1 : c ≠ 1 := by
    intro h; rw [h, orderOf_one] at hc3; omega
  have hyE : y ∈ closure ({y, c, t * c * t⁻¹} : Set T) := Subgroup.subset_closure (by simp)
  have hcE : c ∈ closure ({y, c, t * c * t⁻¹} : Set T) := Subgroup.subset_closure (by simp)
  have hκy : κ y ≠ 1 := fun h => hy1 (hE y hyE h)
  have hκc : κ c ≠ 1 := fun h => hc1 (hE c hcE h)
  have hordy : orderOf (κ y) = 3 := orderOf_eq_prime (by rw [← map_pow, hy', map_one]) hκy
  have hordc : orderOf (κ c) = 3 := orderOf_eq_prime (by rw [← map_pow, hc', map_one]) hκc
  have hk1 : κ k ≠ 1 := by
    intro h
    have h1 := congrArg κ hkc
    simp only [map_mul, map_inv, h, one_mul, inv_one, mul_one] at h1
    have h2 : (κ c) ^ 2 = 1 := by
      rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hordc] at this
    omega
  have hcard : Nat.card ↥(closure ({κ y, κ c, κ t * κ c * (κ t)⁻¹} : Set X)) = 27 := by
    have himg : (closure ({y, c, t * c * t⁻¹} : Set T)).map κ =
        closure ({κ y, κ c, κ t * κ c * (κ t)⁻¹} : Set X) := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq]
    have hinj : Function.Injective
        (κ.comp (closure ({y, c, t * c * t⁻¹} : Set T)).subtype) := by
      intro a b hab
      have h1 : κ (a : T) = κ (b : T) := hab
      have h2 : κ ((a : T)⁻¹ * (b : T)) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hE _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2) h2
      exact Subtype.ext (inv_mul_eq_one.1 h3)
    have hrange : (κ.comp (closure ({y, c, t * c * t⁻¹} : Set T)).subtype).range =
        (closure ({y, c, t * c * t⁻¹} : Set T)).map κ := by
      ext x
      constructor
      · rintro ⟨e, rfl⟩; exact ⟨e.1, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
    rw [← himg, ← hrange]
    rw [← h27]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine ⟨hordy, hyL, hordc, by rw [← map_mul, hk2, map_one], hk1,
    by rw [← map_mul, ← map_mul, hyc], ?_, ?_, by rw [← map_mul, ← map_mul, hyk], hcard, ?_, ?_, ?_⟩
  · have := congrArg κ hyc'
    simpa [map_mul, map_inv] using this
  · have := congrArg κ hcc'
    simpa [map_mul, map_inv] using this
  · have := congrArg κ hkc
    simpa [map_mul, map_inv] using this
  · have := congrArg κ hkc'
    simpa [map_mul, map_inv] using this
  · have := congrArg κ hkk'
    simpa [map_mul, map_inv] using this

end Apply

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
