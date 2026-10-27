module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Cent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HL34

theorem exists_not_commute_perm_five {σ : Perm (Fin 5)} (h : σ ≠ 1) :
    ∃ τ : Perm (Fin 5), τ * σ ≠ σ * τ := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    exact h (Equiv.ext fun a => by_contra fun hne => hcon ⟨a, hne⟩)
  have : ∃ c : Fin 5, c ≠ a ∧ c ≠ σ a := by
    have h5 : ({a, σ a} : Finset (Fin 5)).card < (Finset.univ : Finset (Fin 5)).card := by
      refine lt_of_le_of_lt (Finset.card_le_two) ?_
      simp
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card h5
    exact ⟨c, fun h' => hc (by simp [h']), fun h' => hc (by simp [h'])⟩
  obtain ⟨c, hca, hcb⟩ := this
  refine ⟨swap (σ a) c, fun hcomm => ?_⟩
  have := congrArg (fun f : Perm (Fin 5) => f a) hcomm
  simp only [Perm.mul_apply] at this
  rw [swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hca)] at this
  rw [swap_apply_left] at this
  exact hcb this

section Complement

variable {D : Type*} [Group D] {t : D}

theorem exists_complement (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)) :
    ∃ K : Subgroup D, centralizer ({t} : Set D) = zpowers t ⊔ K ∧ Disjoint (zpowers t) K ∧
      Nonempty (↥K ≃* Perm (Fin 5)) := by
  set T := centralizer ({t} : Set D) with hT
  have htT : t ∈ T := mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]
  let tT : T := ⟨t, htT⟩
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hσ : (e tT).2 = 1 := by
    by_contra hne
    obtain ⟨τ, hτ⟩ := exists_not_commute_perm_five hne
    have hcomm : tT * e.symm (1, τ) = e.symm (1, τ) * tT :=
      Subtype.ext (mem_centralizer_iff.1 (e.symm (1, τ)).2 t rfl)
    have := congrArg Prod.snd (congrArg e hcomm)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact hτ (by simpa using this.symm)
  have ha : (e tT).1 ≠ 1 := fun h1 => ht1 (by
    have : e tT = 1 := Prod.ext h1 hσ
    exact congrArg Subtype.val (e.injective (this.trans (map_one e).symm)))
  have ha2 : ∀ a a' : Multiplicative (ZMod 2), a ≠ 1 → a' = 1 ∨ a' = a := by decide
  let φ : Perm (Fin 5) →* D := T.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))
  have hinr : Function.Injective
      (MonoidHom.inr (Multiplicative (ZMod 2)) (Perm (Fin 5))) := fun x y h => congrArg Prod.snd h
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp (e.symm.injective.comp hinr)
  have hφT : ∀ σ', φ σ' ∈ T := fun σ' => (e.symm (1, σ')).2
  have hφe : ∀ σ', e ⟨φ σ', hφT σ'⟩ = (1, σ') := fun σ' => by
    have : (⟨φ σ', hφT σ'⟩ : T) = e.symm (1, σ') := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have h11 : e.symm ((1 : Multiplicative (ZMod 2)), (1 : Perm (Fin 5))) = 1 := map_one e.symm
  have het : e tT = ((e tT).1, 1) := Prod.ext rfl hσ
  refine ⟨φ.range, le_antisymm (fun x hx => ?_) (sup_le zpowers_le_centralizer
    (by rintro _ ⟨σ', rfl⟩; exact hφT σ')), ?_, ⟨(MonoidHom.ofInjective hφ).symm⟩⟩
  · rcases hp : e ⟨x, hx⟩ with ⟨a', σ'⟩
    have hxy : (⟨x, hx⟩ : T) = e.symm (a', 1) * e.symm (1, σ') := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← hp, MulEquiv.symm_apply_apply]
    have hx' : x = ((e.symm (a', 1) : T) : D) * φ σ' := congrArg Subtype.val hxy
    rcases ha2 _ a' ha with h1 | h1
    · rw [h1, h11, OneMemClass.coe_one, one_mul] at hx'
      rw [hx']
      exact mem_sup_right ⟨σ', rfl⟩
    · have : e.symm (a', 1) = tT := by
        rw [h1, ← het, MulEquiv.symm_apply_apply]
      rw [this] at hx'
      rw [hx']
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ⟨σ', rfl⟩)
  · rw [Subgroup.disjoint_def]
    rintro x hx ⟨σ', rfl⟩
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hx
    have h2 : (⟨φ σ', hφT σ'⟩ : T) = tT ^ n := Subtype.ext hn.symm
    have h3 : (e ⟨φ σ', hφT σ'⟩).2 = 1 := by
      rw [h2, map_zpow]
      show (e tT).2 ^ n = 1
      rw [hσ, one_zpow]
    rw [hφe σ'] at h3
    have : σ' = 1 := h3
    rw [this, map_one]

end Complement

section Dichotomy

variable {D : Type*} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem sixty_le_card_of_normal_perm_five (N : Subgroup (Perm (Fin 5))) [N.Normal]
    (hN : ∃ n ∈ N, n ≠ 1) : 60 ≤ Nat.card N := by
  obtain ⟨n, hn, hn1⟩ := hN
  have hnt : Nontrivial N := ⟨⟨⟨n, hn⟩, 1, fun h => hn1 (congrArg Subtype.val h)⟩⟩
  have hA : alternatingGroup (Fin 5) ≤ N :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  rw [← card_alternatingGroup_five]
  exact Subgroup.card_le_of_le hA

theorem sixty_le_card_of_not_le_zpowers
    (hC : centralizer ({t} : Set D) = zpowers t ⊔ K) (eK : ↥K ≃* Perm (Fin 5))
    {X : Subgroup D} (hXn : ∀ τ ∈ centralizer ({t} : Set D), ∀ x ∈ X, τ * x * τ⁻¹ ∈ X)
    (hXT : X ≤ centralizer ({t} : Set D)) (hX : ¬ X ≤ zpowers t) : 60 ≤ Nat.card X := by
  have hKC : K ≤ centralizer ({t} : Set D) := le_sup_right.trans hC.ge
  obtain ⟨x, hxX, hxz⟩ := Set.not_subset.1 hX
  obtain ⟨z, hz, k, hk, rfl⟩ := exists_mul_of_mem_sup hKC (hC ▸ hXT hxX)
  have hk1 : k ≠ 1 := fun h => hxz (by rw [h, mul_one]; exact hz)
  have hσ : eK ⟨k, hk⟩ ≠ 1 := fun h =>
    hk1 (congrArg Subtype.val (eK.injective (h.trans (map_one eK).symm)))
  obtain ⟨τ, hτ⟩ := exists_not_commute_perm_five hσ
  set κ : D := ((eK.symm τ : ↥K) : D) with hκdef
  have hκK : κ ∈ K := (eK.symm τ).2
  have hκT : κ ∈ centralizer ({t} : Set D) := hKC hκK
  have hcK : k * κ * k⁻¹ * κ⁻¹ ∈ K :=
    mul_mem (mul_mem (mul_mem hk hκK) (inv_mem hk)) (inv_mem hκK)
  have hzc : z * (k * κ * k⁻¹) * z⁻¹ = k * κ * k⁻¹ := by
    rw [commute_of_mem_zpowers hz (hKC (mul_mem (mul_mem hk hκK) (inv_mem hk))),
      mul_inv_cancel_right]
  have hcX : k * κ * k⁻¹ * κ⁻¹ ∈ X := by
    have h1 := X.mul_mem hxX (hXn κ hκT _ (X.inv_mem hxX))
    have h2 : z * k * (κ * (z * k)⁻¹ * κ⁻¹) = k * κ * k⁻¹ * κ⁻¹ := by
      calc z * k * (κ * (z * k)⁻¹ * κ⁻¹) = (z * (k * κ * k⁻¹) * z⁻¹) * κ⁻¹ := by group
        _ = k * κ * k⁻¹ * κ⁻¹ := by rw [hzc]
    rwa [h2] at h1
  have hc1 : eK ⟨k * κ * k⁻¹ * κ⁻¹, hcK⟩ ≠ 1 := by
    intro h
    apply hτ
    have h' : eK (⟨k, hk⟩ * ⟨κ, hκK⟩ * ⟨k, hk⟩⁻¹ * ⟨κ, hκK⟩⁻¹) = 1 := h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h'
    have hκτ : eK ⟨κ, hκK⟩ = τ := by
      have : (⟨κ, hκK⟩ : ↥K) = eK.symm τ := rfl
      rw [this, MulEquiv.apply_symm_apply]
    rw [hκτ] at h'
    set σ := eK ⟨k, hk⟩
    have : σ * τ * σ⁻¹ * τ⁻¹ = 1 := h'
    have h3 : σ * τ = τ * σ := by
      calc σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
        _ = τ * σ := by rw [this, one_mul]
    exact h3.symm
  let N : Subgroup (Perm (Fin 5)) := (X.subgroupOf K).map eK.toMonoidHom
  have hNmem : ∀ σ' ∈ N, ∃ m : D, ∃ hm : m ∈ K, m ∈ X ∧ eK ⟨m, hm⟩ = σ' := by
    rintro _ ⟨⟨m, hm⟩, hmX, rfl⟩
    exact ⟨m, hm, hmX, rfl⟩
  have hNn : N.Normal := ⟨by
    intro n hn g
    obtain ⟨m, hm, hmX, rfl⟩ := hNmem n hn
    set κ' : K := eK.symm g with hκ'
    have hκ'T : (κ' : D) ∈ centralizer ({t} : Set D) := hKC κ'.2
    refine ⟨κ' * ⟨m, hm⟩ * κ'⁻¹, hXn _ hκ'T m hmX, ?_⟩
    show eK (κ' * ⟨m, hm⟩ * κ'⁻¹) = g * eK ⟨m, hm⟩ * g⁻¹
    rw [map_mul, map_mul, map_inv, hκ', MulEquiv.apply_symm_apply]⟩
  have hcN : eK ⟨k * κ * k⁻¹ * κ⁻¹, hcK⟩ ∈ N := ⟨⟨_, hcK⟩, hcX, rfl⟩
  have h60 := sixty_le_card_of_normal_perm_five N ⟨_, hcN, hc1⟩
  have hNle : Nat.card N ≤ Nat.card X := by
    rw [Subgroup.card_map_of_injective (f := eK.toMonoidHom) eK.injective]
    refine Nat.card_le_card_of_injective (fun y => (⟨y.1.1, y.2⟩ : X)) ?_
    intro a b h
    have h' := Subtype.ext_iff.1 h
    exact Subtype.ext (Subtype.ext h')
  exact h60.trans hNle

end Dichotomy

section Small

variable {D : Type*} [Group D] [Finite D] {t : D}

theorem false_of_not_mem_of_inf_le (ht : orderOf t = 2) (S : Subgroup D) [S.Normal]
    (h4 : 4 ∣ Nat.card S) (htS : t ∉ S)
    (hsub : S ⊓ centralizer ({t} : Set D) ≤ zpowers t) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : ∀ n ∈ S, t * n * t⁻¹ = n → n = 1 := by
    intro n hn hcomm
    have hnC : n ∈ centralizer ({t} : Set D) :=
      mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]
        exact (mul_inv_eq_iff_eq_mul.1 hcomm)
    rcases eq_one_or_eq_of_mem_zpowers ht (hsub ⟨hn, hnC⟩) with h | h
    · exact h
    · exact absurd (h ▸ hn) htS
  have hinv := conj_eq_inv_of_fixed_point_free S ht2
    (fun n hn => Normal.conj_mem inferInstance n hn t) hbot
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2
    (dvd_trans (by norm_num) h4)
  have hxx : (x : D) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, pow_two] at this
    exact congrArg Subtype.val this
  have hxi : (x : D)⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  apply hx1
  exact Subtype.ext (hbot x x.2 (by rw [hinv x x.2, hxi]))

theorem false_of_mem_of_inf_le (ht : orderOf t = 2) (S : Subgroup D)
    (h4 : 4 ∣ Nat.card S) (htS : t ∈ S)
    (hsub : S ⊓ centralizer ({t} : Set D) ≤ zpowers t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : ↥S := ⟨t, htS⟩
  have ht'ord : orderOf t' = 2 := by rw [← ht]; exact Subgroup.orderOf_mk t htS
  have ht1 : t' ≠ 1 := fun h => by rw [h, orderOf_one] at ht'ord; omega
  have hP : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'ord]; norm_num)
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  have ht'P : t' ∈ (P : Subgroup ↥S) := hP' (mem_zpowers t')
  have hY : centralizer ({t'} : Set ↥S) ≤ zpowers t' := by
    intro y hy
    have hyC : (y : D) ∈ centralizer ({t} : Set D) :=
      mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]
        exact congrArg Subtype.val (mem_centralizer_iff.1 hy t' rfl)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hsub ⟨y.2, hyC⟩)
    exact mem_zpowers_iff.2 ⟨n, Subtype.ext hn⟩
  have hYcard : Nat.card (centralizer ({t'} : Set ↥S)) ≤ 2 := by
    refine le_trans (Subgroup.card_le_of_le hY) ?_
    rw [Nat.card_zpowers, ht'ord]
  have hPcard : 4 ≤ Nat.card P := by
    rw [Sylow.card_eq_multiplicity]
    have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ^ 2 ∣ Nat.card S := by norm_num; exact h4
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hS0).1 h2
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Nat.card S).factorization 2 := Nat.pow_le_pow_right (by norm_num) this
  have hnt : Nontrivial ↥(P : Subgroup ↥S) :=
    ⟨⟨⟨t', ht'P⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  have hcenter := (P.isPGroup').center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup ↥S))
  have hzc : ((z : ↥(P : Subgroup ↥S)) : ↥S) ∈ centralizer ({t'} : Set ↥S) := by
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨t', ht'P⟩)
  rcases eq_one_or_eq_of_mem_zpowers ht'ord (hY hzc) with h | h
  · exact hz1 (Subtype.ext (Subtype.ext h))
  · have hcent : (⟨t', ht'P⟩ : ↥(P : Subgroup ↥S)) ∈ Subgroup.center ↥(P : Subgroup ↥S) := by
      have : (z : ↥(P : Subgroup ↥S)) = ⟨t', ht'P⟩ := Subtype.ext h
      rw [← this]
      exact z.2
    have hPY : (P : Subgroup ↥S) ≤ centralizer ({t'} : Set ↥S) := by
      intro p hp
      rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hcent) ⟨p, hp⟩).symm
    have := Subgroup.card_le_of_le hPY
    omega

end Small

section Main

variable {D : Type*} [Group D] [Finite D] {t : D}

theorem centralizer_eq_bot_of_normal_of_card
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (S : Subgroup D) [S.Normal] (h4 : 4 ∣ Nat.card S) (h240 : 240 < Nat.card S) :
    centralizer (S : Set D) = ⊥ := by
  obtain ⟨e⟩ := e
  obtain ⟨K, hC, hd, ⟨eK⟩⟩ := exists_complement ht e
  have hH : ¬ S ≤ centralizer ({t} : Set D) := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [card_centralizer_eq ht hC hd eK] at this
    omega
  refine centralizer_eq_bot_of_normal hZ ht hC hd eK S hH ?_
  by_cases hsub : S ⊓ centralizer ({t} : Set D) ≤ zpowers t
  · exfalso
    by_cases htS : t ∈ S
    · exact false_of_mem_of_inf_le ht S h4 htS hsub
    · exact false_of_not_mem_of_inf_le ht S h4 htS hsub
  · have hXn : ∀ τ ∈ centralizer ({t} : Set D), ∀ x ∈ S ⊓ centralizer ({t} : Set D),
        τ * x * τ⁻¹ ∈ S ⊓ centralizer ({t} : Set D) := by
      intro τ hτ x hx
      refine ⟨Normal.conj_mem inferInstance x hx.1 τ, ?_⟩
      exact (centralizer ({t} : Set D)).mul_mem
        ((centralizer ({t} : Set D)).mul_mem hτ hx.2) ((centralizer ({t} : Set D)).inv_mem hτ)
    have h60 := sixty_le_card_of_not_le_zpowers hC eK hXn inf_le_right hsub
    omega

end Main

end CFSG.EvenSporadicStandard.HSStd.HOv
