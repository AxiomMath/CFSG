module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

open scoped commutatorElement

theorem isSubnormal_trans {G : Type*} [Group G] {A B C : Subgroup G} (h1 : IsSubnormal A B)
    (h2 : IsSubnormal B C) : IsSubnormal A C := by
  induction h1 with
  | refl => exact h2
  | step hle hn _ ih => exact IsSubnormal.step hle hn (ih h2)

theorem isSubnormal_of_normal {G : Type*} [Group G] {A B : Subgroup G} (hle : A ≤ B)
    (hn : (A.subgroupOf B).Normal) : IsSubnormal A B :=
  IsSubnormal.step hle hn (IsSubnormal.refl B)

theorem mem_normalizer_sup {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (H : Set G) →
      g ∈ Subgroup.normalizer (K : Set G) → ∀ t ∈ H ⊔ K, g * t * g⁻¹ ∈ H ⊔ K := by
    intro g hH hK t ht
    have : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (fun l hl => ?_)
      · exact (le_sup_left : H ≤ H ⊔ K) ((Subgroup.mem_normalizer_iff.1 hH s).1 hs)
      · exact (le_sup_right : K ≤ H ⊔ K) ((Subgroup.mem_normalizer_iff.1 hK l).1 hl)
    exact this ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key hH hK x, fun hx => ?_⟩
  have h1 := key (inv_mem hH) (inv_mem hK) _ hx
  simpa [mul_assoc] using h1

theorem mem_normalizer_inf {G : Type*} [Group G] {K S : Subgroup G} {a : G}
    (hK : a ∈ Subgroup.normalizer (K : Set G)) (hS : a ∈ Subgroup.normalizer (S : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hK hS ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hK y, hS y]

theorem commutator_mem_of_sup_eq_top {G : Type*} [Group G] {M T : Subgroup G} [M.Normal]
    (hMT : M ⊔ T = ⊤) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (x y : G) : ⁅x, y⁆ ∈ M := by
  have hdec : ∀ g : G, ∃ t ∈ T, g * t⁻¹ ∈ M := by
    intro g
    have hg : g ∈ M ⊔ T := by rw [hMT]; exact Subgroup.mem_top g
    obtain ⟨m, hm, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    exact ⟨t, ht, by simpa using hm⟩
  obtain ⟨s, hs, hxs⟩ := hdec x
  obtain ⟨t, ht, hyt⟩ := hdec y
  have hmk : ∀ {g h : G}, g * h⁻¹ ∈ M → (QuotientGroup.mk' M) g = (QuotientGroup.mk' M) h := by
    intro g h hgh
    have h1 : (QuotientGroup.mk' M) (g * h⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hgh
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have hst : s * t = t * s := hT s hs t ht
  rw [← QuotientGroup.ker_mk' M, MonoidHom.mem_ker, map_commutatorElement, hmk hxs, hmk hyt,
    ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 hst, map_one]

theorem pow_mem_of_mem_sup {G : Type*} [Group G] [Finite G] {K W : Subgroup G}
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ W) :
    x ^ Nat.card W ∈ K := by
  set Nn := Subgroup.normalizer (K : Set G) with hNn
  have hKN : K ≤ Nn := Subgroup.le_normalizer
  have hKWN : K ⊔ W ≤ Nn := sup_le hKN hWK
  have hn : (K.subgroupOf Nn).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 le_rfl
  have hx' : (⟨x, hKWN hx⟩ : ↥Nn) ∈ K.subgroupOf Nn ⊔ W.subgroupOf Nn := by
    rw [← Subgroup.subgroupOf_sup hKN hWK]
    exact (Subgroup.mem_subgroupOf).2 hx
  obtain ⟨k, hk, w, hw, hkw⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  have hwn : w ^ Nat.card W = 1 := by
    have hc : Nat.card (W.subgroupOf Nn) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv
    have := pow_card_eq_one' (G := ↥(W.subgroupOf Nn)) (x := ⟨w, hw⟩)
    rw [hc] at this
    exact congrArg Subtype.val this
  have hmk : (QuotientGroup.mk' (K.subgroupOf Nn)) k = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hk
  have h1 : (QuotientGroup.mk' (K.subgroupOf Nn)) ((⟨x, hKWN hx⟩ : ↥Nn) ^ Nat.card W) = 1 := by
    rw [← hkw, map_pow, map_mul, hmk, one_mul, ← map_pow, hwn, map_one]
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  exact (Subgroup.mem_subgroupOf).1 h1

end CFSG.HardMathSupport.Dickson.I271
