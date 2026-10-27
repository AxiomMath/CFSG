module

public import CFSG.LocalAnalysis.GH72.Sec4Residual

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement

namespace G4b

section Odd

variable {X : Type*} [Group X]

theorem exists_pow_odd_map_eq [Finite X] {Y : Type*} [Group Y] (f : X →* Y) (x : X)
    (hx : Odd (orderOf (f x))) : ∃ k : ℕ, Odd (orderOf (x ^ k)) ∧ f (x ^ k) = f x := by
  obtain ⟨a, ha⟩ := exists_odd_orderOf_pow x
  have hcop : (2 ^ a).Coprime (orderOf (f x)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨2 ^ a * m, ?_, ?_⟩
  · rw [pow_mul]
    exact Odd.of_dvd_nat ha (orderOf_pow_dvd m)
  · rw [map_pow, pow_mul]
    exact hm

end Odd

section OddCore

variable {G : Type*} [Group G]

theorem O_le_self (H : Subgroup G) : O H ≤ H := map_subtype_le _

theorem O_le_O2 [Finite G] (H : Subgroup G) : O H ≤ O2 H := by
  intro x hx
  refine mem_twoResidualOf_of_odd (O_le_self H hx) (Odd.of_dvd_nat (card_O_odd H) ?_)
  have := orderOf_dvd_natCard (⟨x, hx⟩ : O H)
  rwa [Subgroup.orderOf_mk] at this

theorem le_O_of_odd [Finite G] {H D : Subgroup G} (hDH : D ≤ H) (hHD : H ≤ normalizer (D : Set G))
    (hD : Odd (Nat.card D)) : D ≤ O H := by
  intro x hx
  refine ⟨⟨x, hDH hx⟩, ?_, rfl⟩
  have hnorm : (D.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hHD g.2) _).1 hn
  refine le_sSup (s := {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}) ⟨hnorm, ?_⟩
    (by rw [mem_subgroupOf]; exact hx)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]

theorem mem_oddCore_iff {H : Subgroup G} (h : H) : h ∈ CFSG.oddCore H ↔ (h : G) ∈ O H := by
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h', hh', he⟩
    rwa [← Subtype.ext he]

end OddCore

section Coset

variable {G : Type*} [Group G]

theorem exists_mul_mem_centralizer [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T)
    (hN : Odd (Nat.card N)) (hTN : T ≤ normalizer (N : Set G)) {x : G}
    (hx : ∀ t ∈ T, x⁻¹ * (t * x * t⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ t ∈ T, t * (x * n) * t⁻¹ = x * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ t ∈ T, ∀ n ∈ N, x⁻¹ * (t * (x * n) * t⁻¹) ∈ N := by
    intro t ht n hn
    have e : x⁻¹ * (t * (x * n) * t⁻¹) = (x⁻¹ * (t * x * t⁻¹)) * (t * n * t⁻¹) := by group
    rw [e]
    exact mul_mem (hx t ht) ((mem_normalizer_iff.1 (hTN ht) n).1 hn)
  let act : MulAction T N :=
    { smul := fun t n => ⟨x⁻¹ * ((t : G) * (x * n) * (t : G)⁻¹), hmem t t.2 n n.2⟩
      one_smul := fun n => Subtype.ext (by
        change x⁻¹ * (((1 : T) : G) * (x * n) * ((1 : T) : G)⁻¹) = n
        simp)
      mul_smul := fun s t n => Subtype.ext (by
        change x⁻¹ * ((s : G) * (t : G) * (x * n) * ((s : G) * (t : G))⁻¹) =
          x⁻¹ * ((s : G) * (x * (x⁻¹ * ((t : G) * (x * n) * (t : G)⁻¹))) * (s : G)⁻¹)
        group) }
  have hcard : ¬ 2 ∣ Nat.card N := Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hN)
  obtain ⟨n, hn⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card N hcard
  refine ⟨n, n.2, fun t ht => ?_⟩
  have h := congrArg Subtype.val (hn ⟨t, ht⟩)
  change x⁻¹ * (t * (x * n) * t⁻¹) = n at h
  calc t * (x * n) * t⁻¹ = x * (x⁻¹ * (t * (x * n) * t⁻¹)) := by group
    _ = x * n := by rw [h]

end Coset

section Joins

variable {G : Type*} [Group G]

theorem sup_inf_eq_of_le {A N B : Subgroup G} (hAB : A ≤ B) (hAN : A ≤ normalizer (N : Set G)) :
    (A ⊔ N) ⊓ B = A ⊔ (N ⊓ B) := by
  apply le_antisymm
  · intro x hx'
    obtain ⟨hx, hxB⟩ := mem_inf.1 hx'
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A N hAN] at hx
    obtain ⟨a, ha, n, hn, rfl⟩ := hx
    have hnB : n ∈ B := by simpa using mul_mem (inv_mem (hAB ha)) hxB
    exact mul_mem_sup ha (mem_inf.2 ⟨hn, hnB⟩)
  · exact le_inf (sup_le_sup_left inf_le_left _) (sup_le hAB inf_le_right)

theorem mem_sup_of_le_normalizer {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) {x : G}
    (hx : x ∈ A ⊔ N) : ∃ a ∈ A, ∃ n ∈ N, a * n = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A N hAN] at hx
  exact hx

theorem commutator_sup_le {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) :
    ⁅A ⊔ N, A ⊔ N⁆ ≤ ⁅A, A⁆ ⊔ N := by
  have hN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn =>
    (mem_normalizer_iff.1 (hAN ha) n).1 hn
  have hN' : ∀ a ∈ A, ∀ n ∈ N, a⁻¹ * n * a ∈ N := fun a ha n hn => by
    simpa using hN a⁻¹ (inv_mem ha) n hn
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := mem_sup_of_le_normalizer hAN hg₁
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := mem_sup_of_le_normalizer hAN hg₂
  have hu : a₂⁻¹ * n₁ * a₂ * n₂ * n₁⁻¹ ∈ N :=
    mul_mem (mul_mem (hN' a₂ ha₂ n₁ hn₁) hn₂) (inv_mem hn₁)
  have hv : a₁ * (a₂⁻¹ * n₁ * a₂ * n₂ * n₁⁻¹) * a₁⁻¹ * n₂⁻¹ ∈ N :=
    mul_mem (hN a₁ ha₁ _ hu) (inv_mem hn₂)
  have hm : a₂ * (a₁ * (a₂⁻¹ * n₁ * a₂ * n₂ * n₁⁻¹) * a₁⁻¹ * n₂⁻¹) * a₂⁻¹ ∈ N :=
    hN a₂ ha₂ _ hv
  have e : ⁅a₁ * n₁, a₂ * n₂⁆ =
      ⁅a₁, a₂⁆ * (a₂ * (a₁ * (a₂⁻¹ * n₁ * a₂ * n₂ * n₁⁻¹) * a₁⁻¹ * n₂⁻¹) * a₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem_sup (commutator_mem_commutator ha₁ ha₂) hm

theorem commutator_sup_sup_eq {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) :
    ⁅A ⊔ N, A ⊔ N⁆ ⊔ N = ⁅A, A⁆ ⊔ N :=
  le_antisymm (sup_le (commutator_sup_le hAN) le_sup_right)
    (sup_le_sup_right (commutator_mono le_sup_left le_sup_left) N)

theorem exists_surjective_quotient {E N K : Subgroup G} [(N.subgroupOf E).Normal] (hEK : E ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) (hsup : E ⊔ N = K) :
    ∃ f : K →* (E ⧸ N.subgroupOf E), Function.Surjective f ∧ f.ker = N.subgroupOf K := by
  set N' : Subgroup K := N.subgroupOf K
  have : N'.Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hKN g.2) n).1 hn
  let ψ : E →* K ⧸ N' := (QuotientGroup.mk' N').comp (inclusion hEK)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective N' y
    have hk' : k ∈ E ⊔ N := hsup ▸ hk
    obtain ⟨e, he, n, hn, rfl⟩ := mem_sup_of_le_normalizer (hEK.trans hKN) hk'
    refine ⟨⟨e, he⟩, ?_⟩
    change (QuotientGroup.mk (inclusion hEK ⟨e, he⟩) : K ⧸ N') = QuotientGroup.mk ⟨e * n, hk⟩
    rw [QuotientGroup.eq]
    change (⟨e, hEK he⟩ : K)⁻¹ * ⟨e * n, hk⟩ ∈ N'
    rw [mem_subgroupOf]
    simpa using hn
  have hker : ψ.ker = N.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (QuotientGroup.mk (inclusion hEK e) : K ⧸ N') = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  let φ : E ⧸ N.subgroupOf E ≃* K ⧸ N' :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  refine ⟨φ.symm.toMonoidHom.comp (QuotientGroup.mk' N'), ?_, ?_⟩
  · exact φ.symm.surjective.comp (QuotientGroup.mk'_surjective N')
  · ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem quotIso_of_sup {G : Type} [Group G] {E N₁ K₁ N₂ K₂ : Subgroup G} (hEK₁ : E ≤ K₁)
    (hKN₁ : K₁ ≤ normalizer (N₁ : Set G)) (hsup₁ : E ⊔ N₁ = K₁)
    (hEK₂ : E ≤ K₂) (hKN₂ : K₂ ≤ normalizer (N₂ : Set G))
    (hsup₂ : E ⊔ N₂ = K₂) (hN : E ⊓ N₁ = E ⊓ N₂) : QuotIso K₁ N₁ K₂ N₂ := by
  have hnorm : ∀ {N K : Subgroup G}, E ≤ K → K ≤ normalizer (N : Set G) →
      (N.subgroupOf E).Normal := by
    intro N K hEK hKN
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hKN (hEK g.2)) n).1 hn
  have := hnorm hEK₁ hKN₁
  have := hnorm hEK₂ hKN₂
  obtain ⟨f₁, hf₁, hk₁⟩ := exists_surjective_quotient hEK₁ hKN₁ hsup₁
  obtain ⟨f₂, hf₂, hk₂⟩ := exists_surjective_quotient hEK₂ hKN₂ hsup₂
  have heq : N₂.subgroupOf E = N₁.subgroupOf E := by
    ext e
    rw [mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro h
      have : (e : G) ∈ E ⊓ N₂ := mem_inf.2 ⟨e.2, h⟩
      rw [← hN] at this
      exact (mem_inf.1 this).2
    · intro h
      have : (e : G) ∈ E ⊓ N₁ := mem_inf.2 ⟨e.2, h⟩
      rw [hN] at this
      exact (mem_inf.1 this).2
  let e : (E ⧸ N₂.subgroupOf E) ≃* (E ⧸ N₁.subgroupOf E) :=
    QuotientGroup.quotientMulEquivOfEq heq
  exact ⟨E ⧸ N₁.subgroupOf E, inferInstance, f₁, e.toMonoidHom.comp f₂, hf₁,
    e.surjective.comp hf₂, hk₁, by
      rw [← hk₂]
      ext k
      simp⟩

end Joins

end G4b

end CFSG.GH72
