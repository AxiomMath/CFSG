module

public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

theorem pow_four_eq_one_of_card_eight {M : Type*} [Group M] (hM : Nat.card M = 8)
    (hnc : ∃ x y : M, x * y ≠ y * x) (g : M) : g ^ 4 = 1 := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (by omega)
  have hd : orderOf g ∣ 2 ^ 3 := by
    have := orderOf_dvd_natCard g
    rwa [hM] at this
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  by_cases h3 : i = 3
  · exfalso
    have hcyc : IsCyclic M := isCyclic_of_orderOf_eq_card g (by rw [hM, hgi, h3]; norm_num)
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (IsMulCommutative.is_comm.comm x y)
  · refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hgi]
    have : i ≤ 2 := by omega
    calc 2 ^ i ∣ 2 ^ 2 := pow_dvd_pow 2 this
      _ = 4 := by norm_num

theorem commute_map_quaternion {k : ℕ} (hk : 2 ≤ k) {H : Type*} [Group H]
    (ψ : QuaternionGroup (2 ^ k) →* H) (hexp : ∀ g, ψ g ^ 4 = 1)
    (hcen : ∀ g, ψ g * ψ g = 1 → ∀ g', ψ g * ψ g' = ψ g' * ψ g)
    (g g' : QuaternionGroup (2 ^ k)) : ψ g * ψ g' = ψ g' * ψ g := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  haveI : NeZero (2 * 2 ^ k) := ⟨by positivity⟩
  set u : H := ψ (QuaternionGroup.a 1) with hu
  have hpow : 2 ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hu1 : u ^ (2 ^ k) = 1 := by
    rw [hpow, pow_mul, hexp, one_pow]
  have hcc : ψ (QuaternionGroup.xa 0) * ψ (QuaternionGroup.xa 0) = 1 := by
    rw [← map_mul, ← sq, QuaternionGroup.xa_sq, ← QuaternionGroup.a_one_pow, map_pow, ← hu, hu1]
  set c : H := ψ (QuaternionGroup.xa 0) with hc
  have hcomm : ∀ g', Commute c (ψ g') := fun g' => hcen _ hcc g'
  have hA : ∀ t : ZMod (2 * 2 ^ k), ψ (QuaternionGroup.a t) = u ^ t.val := by
    intro t
    rw [hu, ← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
  have hX : ∀ t : ZMod (2 * 2 ^ k), ψ (QuaternionGroup.xa t) = c * u ^ t.val := by
    intro t
    rw [← hA t, hc, ← map_mul, QuaternionGroup.xa_mul_a, zero_add]
  have hcu : ∀ t : ZMod (2 * 2 ^ k), Commute c (u ^ t.val) := by
    intro t
    have := hcomm (QuaternionGroup.a t)
    rwa [hA] at this
  have huu : ∀ s t : ZMod (2 * 2 ^ k), Commute (u ^ s.val) (u ^ t.val) :=
    fun s t => Commute.pow_pow_self u _ _
  have hcm : ∀ s t : ZMod (2 * 2 ^ k), Commute (c * u ^ s.val) (c * u ^ t.val) := fun s t =>
    Commute.mul_right (Commute.mul_left (Commute.refl c) (hcu s).symm)
      (Commute.mul_left (hcu t) (huu s t))
  show Commute (ψ g) (ψ g')
  cases g with
  | a s =>
    cases g' with
    | a t => rw [hA, hA]; exact huu s t
    | xa t => rw [hA, hX]; exact (hcu s).symm.mul_right (huu s t)
  | xa s =>
    cases g' with
    | a t => rw [hA, hX]; exact (hcu t).mul_left (huu s t)
    | xa t => rw [hX, hX]; exact hcm s t

section Members

variable {G : Type} [Group G]

theorem card_eq_eight_of_map_memBar {n : ℕ} (hn : 5 ≤ n) {X L : Subgroup G} (hLX : L ≤ X)
    (hq : IsQuatSub L) (φ : ↥X →* AE.AEQ n) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf X).map φ = AE.memBar α h b) : Nat.card L = 8 := by
  obtain ⟨k, hk1, ⟨e⟩⟩ := hq
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  have hcard : Nat.card L = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  by_contra hne
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk : k = 1 := by omega
    exact hne (by rw [hcard, hk]; norm_num)
  let ψ : QuaternionGroup (2 ^ k) →* AE.AEQ n :=
    φ.comp ((Subgroup.inclusion hLX).comp e.symm.toMonoidHom)
  have hmem : ∀ g, ψ g ∈ AE.memBar α h b := by
    intro g
    rw [← hlab]
    exact ⟨Subgroup.inclusion hLX (e.symm g), Subgroup.mem_subgroupOf.mpr (e.symm g).2, rfl⟩
  have hsurj : ∀ x ∈ AE.memBar α h b, ∃ g, ψ g = x := by
    intro x hx
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨e ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    show φ (Subgroup.inclusion hLX (e.symm (e ⟨(y : G), _⟩))) = φ y
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨x, hx, x', hx', hnc⟩ := AE.exists_not_comm_memBar hn α h b
  have hexp : ∀ g, ψ g ^ 4 = 1 := by
    intro g
    have := pow_four_eq_one_of_card_eight (M := AE.memBar α h b) (AE.natCard_memBar hn α h b)
      ⟨⟨x, hx⟩, ⟨x', hx'⟩, fun hc => hnc (congrArg Subtype.val hc)⟩ ⟨ψ g, hmem g⟩
    exact congrArg Subtype.val this
  have hcen : ∀ g, ψ g * ψ g = 1 → ∀ g', ψ g * ψ g' = ψ g' * ψ g := by
    intro g hg g'
    rcases AE.eq_of_mem_memBar_mul_self hn (hmem g) hg with h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]
      exact AE.zBar_comm_memBar α h b _ (hmem g')
  obtain ⟨g, hg⟩ := hsurj x hx
  obtain ⟨g', hg'⟩ := hsurj x' hx'
  exact hnc (by rw [← hg, ← hg']; exact commute_map_quaternion hk2 ψ hexp hcen g g')

end Members

section Outcomes

variable {G : Type} [Group G]

theorem card_eq_eight_of_aeIdent {P : Set (Subgroup G)} {n : ℕ} (hn : 5 ≤ n) (I : AEIdent P n)
    {L : Subgroup G} (hL : L ∈ P) (hq : IsQuatSub L) : Nat.card L = 8 := by
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  exact card_eq_eight_of_map_memBar hn (le_pSpan hL) hq I.φ hlab

theorem card_eq_eight_of_aeIdentOn {P : Set (Subgroup G)} {n : ℕ} {𝒜 : Set (Finset (Fin n))}
    {M : Subgroup (AE.AEQ n)} (hn : 5 ≤ n) (I : AEIdentOn P n 𝒜 M) {L : Subgroup G}
    (hL : L ∈ P) (hq : IsQuatSub L) : Nat.card L = 8 := by
  obtain ⟨α, -, h, b, hlab⟩ := I.label L hL
  exact card_eq_eight_of_map_memBar hn (le_pSpan hL) hq I.φ hlab

private theorem eq_three_of_pow_eq_eight {r : ℕ} (h : 2 ^ r = 8) : r = 3 :=
  Nat.pow_right_injective (le_refl 2) (show 2 ^ r = 2 ^ 3 by omega)

variable [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem false_of_aeIdent_of_four_le (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) {P : Set (Subgroup G)}
    (hPΩ : P ⊆ Ω) {n : ℕ} (hn : 5 ≤ n) (I : AEIdent P n) {L : Subgroup G} (hL : L ∈ P) :
    False := by
  have hq : IsQuatSub L :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup (hPΩ hL) (h2 L (hPΩ hL)))
  have h := card_eq_eight_of_aeIdent hn I hL hq
  rw [h8 L (hPΩ hL)] at h
  have := eq_three_of_pow_eq_eight h
  omega

theorem false_of_aeIdentOn_of_four_le (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) {P : Set (Subgroup G)}
    (hPΩ : P ⊆ Ω) {n : ℕ} {𝒜 : Set (Finset (Fin n))} {M : Subgroup (AE.AEQ n)} (hn : 5 ≤ n)
    (I : AEIdentOn P n 𝒜 M) {L : Subgroup G} (hL : L ∈ P) : False := by
  have hq : IsQuatSub L :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup (hPΩ hL) (h2 L (hPΩ hL)))
  have h := card_eq_eight_of_aeIdentOn hn I hL hq
  rw [h8 L (hPΩ hL)] at h
  have := eq_three_of_pow_eq_eight h
  omega

end Outcomes

@[expose] def ThmDAbsCollapsedAt (r : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ Ω : Set (Subgroup G), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 2 ^ r) → (∀ J ∈ Ω, AEmpty Ω J) →
    pSpan Ω = ⊤ → (∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') →
    classicalInvolutionOddCore G = ⊥ →
    (∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ Ω, ∀ L' ∈ Ω, L = L') ∨ ∃ W : Subgroup G, WSet Ω = {W}

@[expose] def ThmDAbsCollapsed (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ThmDAbsCollapsedAt r G

section Packaging

variable {G : Type} [Group G] [Finite G]

theorem thmDAbsAt_of_collapsed {r : ℕ} (h : ThmDAbsCollapsedAt r G) : ThmDAbsAt r G := by
  intro Ω hΩ h2 h8 hA hgen htrans hodd hinO2
  rcases h Ω hΩ h2 h8 hA hgen htrans hodd hinO2 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)

theorem thmDAbs_of_collapsed {r : ℕ} (h : ThmDAbsCollapsed r) : ThmDAbs r :=
  fun G _ _ => thmDAbsAt_of_collapsed (h G)

end Packaging

end CFSG.CGT.PushingUpLit.SolKNA.R4
