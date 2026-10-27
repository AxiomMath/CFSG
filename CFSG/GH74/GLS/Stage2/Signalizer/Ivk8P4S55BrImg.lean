module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CentExt
public import CFSG.GH74.GLS.Stage2.Final.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

section Images

variable {G : Type} [Group G] {Γ₀ : Type} [Group Γ₀] {H : Subgroup G}

theorem map_isPGroup {p : ℕ} (π : ↥H →* Γ₀) {P : Subgroup G} (hP : IsPGroup p ↥P) :
    IsPGroup p ↥((P.subgroupOf H).map π) := by
  have h1 : IsPGroup p ↥(P.subgroupOf H) := by
    intro x
    obtain ⟨k, hk⟩ := hP ⟨((x : ↥H) : G), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  exact h1.map π

theorem map_le_normalizer (π : ↥H →* Γ₀) {T P : Subgroup G}
    (hTP : T ≤ normalizer (P : Set G)) :
    (T.subgroupOf H).map π ≤ normalizer (((P.subgroupOf H).map π : Subgroup Γ₀) : Set Γ₀) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_normalizer_iff]
  intro w
  have hnorm : ∀ (s : ↥H), (s : G) ∈ T → ∀ u : ↥H,
      (u : G) ∈ P ↔ (s * u * s⁻¹ : ↥H) ∈ P.subgroupOf H :=
    fun s hs u => mem_normalizer_iff.mp (hTP hs) (u : G)
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨t * u * t⁻¹, (hnorm t ht u).mp hu, ?_⟩
    simp
  · rintro ⟨u', hu', hu'w⟩
    refine ⟨t⁻¹ * u' * t, ?_, ?_⟩
    · have hti : ((t⁻¹ : ↥H) : G) ∈ T := T.inv_mem ht
      have := (hnorm t⁻¹ hti u').mp hu'
      simpa using this
    · have : π (t⁻¹ * u' * t) = (π t)⁻¹ * π u' * π t := by simp
      rw [this, hu'w]
      group

end Images

section Sylow

variable {G : Type} [Group G] [Finite G] {Γ₀ : Type} [Group Γ₀] {H : Subgroup G}

theorem exists_sylow_map (π : ↥H →* Γ₀) (hπ : Function.Surjective π) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTH : T ≤ H) :
    ∃ T₀ : Sylow 2 Γ₀, (T₀ : Subgroup Γ₀) = (T.subgroupOf H).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CFSG.GH74.GLS.Stage2.Final.sylow_of_sylowTop hT
  refine ⟨(Q.subtype (hQ ▸ hTH)).mapSurjective hπ, ?_⟩
  rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, hQ]

end Sylow

section Normal

variable {Γ₀ : Type} [Group Γ₀] [Finite Γ₀]

omit [Finite Γ₀] in
theorem pCore_eq_bot_of_normal {p : ℕ} (hO : pCore p Γ₀ = ⊥) (Γ : Subgroup Γ₀) [Γ.Normal] :
    pCore p ↥Γ = ⊥ := by
  let O : Subgroup Γ₀ := (pCore p ↥Γ).map Γ.subtype
  have hOn : O.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hn
    have hinv : (pCore p ↥Γ).map (MulAut.conjNormal (H := Γ) x).toMonoidHom = pCore p ↥Γ :=
      pCore_map_iso p (MulAut.conjNormal (H := Γ) x)
    have hmem : (MulAut.conjNormal (H := Γ) x) m ∈ pCore p ↥Γ := by
      rw [← hinv]
      exact ⟨m, hm, rfl⟩
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  have hOp : IsPGroup p ↥O := (pCore_isPGroup (p := p) (G := ↥Γ)).map Γ.subtype
  have hle : O ≤ pCore p Γ₀ := le_sSup ⟨hOn, hOp⟩
  rw [hO] at hle
  have : O = ⊥ := le_bot_iff.mp hle
  exact (Subgroup.map_eq_bot_iff_of_injective (pCore p ↥Γ) Γ.subtype_injective).mp this

omit [Finite Γ₀] in
theorem eq_bot_of_normal_pgroup {p : ℕ} (hO : pCore p Γ₀ = ⊥) (Γ : Subgroup Γ₀) [Γ.Normal]
    (N : Subgroup ↥Γ) (hN : N.Normal) (hNp : IsPGroup p ↥N) : N = ⊥ := by
  have hle : N ≤ pCore p ↥Γ := le_sSup ⟨hN, hNp⟩
  rw [pCore_eq_bot_of_normal hO Γ] at hle
  exact le_bot_iff.mp hle

theorem mem_of_pow_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Γ : Subgroup Γ₀) [Γ.Normal]
    (hidx : Γ.index ≤ 2) {x : Γ₀} {k : ℕ} (hx : x ^ p ^ k = 1) : x ∈ Γ := by
  rw [← QuotientGroup.eq_one_iff]
  have hcard : Nat.card (Γ₀ ⧸ Γ) = Γ.index := rfl
  have hcop : Nat.Coprime p (Nat.card (Γ₀ ⧸ Γ)) := by
    rw [hcard]
    have hpos : 0 < Γ.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    interval_cases h : Γ.index
    · exact Nat.coprime_one_right p
    · exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have h1 : ((x : Γ₀) : Γ₀ ⧸ Γ) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  exact eq_one_of_pow_pow_of_pow hcop h1 pow_card_eq_one'

end Normal

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
