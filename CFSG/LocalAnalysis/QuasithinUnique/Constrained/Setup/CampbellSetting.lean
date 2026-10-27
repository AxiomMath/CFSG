module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.BlueprintB2Basic

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 Matrix CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization

@[expose] def Ecore (G : Type*) [Group G] : Subgroup G := centerTorsion 2 (CFSG.pCore 2 G)

structure IsNatBase {G : Type*} [Group G] {k : Type*} [Field k] (S : Sylow 2 G)
    (ρ : G →* SpecialLinearGroup (Fin 2) k) (X : Subgroup G)
    (ψ : X →* Multiplicative (Fin 2 → k)) : Prop where
  card_k : ∃ n : ℕ, 1 ≤ n ∧ Nat.card k = 2 ^ n
  surj : Function.Surjective ρ
  core_le : CFSG.pCore 2 G ≤ ρ.ker
  frattini_le : ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)) ≤
    frattini (G ⧸ CFSG.pCore 2 G)
  normal : X.Normal
  le_E : X ≤ Ecore G
  ψ_surj : Function.Surjective ψ
  ψ_equiv : ∀ (g : G) (x x' : X), (x' : G) = g * x * g⁻¹ →
    Multiplicative.toAdd (ψ x') = (ρ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψ x))
  ψ_ker : ψ.ker = (X ⊓ Subgroup.center G).subgroupOf X

structure IsSeed {G : Type*} [Group G] {k : Type*} [Field k] (S : Sylow 2 G)
    (ρ : G →* SpecialLinearGroup (Fin 2) k) (X : Subgroup G)
    (ψ : X →* Multiplicative (Fin 2 → k)) : Prop extends IsNatBase S ρ X ψ where
  not_le : ¬ thompsonJ (S : Subgroup G) ≤ CFSG.pCore 2 G

section Core

variable {G : Type*} [Group G]

theorem pCore_quotient_pCore_eq_bot' (p : ℕ) :
    CFSG.pCore p (G ⧸ CFSG.pCore p G) = ⊥ := by
  set N : Subgroup G := CFSG.pCore p G with hN
  set K : Subgroup G := (CFSG.pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := G ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := G) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKn : K.Normal := (CFSG.pCore_normal (G := G ⧸ N) (p := p)).comap _
  have hKN : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

end Core

section Seed

theorem odd_card_frattini_of_pCore_eq_bot {Gb : Type*} [Group Gb] [Finite Gb]
    (h : CFSG.pCore 2 Gb = ⊥) : Odd (Nat.card (frattini Gb)) := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 2 (frattini Gb)) := inferInstance
  have hn : (P.map (frattini Gb).subtype).Normal := frattini_sylow_normal Gb 2 P
  have h2 : IsPGroup 2 (P.map (frattini Gb).subtype) := P.isPGroup'.map _
  have hle : P.map (frattini Gb).subtype ≤ CFSG.pCore 2 Gb := le_sSup ⟨hn, h2⟩
  rw [h] at hle
  have hP : (P : Subgroup (frattini Gb)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Gb) ∈ (⊥ : Subgroup Gb) := hle ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  have hcard : Nat.card P = 2 ^ (Nat.card (frattini Gb)).factorization 2 := P.card_eq_multiplicity
  rw [hP, Subgroup.card_bot] at hcard
  have hf : (Nat.card (frattini Gb)).factorization 2 = 0 := by
    rcases Nat.pow_eq_one.mp hcard.symm with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hndvd : ¬ 2 ∣ Nat.card (frattini Gb) := by
    intro hd
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hd
    omega
  exact Nat.odd_iff.mpr (by omega)

theorem odd_card_frattini_quotient_core (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (frattini (G ⧸ CFSG.pCore 2 G))) :=
  odd_card_frattini_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot' 2)

variable {G : Type*} [Group G] {k : Type*} [Field k]
  {S : Sylow 2 G} {ρ : G →* SpecialLinearGroup (Fin 2) k} {X : Subgroup G}
  {ψ : X →* Multiplicative (Fin 2 → k)}

theorem core_le_sylow {G : Type*} [Group G] (S : Sylow 2 G) : CFSG.pCore 2 G ≤ S :=
  (CFSG.pCore_isPGroup (G := G) (p := 2)).le_sylow_of_normal S

namespace IsNatBase

theorem charP_two (h : IsNatBase S ρ X ψ) : CharP k 2 := by
  obtain ⟨n, hn, hk⟩ := h.card_k
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hn hk

theorem odd_card_ker [Finite G] (h : IsNatBase S ρ X ψ) :
    Odd (Nat.card (ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)))) :=
  (odd_card_frattini_quotient_core G).of_dvd_nat (Subgroup.card_dvd_of_le h.frattini_le)

theorem ker_inf_le_core [Finite G] (h : IsNatBase S ρ X ψ) {P : Subgroup G} (hP : IsPGroup 2 P) :
    ρ.ker ⊓ P ≤ CFSG.pCore 2 G := by
  rintro x ⟨hxN, hxP⟩
  obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
  have hx2 : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 G) x ∈
      ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)) := ⟨x, hxN, rfl⟩
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 G) x) ∣
      Nat.card (ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G))) := by
    have := _root_.orderOf_dvd_natCard (⟨_, hmk⟩ : ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 G) x) ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx2, map_one])
  have hcop : Nat.Coprime (2 ^ a) (Nat.card (ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)))) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr h.odd_card_ker)
  have h3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 G) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3


theorem sylow_inf_ker [Finite G] (h : IsNatBase S ρ X ψ) : (S : Subgroup G) ⊓ ρ.ker = CFSG.pCore 2 G :=
  le_antisymm (by rw [inf_comm]; exact h.ker_inf_le_core S.isPGroup')
    (le_inf (core_le_sylow S) h.core_le)

theorem exists_rootGrp_eq [Finite G] [Finite k] (h : IsNatBase S ρ X ψ) :
    ∃ ℓ : ℙ k (Fin 2 → k), (S : Subgroup G).map ρ = rootGrp ℓ := by
  obtain ⟨n, hn, hk⟩ := h.card_k
  have hq1 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    intro hd
    have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h3 : 0 < (2 ^ n) ^ 2 := by positivity
    omega
  have hfac : (2 ^ n * ((2 ^ n) ^ 2 - 1)).factorization 2 = n := by
    have hne1 : 2 ^ n ≠ 0 := by positivity
    have hne2 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
      intro h0
      rw [h0] at hq1
      exact hq1 (dvd_zero 2)
    rw [Nat.factorization_mul hne1 hne2]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hq1]
  have hsyl : Nat.card ((Sylow.mapSurjective h.surj S : Sylow 2 (SpecialLinearGroup (Fin 2) k)) :
      Subgroup (SpecialLinearGroup (Fin 2) k)) = Nat.card k := by
    rw [Sylow.card_eq_multiplicity, card_specialLinearGroup_fin_two, hk, hfac]
  have hmap : ((Sylow.mapSurjective h.surj S : Sylow 2 (SpecialLinearGroup (Fin 2) k)) :
      Subgroup (SpecialLinearGroup (Fin 2) k)) = (S : Subgroup G).map ρ := rfl
  rw [← hmap]
  exact exists_point_eq_rootGrp Nat.prime_two hk hsyl

theorem eq_top_of_map_eq_top [Finite G] (h : IsNatBase S ρ X ψ) {Y : Subgroup G}
    (hQY : CFSG.pCore 2 G ≤ Y) (hY : Y.map ρ = ⊤) : Y = ⊤ := by
  have h1 : Y ⊔ ρ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hY, Subgroup.comap_top]
  set Q := CFSG.pCore 2 G with hQ
  have h2 : Y.map (QuotientGroup.mk' Q) ⊔ frattini (G ⧸ Q) = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : Subgroup (G ⧸ Q)) = (Y ⊔ ρ.ker).map (QuotientGroup.mk' Q) := by
          rw [h1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
      _ = Y.map (QuotientGroup.mk' Q) ⊔ ρ.ker.map (QuotientGroup.mk' Q) := Subgroup.map_sup _ _ _
      _ ≤ Y.map (QuotientGroup.mk' Q) ⊔ frattini (G ⧸ Q) := sup_le_sup_left h.frattini_le _
  have h3 : Y.map (QuotientGroup.mk' Q) = ⊤ := frattini_nongenerating h2
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Y, QuotientGroup.mk' Q y = QuotientGroup.mk' Q x := by
    have : QuotientGroup.mk' Q x ∈ Y.map (QuotientGroup.mk' Q) := by
      rw [h3]; exact Subgroup.mem_top _
    exact this
  have hyx' : y⁻¹ * x ∈ Q := QuotientGroup.eq.mp hyx
  have hx : x = y * (y⁻¹ * x) := by group
  rw [hx]
  exact mul_mem hy (hQY hyx')

end IsNatBase

end Seed

end CFSG.QuasithinUnique.Setup.Campbell
