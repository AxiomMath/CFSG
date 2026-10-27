module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78PairComp
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

theorem exists_isSolomonPair (hmax : SolAltLit.MaximalAltComponentInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (h : ∃ (t₀ : X) (K₀ : Subgroup X) (m : ℕ),
      SolAltLit.IsAltTwoComponent t₀ K₀ m ∧ Odd m ∧ 9 ≤ m) :
    ∃ (t : X) (J : Subgroup X) (n : ℕ), IsSolomonPair t J n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, J₀, n, h₀, hodd, h9, hmaxn⟩ := SolAltLit.exists_isAltTwoComponent_max_odd h
  let v : Subgroup X → ℕ := fun J => (Nat.card (normalizer (J : Set X))).factorization 2
  let P := {p : X × Subgroup X // SolAltLit.IsAltTwoComponent p.1 p.2 n}
  have : Nonempty P := ⟨⟨(t₀, J₀), h₀⟩⟩
  obtain ⟨⟨⟨t₁, J₁⟩, h₁⟩, hbest⟩ := Finite.exists_max (fun p : P => v p.1.2)
  have hbest' : ∀ (t' : X) (J' : Subgroup X), SolAltLit.IsAltTwoComponent t' J' n →
      v J' ≤ v J₁ := fun t' J' h' => hbest ⟨(t', J'), h'⟩
  set N := normalizer (J₁ : Set X) with hN
  have hJ₁t₁ : J₁ ≤ centralizer ({t₁} : Set X) := h₁.2.1
  have ht₁C : t₁ ∈ centralizer (J₁ : Set X) := mem_centralizer_iff.mpr fun j hj =>
    mem_centralizer_singleton_iff.mp (hJ₁t₁ hj)
  have ht₁N : t₁ ∈ N := centralizer_le_normalizer _ ht₁C
  have ht₁o : orderOf t₁ = 2 := h₁.1
  have hP : IsPGroup 2 (zpowers (⟨t₁, ht₁N⟩ : N)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht₁o, pow_one]
  obtain ⟨S₀, hS₀⟩ := hP.exists_le_sylow
  set S : Subgroup X := (S₀ : Subgroup N).map N.subtype with hS
  have hSN : S ≤ N := map_subtype_le _
  have hSp : IsPGroup 2 S := S₀.isPGroup'.map N.subtype
  have hScard : Nat.card S = 2 ^ v J₁ := by
    rw [hS, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity S₀]
  have ht₁S : t₁ ∈ S := ⟨⟨t₁, ht₁N⟩, hS₀ (mem_zpowers _), rfl⟩
  set K : Subgroup S := (centralizer (J₁ : Set X)).subgroupOf S with hKdef
  have hKn : K.Normal := by
    refine ⟨fun k hk s => ?_⟩
    rw [hKdef, mem_subgroupOf] at hk ⊢
    have hsN : (s : X) ∈ N := hSN s.2
    rw [mem_centralizer_iff] at hk ⊢
    intro j hj
    have hj' : (s : X)⁻¹ * j * (s : X)⁻¹⁻¹ ∈ J₁ := (mem_normalizer_iff.mp (inv_mem hsN) j).mp hj
    have h1 := hk _ hj'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1 ⊢
    calc j * ((s : X) * (k : X) * (s : X)⁻¹) =
          (s : X) * (((s : X)⁻¹ * j * (s : X)) * (k : X)) * (s : X)⁻¹ := by group
      _ = (s : X) * ((k : X) * ((s : X)⁻¹ * j * (s : X))) * (s : X)⁻¹ := by rw [h1]
      _ = (s : X) * (k : X) * (s : X)⁻¹ * j := by group
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hmem : (⟨t₁, ht₁S⟩ : S) ∈ K := ht₁C
    rw [hbot, mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ht₁o
    norm_num at ht₁o
  have hnil : Group.IsNilpotent S := hSp.isNilpotent
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hKne)
  obtain ⟨hwK, hwZ⟩ := Subgroup.mem_inf.mp w.2
  have hw1' : (w : S) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw2 : 2 ∣ Nat.card (zpowers (w : S)) := by
    rw [Nat.card_zpowers]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hSp) (w : S)
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hw1'
    · rw [hk]
      exact dvd_pow_self 2 hpos.ne'
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := zpowers (w : S)) 2 hw2
  set u : X := ((u' : S) : X) with hudef
  have hu2 : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu']
  have huS : u ∈ S := (u' : S).2
  have huZ : (u' : S) ∈ center S := zpowers_le.mpr hwZ u'.2
  have huK : (u' : S) ∈ K := zpowers_le.mpr hwK u'.2
  have hSu : S ≤ centralizer ({u} : Set X) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have h1 := (mem_center_iff.mp huZ) ⟨x, hx⟩
    exact congrArg Subtype.val h1
  have hJ₁u : J₁ ≤ centralizer ({u} : Set X) := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (show u ∈ centralizer (J₁ : Set X) from huK) j hj
  obtain ⟨-, hii⟩ := hmax X hnonab hK hz hU t₁ J₁ n h₁ hodd h9 hmaxn
  have hnorm := hii u hu2 hJ₁u
  set J := oPrimeResidualOf 2 (pPrimeCoreOf 2 (centralizer ({u} : Set X)) ⊔ J₁) with hJdef
  have hJ : SolAltLit.IsAltTwoComponent u J n :=
    isAltTwoComponent_oPrimeResidualOf (by omega) hu2 h₁ hJ₁u hnorm
  have hSJ : S ≤ normalizer (J : Set X) := fun x hx =>
    mem_normalizer_oPrimeResidualOf (hnorm (hSu hx))
  have hvJ : v J ≤ v J₁ := hbest' u J hJ
  have hvJ' : v J₁ ≤ v J := by
    have h1 := Subgroup.card_dvd_of_le hSJ
    rw [hScard] at h1
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h1
  refine ⟨u, J, n, hJ, hodd, h9, hmaxn, fun t' J' h' => (hbest' t' J' h').trans hvJ',
    S, hSJ, hSp, ?_, huS, hSu⟩
  rw [hScard]
  exact congrArg (2 ^ ·) (le_antisymm hvJ' hvJ)

end CFSG.ComponentClassification.Sol78
