module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

section Transport

variable {S : Type} [Group S]

theorem SylowAutTrivial.of_sylow [Finite S] (P₀ : Sylow 2 S)
    (h : ∀ α : MulAut S, Odd (orderOf α) → (∀ t ∈ (P₀ : Subgroup S), α t = t) → α = 1) :
    SylowAutTrivial S := by
  intro P α hα hfix
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₀ P
  set c : MulAut S := MulAut.conj g with hc
  have hmem : ∀ x ∈ (P₀ : Subgroup S), c x ∈ (P : Subgroup S) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
  have h1 : c⁻¹ * α * c = 1 := by
    refine h _ ?_ ?_
    · have hpow : (c⁻¹ * α * c) ^ orderOf α = c⁻¹ * α ^ orderOf α * c := by
        have := conj_pow (a := c⁻¹) (b := α) (i := orderOf α)
        simpa using this
      rw [pow_orderOf_eq_one, mul_one, inv_mul_cancel] at hpow
      exact Odd.of_dvd_nat hα (orderOf_dvd_of_pow_eq_one hpow)
    · intro t ht
      have := hfix _ (hmem t ht)
      simp only [MulAut.mul_apply]
      rw [this]
      simp
  have : α = c * (c⁻¹ * α * c) * c⁻¹ := by group
  rw [this, h1]
  group

end Transport

section Inner

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem conj_injective_of_center_eq_bot (hc : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun f : MulAut S => f z) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * x = (x * z * x⁻¹) * x := by rw [this]
      _ = x * z := by group
  rw [hc] at hxc
  exact hxc

theorem mem_inner_of_odd_of_card (hc : Subgroup.center S = ⊥) {a : ℕ}
    (hcard : Nat.card (MulAut S) = 2 ^ a * Nat.card S) (α : MulAut S)
    (hα : Odd (orderOf α)) : α ∈ inner S := by
  have h1 : Nat.card (inner S) = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).toEquiv).symm
  have h2 : Nat.card (inner S) * (inner S).index = Nat.card (MulAut S) :=
    Subgroup.card_mul_index (inner S)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h3 : (inner S).index = 2 ^ a := by
    rw [h1] at h2
    have : Nat.card S * (inner S).index = Nat.card S * 2 ^ a := by rw [h2, hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h4 : orderOf (QuotientGroup.mk α : MulAut S ⧸ inner S) ∣ 2 ^ a := by
    rw [← h3, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h5 : orderOf (QuotientGroup.mk α : MulAut S ⧸ inner S) ∣ orderOf α :=
    orderOf_map_dvd (QuotientGroup.mk' (inner S)) α
  have hodd : Odd (orderOf (QuotientGroup.mk α : MulAut S ⧸ inner S)) := Odd.of_dvd_nat hα h5
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk α : MulAut S ⧸ inner S)) (2 ^ a) :=
    Nat.Coprime.pow_right a hodd.coprime_two_right
  have h6 : orderOf (QuotientGroup.mk α : MulAut S ⧸ inner S) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h4
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h6)

end Inner

section Simple

variable {S : Type} [Group S] [Finite S]

theorem sylowAutTrivial_of_overgroups [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x)
    (h2 : 2 ∣ Nat.card S) (hOv : Over.Overgroups S) {a : ℕ}
    (hcard : Nat.card (MulAut S) = 2 ^ a * Nat.card S) : SylowAutTrivial S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : x ∈ Subgroup.center S := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.1 hx y).symm)
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 S))
  refine SylowAutTrivial.of_sylow P₀ fun α hα hfix => ?_
  set P : Subgroup S := (P₀ : Subgroup S) with hP
  set N : Subgroup S := Subgroup.normalizer (P : Set S) with hN
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card P₀ = 1 := by
      have : Subsingleton (↥(P₀ : Subgroup S)) := by
        rw [← hP, hbot]
        infer_instance
      exact Nat.card_unique
    have hcard2 : Nat.card P₀ = 2 ^ (Nat.card S).factorization 2 :=
      Sylow.card_eq_multiplicity P₀
    have : 1 ≤ (Nat.card S).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
    have h4 : 2 ^ 1 ≤ 2 ^ (Nat.card S).factorization 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hnorm : P.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
    · exact hPne h
    · have hP2 : IsPGroup 2 S := by
        have h' : IsPGroup 2 ↥(⊤ : Subgroup S) := by
          rw [← h]
          exact P₀.isPGroup'
        exact h'.of_equiv (Subgroup.topEquiv (G := S))
      obtain ⟨x, y, hxy⟩ := hnc
      have : Nontrivial S := ⟨⟨x, y, fun h => hxy (by rw [h])⟩⟩
      have := hP2.center_nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).1 this hcen
  have hSyl : IsSylowTwoOf P ⊤ := isSylowTwoOf_top_of_sylow P₀
  have hCh : CharTwo N := hOv P N hSyl hPN hNtop
  have hSN : IsSylowTwoOf P N := isSylowTwoOf_of_le hSyl hPN
  have hcore : pCoreOf 2 N = P :=
    le_antisymm (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSN)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPN le_rfl P₀.isPGroup')
  obtain ⟨s, rfl⟩ := mem_inner_of_odd_of_card hcen hcard α hα
  have hsC : s ∈ Subgroup.centralizer (P : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := hfix t ht
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hsN : s ∈ N := Subgroup.centralizer_le_normalizer (P : Set S) hsC
  have hsP : s ∈ P := by
    have : s ∈ N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set S) := by
      rw [hcore]
      exact ⟨hsN, hsC⟩
    have := hCh this
    rwa [hcore] at this
  obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨s, hsP⟩
  have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hpow : (MulAut.conj s) ^ 2 ^ k = 1 := by rw [← map_pow, hsk, map_one]
  have hdvd : orderOf (MulAut.conj s) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime (orderOf (MulAut.conj s)) (2 ^ k) :=
    Nat.Coprime.pow_right k hα.coprime_two_right
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

end Simple

end CFSG.QuasithinUnique.Bridge
