module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericUnique

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericStructureRes (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        Group.IsSolvable M ∧
          (∀ v ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
            Set G), v ≠ 1 → Nat.Coprime p (orderOf v) →
              ∀ k ∈ pCoreOf 2 M, k * v = v * k → k = 1) ∧
          rankThreePrimeCore p M ≤ pCoreOf 2 M ⊔
            centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)

theorem gl83GenericStructureMin_of_res (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) (h : GL83GenericStructureRes G) :
    GL83GenericStructureMin G := by
  intro p hp P M hM hfail hIH x hgen
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hsol, hcop, hpc⟩ := h p hp P M hM hfail hIH x hgen
  obtain ⟨h5, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hgen
  refine ⟨zpowers_eq_of_isGenericPoint hS hD1 hU0 hL hp hM hfail hIH hgen, hsol, ?_, hpc⟩
  intro v hv hv1 k hk hkv
  by_cases hpv : Nat.Coprime p (orderOf v)
  · exact hcop v hv hv1 hpv k hk hkv
  ·
    have hpdvd : p ∣ orderOf v := by
      rcases (Nat.coprime_or_dvd_of_prime hfact.out (orderOf v)) with h' | h'
      · exact absurd h' hpv
      · exact h'
    have hord0 : orderOf v ≠ 0 := (orderOf_pos v).ne'
    obtain ⟨a, n', hn', hvn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord0 p hfact.out.one_lt.ne'
    have ha : a ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hvn
      exact hn' (hvn ▸ hpdvd)
    have hn'0 : n' ≠ 0 := by
      rintro rfl
      exact hord0 (by rw [hvn, mul_zero])
    have hwo : orderOf (v ^ n') = p ^ a := by
      rw [orderOf_pow_of_dvd hn'0 ⟨p ^ a, by rw [hvn, mul_comm]⟩, hvn,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)]
    have hw1 : v ^ n' ≠ 1 := by
      intro h1
      have h2 : p ^ a = 1 := by rw [← hwo, h1, orderOf_one]
      exact ha ((Nat.pow_eq_one.mp h2).resolve_left hfact.out.one_lt.ne')
    have hwZ : v ^ n' ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) :
        Subgroup G) : Set G) := Subgroup.pow_mem _ hv n'
    have hkw : k * v ^ n' = v ^ n' * k := ((Commute.pow_right (show Commute k v from hkv) n').eq)
    exact fixedPointFree_of_isPGroup hS hD1 hU0 hp hM hgen h5 hm2 e _ hwZ hw1
      ⟨a, by rw [← hwo]; exact pow_orderOf_eq_one _⟩ k hk hkw

end CFSG.LocalAnalysis.RankThreeTheoremC
