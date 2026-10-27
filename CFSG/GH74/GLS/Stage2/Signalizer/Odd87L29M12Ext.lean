module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilpDef
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12

theorem twoNilp_of_hom_central_two_kernel {D A : Type} [Group D] [Finite D] [Group A]
    (hA : TwoNilp A) (f : D →* A)
    (hcen : ∀ d ∈ f.ker, (∃ m : ℕ, d ^ (2 ^ m) = 1) → d ∈ Subgroup.center D) : TwoNilp D := by
  obtain ⟨N, hN, hodd, hidx⟩ := hA
  have hker : f.ker ≤ N.comap f := f.ker_le_comap N
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥f.ker) := inferInstance
  let ι : ↥f.ker →* ↥(N.comap f) := Subgroup.inclusion hker
  have hι : Function.Injective ι := Subgroup.inclusion_injective hker
  let Q : Subgroup ↥(N.comap f) := (S : Subgroup ↥f.ker).map ι
  have hQ2 : IsPGroup 2 ↥Q := S.isPGroup'.map ι
  have hQc : Q ≤ Subgroup.center ↥(N.comap f) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨s, hs⟩
    have hs2 : ((s : ↥f.ker) : D) ^ 2 ^ m = 1 := by
      have h1 := congrArg (fun x : ↥(S : Subgroup ↥f.ker) => (((x : ↥f.ker)) : D)) hm
      simpa using h1
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen _ s.2 ⟨m, hs2⟩) (g : D))
  have hQi : Odd Q.index := by
    have hn1 : Odd (Nat.card ↥(f.range ⊓ N)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
    have hS : Odd (S : Subgroup ↥f.ker).index :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Sylow.not_dvd_index S))
    have hc1 := L29TwoNilp.card_comap_eq f N
    have hc2 := Subgroup.card_mul_index (S : Subgroup ↥f.ker)
    have hc3 := Subgroup.card_mul_index Q
    have hc4 : Nat.card ↥Q = Nat.card ↥(S : Subgroup ↥f.ker) :=
      Subgroup.card_map_of_injective hι
    have hpos : 0 < Nat.card ↥(S : Subgroup ↥f.ker) := Nat.card_pos
    have hidxQ : Q.index = Nat.card ↥(f.range ⊓ N) * (S : Subgroup ↥f.ker).index := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc Nat.card ↥(S : Subgroup ↥f.ker) * Q.index = Nat.card ↥Q * Q.index := by rw [hc4]
        _ = Nat.card ↥(N.comap f) := hc3
        _ = Nat.card ↥(f.range ⊓ N) * Nat.card ↥f.ker := hc1
        _ = Nat.card ↥(f.range ⊓ N) * (Nat.card ↥(S : Subgroup ↥f.ker) *
              (S : Subgroup ↥f.ker).index) := by rw [hc2]
        _ = Nat.card ↥(S : Subgroup ↥f.ker) * (Nat.card ↥(f.range ⊓ N) *
              (S : Subgroup ↥f.ker).index) := by ring
    rw [hidxQ]
    exact Nat.odd_mul.mpr ⟨hn1, hS⟩
  have hN' : TwoNilp ↥(N.comap f) := L29TwoNilp.twoNilp_of_central_odd_index Q hQc hQ2 hQi
  have : N.Normal := hN
  exact twoNilp_of_normal_two_index (N.comap f) hN' (L29TwoNilp.exists_index_comap_two f N hidx)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12
