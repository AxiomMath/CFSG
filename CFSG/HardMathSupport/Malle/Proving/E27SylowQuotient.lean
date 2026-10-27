module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem exists_sylow_hom_comm_of_surjective
    {G J A : Type*} [Group G] [Group J] [CommGroup A] [Finite G] (π : G →* J)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) (P : Subgroup G)
    (hP : Nat.card P = 3 ^ (Nat.card G).factorization 3) (φ : P →* A)
    (hφ : Function.Surjective φ) :
    ∃ (Q : Subgroup J) (φ' : Q →* A), Nat.card Q = 3 ^ (Nat.card J).factorization 3 ∧
      Function.Surjective φ' := by
  classical
  have : Finite J := Finite.of_surjective π hπ
  have hH : P ⊓ π.ker = ⊥ := by
    have h1 : Nat.card ↥(P ⊓ π.ker) ∣ 3 ^ (Nat.card G).factorization 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ π.ker ≤ P)
      rwa [hP] at h
    have h2 : Nat.card ↥(P ⊓ π.ker) ∣ Nat.card π.ker :=
      Subgroup.card_dvd_of_le (inf_le_right : P ⊓ π.ker ≤ π.ker)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero] at hj
      exact Subgroup.card_eq_one.1 hj
    · exfalso
      have h3 : 3 ∣ Nat.card ↥(P ⊓ π.ker) := by
        rw [hj]
        exact dvd_pow_self 3 hj0.ne'
      exact hker (h3.trans h2)
  set f : P →* J := π.comp P.subtype with hfdef
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : G) ∈ P ⊓ π.ker :=
      Subgroup.mem_inf.2 ⟨x.2, MonoidHom.mem_ker.2 hx⟩
    rw [hH, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hJ : Nat.card π.ker * Nat.card J = Nat.card G := by
    have h := Subgroup.card_mul_index π.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hπ, Subgroup.card_top] at h
    exact h
  have hv : (Nat.card G).factorization 3 = (Nat.card J).factorization 3 := by
    have hkpos : Nat.card π.ker ≠ 0 := (Nat.card_pos (α := π.ker)).ne'
    have hJpos : Nat.card J ≠ 0 := (Nat.card_pos (α := J)).ne'
    rw [← hJ, Nat.factorization_mul hkpos hJpos, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  let e : P ≃* f.range := MonoidHom.ofInjective hinj
  refine ⟨f.range, φ.comp e.symm.toMonoidHom, ?_, ?_⟩
  · have hQ : Nat.card f.range = Nat.card P := (Nat.card_congr e.toEquiv).symm
    rw [hQ, hP, hv]
  · intro a
    obtain ⟨p, hp⟩ := hφ a
    refine ⟨e p, ?_⟩
    show φ (e.symm (e p)) = a
    rw [MulEquiv.symm_apply_apply]
    exact hp

end CFSG.HardMathSupport.Malle.Proving
