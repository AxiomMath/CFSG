module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Small.Eigenbasis
public import CFSG.GH74.SmallRanks.Basic
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Filter

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank

theorem twoRank_statedProj_le_two {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (H : Subgroup (GL (Fin 3) K)) (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    twoRank (StatedProj H) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := (StatedScalars (Fin 3) K).subgroupOf H with hN
  have hN3 : ∀ x : H, x ∈ N → x ^ 3 = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hc3 : (c : K) ^ 3 = 1 := by
      have := hdet x x.2
      rw [← hc, GeneralLinearGroup.coe_scalar] at this
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using this
    have hc1 : c ^ 3 = 1 := Units.ext (by simpa using hc3)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc1, map_one]
    rfl
  have hN2 : ¬ 2 ∣ Nat.card N := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hN3 x x.2))
    rw [hx] at h3
    omega
  change CFSG.Open.pRank 2 (⊤ : Subgroup (H ⧸ N)) ≤ 2
  rw [CFSG.SectionRank.pRank_quotient_eq N hN2]
  refine CFSG.SectionRank.pRank_le Nat.one_lt_two (fun E _ hE => ?_)
  have hE' : ∀ x ∈ E.map H.subtype, ∀ y ∈ E.map H.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hE.1
    exact congrArg (fun z : E => ((z : H) : GL (Fin 3) K)) (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have h := card_le_two_pow_of_elemAbelian_det h2 (n := 2) (E.map H.subtype) hE'
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact congrArg Subtype.val (hE.2 y hy))
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdet y y.2)
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at h

theorem two_ne_zero_of_card_eq {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ m) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((CharP.cast_eq_zero_iff K p 2).1 h'))

theorem t_PSL_three_odd : S_PSL_three_odd := by
  intro G _ _ p f hp2 hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Finite (StatedProj (StatedSL 3 K)) := Finite.of_equiv G e.toEquiv
  rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
  exact twoRank_statedProj_le_two (two_ne_zero_of_card_eq hp hp2 hK) _
    (fun x hx => CFSG.SectionRank.OddCover.det_eq_one_of_mem_statedSL hx)

theorem t_PSU_three_odd : S_PSU_three_odd := by
  intro G _ _ p f hp2 hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Finite (StatedProj (StatedSU 3 (p ^ f) K)) := Finite.of_equiv G e.toEquiv
  rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
  exact twoRank_statedProj_le_two
    (two_ne_zero_of_card_eq hp hp2 (m := f * 2) (by rw [hK, pow_mul])) _
    (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx)

end CFSG.GH74.Filter
