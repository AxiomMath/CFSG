module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.DisconnectedInvolutionGraph.Helpers
open scoped commutatorElement

theorem eq_bot_of_perfect_of_isSolvable {H : Type*} [Group H] (P : Subgroup H) (hperf : ⁅P, P⁆ = P)
    (hsolv : Group.IsSolvable ↥P) : P = ⊥ := by
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  have h2 : commutator ↥P = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem isSolvable_of_isCyclic_sylow_two {Q : Type*} [Group Q] [Finite Q] (T : Sylow 2 Q)
    (hT : IsCyclic ↥(T : Subgroup Q)) : Group.IsSolvable Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hn, hodd, hidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement T hT
  have hO : Group.IsSolvable ↥(pPrimeCore 2 Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hQ2 : IsPGroup 2 (Q ⧸ pPrimeCore 2 Q) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    show (pPrimeCore 2 Q).index = 2 ^ k
    rw [hidx]
    exact hk
  have : Group.IsNilpotent (Q ⧸ pPrimeCore 2 Q) := hQ2.isNilpotent
  have hq : Group.IsSolvable (Q ⧸ pPrimeCore 2 Q) := inferInstance
  exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 Q).subtype (QuotientGroup.mk' (pPrimeCore 2 Q))
    (by
      intro x hx
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

open QuaternionGroup in
theorem quat_facts {n m : ℕ} (hn : n = 2 * m) (hm : 0 < m) :
    (a (m : ZMod (2 * n)) : QuaternionGroup n) * a (m : ZMod (2 * n)) = a (n : ZMod (2 * n)) ∧
    (xa (0 : ZMod (2 * n)) : QuaternionGroup n) * xa 0 = a (n : ZMod (2 * n)) ∧
    (a (m : ZMod (2 * n)) : QuaternionGroup n) * xa 0 =
      xa 0 * a (m : ZMod (2 * n)) * a (n : ZMod (2 * n)) ∧
    (xa (0 : ZMod (2 * n)) : QuaternionGroup n) * xa (n : ZMod (2 * n)) = 1 ∧
    (a (m : ZMod (2 * n)) * xa (n : ZMod (2 * n)) : QuaternionGroup n) *
      (a (m : ZMod (2 * n)) * xa (n : ZMod (2 * n))) = a (n : ZMod (2 * n)) ∧
    (a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 ∧
    (a (n : ZMod (2 * n)) : QuaternionGroup n) * a (n : ZMod (2 * n)) = 1 := by
  have hn0 : 0 < n := by omega
  have h2n : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
  have h2n' : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
    have := h2n
    push_cast at this
    exact this
  have hmm : (2 : ZMod (2 * n)) * (m : ZMod (2 * n)) = (n : ZMod (2 * n)) := by
    have : ((2 * m : ℕ) : ZMod (2 * n)) = (n : ZMod (2 * n)) := by rw [hn]
    push_cast at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_mul_a]
    congr 1
    rw [← hmm]
    ring
  · rw [xa_mul_xa]
    congr 1
    ring
  · rw [a_mul_xa, xa_mul_a, xa_mul_a]
    congr 1
    linear_combination (-1 : ZMod (2 * n)) * hmm + (-1 : ZMod (2 * n)) * h2n'
  · rw [xa_mul_xa, one_def]
    congr 1
    linear_combination h2n'
  · rw [a_mul_xa, xa_mul_xa]
    congr 1
    ring
  · intro h
    rw [one_def] at h
    have h' : (n : ZMod (2 * n)) = 0 := by injection h
    have h'' := (ZMod.natCast_eq_zero_iff n (2 * n)).mp h'
    have := Nat.le_of_dvd hn0 h''
    omega
  · rw [a_mul_a, one_def]
    congr 1
    linear_combination h2n'

theorem orderOf_eq_two_of_diag {L H : Type*} [Group L] [Finite L] [Group H] [Finite H] (δ : L →* H)
    (hu : ∀ u v : L, orderOf u = 2 → orderOf v = 2 → u = v)
    (hk : ∀ x : L, δ x = 1 → x * x = 1)
    {P : Subgroup H} (hperf : ⁅P, P⁆ = P)
    (hP1 : ∀ u v : H, u ∈ P → v ∈ P → orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (hPδ : ∀ p ∈ P, ∃ x : L, δ x = p)
    {l : L} (hl : δ l ∈ P) (hl2 : orderOf (δ l) = 2) : orderOf l = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : δ l * δ l = 1 := by
    have := pow_orderOf_eq_one (δ l)
    rwa [hl2, pow_two] at this
  have h1 : δ (l * l) = 1 := by rw [map_mul]; exact hsq
  have h4 : (l * l) * (l * l) = 1 := hk _ h1
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hl2
    omega
  by_contra hne
  have hl4 : orderOf l = 4 := by
    have hpow : l ^ (2 ^ 2) = 1 := by
      have : l ^ (2 ^ 2) = (l * l) * (l * l) := by
        rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
      rw [this]
      exact h4
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
    interval_cases j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hjo)) hl1
    · exact absurd (by simpa using hjo) hne
    · simpa using hjo
  have hz1 : l * l ≠ 1 := by
    intro h
    have h2 : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hl4] at h2
    omega
  have hz2 : orderOf (l * l) = 2 := orderOf_eq_prime (by rw [pow_two]; exact h4) hz1
  have hz : ∀ u : L, orderOf u = 2 → u = l * l := fun u hu2 => hu u _ hu2 hz2
  set Q : Subgroup L := P.comap δ with hQdef
  have hQmem : ∀ x : ↥Q, δ (x : L) ∈ P := fun x => x.2
  have hQnotsolv : ¬ Group.IsSolvable ↥Q := by
    intro hs
    let f : ↥Q →* ↥P := (δ.comp Q.subtype).codRestrict P hQmem
    have hf : Function.Surjective f := by
      intro p
      obtain ⟨x, hx⟩ := hPδ p p.2
      exact ⟨⟨x, by rw [hQdef, Subgroup.mem_comap, hx]; exact p.2⟩, Subtype.ext hx⟩
    have : Group.IsSolvable ↥P := Group.isSolvable_of_surjective hf
    have hbot := eq_bot_of_perfect_of_isSolvable P hperf this
    have : δ l ∈ (⊥ : Subgroup H) := hbot ▸ hl
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hl2
    omega
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Q) := inferInstance
  have hrank : NoCommutingDistinctInvolutions ↥(T : Subgroup ↥Q) := by
    intro u v _
    have hu' : orderOf (((u.1 : ↥(T : Subgroup ↥Q)) : ↥Q) : L) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact u.2
    have hv' : orderOf (((v.1 : ↥(T : Subgroup ↥Q)) : ↥Q) : L) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact v.2
    have := hu _ _ hu' hv'
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  rcases rank_one_two_cyclic_or_quaternion T.isPGroup' hrank with hcyc | ⟨e, he1, ⟨ε⟩⟩
  · exact hQnotsolv (isSolvable_of_isCyclic_sylow_two T hcyc)
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ :=
      quat_facts (n := 2 ^ (e' + 1)) (m := 2 ^ e') (by rw [pow_succ']) (by positivity)
    let ψ : QuaternionGroup (2 ^ (e' + 1)) →* ↥Q := (T : Subgroup ↥Q).subtype.comp ε.toMonoidHom
    have hψinj : Function.Injective ψ :=
      Subtype.val_injective.comp ε.injective
    let φ : QuaternionGroup (2 ^ (e' + 1)) →* L := Q.subtype.comp ψ
    have hφinj : Function.Injective φ := Subtype.val_injective.comp hψinj
    have hφP : ∀ x, δ (φ x) ∈ P := fun x => hQmem (ψ x)
    set u₀ : L := φ (QuaternionGroup.a ((2 ^ e' : ℕ) : ZMod (2 * 2 ^ (e' + 1)))) with hu₀
    set v₀ : L := φ (QuaternionGroup.xa 0) with hv₀
    set ν : L := φ (QuaternionGroup.xa ((2 ^ (e' + 1) : ℕ) : ZMod (2 * 2 ^ (e' + 1)))) with hν
    set ζ : L := φ (QuaternionGroup.a ((2 ^ (e' + 1) : ℕ) : ZMod (2 * 2 ^ (e' + 1)))) with hζ
    have hζ1 : ζ ≠ 1 := fun h => hq6 (hφinj (h.trans (map_one φ).symm))
    have hζζ : ζ * ζ = 1 := by rw [hζ, ← map_mul, hq7, map_one]
    have hζ2 : orderOf ζ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hζζ) hζ1
    have hζz : ζ = l * l := hz ζ hζ2
    have hδζ : δ ζ = 1 := by rw [hζz]; exact h1
    have huu : u₀ * u₀ = ζ := by rw [hu₀, hζ, ← map_mul, hq1]
    have hvv : v₀ * v₀ = ζ := by rw [hv₀, hζ, ← map_mul, hq2]
    have huv : u₀ * v₀ = v₀ * u₀ * ζ := by
      rw [hu₀, hv₀, hζ, ← map_mul, ← map_mul, ← map_mul, hq3]
    have hvν : v₀ * ν = 1 := by rw [hv₀, hν, ← map_mul, hq4, map_one]
    have hwsq : (u₀ * ν) * (u₀ * ν) = ζ := by rw [hu₀, hν, hζ, ← map_mul, ← map_mul, hq5]
    have hd1 : δ u₀ * δ u₀ = 1 := by rw [← map_mul, huu]; exact hδζ
    have hd2 : δ v₀ * δ v₀ = 1 := by rw [← map_mul, hvv]; exact hδζ
    have hd1n : δ u₀ ≠ 1 := by
      intro h
      have := hk _ h
      rw [huu] at this
      exact hζ1 this
    have hd2n : δ v₀ ≠ 1 := by
      intro h
      have := hk _ h
      rw [hvv] at this
      exact hζ1 this
    have hcomm : δ u₀ * δ v₀ = δ v₀ * δ u₀ := by
      have := congrArg δ huv
      rw [map_mul, map_mul, map_mul, hδζ, mul_one] at this
      exact this
    have hne12 : δ u₀ ≠ δ v₀ := by
      intro h
      have h' : δ (u₀ * ν) = 1 := by
        rw [map_mul, h, ← map_mul, hvν, map_one]
      have := hk _ h'
      rw [hwsq] at this
      exact hζ1 this
    have ho1 : orderOf (δ u₀) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd1) hd1n
    have ho2 : orderOf (δ v₀) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd2) hd2n
    exact hne12 (hP1 _ _ (hφP _) (hφP _) ho1 ho2 hcomm)

end CFSG.GH74.GLS.Bg.Pu5
