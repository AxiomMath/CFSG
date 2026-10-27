module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Realizer

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem rk2_exists_realizer (hp : p.Prime) (h1 : 1 ≤ GLATwoLocalRank p Y) :
    ∃ A Q : Subgroup Y, IsElemAbelian p A ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      A ≤ Subgroup.normalizer (Q : Set Y) ∧ Nat.card A = p ^ GLATwoLocalRank p Y := by
  have hS : GLATwoLocalRank p Y = sSup {k | ∃ H : Subgroup Y, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := rfl
  have hne : {k | ∃ H : Subgroup Y, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : sSup (∅ : Set ℕ) = 0 := by simp
    rw [hS, h, h0] at h1
    omega
  obtain ⟨H, ⟨Q, hQ1, hQ2, rfl⟩, hH⟩ := Nat.sSup_mem hne (bddAbove_twoLocalPRanks hp.one_lt)
  obtain ⟨A, hAH, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.normalizer (Q : Set Y))
  refine ⟨A, Q, hA, hQ1, hQ2, hAH, ?_⟩
  rw [hAcard, hS, ← hH]

end Realizer

theorem rk2_isElemAbelian_sup_zpowers {G : Type} [Group G] {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A)
    {c : G} (hc : c ^ p = 1) (hcomm : ∀ a ∈ A, a * c = c * a) :
    IsElemAbelian p (A ⊔ Subgroup.zpowers c) := by
  have hcl : A ⊔ Subgroup.zpowers c = Subgroup.closure ((A : Set G) ∪ {c}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  rw [hcl]
  have hpair : ((A : Set G) ∪ {c}).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact isElemAbelian_commute hA hx hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hcomm x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact (hcomm y hy).symm
    · exact absurd ((Set.mem_singleton_iff.1 hx).trans (Set.mem_singleton_iff.1 hy).symm) hxy
  have hcomm' := Subgroup.isMulCommutative_closure hpair
  refine ⟨hcomm', fun x hx => ?_⟩
  refine Subgroup.closure_induction (p := fun x _ => x ^ p = 1) ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with hx | hx
    · exact hA.2 x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hc
  · exact one_pow p
  · intro x y hx hy hx1 hy1
    have hxy : Commute x y := Subtype.ext_iff.1 (hcomm'.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, hx1, hy1, one_mul]
  · intro x hx hx1
    rw [inv_pow, hx1, inv_one]

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem rk2_twoLocal_add_one_le (hp : p.Prime) {K X : Subgroup G} (hKX : K ≤ X)
    (h1 : 1 ≤ GLATwoLocalRank p ↥K) {c : G} (hcX : c ∈ X) (hcK : c ∈ Subgroup.centralizer (K : Set G))
    (hc1 : c ≠ 1) (hcp : c ^ p = 1) :
    GLATwoLocalRank p ↥K + 1 ≤ GLATwoLocalRank p ↥X + CFSG.Open.pRank p (Subgroup.center ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, Q, hA, hQ1, hQ2, hAQ, hAcard⟩ := rk2_exists_realizer hp h1
  let i : ↥K →* ↥X := Subgroup.inclusion hKX
  have hi : Function.Injective i := Subgroup.inclusion_injective hKX
  let c' : ↥X := ⟨c, hcX⟩
  have hcomm : ∀ k : ↥K, i k * c' = c' * i k := fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hcK k.1 k.2)
  have hc'p : c' ^ p = 1 := Subtype.ext (by simpa using hcp)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hA'' : IsElemAbelian p (A.map i) := CFSG.SectionRank.isElemAbelian_map hA i
  have hQ''1 : Q.map i ≠ ⊥ := by
    intro h
    apply hQ1
    rw [eq_bot_iff]
    intro x hx
    have : i x ∈ Q.map i := Subgroup.mem_map_of_mem i hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact hi (this.trans (map_one i).symm)
  have hQ''2 : IsPGroup 2 (Q.map i) :=
    IsPGroup.of_surjective hQ2 (Subgroup.equivMapOfInjective Q i hi).toMonoidHom
      (Subgroup.equivMapOfInjective Q i hi).surjective
  have hAQ'' : A.map i ≤ Subgroup.normalizer ((Q.map i : Subgroup ↥X) : Set ↥X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨a * q * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAQ ha) q).1 hq, by simp⟩
    · rintro ⟨q, hq, hqy⟩
      refine ⟨a⁻¹ * q * a, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hAQ (A.inv_mem ha)) q).1 hq
        simpa using this
      · simp only [map_mul, map_inv, hqy]
        group
  have hcQ'' : c' ∈ Subgroup.normalizer ((Q.map i : Subgroup ↥X) : Set ↥X) := by
    have hcen : ∀ z ∈ Q.map i, c' * z * c'⁻¹ = z := by
      rintro _ ⟨q, -, rfl⟩
      rw [← hcomm q]
      simp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcen y hy]
      exact hy
    · intro hy
      have hy1 : c' * y * c'⁻¹ ∈ Q.map i := hy
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 hy1
      have hyq : y = i q := by
        calc y = c'⁻¹ * (c' * y * c'⁻¹) * c' := by group
          _ = c'⁻¹ * (i q) * c' := by rw [← hqe]
          _ = i q := by rw [mul_assoc, hcomm q, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hyq]
      exact Subgroup.mem_map_of_mem i hq
  have hAcard'' : Nat.card (A.map i) = p ^ GLATwoLocalRank p ↥K := by
    rw [Subgroup.card_map_of_injective hi, hAcard]
  by_cases hcA : c' ∈ A.map i
  · have hle : Nat.card (A.map i) ≤ p ^ GLATwoLocalRank p ↥X :=
      card_le_pow_glaTwoLocalRank hp hA'' hQ''1 hQ''2 hAQ''
    rw [hAcard''] at hle
    have h2 : GLATwoLocalRank p ↥K ≤ GLATwoLocalRank p ↥X :=
      (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
    obtain ⟨a, -, hac⟩ := Subgroup.mem_map.1 hcA
    have hac' : (a : G) = c := congrArg Subtype.val hac
    have hacent : a ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hac']
      exact (Subgroup.mem_centralizer_iff.1 hcK k.1 k.2)
    have ha1 : a ≠ 1 := fun h => hc1 (by rw [← hac', h]; rfl)
    have hap : a ^ p = 1 := Subtype.ext (by simpa [hac'] using hcp)
    have hE : IsElemAbelian p (Subgroup.zpowers a) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
        apply Subtype.ext
        change (x : ↥K) * y = y * x
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    have hEcard : Nat.card (Subgroup.zpowers a) = p ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hap ha1, pow_one]
    have h3 : 1 ≤ CFSG.Open.pRank p (Subgroup.center ↥K) :=
      CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.2 hacent) hE hEcard
    omega
  · set E := A.map i ⊔ Subgroup.zpowers c' with hEdef
    have hcomm' : ∀ a ∈ A.map i, a * c' = c' * a := by
      rintro _ ⟨a, -, rfl⟩
      exact hcomm a
    have hEel : IsElemAbelian p E := rk2_isElemAbelian_sup_zpowers hA'' hc'p hcomm'
    have hEn : E ≤ Subgroup.normalizer ((Q.map i : Subgroup ↥X) : Set ↥X) :=
      sup_le hAQ'' (Subgroup.zpowers_le.2 hcQ'')
    have hle : Nat.card E ≤ p ^ GLATwoLocalRank p ↥X :=
      card_le_pow_glaTwoLocalRank hp hEel hQ''1 hQ''2 hEn
    have hnorm : Subgroup.zpowers c' ≤ Subgroup.normalizer ((A.map i : Subgroup ↥X) : Set ↥X) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha => hcomm' a ha)
    have hmul := card_sup_mul_card_inf_of_le_normalizer hnorm
    have hCcard : Nat.card (Subgroup.zpowers c') = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hc'p hc'1]
    have hinf : Nat.card ↥(A.map i ⊓ Subgroup.zpowers c') = 1 := by
      have hdvd : Nat.card ↥(A.map i ⊓ Subgroup.zpowers c') ∣ p := by
        rw [← hCcard]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact h
      · exfalso
        have heq : A.map i ⊓ Subgroup.zpowers c' = Subgroup.zpowers c' :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hCcard])
        exact hcA ((inf_eq_right.1 heq) (Subgroup.mem_zpowers c'))
    rw [hinf, mul_one, hCcard, hAcard'', ← pow_succ] at hmul
    have hle' : p ^ (GLATwoLocalRank p ↥K + 1) ≤ p ^ GLATwoLocalRank p ↥X := by
      rw [← hmul]; exact hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle'
    omega

end Main

theorem i164At_of_tables (hSplit : Rk2Split) (G : Type) [Group G] [Finite G] : I164At G := by
  intro p hp hp2 X K B hKX hchev hBX hB hBK h4 hc hX hlt lab hLab hsplit
  have he5 : 5 ≤ evenRank ↥K := by omega
  have hS := hSplit ↥K lab p hLab hp hp2 hsplit he5
  obtain ⟨c, hcB, hc1⟩ := hc
  have hmk : 1 ≤ GLATwoLocalRank p ↥K := by omega
  have hstar := rk2_twoLocal_add_one_le hp hKX.1 hmk (hBX hcB.1) hcB.2 hc1 (hB.2 c hcB.1)
  omega

end CFSG.LocalAnalysis.GLTheoremA
