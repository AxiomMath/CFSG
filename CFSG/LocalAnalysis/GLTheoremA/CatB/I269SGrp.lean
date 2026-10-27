module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Red
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

private theorem i269s_perm6 : ∀ σ : Equiv.Perm (Fin 6), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

theorem i269s_alt6_no15 (x : alternatingGroup (Fin 6)) : orderOf x ≠ 15 := by
  intro h15
  have h1 : x ^ 15 = 1 := by
    rw [← h15]
    exact pow_orderOf_eq_one x
  have h2 : (x : Equiv.Perm (Fin 6)) ^ 15 = 1 := by
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  rcases i269s_perm6 _ h2 with h3 | h5
  · have h3' : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one])
    have hd := orderOf_dvd_of_pow_eq_one h3'
    rw [h15] at hd
    norm_num at hd
  · have h5' : x ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h5, Subgroup.coe_one])
    have hd := orderOf_dvd_of_pow_eq_one h5'
    rw [h15] at hd
    norm_num at hd

theorem i269s_prime_dvd_720 {r : ℕ} (hr : r.Prime) (h : r ∣ 720) : r = 2 ∨ r = 3 ∨ r = 5 := by
  have h' : r ∣ 2 ^ 4 * 3 ^ 2 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1))

theorem i269s_fixed_sp4_solvable {G : Type} [Group G] [Finite G] (F D : Subgroup G)
    (hF : Nat.card F = 720) (hDF : D ≤ F) (eD : ↥D ≃* alternatingGroup (Fin 6))
    (hD : ∀ w ∈ F, ∀ q : ℕ, q.Prime → q ≠ 2 → w ^ q = 1 → w ∈ D)
    (y : G) (hyF : y ∈ F) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set G) ⊓ F) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) ⊓ F with hCdef
  have hCF : C ≤ F := inf_le_right
  have hdvd720 : Nat.card ↥C ∣ 720 := hF ▸ Subgroup.card_dvd_of_le hCF
  have h5 : ¬ 5 ∣ Nat.card ↥C := by
    intro hdvd
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
    have htC : (t : G) ∈ Subgroup.centralizer ({y} : Set G) := (t.2 : (t : G) ∈ C).1
    have htF : (t : G) ∈ F := (t.2 : (t : G) ∈ C).2
    have hcomm : Commute (t : G) y := by
      rw [Subgroup.mem_centralizer_iff] at htC
      exact (htC y (Set.mem_singleton y)).symm
    have hot : orderOf (t : G) = 5 := by rw [Subgroup.orderOf_coe, ht]
    have ht5 : (t : G) ^ 5 = 1 := by rw [← hot]; exact pow_orderOf_eq_one _
    have hyD : y ∈ D := hD y hyF 3 Nat.prime_three (by norm_num) hy3
    have htD : (t : G) ∈ D := hD _ htF 5 (by norm_num) (by norm_num) ht5
    let a : ↥D := ⟨(t : G), htD⟩
    let b : ↥D := ⟨y, hyD⟩
    have hab : Commute a b := Subtype.ext hcomm
    have hao : orderOf a = 5 := by rw [← Subgroup.orderOf_coe (H := D) a]; exact hot
    have hbo : orderOf b = 3 := by
      have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      have hbne : b ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
      exact orderOf_eq_prime hb3 hbne
    have hprod : orderOf (a * b) = 15 := by
      rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hao, hbo]; norm_num), hao, hbo]
    have himg : orderOf (eD (a * b)) = 15 := by
      rw [← hprod]
      exact orderOf_injective eD.toMonoidHom eD.injective (a * b)
    exact i269s_alt6_no15 _ himg
  have hpf : (Nat.card ↥C).primeFactors.card ≤ 2 := by
    have hsub : (Nat.card ↥C).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrm : r ∣ Nat.card ↥C := Nat.dvd_of_mem_primeFactors hr
      rcases i269s_prime_dvd_720 hrp (hrm.trans hdvd720) with h | h | h
      · simp [h]
      · simp [h]
      · exact absurd (h ▸ hrm) h5
    exact (Finset.card_le_card hsub).trans (by decide)
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hpf

theorem i269s_solvable_of_prod {G : Type} [Group G] (P Q R : Subgroup G) [Group.IsSolvable ↥P]
    [Group.IsSolvable ↥Q] (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hR : ∀ g ∈ R, ∃ p ∈ P, ∃ q ∈ Q, g = p * q) : Group.IsSolvable ↥R := by
  let M : (↥P × ↥Q) →* G :=
    { toFun := fun pq => (pq.1 : G) * (pq.2 : G)
      map_one' := by simp
      map_mul' := fun a b => by
        have hcomm : (b.1 : G) * (a.2 : G) = (a.2 : G) * (b.1 : G) :=
          hc _ b.1.2 _ a.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (a.1 : G) * (b.1 : G) * ((a.2 : G) * (b.2 : G))
            = (a.1 : G) * ((b.1 : G) * (a.2 : G)) * (b.2 : G) := by simp only [mul_assoc]
          _ = (a.1 : G) * ((a.2 : G) * (b.1 : G)) * (b.2 : G) := by rw [hcomm]
          _ = (a.1 : G) * (a.2 : G) * ((b.1 : G) * (b.2 : G)) := by simp only [mul_assoc] }
  have hle : R ≤ M.range := by
    intro g hg
    obtain ⟨p, hp, q, hq, rfl⟩ := hR g hg
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hsolv : Group.IsSolvable ↥M.range :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective M)
  exact CFSG.LocalAnalysis.GLTheoremA.isSolvable_of_le_isSolvable hle

end CFSG.LocalAnalysis.GLTheoremA

end
