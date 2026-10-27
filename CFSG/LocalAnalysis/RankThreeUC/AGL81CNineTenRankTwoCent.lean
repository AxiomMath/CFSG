module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem mem_of_mem_centralizer_of_pow_eq_one (hp : p.Prime)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {A : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) {z : X}
    (hz : z ∈ centralizer (A : Set X)) (hzp : z ^ p = 1) : z ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hzA : z ∈ A
  · exact hzA
  exfalso
  have hz1 : z ≠ 1 := fun h => hzA (by rw [h]; exact A.one_mem)
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1
  let Z : Subgroup X := Subgroup.zpowers z
  have hZcard : Nat.card Z = p := by
    change Nat.card (Subgroup.zpowers z) = p
    rw [Nat.card_zpowers, hord]
  haveI : Fact (Nat.card Z).Prime := ⟨by rw [hZcard]; exact hp⟩
  rcases (A.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · have hinf : Z ⊓ A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hy' : (⟨y, hy.1⟩ : Z) ∈ A.subgroupOf Z := by
        rw [Subgroup.mem_subgroupOf]
        exact hy.2
      rw [hbot] at hy'
      have h1 : (⟨y, hy.1⟩ : Z) = 1 := Subgroup.mem_bot.mp hy'
      simpa using congrArg Subtype.val h1
    have hZcent : Z ≤ centralizer (A : Set X) := Subgroup.zpowers_le.mpr hz
    have hc : ∀ a ∈ Z, ∀ b ∈ A, a * b = b * a :=
      fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hZcent ha) b hb).symm
    have hElem : CFSG.Open.IsElemAbelian p (Z ⊔ A) :=
      CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hzp) hA hc
    have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hc
    have hBcard : Nat.card ↥(Z ⊔ A) = p ^ 3 := by
      have hp3 : p * p ^ 2 = p ^ 3 := by rw [← pow_succ' p 2]
      rw [hinf, Subgroup.card_bot, hZcard, hAc, mul_one] at hprod
      rw [hprod, hp3]
    have hle : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hElem hBcard
    omega
  · refine hzA ?_
    have hmem : (⟨z, Subgroup.mem_zpowers z⟩ : Z) ∈ A.subgroupOf Z := by
      rw [htop]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at hmem

theorem isPGroup_centralizer_of_pRank_le_two (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {A : Subgroup X} (hAn : A.Normal)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    IsPGroup p ↥(centralizer (A : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : A.Normal := hAn
  let K : Subgroup X := centralizer (A : Set X)
  haveI : K.Normal := by
    change (centralizer (A : Set X)).Normal
    infer_instance
  let P : Subgroup ↥K := CFSG.pCore p ↥K
  haveI : P.Normal := CFSG.pCore_normal (p := p) (G := ↥K)
  have hK : centralizer (P : Set ↥K) ≤ P :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_self_centralizing_pCore
      p hp hX K inferInstance
  have hp1 : ∀ x : ↥K, Nat.Coprime (orderOf x) p → x = 1 := by
    intro x hx
    let α : MulAut ↥P := MulAut.conjNormal (H := P) x
    have hαcop : Nat.Coprime (orderOf α) p :=
      hx.coprime_dvd_left (orderOf_map_dvd (MulAut.conjNormal (H := P)) x)
    have hfix : ∀ u : ↥P, u ^ p = 1 → α u = u := by
      intro u hu
      have hux : (((u : ↥P) : ↥K) : X) ∈ A := by
        refine mem_of_mem_centralizer_of_pow_eq_one hp hrk hA hAc ?_ ?_
        · exact ((u : ↥P) : ↥K).2
        · have h := congrArg (fun w : ↥P => (((w : ↥K) : X))) hu
          simpa using h
      have hcomm : x * (u : ↥K) = (u : ↥K) * x := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp
          (show (x : X) ∈ centralizer (A : Set X) from x.2) _ hux).symm
      apply Subtype.ext
      change ((MulAut.conjNormal (H := P) x) u : ↥K) = (u : ↥K)
      rw [MulAut.conjNormal_apply, hcomm]
      group
    have hα1 : α = 1 :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
        hp2 (CFSG.pCore_isPGroup (p := p) (G := ↥K)) hαcop hfix
    have hxcent : x ∈ centralizer (P : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h : (MulAut.conjNormal (H := P) x) ⟨y, hy⟩ = ⟨y, hy⟩ := by
        simpa [α] using congrArg (fun σ : MulAut ↥P => σ ⟨y, hy⟩) hα1
      have h2 := congrArg Subtype.val h
      simp only [Subtype.coe_mk, MulAut.conjNormal_apply] at h2
      have h' : x * y = y * x := by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = y * x := by rw [h2]
      exact h'.symm
    have hxP : x ∈ P := hK hxcent
    have hxord : orderOf x = 1 := by
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥K)).exists_orderOf_eq_pow
        ⟨x, hxP⟩
      have hn' : orderOf x = p ^ n := (Subgroup.orderOf_coe ⟨x, hxP⟩).trans hn
      have hdiv : orderOf x ∣ p ^ n := by rw [hn']
      exact Nat.eq_one_of_dvd_coprimes (hx.pow_right n) dvd_rfl hdiv
    exact orderOf_eq_one_iff.mp hxord
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.pos_iff_ne_zero.mp (orderOf_pos x)) p hp.ne_one
  have hYdvd : orderOf (x ^ p ^ a) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  have hmcop : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hm).symm
  have hYcop : Nat.Coprime (orderOf (x ^ p ^ a)) p := hmcop.coprime_dvd_left hYdvd
  have hxpa1 : x ^ p ^ a = 1 := hp1 _ hYcop
  have hdiv : orderOf x ∣ p ^ a := orderOf_dvd_of_pow_eq_one hxpa1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdiv
  exact ⟨j, hj⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
