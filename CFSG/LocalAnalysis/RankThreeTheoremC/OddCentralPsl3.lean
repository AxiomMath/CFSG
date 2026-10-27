module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped MatrixGroups

theorem eq_bot_of_central_odd_kernel_psl {J Q : Type} [Group J] [Finite J] [Group Q] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (ψ : J →* Q) (hker : ψ.ker ≤ Subgroup.center J)
    (hodd : Odd (Nat.card ψ.ker)) (hpk : ¬ p ∣ Nat.card ψ.ker) (hperf : commutator J = ⊤)
    (e : Q ≃* PSL(2, GaloisField p 2)) : ψ.ker = ⊥ := by
  by_contra hne
  have hcard1 : Nat.card ψ.ker ≠ 1 := by
    intro h
    exact hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hcard1
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrdvd)
  have hrp : r ≠ p := by
    rintro rfl
    exact hpk hrdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hzc : (z : J) ∈ Subgroup.center J := hker z.2
  have hzo : orderOf (z : J) = r := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : IsPGroup r (zpowers (z : J)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  obtain ⟨R, hzR⟩ := hzp.exists_le_sylow
  have hzR' : (z : J) ∈ (R : Subgroup J) := hzR (mem_zpowers _)
  set f : J →* PSL(2, GaloisField p 2) := e.toMonoidHom.comp ψ with hf
  obtain ⟨S, hS⟩ := (R.isPGroup'.map f).exists_le_sylow
  have hKcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hK7 : 7 ≤ Nat.card (GaloisField p 2) := by
    rw [hKcard]
    nlinarith
  have hcop : Nat.Coprime r (Nat.card (GaloisField p 2)) := by
    rw [hKcard]
    exact ((Nat.coprime_primes hr Fact.out).mpr hrp).pow_right 2
  have hScyc : IsCyclic S :=
    CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField p 2) hKcard hK7
      r hr2 hcop S
  have hTcyc : IsCyclic ↥((R : Subgroup J).map f) :=
    isCyclic_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
  have hRcomm : ∀ a b : (R : Subgroup J), a * b = b * a := by
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (f.subgroupMap R) ?_
    · exact fun a b => hcomm.is_comm.comm a b
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : f (a : J) = 1 := congrArg Subtype.val ha
    have h2 : ψ (a : J) = 1 := by
      have : e (ψ (a : J)) = 1 := h1
      simpa using this
    have h3 : (a : J) ∈ Subgroup.center J := hker h2
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp h3 (b : J))
  let _ : CommGroup (R : Subgroup J) :=
    { (inferInstance : Group (R : Subgroup J)) with mul_comm := hRcomm }
  let ϕ : (R : Subgroup J) →* (R : Subgroup J) :=
    { toFun := id, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hkey : ∀ (k : ℕ) (g₀ : J), g₀⁻¹ * (z : J) ^ k * g₀ ∈ (R : Subgroup J) →
      g₀⁻¹ * (z : J) ^ k * g₀ = (z : J) ^ k := by
    intro k g₀ _
    have hzk : (z : J) ^ k ∈ Subgroup.center J := Subgroup.pow_mem _ hzc k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow ϕ (z : J) hkey
  have hone : MonoidHom.transfer ϕ (z : J) = 1 := by
    have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
    rw [hperf] at hle
    exact (MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _)))
  rw [hone] at htr
  have hpow : (z : J) ^ (R : Subgroup J).index = 1 := congrArg Subtype.val htr.symm
  have hdvd : orderOf (z : J) ∣ (R : Subgroup J).index := orderOf_dvd_of_pow_eq_one hpow
  rw [hzo] at hdvd
  exact Sylow.not_dvd_index R hdvd

theorem eq_bot_of_central_odd_subgroup_psl {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {J O : Subgroup X} (hOJ : O ≤ J) (hcent : ⁅J, O⁆ = ⊥) (hodd : Odd (Nat.card O))
    (hpO : ¬ p ∣ Nat.card O) (hperf : ⁅J, J⁆ = J) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hker : ψ.ker = O.subgroupOf J) (e : Q ≃* PSL(2, GaloisField p 2)) : O = ⊥ := by
  have hcard : Nat.card ψ.ker = Nat.card O := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  have hJO : J ≤ Subgroup.centralizer (O : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent
  have hkc : ψ.ker ≤ Subgroup.center ↥J := by
    rw [hker]
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hJO b.2) (a : X) ha).symm
  have hperf' : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  have h0 := eq_bot_of_central_odd_kernel_psl hp5 ψ hkc (hcard ▸ hodd) (hcard ▸ hpO) hperf' e
  rw [hker, Subgroup.subgroupOf_eq_bot] at h0
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ O ⊓ J := ⟨hx, hOJ hx⟩
  rw [disjoint_iff.mp h0] at hmem
  exact hmem

end CFSG.LocalAnalysis.RankThreeTheoremC
