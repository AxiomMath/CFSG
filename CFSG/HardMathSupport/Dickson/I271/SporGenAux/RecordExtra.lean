module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ExtraPlane
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.LinesGood

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.Sporadic.SmallOddCore

theorem noSig_planes_of_extra {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup M} (hAP : A ≤ P) (hA3 : Nat.card A = p ^ 3)
    (hA_sylow : ∃ S : Sylow p ↥P, (S : Subgroup ↥P) = A.subgroupOf P)
    (hAexp : ∀ x ∈ A, x ^ p = 1)
    {z : M} (hzR : z ∈ R) (hz1 : z ≠ 1) (hAC : A ≤ centralizer ({z} : Set M))
    (hAn : ∀ c ∈ R ⊓ centralizer ({z} : Set M), ∀ q ∈ A, c * q * c⁻¹ ∈ A)
    (hAcent : centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) ≤ A)
    (hAcard : Nat.card (centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) :
      Subgroup M) = p)
    (hB : ∀ y ∈ P, orderOf y = p → RankOK p (R ⊓ centralizer ({y} : Set M) : Subgroup M)) :
    ∀ Ê : Subgroup (MulAut ↥P), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzC : z ∈ centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) :=
    ⟨Subgroup.mem_centralizer_iff.2 fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.1 (hAC hq),
      hzR, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hzA : z ∈ A := hAcent hzC
  have hzord : orderOf z = p := orderOf_eq_prime (hAexp z hzA) hz1
  have hzcard : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hZeq : centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) = zpowers z := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hzC) ?_
    rw [hAcard, hzcard]
  have hzc : ∀ q ∈ A, z * q = q * z := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hAC hq)).symm
  have hZ : ∀ x ∈ A, (∀ q ∈ A, x * q = q * x) → x ∈ zpowers z := by
    intro x hx hxc
    rw [← hZeq]
    exact ⟨Subgroup.mem_centralizer_iff.2 fun q hq => (hxc q hq).symm, h.le (hAP hx), hAC hx⟩
  have hCC : PFree p (R ⊓ centralizer ({z} : Set M) ⊓ centralizer (A : Set M) : Subgroup M) := by
    intro u hu hcop
    have huA : u ∈ A := hAcent ⟨hu.2, hu.1⟩
    have hdvd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one (hAexp u huA)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  refine noSig_planes_of_autModel_rank h hidx hp hp2 (Q := A) hA_sylow ?_ hB
  intro E hEA hEel hE2
  exact pfree_centralizer_plane_extra hp hA3 hAexp hzA hz1 hzc hZ hAn hCC hEA hEel hE2

theorem noSig_planes_of_record_extra_rank {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup M} (hQ3 : Nat.card Q = p ^ 3) (hQP : Q ≤ P)
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    {ι : Type*} {xs : ι → M}
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      RankOK p (R ⊓ centralizer ({xs i} : Set M) : Subgroup M))
    {A : Subgroup M} (hAP : A ≤ P) (hA3 : Nat.card A = p ^ 3) (hAexp : ∀ x ∈ A, x ^ p = 1)
    {z : M} (hzR : z ∈ R) (hz1 : z ≠ 1) (hAC : A ≤ centralizer ({z} : Set M))
    (hAn : ∀ c ∈ R ⊓ centralizer ({z} : Set M), ∀ q ∈ A, c * q * c⁻¹ ∈ A)
    (hAcent : centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) ≤ A)
    (hAcard : Nat.card (centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) :
      Subgroup M) = p) :
    ∀ Ê : Subgroup (MulAut ↥P), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA_sylow : ∃ S : Sylow p ↥P, (S : Subgroup ↥P) = A.subgroupOf P := by
    obtain ⟨S0, hS0⟩ := hSyl
    have hfac : p ^ 3 = p ^ (Nat.card P).factorization p := by
      have h1 := S0.card_eq_multiplicity
      rw [hS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ3] at h1
      exact h1
    have hAcard' : Nat.card (A.subgroupOf P) = p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hA3]
    exact ⟨Sylow.ofCard (A.subgroupOf P) (by rw [hAcard']; exact hfac), rfl⟩
  exact noSig_planes_of_extra h hidx hp hp2 hAP hA3 hA_sylow hAexp hzR hz1 hAC hAn hAcent hAcard
    (rankOK_of_lines hp h.le hSyl hlines hrep)

theorem noSig_planes_of_record_extra {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup M} (hQ3 : Nat.card Q = p ^ 3) (hQP : Q ≤ P)
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    {ι : Type*} {xs : ι → M}
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      PrimePowOK p (Nat.card (R ⊓ centralizer ({xs i} : Set M) : Subgroup M)))
    {A : Subgroup M} (hAP : A ≤ P) (hA3 : Nat.card A = p ^ 3) (hAexp : ∀ x ∈ A, x ^ p = 1)
    {z : M} (hzR : z ∈ R) (hz1 : z ≠ 1) (hAC : A ≤ centralizer ({z} : Set M))
    (hAn : ∀ c ∈ R ⊓ centralizer ({z} : Set M), ∀ q ∈ A, c * q * c⁻¹ ∈ A)
    (hAcent : centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) ≤ A)
    (hAcard : Nat.card (centralizer (A : Set M) ⊓ (R ⊓ centralizer ({z} : Set M)) :
      Subgroup M) = p) :
    ∀ Ê : Subgroup (MulAut ↥P), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê :=
  noSig_planes_of_record_extra_rank h hidx hp hp2 hQ3 hQP hSyl hlines
    (fun j => let ⟨i, hi, hok⟩ := hrep j; ⟨i, hi, rankOK_of_primePowOK hok⟩)
    hAP hA3 hAexp hzR hz1 hAC hAn hAcent hAcard

end CFSG.HardMathSupport.Dickson.I271
