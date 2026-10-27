module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
public import Certificates.Data.CFSGNative.Timmesfeld.PcFus

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcCover

open _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular

section Good

variable {G : Type*} [Group G]

theorem centralizer_pow_eq_of_coprime' {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {k : ℕ}
    (hk : Nat.Coprime k p) :
    Subgroup.centralizer ({x ^ k} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hp.one_lt
  have hxk : (x ^ k) ^ k' = x := by
    rw [← pow_mul]
    have e : k * k' = p * (k * k' / p) + 1 := by
      have := Nat.div_add_mod (k * k') p
      omega
    rw [e, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  ext c
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : c * (x ^ k) ^ k' = (x ^ k) ^ k' * c :=
      (Commute.pow_right (show Commute c (x ^ k) from h) k').eq
    rwa [hxk] at h2
  · intro h
    exact (Commute.pow_right (show Commute c x from h) k).eq

end Good

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcCover
