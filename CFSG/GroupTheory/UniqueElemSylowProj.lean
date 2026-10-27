module

public import CFSG.GroupTheory.UniqueElemSylowTransfer
public import CFSG.Open.StatedDefs

public section

namespace CFSG.GroupTheory

theorem not_dvd_card_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] {p d : ℕ}
    [Fact p.Prime] (hd : ¬ p ∣ d) (h : ∀ g : G, g ^ d = 1) : ¬ p ∣ Nat.card G := by
  intro hpd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
  exact hd (hg ▸ orderOf_dvd_of_pow_eq_one (h g))

theorem UniqueElemSylow.statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {p k d : ℕ} [Fact p.Prime] {H : Subgroup (GL ι K)} (hd : ¬ p ∣ d)
    (hsc : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ H → c ^ d = 1)
    (h : UniqueElemSylow p k H) : UniqueElemSylow p k (CFSG.Open.StatedProj H) := by
  let N : Subgroup H := (CFSG.Open.StatedScalars ι K).subgroupOf H
  have hN : ¬ p ∣ Nat.card N := by
    refine not_dvd_card_of_forall_pow_eq_one (G := N) (p := p) (d := d) hd (fun x => ?_)
    have hxmem : ((x : N) : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι).range := by
      simpa only [CFSG.Open.StatedScalars] using
        (Subgroup.mem_subgroupOf (H := CFSG.Open.StatedScalars ι K) (K := H)
          (h := x)).mp x.2
    obtain ⟨c, hc⟩ :=
      (MonoidHom.mem_range (f := Matrix.GeneralLinearGroup.scalar ι)).mp hxmem
    have hmem : Matrix.GeneralLinearGroup.scalar ι c ∈ H := by
      rw [hc]; exact (x : H).2
    have hcd : c ^ d = 1 := hsc c hmem
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    calc ((x : H) : GL ι K) ^ d
        = (Matrix.GeneralLinearGroup.scalar ι c) ^ d := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar ι (c ^ d) :=
            (map_pow (Matrix.GeneralLinearGroup.scalar ι) c d).symm
      _ = Matrix.GeneralLinearGroup.scalar ι 1 := by rw [hcd]
      _ = 1 := map_one (Matrix.GeneralLinearGroup.scalar ι)
  haveI : N.Normal := inferInstance
  exact (UniqueElemSylow.quotient_iff (p := p) (k := k) N hN).2 h

end CFSG.GroupTheory
