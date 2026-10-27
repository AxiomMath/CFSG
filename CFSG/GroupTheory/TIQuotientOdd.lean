module

public import CFSG.GroupTheory.InvariantSubgroup

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.CGT.Timmesfeld75

variable {Y : Type*} [Group Y] [Finite Y]

theorem isTI_map_mk'_of_odd {T Z : Subgroup Y} [Z.Normal]
    (hT : IsPGroup 2 T) (hTI : IsTI T) (hZodd : Odd (Nat.card Z))
    (hTZ : T ≤ centralizer (Z : Set Y)) :
    IsTI (T.map (QuotientGroup.mk' Z)) := by
  classical
  intro gbar
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective gbar
  rw [← hg]
  change T.map (QuotientGroup.mk' Z) ⊓
      conjSubgroup (QuotientGroup.mk' Z g) (T.map (QuotientGroup.mk' Z)) = ⊥ ∨
    T.map (QuotientGroup.mk' Z) ⊓
      conjSubgroup (QuotientGroup.mk' Z g) (T.map (QuotientGroup.mk' Z)) =
        T.map (QuotientGroup.mk' Z)
  have hmap : conjSubgroup (QuotientGroup.mk' Z g) (T.map (QuotientGroup.mk' Z)) =
      (conjSubgroup g T).map (QuotientGroup.mk' Z) :=
    map_conjSubgroup (QuotientGroup.mk' Z) T g
  rw [hmap]
  have hinf : T.map (QuotientGroup.mk' Z) ⊓ (conjSubgroup g T).map (QuotientGroup.mk' Z) =
      (T ⊓ conjSubgroup g T).map (QuotientGroup.mk' Z) := by
    refine le_antisymm ?_ (le_inf (Subgroup.map_mono inf_le_left)
      (Subgroup.map_mono inf_le_right))
    rintro x ⟨hxT, hxS⟩
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hxT
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hxS
    have hz : t⁻¹ * s ∈ Z := QuotientGroup.eq.mp (htx.trans hsx.symm)
    have htz : t * (t⁻¹ * s) = (t⁻¹ * s) * t :=
      (Subgroup.mem_centralizer_iff.mp (hTZ ht) _ hz).symm
    have hs_eq : s = t * (t⁻¹ * s) := by group
    have htpow : ∃ k : ℕ, orderOf t = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨t, ht⟩
      exact ⟨k, (Subgroup.orderOf_coe ⟨t, ht⟩).trans hk⟩
    have hspow : ∃ m : ℕ, orderOf s = 2 ^ m := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (hT.map (MulAut.conj g).toMonoidHom))
        ⟨s, hs⟩
      exact ⟨m, (Subgroup.orderOf_coe ⟨s, hs⟩).trans hm⟩
    obtain ⟨k, hk⟩ := htpow
    obtain ⟨m, hm⟩ := hspow
    have hzodd : Odd (orderOf (t⁻¹ * s)) :=
      Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hz)
    have hcop : Nat.Coprime (orderOf t) (orderOf (t⁻¹ * s)) := by
      rw [hk]
      exact (Nat.coprime_two_left.mpr hzodd).pow_left k
    have horder : orderOf s = orderOf t * orderOf (t⁻¹ * s) := by
      calc orderOf s = orderOf (t * (t⁻¹ * s)) := congrArg orderOf hs_eq
        _ = orderOf t * orderOf (t⁻¹ * s) :=
          Commute.orderOf_mul_eq_mul_orderOf_of_coprime htz hcop
    have hdvd0 : orderOf (t⁻¹ * s) ∣ orderOf s := by
      rw [horder]
      exact dvd_mul_left _ _
    have hdvd : orderOf (t⁻¹ * s) ∣ 2 ^ m := by
      rwa [hm] at hdvd0
    have hcopz : Nat.Coprime (orderOf (t⁻¹ * s)) (2 ^ m) :=
      hzodd.coprime_two_right.pow_right m
    have hzone : t⁻¹ * s = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopz dvd_rfl hdvd)
    have hts : t = s := by rw [hs_eq, hzone, mul_one]
    exact Subgroup.mem_map.mpr ⟨t, ⟨ht, by rwa [hts]⟩, htx⟩
  rw [hinf]
  rcases hTI g with hbot | htop
  · rw [hbot, Subgroup.map_bot]
    exact Or.inl rfl
  · rw [htop]
    exact Or.inr rfl

theorem le_sup_comap_of_map_le {X Q : Type*} [Group X] [Group Q] (π : X →* Q)
    {K : Subgroup X} {A B : Subgroup Q} (hA : A ≤ K.map π) (hB : B ≤ K.map π)
    (h : K.map π ≤ A ⊔ B) :
    K ≤ (A.comap π ⊓ K) ⊔ (B.comap π ⊓ K) ⊔ (π.ker ⊓ K) := by
  let H : Subgroup X := (A.comap π ⊓ K) ⊔ (B.comap π ⊓ K) ⊔ (π.ker ⊓ K)
  have hHK : H ≤ K := by
    refine sup_le (sup_le (inf_le_right) (inf_le_right)) inf_le_right
  have hAmap : (A.comap π ⊓ K).map π = A := by
    refine le_antisymm ?_ ?_
    · rintro q ⟨x, ⟨hxA, -⟩, rfl⟩
      exact hxA
    · intro a ha
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (hA ha)
      exact Subgroup.mem_map.mpr ⟨k, ⟨Subgroup.mem_comap.mpr (by rwa [hkπ]), hk⟩, hkπ⟩
  have hBmap : (B.comap π ⊓ K).map π = B := by
    refine le_antisymm ?_ ?_
    · rintro q ⟨x, ⟨hxB, -⟩, rfl⟩
      exact hxB
    · intro b hb
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (hB hb)
      exact Subgroup.mem_map.mpr ⟨k, ⟨Subgroup.mem_comap.mpr (by rwa [hkπ]), hk⟩, hkπ⟩
  have hkermap : (π.ker ⊓ K).map π = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hx.1)
  have hHmap : H.map π = A ⊔ B := by
    dsimp only [H]
    rw [Subgroup.map_sup, Subgroup.map_sup, hAmap, hBmap, hkermap, sup_bot_eq]
  intro k hk
  have hkmap : π k ∈ H.map π := by
    rw [hHmap]
    exact h (Subgroup.mem_map_of_mem π hk)
  obtain ⟨h, hh, hhk⟩ := Subgroup.mem_map.mp hkmap
  have hkerK : k * h⁻¹ ∈ π.ker ⊓ K := by
    refine ⟨?_, K.mul_mem hk (K.inv_mem (hHK hh))⟩
    change π (k * h⁻¹) = 1
    rw [map_mul, map_inv, hhk, mul_inv_cancel]
  have hk_eq : k = (k * h⁻¹) * h := by group
  rw [hk_eq]
  exact H.mul_mem ((le_sup_right : π.ker ⊓ K ≤ H) hkerK) hh

end CFSG.GroupTheory

end
