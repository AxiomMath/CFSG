module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_one_lt_card_inter {G : Type} [Group G] [Finite G] {a x z ρ : G}
    (hx : IsF5Type a x) (hzx : z ∈ Gx x) (hz2 : z ^ 2 = 1) (hzQ : z ∉ Qz x) (hρz : ρ ∈ Gx z)
    (hρx : ρ ∈ Gx x) (hρ5 : orderOf ρ = 5) (hD : Nat.card ↥(Qz z ⊓ Gx x) = 2 ^ 5) :
    1 < Nat.card ↥(Qz z ⊓ Qz x) := by
  let C := ↥(Gx x)
  let Q' : Subgroup C := CFSG.pCore 2 C
  let f : C →* Gbar x := QuotientGroup.mk' Q'
  let zc : C := ⟨z, hzx⟩
  let rc : C := ⟨ρ, hρx⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar hx
  let u : Gbar x := barOf x zc
  let v : Gbar x := barOf x rc
  have hzhat2 : zc ^ 2 = 1 := by
    apply Subtype.ext
    show z ^ 2 = (1 : G)
    exact hz2
  have hu2 : u ^ 2 = 1 := by
    change f zc ^ 2 = 1
    rw [← map_pow, hzhat2, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    exact hzQ ((barOf_eq_one_iff (z := x) zc).mp h1)
  have hρhat5 : orderOf rc = 5 := by
    rw [show rc = ⟨ρ, hρx⟩ from rfl, Subgroup.orderOf_mk, hρ5]
  have hv5 : orderOf v = 5 := by
    change orderOf (barOf x rc) = 5
    exact orderOf_barOf_five hρhat5
  have hρhat_comm : rc * zc = zc * rc := by
    apply Subtype.ext
    show ρ * z = z * ρ
    exact (mem_Gx.mp hρz).symm
  have hvcomm : v * u = u * v := by
    change f rc * f zc = f zc * f rc
    rw [← map_mul, ← map_mul, hρhat_comm]
  have hvmem : v ∈ Subgroup.centralizer ({u} : Set (Gbar x)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hvcomm
  let n := Nat.card ↥(Subgroup.centralizer ({u} : Set (Gbar x)))
  have h5dvd : 5 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set (Gbar x))) := by
    have h := orderOf_dvd_natCard
      (⟨v, hvmem⟩ : ↥(Subgroup.centralizer ({u} : Set (Gbar x))))
    rw [Subgroup.orderOf_mk, hv5] at h
    exact h
  have hn : n = 120 ∨ n = 240 := by
    rcases involution_cases_of_mulEquiv e hu2 hu1 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h] at h5dvd
      norm_num at h5dvd
  let P : Subgroup C := (Qz z ⊓ Gx x).comap (Gx x).subtype
  have hPcard : Nat.card ↥P = 2 ^ 5 := by
    have hP : P = (Qz z ⊓ Gx x).subgroupOf (Gx x) :=
      Subgroup.comap_subtype (Qz z ⊓ Gx x) (Gx x)
    rw [hP]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Qz z ⊓ Gx x ≤ Gx x)).toEquiv).trans hD
  have hmap_le : P.map f ≤ Subgroup.centralizer ({u} : Set (Gbar x)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨p, hpP, rfl⟩ := Subgroup.mem_map.mp hy
    have hpz : (p : G) ∈ Qz z := (Subgroup.mem_comap.mp hpP).1
    have hpGz : (p : G) ∈ Gx z :=
      Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Gx z)) hpz
    have hcomm : p * zc = zc * p := by
      apply Subtype.ext
      show (p : G) * z = z * (p : G)
      exact (mem_Gx.mp hpGz).symm
    change f p * f zc = f zc * f p
    rw [← map_mul, ← map_mul, hcomm]
  have hdiv : Nat.card ↥(P.map f) ∣ n := Subgroup.card_dvd_of_le hmap_le
  have hdiv32 : Nat.card ↥(P.map f) ∣ 32 := by
    have h := Subgroup.card_map_dvd (H := P) f
    rw [hPcard] at h
    norm_num at h ⊢
    exact h
  have hle16 : Nat.card ↥(P.map f) ≤ 16 := by
    rcases hn with hn | hn
    · rw [hn] at hdiv
      have hg : Nat.card ↥(P.map f) ∣ 8 := by
        have h := Nat.dvd_gcd hdiv hdiv32
        norm_num at h ⊢
        exact h
      exact (Nat.le_of_dvd (by norm_num) hg).trans (by norm_num)
    · rw [hn] at hdiv
      have hg : Nat.card ↥(P.map f) ∣ 16 := by
        have h := Nat.dvd_gcd hdiv hdiv32
        norm_num at h ⊢
        exact h
      exact Nat.le_of_dvd (by norm_num) hg
  have hrel : f.ker.relIndex P = Nat.card ↥(P.map f) := Subgroup.relIndex_ker P f
  have hmul : f.ker.relIndex P * Nat.card ↥(f.ker ⊓ P) = Nat.card ↥P :=
    Subgroup.relIndex_mul_card (H := f.ker) (K := P)
  have hk2 : 2 ≤ Nat.card ↥(f.ker ⊓ P) := by
    have hrle : f.ker.relIndex P ≤ 16 := by
      rw [hrel]
      exact hle16
    have hP32 : Nat.card ↥P = 32 := by
      rw [hPcard]
      norm_num
    rw [hP32] at hmul
    have hkpos : 0 < Nat.card ↥(f.ker ⊓ P) := Nat.card_pos
    by_contra h
    push Not at h
    have hk1 : Nat.card ↥(f.ker ⊓ P) = 1 := by omega
    rw [hk1, mul_one] at hmul
    omega
  have hfker : f.ker = Q' := QuotientGroup.ker_mk' (N := Q')
  have hcardle : Nat.card ↥(f.ker ⊓ P) ≤ Nat.card ↥(Qz z ⊓ Qz x) := by
    refine Nat.card_le_card_of_injective (f := fun c : ↥(f.ker ⊓ P) => ?_) ?_
    · refine ⟨(c : C), ?_⟩
      have hk : (c : C) ∈ f.ker := c.2.1
      have hPc : (c : C) ∈ P := c.2.2
      have hQx : (c : C) ∈ Q' := by
        rw [← hfker]
        exact hk
      have hQx' : ((c : C) : G) ∈ Qz x :=
        Subgroup.mem_map_of_mem (Gx x).subtype hQx
      have hQz : ((c : C) : G) ∈ Qz z := (Subgroup.mem_comap.mp hPc).1
      exact ⟨hQz, hQx'⟩
    · intro a b hab
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(Qz z ⊓ Qz x) => (z : G)) hab))
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
