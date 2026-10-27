module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.TwoB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Symm
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Five
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Lagrange
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_inter (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : GzClassFacts a z) (x : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1)
    (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) :
    z ∉ Qz (x : G) ∧ Nat.card ↥(Qz z ⊓ Qz (x : G)) = 2 ^ 4 ∧
      ∀ t ∈ Qz z ⊓ Qz (x : G), t ^ 2 = 1 := by
  have hz2 : z ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at hpow
  have hzQ : z ∈ Qz z := self_mem_Qz hz2
  obtain ⟨hxB, hxQ⟩ := gzNo_twoB hC h hF3 hOrb.self hCls x hx2 hsh
  have hzQx : z ∉ Qz (x : G) := by
    intro hzx
    exact hxQ (gzNo_mem_Qz_symm h hOrb hxB (IsConj.refl z) hzx)
  obtain ⟨hD, ρ, hρ5, hρx, hρQ, -⟩ := gzNo_five hC h hOrb.self hCls x hx2 hsh
  have hx' : IsF5Type a (x : G) := isF5Type_of_isConj h (IsConj.refl a) hxB
  have hzx' : z ∈ Gx (x : G) := mem_Gx.mpr (mem_Gx.mp x.2).symm
  have hρz' : (ρ : G) ∈ Gx z := ρ.2
  have hρx' : (ρ : G) ∈ Gx (x : G) := by
    apply mem_Gx.mpr
    exact (congrArg Subtype.val hρx).symm
  have hρ5' : orderOf (ρ : G) = 5 := by
    rw [Subgroup.orderOf_coe, hρ5]
  have h1 : 1 < Nat.card ↥(Qz z ⊓ Qz (x : G)) :=
    gzNo_one_lt_card_inter hx' hzx' hz2 hzQx hρz' hρx' hρ5' hD
  let S : Set G := ↑(Qz z ⊓ Qz (x : G))
  have hS_inv : ∀ s ∈ S, (ρ : G) * s * (ρ : G)⁻¹ ∈ S := by
    intro s hs
    have hs' : s ∈ Qz z ⊓ Qz (x : G) := hs
    exact ⟨gzNo_conj_mem_Qz hρz' (Subgroup.mem_inf.mp hs').1,
      gzNo_conj_mem_Qz hρx' (Subgroup.mem_inf.mp hs').2⟩
  have hfix : Nat.card {s : G // s ∈ S ∧ s * (ρ : G) = (ρ : G) * s} = 1 := by
    have hsub : Subsingleton {s : G // s ∈ S ∧ s * (ρ : G) = (ρ : G) * s} := by
      refine ⟨fun s t => ?_⟩
      have hs1 : (s : G) = 1 := by
        have hsS : (s : G) ∈ Qz z ⊓ Qz (x : G) := s.2.1
        rcases hρQ (s : G) (Subgroup.mem_inf.mp hsS).1 s.2.2 with h | h
        · exact h
        · exfalso
          have hsx : z ∈ Qz (x : G) :=
            Eq.mp (congrArg (fun a : G => a ∈ Qz (x : G)) h)
              (Subgroup.mem_inf.mp hsS).2
          exact hzQx hsx
      have ht1 : (t : G) = 1 := by
        have htS : (t : G) ∈ Qz z ⊓ Qz (x : G) := t.2.1
        rcases hρQ (t : G) (Subgroup.mem_inf.mp htS).1 t.2.2 with h | h
        · exact h
        · exfalso
          have htx : z ∈ Qz (x : G) :=
            Eq.mp (congrArg (fun a : G => a ∈ Qz (x : G)) h)
              (Subgroup.mem_inf.mp htS).2
          exact hzQx htx
      exact Subtype.ext (hs1.trans ht1.symm)
    let a' : {s : G // s ∈ S ∧ s * (ρ : G) = (ρ : G) * s} :=
      ⟨1, show (1 : G) ∈ S from Subgroup.one_mem _, by simp⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨a'⟩⟩
  have hcong : Nat.card S ≡ 1 [MOD 5] := by
    have hcm := gzNo_card_modEq_five hρ5' S hS_inv
    rwa [hfix] at hcm
  have hS_le : Qz z ⊓ Qz (x : G) ≤ Qz z ⊓ Gx (x : G) :=
    le_inf inf_le_left (le_trans inf_le_right (gzNo_Qz_le (x : G)))
  have hS_dvd : Nat.card ↥(Qz z ⊓ Qz (x : G)) ∣ 2 ^ 5 := by
    have h := Subgroup.card_dvd_of_le hS_le
    rwa [hD] at h
  have hS_ne : Nat.card ↥(Qz z ⊓ Qz (x : G)) ≠ 2 ^ 5 := by
    intro hcard
    have heq : Qz z ⊓ Qz (x : G) = Qz z ⊓ Gx (x : G) :=
      Subgroup.eq_of_le_of_card_ge hS_le (by rw [hD, hcard])
    have hzK : z ∈ Qz z ⊓ Gx (x : G) := ⟨hzQ, hzx'⟩
    have hzS : z ∈ Qz z ⊓ Qz (x : G) := heq ▸ hzK
    exact hzQx (Subgroup.mem_inf.mp hzS).2
  obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hS_dvd
  have hmod : 2 ^ i % 5 = 1 := by
    have hScoe : Nat.card S = Nat.card ↥(Qz z ⊓ Qz (x : G)) := rfl
    have h : Nat.card S ≡ 1 [MOD 5] := hcong
    rw [hScoe, hi_eq] at h
    exact h
  have hS_eq : Nat.card ↥(Qz z ⊓ Qz (x : G)) = 2 ^ 4 := by
    rw [hi_eq]
    interval_cases i
    · exfalso; rw [hi_eq] at h1; norm_num at h1
    · exfalso; exact absurd hmod (by norm_num)
    · exfalso; exact absurd hmod (by norm_num)
    · exfalso; exact absurd hmod (by norm_num)
    · rfl
    · exfalso; exact absurd hi_eq hS_ne
  refine ⟨hzQx, hS_eq, ?_⟩
  intro t ht
  have htQz : t ∈ Qz z := (Subgroup.mem_inf.mp ht).1
  have htQx : t ∈ Qz (x : G) := (Subgroup.mem_inf.mp ht).2
  have hsq : t ^ 2 ∈ Subgroup.zpowers z := gzNo_sq_mem_zpowers h htQz
  rcases (gzNo_mem_zpowers_iff h.orderOf_z).mp hsq with hsq1 | hsq1
  · exact hsq1
  · exfalso
    have ht2 : t ^ 2 ∈ Qz (x : G) := Subgroup.pow_mem (Qz (x : G)) htQx 2
    exact hzQx (Eq.mp (congrArg (fun a : G => a ∈ Qz (x : G)) hsq1) ht2)

end CFSG.EvenSporadicStandard.HNRecog.Section3
