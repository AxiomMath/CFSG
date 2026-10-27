module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma oTwoRes_top_normal {G : Type} [Group G] :
    (oTwoRes (⊤ : Subgroup G)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [oTwoRes] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      refine Subgroup.subset_closure ⟨trivial, ?_⟩
      have hconj : orderOf (g * y * g⁻¹) = orderOf y := by
        rw [← MulAut.conj_apply g y]
        exact (MulAut.conj g).orderOf_eq y
      rw [hconj]
      exact hy.2
  | one => simpa using Subgroup.one_mem (Subgroup.closure _)
  | mul y z _ _ ihy ihz => simpa only [conj_mul] using Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy => simpa only [conj_inv] using Subgroup.inv_mem _ ihy

theorem oTwoRes_top_eq_top {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : oTwoRes (⊤ : Subgroup G) = ⊤ := by
  haveI : Nontrivial G := hs.toNontrivial
  haveI hnorm : (oTwoRes (⊤ : Subgroup G)).Normal := oTwoRes_top_normal
  rcases hs.eq_bot_or_eq_top_of_normal (oTwoRes (⊤ : Subgroup G)) with hM | hM
  · exfalso
    have hodd : ∀ x : G, Odd (orderOf x) → x = 1 := by
      intro x hx
      have hxmem : x ∈ oTwoRes (⊤ : Subgroup G) := Subgroup.subset_closure ⟨trivial, hx⟩
      rw [hM] at hxmem
      simpa using hxmem
    have hpgroup : IsPGroup 2 G := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro x
      obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨k, ?_⟩
      have hxpow : x ^ 2 ^ k = 1 := by
        apply hodd
        refine hm.of_dvd_nat ?_
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← hxm, pow_orderOf_eq_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hxpow
    have hcenter : Subgroup.center G = ⊤ := by
      rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
      · exact absurd hc (IsPGroup.bot_lt_center (p := 2) hpgroup).ne'
      · exact hc
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((Subgroup.mem_center_iff.mp (by rw [hcenter]; trivial) b).symm)
  · exact hM

theorem exists_noncomm_of_sec3Setting {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (h : Sec3Setting G t L) : ∃ a b : G, a * b ≠ b * a :=
  sec4_nonabelian h

theorem mem_oTwoRes_top_of_sec3Setting {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (h : Sec3Setting G t L) (x : G) : x ∈ oTwoRes (⊤ : Subgroup G) := by
  rw [oTwoRes_top_eq_top h.simple (exists_noncomm_of_sec3Setting h)]
  exact Subgroup.mem_top x

end CFSG.OddStandard.SmallF3.Omega
