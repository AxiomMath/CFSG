module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem psimple_equiv_center_quot {G : Type} [Group G] (p : ℕ) (L : Subgroup G)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hcat : catalogIs (PSimple p L) S9.isD4two) :
    catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isD4two := by
  let π : ↥L →* PQuot p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L)
  let W : Subgroup ↥L := (Subgroup.center (PQuot p L)).comap π
  have hWn : W.Normal := Subgroup.Normal.comap inferInstance π
  have hZW : Subgroup.center ↥L ≤ W := by
    intro z hz
    show π z ∈ Subgroup.center (PQuot p L)
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) q
    have hzx : z * x = x * z := (Subgroup.mem_center_iff.1 hz x).symm
    show π x * π z = π z * π x
    rw [← map_mul, ← map_mul, hzx]
  have hWb : (W.map (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
    Subgroup.Normal.map hWn _ (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map (QuotientGroup.mk' (Subgroup.center ↥L))) with hb | ht
  ·
    have hWeq : Subgroup.center ↥L = W := by
      have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Subgroup.center ↥L)) (H := W)
        (by rw [QuotientGroup.ker_mk']; exact hZW)
      rw [hb, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h1
      exact h1
    let f : ↥L →* PSimple p L := (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp π
    have hfs : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hker : f.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker, hWeq]
      exact QuotientGroup.eq_one_iff (π x)
    let e : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans (QuotientGroup.quotientKerEquivOfSurjective f hfs)
    obtain ⟨i, hi, ⟨e'⟩⟩ := hcat
    exact ⟨i, hi, ⟨e.trans e'⟩⟩
  ·
    exfalso
    have hWtop : W = ⊤ := by
      have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Subgroup.center ↥L)) (H := W)
        (by rw [QuotientGroup.ker_mk']; exact hZW)
      rw [ht, Subgroup.comap_top] at h1
      exact h1.symm
    have hZQ : Subgroup.center (PQuot p L) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) q
      have hx : x ∈ W := by rw [hWtop]; exact Subgroup.mem_top x
      exact hx
    have hsub : Subsingleton (PSimple p L) := by
      constructor
      intro a b
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, hZQ]
      exact Subgroup.mem_top _
    have h1 : Nat.card (PSimple p L) = 1 := Nat.card_of_subsingleton (1 : PSimple p L)
    have h2 := card_o8p2 hcat
    rw [h1] at h2
    norm_num at h2

end CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4
