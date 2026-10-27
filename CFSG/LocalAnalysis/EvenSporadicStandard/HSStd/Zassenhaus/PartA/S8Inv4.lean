module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Gamma

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Cat

variable {G : Type} [Group G]

theorem catalog_quot_center (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (K : Subgroup G)
    (hK : K ≠ ⊤) (hq : CFSG.IsQuasisimple ↥K) : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) := by
  set L : Subgroup G := (center ↥K).map K.subtype with hL
  have hLK : L.subgroupOf K = center ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hLle : L ≤ K := Subgroup.map_subtype_le _
  haveI : (L.subgroupOf K).Normal := by rw [hLK]; infer_instance
  let e : ↥K ⧸ center ↥K ≃* ↥K ⧸ L.subgroupOf K := QuotientGroup.quotientMulEquivOfEq hLK.symm
  have hs : IsSimpleGroup (↥K ⧸ L.subgroupOf K) := (MulEquiv.isSimpleGroup_congr e).1 hq.2.1
  have hna : ∃ a b : ↥K ⧸ L.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hq.2.2
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv e (hKP K L hK hLle hs hna)

end Cat

section Sigma

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem inv_mem_normalizer : tG hb a.toPA6.toPA5 ∈ normalizer (K : Set ↥(Cen a.ub)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : tG hb a.toPA6.toPA5 * h * (tG hb a.toPA6.toPA5)⁻¹ ∈ cj (tG hb a.toPA6.toPA5) K :=
      ⟨h, hh, rfl⟩
    rwa [hcj] at this
  · intro hh
    have : h ∈ cj (tG hb a.toPA6.toPA5) K := (mem_cj (tG_mul_tG hb a.toPA6.toPA5)).2 hh
    rwa [hcj] at this

@[expose] noncomputable def sigmaK : MulAut ↥K :=
  conjAutOf K (inv_mem_normalizer hb a hK hcj hall)

theorem sigmaK_apply (k : ↥K) :
    ((sigmaK hb a hK hcj hall k : ↥K) : ↥(Cen a.ub)) =
      tG hb a.toPA6.toPA5 * k * (tG hb a.toPA6.toPA5)⁻¹ := rfl

@[expose] noncomputable def tauHat : MulAut (↥K ⧸ center ↥K) :=
  QuotientGroup.congr (center ↥K) (center ↥K) (sigmaK hb a hK hcj hall)
    (Subgroup.map_center_eq (sigmaK hb a hK hcj hall))

theorem tauHat_mk (k : ↥K) :
    tauHat hb a hK hcj hall (QuotientGroup.mk k) = QuotientGroup.mk (sigmaK hb a hK hcj hall k) :=
  rfl

theorem tauHat_sq : tauHat hb a hK hcj hall * tauHat hb a hK hcj hall = 1 := by
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  show tauHat hb a hK hcj hall (tauHat hb a hK hcj hall (QuotientGroup.mk k)) = QuotientGroup.mk k
  rw [tauHat_mk, tauHat_mk]
  congr 1
  apply Subtype.ext
  rw [sigmaK_apply, sigmaK_apply]
  have htt := tG_mul_tG hb a.toPA6.toPA5
  have hti : (tG hb a.toPA6.toPA5)⁻¹ = tG hb a.toPA6.toPA5 := inv_eq_of_mul_eq_one_right htt
  rw [hti]
  calc tG hb a.toPA6.toPA5 * (tG hb a.toPA6.toPA5 * (k : ↥(Cen a.ub)) * tG hb a.toPA6.toPA5) *
      tG hb a.toPA6.toPA5 = (tG hb a.toPA6.toPA5 * tG hb a.toPA6.toPA5) * (k : ↥(Cen a.ub)) *
        (tG hb a.toPA6.toPA5 * tG hb a.toPA6.toPA5) := by group
    _ = k := by rw [htt]; group

end Sigma

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
