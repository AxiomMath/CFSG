module

import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Assembly

open Subgroup

variable {H : Type} [Group H] [Finite H] {p : ℕ} (O : Subgroup H) [O.Normal]

private theorem isQuasisimple_map_mk'_of_not_le {H' : Type} [Group H'] (O' : Subgroup H')
    [O'.Normal] {K : Subgroup H'} (hK : IsQuasisimple K) (hKO : ¬ K ≤ O') :
    IsQuasisimple (K.map (QuotientGroup.mk' O')) := by
  have hq : CFSG.Open.IsQuasisimple ↥K := ⟨hK.1, hK.2⟩
  let f : ↥K →* H' ⧸ O' := (QuotientGroup.mk' O').domRestrict K
  have hker : f.ker ≠ ⊤ := by
    intro htop
    apply hKO
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) ∈ f.ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h1
    have h2 : (k : H' ⧸ O') = 1 := h1
    exact (QuotientGroup.eq_one_iff k).mp h2
  have hres :=
    CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq f hker
  have hrange : f.range = K.map (QuotientGroup.mk' O') := by
    rw [MonoidHom.domRestrict_range]
  rw [hrange] at hres
  exact hres

theorem bar_centralizer_eq (hp : p.Prime) (hO : ¬ p ∣ Nat.card O) {x : H} (hx : orderOf x = p) :
    centralizer ({QuotientGroup.mk' O x} : Set (H ⧸ O)) =
      (centralizer ({x} : Set H)).map (QuotientGroup.mk' O) := by
  have hcop : Nat.Coprime p (Nat.card O) := (hp.coprime_iff_not_dvd).mpr hO
  have hxpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq (H := H) hp
    (W := (⊤ : Subgroup H)) (N := O) le_top hcop hxpow
  rw [top_inf_eq, Subgroup.map_top_of_surjective (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O), top_inf_eq] at h
  exact h.symm

theorem bar_isComponentOf (hp : p.Prime) (hO : ¬ p ∣ Nat.card O) {x : H} (hx : orderOf x = p)
    {K : Subgroup H} (hK : IsComponentOf K (centralizer ({x} : Set H))) (hKO : ¬ K ≤ O) :
    K ⊓ O ≤ centralizer (K : Set H) ∧
      IsComponentOf (K.map (QuotientGroup.mk' O))
        (centralizer ({QuotientGroup.mk' O x} : Set (H ⧸ O))) := by
  constructor
  ·
    intro z hz
    have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).1
    haveI : ((K ⊓ O).subgroupOf K).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact Subgroup.normal_subgroupOf
    have hZproper : (K ⊓ O).subgroupOf K ≠ ⊤ := by
      intro htop
      apply hKO
      intro k hk
      have hmem : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ O).subgroupOf K := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    have hzc : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K :=
      CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hK.2.2
        ((K ⊓ O).subgroupOf K) hZproper (Subgroup.mem_subgroupOf.mpr hz)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    simpa using congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc) (⟨g, hg⟩ : ↥K))
  · refine ⟨?_, ?_, ?_⟩
    · rw [bar_centralizer_eq (O := O) hp hO hx]
      exact Subgroup.map_mono hK.1
    · have h := hK.2.1.map (QuotientGroup.mk' O)
      rw [← bar_centralizer_eq (O := O) hp hO hx] at h
      exact h
    · exact isQuasisimple_map_mk'_of_not_le O hK.2.2 hKO

end CFSG.Assembly

end
