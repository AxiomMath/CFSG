module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5a1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888C41
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GL1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888EA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888CN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma s888l5b2_kfam_zero : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]

private lemma s888l5b2_kfam_one : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]

theorem relIndex_inf_C6_le_two (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a)
    (h37 : Asc82Lemma37) (hF3 : Asc82FactOm6CentD) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer ({t} : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U) :
    (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)).relIndex
      (Sec5C6 L K₁ K₂ ⊓ U) ≤ 2 := by
  classical
  have hq := sec5b517_quad h514 c
  have hpair01 : twoCoreIn (K₁ ⊔ K₂) = Sec5B517Q8.pair hq 0 1 := by
    have h := Sec5B517Q8.twoCoreIn_sup_eq_pair (K := Kfam5 K₁ K₂ h) hq (i := 0) (j := 1)
      (by decide)
    rwa [s888l5b2_kfam_zero, s888l5b2_kfam_one] at h
  have hP2le : twoCoreIn (K₁ ⊔ K₂) ≤ K₁ ⊔ K₂ := by
    rw [hpair01]
    exact inf_le_right
  have hKsupL : K₁ ⊔ K₂ ≤ L :=
    sup_le (c.pocket₁.2.1.trans inf_le_left) (c.pocket₂.2.1.trans inf_le_left)
  refine relIndex_le_two_of_cyclic_sylow
    (C := centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h))
    (Y := normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer (L : Set G))
    (Y₀ := centralizer (L : Set G))
    (Z := Sec5C6 L K₁ K₂ ⊓ U) inf_le_right
    (h52a G t L c.toSec5Setting) ?_ ?_ (hab.mono inf_le_right)
  · intro y hy x hx
    exact centralizerMod_conj_mem h514 c hy.1 hx
  · intro u hu
    have hu6 : u ∈ Sec5C6 L K₁ K₂ := hu.1
    have huU : u ∈ U := hu.2
    have hcomm : ∀ a ∈ twoCoreIn (K₁ ⊔ K₂),
        ∀ b ∈ normalizer (L : Set G) ⊓
          centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G), a * b = b * a := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp hb.2 a (hP2le ha)
    obtain ⟨p, hp, ν, hν, hu_eq⟩ :=
      sec5b_mem_sup_of_comm (K₃ := twoCoreIn (K₁ ⊔ K₂))
        (K₄ := normalizer (L : Set G) ⊓
          centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) hcomm hu6
    have hp_pair : p ∈ Sec5B517Q8.pair hq 0 1 := hpair01 ▸ hp
    have hpQ : p ∈ Qsub K₁ K₂ h := by
      rw [sec5b517_Qsub_eq, hq.core_eq]
      exact hp_pair.1
    have hp_sup : p ∈ K₁ ⊔ K₂ := by
      have h := hp_pair.2
      rwa [s888l5b2_kfam_zero, s888l5b2_kfam_one] at h
    have hpL : p ∈ L := hKsupL hp_sup
    have hν_eq : ν = p⁻¹ * u := by rw [hu_eq]; group
    have hνt : ν ∈ centralizer ({t} : Set G) := by
      rw [hν_eq]
      exact mul_mem (inv_mem (c.L_le_centralizer hpL)) (hU huU).2
    have hνP : ν ∈ centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) :=
      Subgroup.centralizer_le hP2le hν.2
    obtain ⟨c₀, _hc₀t, hc₀Q, _hc₀K, hyL⟩ := c41 h514 h52a h37 hF3 c hνt hνP
    have hxQ : p * c₀ ∈ Qsub K₁ K₂ h := mul_mem hpQ hc₀Q
    have hu_x : u = (ν * c₀⁻¹) * (p * c₀) := by
      rw [hu_eq]
      have hpy : p * (ν * c₀⁻¹) = (ν * c₀⁻¹) * p :=
        Subgroup.mem_centralizer_iff.mp hyL p hpL
      calc p * ν = p * (ν * c₀⁻¹ * c₀) := by group
        _ = (p * (ν * c₀⁻¹)) * c₀ := by group
        _ = ((ν * c₀⁻¹) * p) * c₀ := by rw [hpy]
        _ = (ν * c₀⁻¹) * (p * c₀) := by group
    refine ⟨ν * c₀⁻¹, ⟨?_, hyL⟩, p * c₀, qsub_le_centralizerMod h514 c hxQ, hu_x⟩
    have hxu : ν * c₀⁻¹ = u * (p * c₀)⁻¹ := by rw [hu_x]; group
    rw [hxu]
    have hxN : p * c₀ ∈ normalizer (Qsub K₁ K₂ h : Set G) := Subgroup.le_normalizer hxQ
    exact (normalizer (Qsub K₁ K₂ h : Set G)).mul_mem (hU huU).1
      ((normalizer (Qsub K₁ K₂ h : Set G)).inv_mem hxN)

end CFSG.OddStandard.SmallF3.Omega
