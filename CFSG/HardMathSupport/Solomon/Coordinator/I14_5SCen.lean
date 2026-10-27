module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5STr
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i145s_central_le {A : Type*} [Group A] (Z : Subgroup A) [Z.Normal] (Q : Subgroup A) :
    (Subgroup.centralizer (Q : Set A)).map (QuotientGroup.mk' Z) ≤
      Subgroup.centralizer ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)) := by
  rintro _ ⟨c, hc, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 ?_
  rintro _ ⟨q, hq, rfl⟩
  have := Subgroup.mem_centralizer_iff.1 hc q hq
  show QuotientGroup.mk q * QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk q
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

theorem i145s_central_normal {A : Type*} [Group A] (Z : Subgroup A) [Z.Normal]
    (hZ : Z ≤ Subgroup.center A) (Q : Subgroup A) :
    (((Subgroup.centralizer (Q : Set A)).map (QuotientGroup.mk' Z)).subgroupOf
      (Subgroup.centralizer ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) :
        Set (A ⧸ Z)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (i145s_central_le Z Q)]
  intro h k hh hk
  obtain ⟨d, hd, rfl⟩ := hh
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨e * d * e⁻¹, ?_, by simp⟩
  refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = e⁻¹ * q * e * q⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ Z := by
    rw [hzdef, ← QuotientGroup.eq_one_iff]
    have h1 := Subgroup.mem_centralizer_iff.1 hk (QuotientGroup.mk q) ⟨q, hq, rfl⟩
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (↑e : A ⧸ Z)⁻¹ * ↑q * ↑e * (↑q)⁻¹ = (↑e)⁻¹ * (↑q * ↑e) * (↑q)⁻¹ := by group
      _ = (↑e)⁻¹ * (↑e * ↑q) * (↑q)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hzc : ∀ g : A, g * z = z * g := fun g => Subgroup.mem_center_iff.1 (hZ hz) g
  have hq' : e⁻¹ * q * e = z * q := by rw [hzdef]; group
  have hqd : q * d = d * q := Subgroup.mem_centralizer_iff.1 hd q hq
  have hzdq : z * (d * q) = d * (z * q) := by rw [← mul_assoc, ← hzc d, mul_assoc]
  calc q * (e * d * e⁻¹) = e * (e⁻¹ * q * e) * d * e⁻¹ := by group
    _ = e * (z * q) * d * e⁻¹ := by rw [hq']
    _ = e * (z * (q * d)) * e⁻¹ := by group
    _ = e * (z * (d * q)) * e⁻¹ := by rw [hqd]
    _ = e * (d * (z * q)) * e⁻¹ := by rw [hzdq]
    _ = e * d * (e⁻¹ * q * e) * e⁻¹ := by rw [hq']; group
    _ = e * d * e⁻¹ * q := by group

theorem i145s_central_bad {A : Type} [Group A] [Finite A] (Z Q : Subgroup A) [Z.Normal]
    (hZ : Z ≤ Subgroup.center A)
    (hbad : ⁅GLAPLayer 3 (Subgroup.centralizer ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) :
        Set (A ⧸ Z))), GLAPPrimeCoreOf 3 (Subgroup.centralizer
        ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)))⁆ = ⊥) :
    ⁅GLAPLayer 3 (Subgroup.centralizer (Q : Set A)),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A))⁆ ≤ Z := by
  have hc : ∀ y ∈ Subgroup.centralizer (Q : Set A) ⊓ (QuotientGroup.mk' Z).ker,
      ∀ x ∈ Subgroup.centralizer (Q : Set A), x * y = y * x := by
    intro y hy x _
    have hyZ : y ∈ Z := by
      have := hy.2
      rwa [QuotientGroup.ker_mk'] at this
    exact Subgroup.mem_center_iff.1 (hZ hyZ) x
  have h1 := i145s_map_bad_le Nat.prime_three (QuotientGroup.mk' Z) (i145s_central_le Z Q)
    (i145s_central_normal Z hZ Q)
    (fun J hJ => glaPComponent_map_central Nat.prime_three (QuotientGroup.mk' Z) hc hJ)
  rw [hbad, le_bot_iff] at h1
  have h2 := (Subgroup.map_eq_bot_iff _).1 h1
  rwa [QuotientGroup.ker_mk'] at h2

end CFSG.HardMathSupport.Solomon.Coordinator
