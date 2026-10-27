module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma conj_mem_centralizer_of_mem_normalizer {X : Subgroup G} {k m : G}
    (hk : k ∈ normalizer (X : Set G)) (hm : m ∈ centralizer (X : Set G)) :
    k * m * k⁻¹ ∈ centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hm ⊢
  intro f hf
  have hkf : k⁻¹ * f * k ∈ X := (Subgroup.mem_normalizer_iff''.mp hk f).mp hf
  calc f * (k * m * k⁻¹) = k * ((k⁻¹ * f * k) * m) * k⁻¹ := by group
    _ = k * (m * (k⁻¹ * f * k)) * k⁻¹ := by rw [hm (k⁻¹ * f * k) hkf]
    _ = (k * m * k⁻¹) * f := by group

private lemma conj_mem_cen_of_mem_normIn {s : Setting3 G L} {k : G}
    (hk : k ∈ normIn L s.fr.B) {v : G} (hv : v ∈ cen s.fr.B) :
    k * v * k⁻¹ ∈ cen s.fr.B :=
  Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hk.2 v).mp (Subgroup.mem_inf.mp hv).1,
      conj_mem_centralizer_of_mem_normalizer hk.2 (Subgroup.mem_inf.mp hv).2⟩

private lemma conj_mem_centIn_of_pointwise {A X : Subgroup G} {k : G}
    (hA : ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hkX : k ∈ normalizer (X : Set G))
    {m : G} (hm : m ∈ centIn A X) : k * m * k⁻¹ ∈ centIn A X :=
  Subgroup.mem_inf.mpr
    ⟨hA m (Subgroup.mem_inf.mp hm).1,
      conj_mem_centralizer_of_mem_normalizer hkX (Subgroup.mem_inf.mp hm).2⟩

theorem y54_V_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ v ∈ cen s.fr.B, v ^ 2 = 1 := by
  intro v hv
  have h := (f3_V_isE2 hH).1.2 (⟨v, hv⟩ : ↥(cen s.fr.B)) (Subgroup.mem_top _)
  simpa using Subtype.ext_iff.mp h

theorem y54_V_card {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(cen s.fr.B) = 4 := by
  have h := (f3_V_isE2 hH).2
  norm_num at h
  exact h

theorem y54_kappa (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∃ κ : G, κ ∈ normIn L c.s.fr.F ∧ κ ^ 3 = 1 ∧
      (∀ v ∈ cen c.s.fr.B, κ * v * κ⁻¹ ∈ cen c.s.fr.B) ∧
      (∀ v ∈ cen c.s.fr.B, κ * v * κ⁻¹ = v → v = 1) ∧
      (∀ k ∈ centIn (M2 c.s) c.s.fr.F, κ * k * κ⁻¹ ∈ centIn (M2 c.s) c.s.fr.F) := by
  obtain ⟨κ, hκB, hκ3, -, hκfix, -, -⟩ := f3_exists_k hH
  have hNF : normIn L c.s.fr.B ≤ normIn L c.s.fr.F := hH.hLF.fact18.2.1.2.1
  have hκF : κ ∈ normIn L c.s.fr.F := hNF hκB
  have hκH : κ ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hH.hS hκB.1, hκB.2⟩
  exact ⟨κ, hκF, hκ3, fun v hv => conj_mem_cen_of_mem_normIn hκB hv, hκfix,
    fun k hk => conj_mem_centIn_of_pointwise (y54_M2_inv hH κ hκH) hκF.2 hk⟩

end CFSG.OddStandard.HigherRank.YamadaG23
