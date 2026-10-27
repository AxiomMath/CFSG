module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRel
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem actsAs_pow {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (n : ℕ) :
    ActsAs L (g ^ n) (α ^ n) := by
  induction n with
  | zero => simpa using actsAs_one L
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact actsAs_mul L ih h

private theorem actsAs_comm {g h : G} {α β : MulAut (L ⧸ center L)}
    (hg : ActsAs L g α) (hh : ActsAs L h β) : ActsAs L ⁅g, h⁆ ⁅α, β⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact actsAs_mul L (actsAs_mul L (actsAs_mul L hg hh) (actsAs_inv L hg)) (actsAs_inv L hh)

private theorem comm_mem {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem srel_key (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {x y : G} (hx : x ∈ s.fr.S) (hy : y ∈ s.fr.S)
    {α β : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) (hyβ : ActsAs L y β) (h : α = β) :
    x = y :=
  s3_inj_on_S s hS hZ hx hy hxα (by rw [h]; exact hyβ)

theorem s3_srel (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    SRel s.fr := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, hh₀, hz⟩ := s3_actsAs_gens s
  have hsr := srel_of_fact11 s.fr' s.facts.1
  have ha₁S : s.fr.a₁ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have hb₁S : s.fr.b₁ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have ha₂S : s.fr.a₂ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have hb₂S : s.fr.b₂ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have hh₀S : s.fr.h₀ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have hzS : s.fr.z ∈ s.fr.S := by
    show s.fr.b₁ ^ 2 ∈ s.fr.S
    exact pow_mem hb₁S 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact srel_key hS hZ s (pow_mem hzS 2) (one_mem _) (actsAs_pow hz 2) (actsAs_one L)
      hsr.z_sq
  · exact srel_key hS hZ s (pow_mem hh₀S 2) (one_mem _) (actsAs_pow hh₀ 2) (actsAs_one L)
      hsr.h0_sq
  · exact srel_key hS hZ s (pow_mem ha₁S 2) hzS (actsAs_pow ha₁ 2) hz hsr.a1_sq
  · exact srel_key hS hZ s (pow_mem ha₂S 2) hzS (actsAs_pow ha₂ 2) hz hsr.a2_sq
  · exact srel_key hS hZ s (pow_mem hb₂S 2) hzS (actsAs_pow hb₂ 2) hz hsr.b2_sq
  · exact srel_key hS hZ s (comm_mem ha₁S hb₁S) hzS (actsAs_comm ha₁ hb₁) hz hsr.comm1
  · exact srel_key hS hZ s (comm_mem ha₂S hb₂S) hzS (actsAs_comm ha₂ hb₂) hz hsr.comm2
  · exact srel_key hS hZ s (comm_mem ha₁S hh₀S) (mul_mem hb₁S hzS) (actsAs_comm ha₁ hh₀)
      (actsAs_mul L hb₁ hz) hsr.a1h
  · exact srel_key hS hZ s (comm_mem ha₂S hh₀S) (mul_mem hb₂S hzS) (actsAs_comm ha₂ hh₀)
      (actsAs_mul L hb₂ hz) hsr.a2h
  · exact srel_key hS hZ s (comm_mem hb₁S hh₀S) hzS (actsAs_comm hb₁ hh₀) hz hsr.b1h
  · exact srel_key hS hZ s (comm_mem hb₂S hh₀S) hzS (actsAs_comm hb₂ hh₀) hz hsr.b2h
  · exact srel_key hS hZ s (comm_mem ha₁S ha₂S) (one_mem _) (actsAs_comm ha₁ ha₂) (actsAs_one L)
      hsr.a1a2
  · exact srel_key hS hZ s (comm_mem ha₁S hb₂S) (one_mem _) (actsAs_comm ha₁ hb₂) (actsAs_one L)
      hsr.a1b2
  · exact srel_key hS hZ s (comm_mem hb₁S ha₂S) (one_mem _) (actsAs_comm hb₁ ha₂) (actsAs_one L)
      hsr.b1a2
  · exact srel_key hS hZ s (comm_mem hb₁S hb₂S) (one_mem _) (actsAs_comm hb₁ hb₂) (actsAs_one L)
      hsr.b1b2

end CFSG.OddStandard.HigherRank.YamadaG23
