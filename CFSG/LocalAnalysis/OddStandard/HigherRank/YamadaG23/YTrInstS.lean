module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF12
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF14a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF14b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF14c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private abbrev gS (s : Setting3 G L) : GFrame ↥s.fr.S where
  a₁ := ⟨s.fr.a₁, s3_a₁_mem_S s⟩
  b₁ := ⟨s.fr.b₁, s3_b₁_mem_S s⟩
  a₂ := ⟨s.fr.a₂, s3_a₂_mem_S s⟩
  b₂ := ⟨s.fr.b₂, s3_b₂_mem_S s⟩
  h₀ := ⟨s.fr.h₀, s3_h₀_mem_S s⟩
  σ := 1

private lemma F12_sigma_irrel {Γ : Type} [Group Γ] [Finite Γ] (gf : GFrame Γ) (σ' : Γ) :
    ({gf with σ := σ'} : GFrame Γ).F12 ↔ gf.F12 := by
  cases gf
  rfl

private lemma F14a_sigma_irrel {Γ : Type} [Group Γ] [Finite Γ] (gf : GFrame Γ) (σ' : Γ) :
    ({gf with σ := σ'} : GFrame Γ).F14a ↔ gf.F14a := by
  cases gf
  rfl

private lemma F14b_sigma_irrel {Γ : Type} [Group Γ] [Finite Γ] (gf : GFrame Γ) (σ' : Γ) :
    ({gf with σ := σ'} : GFrame Γ).F14b ↔ gf.F14b := by
  cases gf
  rfl

private lemma F14c_sigma_irrel {Γ : Type} [Group Γ] [Finite Γ] (gf : GFrame Γ) (σ' : Γ) :
    ({gf with σ := σ'} : GFrame Γ).F14c ↔ gf.F14c := by
  cases gf
  rfl

private lemma gS_map_jOn_eq (s : Setting3 G L) :
    (gS s).map (jOn L (s3_S_le_N s)) = {GFrame.ofFrame s.fr' with σ := 1} := by
  change GFrame.mk (jOn L (s3_S_le_N s) (gS s).a₁) (jOn L (s3_S_le_N s) (gS s).b₁)
      (jOn L (s3_S_le_N s) (gS s).a₂) (jOn L (s3_S_le_N s) (gS s).b₂)
      (jOn L (s3_S_le_N s) (gS s).h₀) (jOn L (s3_S_le_N s) (gS s).σ) =
    GFrame.mk s.fr'.a₁ s.fr'.b₁ s.fr'.a₂ s.fr'.b₂ s.fr'.h₀ 1
  rw [GFrame.mk.injEq]
  exact ⟨actsAs_unique L (jOn_actsAs L (s3_S_le_N s) (gS s).a₁) (s3_actsAs_gens s).1,
    actsAs_unique L (jOn_actsAs L (s3_S_le_N s) (gS s).b₁) (s3_actsAs_gens s).2.1,
    actsAs_unique L (jOn_actsAs L (s3_S_le_N s) (gS s).a₂) (s3_actsAs_gens s).2.2.1,
    actsAs_unique L (jOn_actsAs L (s3_S_le_N s) (gS s).b₂) (s3_actsAs_gens s).2.2.2.1,
    actsAs_unique L (jOn_actsAs L (s3_S_le_N s) (gS s).h₀) (s3_actsAs_gens s).2.2.2.2.1,
    map_one (jOn L (s3_S_le_N s))⟩

private lemma gS_map_subtype_eq (s : Setting3 G L) :
    (gS s).map s.fr.S.subtype = GFrame.ofFrame (frameWith s 1) := rfl

private lemma gS_F12_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) (h : (GFrame.ofFrame s.fr').F12) : (gS s).F12 := by
  have h1 : ({GFrame.ofFrame s.fr' with σ := 1} : GFrame _).F12 :=
    (F12_sigma_irrel (GFrame.ofFrame s.fr') 1).mpr h
  rw [← gS_map_jOn_eq s] at h1
  exact (f12_map_iff (s3_jOn_S_injective s hS hZ) (gS s)).mp h1

private lemma gS_F14a_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) (h : (GFrame.ofFrame s.fr').F14a) : (gS s).F14a := by
  have h1 : ({GFrame.ofFrame s.fr' with σ := 1} : GFrame _).F14a :=
    (F14a_sigma_irrel (GFrame.ofFrame s.fr') 1).mpr h
  rw [← gS_map_jOn_eq s] at h1
  exact (f14a_map_iff (s3_jOn_S_injective s hS hZ) (gS s)).mp h1

private lemma gS_F14b_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) (h : (GFrame.ofFrame s.fr').F14b) : (gS s).F14b := by
  have h1 : ({GFrame.ofFrame s.fr' with σ := 1} : GFrame _).F14b :=
    (F14b_sigma_irrel (GFrame.ofFrame s.fr') 1).mpr h
  rw [← gS_map_jOn_eq s] at h1
  exact (f14b_map_iff (s3_jOn_S_injective s hS hZ) (gS s)).mp h1

private lemma gS_F14c_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) (h : (GFrame.ofFrame s.fr').F14c) : (gS s).F14c := by
  have h1 : ({GFrame.ofFrame s.fr' with σ := 1} : GFrame _).F14c :=
    (F14c_sigma_irrel (GFrame.ofFrame s.fr') 1).mpr h
  rw [← gS_map_jOn_eq s] at h1
  exact (f14c_map_iff (s3_jOn_S_injective s hS hZ) (gS s)).mp h1

theorem lf_fact12 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    (frameWith s 1).Fact12 := by
  refine (fact12_iff (frameWith s 1)).mpr ?_
  rw [← gS_map_subtype_eq s]
  refine (f12_map_iff (s.fr.S.subtype_injective) (gS s)).mpr ?_
  exact gS_F12_of hS hZ s ((fact12_iff s.fr').mp s.facts.2.1)

theorem lf_fact14 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    (frameWith s 1).Fact14 := by
  refine (fact14_iff (frameWith s 1)).mpr ?_
  obtain ⟨h14a, h14b, h14c⟩ : (GFrame.ofFrame s.fr').F14 := (fact14_iff s.fr').mp s.facts.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← gS_map_subtype_eq s]
    exact (f14a_map_iff (s.fr.S.subtype_injective) (gS s)).mpr (gS_F14a_of hS hZ s h14a)
  · rw [← gS_map_subtype_eq s]
    exact (f14b_map_iff (s.fr.S.subtype_injective) (gS s)).mpr (gS_F14b_of hS hZ s h14b)
  · rw [← gS_map_subtype_eq s]
    exact (f14c_map_iff (s.fr.S.subtype_injective) (gS s)).mpr (gS_F14c_of hS hZ s h14c)

end CFSG.OddStandard.HigherRank.YamadaG23
