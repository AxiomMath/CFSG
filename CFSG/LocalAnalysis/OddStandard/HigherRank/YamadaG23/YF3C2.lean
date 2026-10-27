module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Sec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f3X0_le_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3X0 s ≤ f3Y s := by
  rw [← f3_Y_inf_H hH]
  exact inf_le_left

private noncomputable def f3phiHom_aux {s : Setting3 G L} {e : Setting3.Ext s}
    (hH : F33Hyp s e) : ↥s.C₂ →* ↥(cen s.fr.B) :=
  MonoidHom.mk' (fun c => ⟨f3phi s c, f3_phi_mem hH c (f3_C₂_le_Y hH c.2)⟩)
    (fun a b => Subtype.ext (f3_phi_mul hH a (f3_C₂_le_Y hH a.2) b (f3_C₂_le_Y hH b.2)))

private theorem f3phiHom_aux_ker {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (c : ↥s.C₂) : f3phiHom_aux hH c = 1 ↔ (c : G) ∈ f3P s := by
  have hcY : (c : G) ∈ f3Y s := f3_C₂_le_Y hH c.2
  constructor
  · intro h
    have hphi : f3phi s (c : G) = 1 :=
      congrArg (fun x : ↥(cen s.fr.B) => (x : G)) h
    have hX0 : (c : G) ∈ f3X0 s := (f3_phi_eq_one hH (c : G) hcY).1 hphi
    have hmem : (c : G) ∈ s.C₂ ⊓ f3X0 s := ⟨c.2, hX0⟩
    rwa [f3_C₂_inf_X0 hH] at hmem
  · intro h
    have hP : f3P s ≤ f3X0 s := by
      intro p hp
      exact ⟨f3_P_le_H s hp, f3_P_le_cent_V s hp⟩
    have hphi : f3phi s (c : G) = 1 :=
      (f3_phi_eq_one hH (c : G) hcY).2 (hP h)
    apply Subtype.ext
    exact hphi

private theorem f3phiHom_aux_surj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Function.Surjective (f3phiHom_aux hH) := by
  intro v
  obtain ⟨y, hyY, hyv⟩ := f3_phi_surj hH (v : G) v.2
  obtain ⟨c, hcY1, a, haX0, rfl⟩ := f3_Y_eq_Y1X0 hH y hyY
  have hcY : c ∈ f3Y s := f3_Y1_le_Y hH hcY1
  have haY : a ∈ f3Y s := f3X0_le_Y hH haX0
  have hca : f3phi s (c * a) = f3phi s c := by
    rw [f3_phi_mul hH c hcY a haY, (f3_phi_eq_one hH a haY).2 haX0, mul_one]
  have hval : f3phi s c = (v : G) := hca.symm.trans hyv
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rw [f3_C₂_eq_Y1 hH]; exact hcY1
  · apply Subtype.ext
    exact hval

theorem f3_phiHom {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ f : ↥s.C₂ →* ↥(cen s.fr.B), (∀ c : ↥s.C₂, ((f c : ↥(cen s.fr.B)) : G) = f3phi s c) ∧
      Function.Surjective f ∧ ∀ c : ↥s.C₂, f c = 1 ↔ (c : G) ∈ f3P s :=
  ⟨f3phiHom_aux hH, fun _ => rfl, f3phiHom_aux_surj hH, f3phiHom_aux_ker hH⟩

theorem f3_P_relIndex_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (f3P s).relIndex s.C₂ = 4 := by
  have hker : (f3P s).subgroupOf s.C₂ = (f3phiHom_aux hH).ker := by
    ext c
    simp only [MonoidHom.mem_ker, f3phiHom_aux_ker hH c, Subgroup.mem_subgroupOf]
  calc (f3P s).relIndex s.C₂ = (f3phiHom_aux hH).ker.index := by
        show ((f3P s).subgroupOf s.C₂).index = (f3phiHom_aux hH).ker.index
        rw [hker]
    _ = Nat.card (f3phiHom_aux hH).range := Subgroup.index_ker (f3phiHom_aux hH)
    _ = Nat.card (⊤ : Subgroup ↥(cen s.fr.B)) := by
        rw [MonoidHom.range_eq_top.mpr (f3phiHom_aux_surj hH)]
    _ = Nat.card ↥(cen s.fr.B) := Subgroup.card_top
    _ = 4 := by
        have h := (f3_V_isE2 hH).2
        norm_num at h
        exact h

theorem f3_c7 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    SecProp s.C₂ (s.fr.B ⊔ zpowers s.t) (fun Y _ _ π =>
      ∃ φ : Y ≃* ↥(cen s.fr.B), ∀ n ∈ normIn s.H s.fr.B, ∀ c c' : ↥s.C₂,
        (c' : G) = n * c * n⁻¹ → ((φ (π c') : ↥(cen s.fr.B)) : G) = n * (φ (π c) : G) * n⁻¹) := by
  obtain ⟨hn, hbody⟩ := secProp_iso (C := s.C₂) (P := f3P s)
    (f3phiHom_aux hH) (f3phiHom_aux_surj hH) (f3phiHom_aux_ker hH)
  obtain ⟨φ, hφ⟩ := hbody
  haveI : ((s.fr.B ⊔ zpowers s.t).subgroupOf s.C₂).Normal := hn
  refine ⟨hn, φ, ?_⟩
  intro n hnmem c c' hcc'
  show ((φ (QuotientGroup.mk' ((f3P s).subgroupOf s.C₂) c') : ↥(cen s.fr.B)) : G) =
    n * ((φ (QuotientGroup.mk' ((f3P s).subgroupOf s.C₂) c) : ↥(cen s.fr.B)) : G) * n⁻¹
  have hnH : n ∈ s.H := (show f3N s ≤ s.H from inf_le_left) hnmem
  have hnt : n * s.t = s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hnH
  rw [hφ c', hφ c]
  have hc' : ((f3phiHom_aux hH c' : ↥(cen s.fr.B)) : G) = f3phi s (c' : G) := rfl
  have hc : ((f3phiHom_aux hH c : ↥(cen s.fr.B)) : G) = f3phi s (c : G) := rfl
  rw [hc', hc, hcc']
  exact f3_phi_conj s hnt (c : G)

end CFSG.OddStandard.HigherRank.YamadaG23
