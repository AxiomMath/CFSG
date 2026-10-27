module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A3

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace S2

omit [Finite G] in
theorem Phi_le_I : frattiniOf (s2I S L) ≤ s2I S L := Subgroup.map_subtype_le _

omit [Finite G] in
theorem phi_le_I : s2Phi S L ≤ s2I S L := inf_le_left.trans Phi_le_I

omit [Finite G] in
theorem L_le_cent_phi : L ≤ Subgroup.centralizer (s2Phi S L : Set G) := by
  intro l hl
  refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
  exact (Subgroup.mem_centralizer_iff.1 (phi_le_I hf).2 l hl).symm

omit [Finite G] in
theorem L_le_normalizer_phi : L ≤ Subgroup.normalizer (s2Phi S L : Set G) :=
  L_le_cent_phi.trans (Subgroup.centralizer_le_normalizer _)

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem phi_isPGroup : IsPGroup 2 ↥(s2Phi S L) := c.isPGroup_I.to_le phi_le_I

theorem phi_le_H : s2Phi S L ≤ H :=
  phi_le_I.trans ((s2I_le_baum).trans ((C1GN.baum_le S).trans c.data.cs.sylow.1))

theorem SI_conf : IsConfining M (s2SI S L) := by
  have h := c.data
  have hQJ : pCoreOf 2 H ≤ thompsonJ S := GammaExtra.le_thompsonJ c.maxQ
  have hJR : thompsonJ S ≤ s2SI S L := (C1GN.thompsonJ_le_baum S).trans c.R_le_SI
  have hQR : pCoreOf 2 H ≤ s2SI S L := hQJ.trans hJR
  exact IsGamma0.isConfining_of_relIndex_two h.cs.setting h.cs.gamma0 h.cs.sylow_inf hJR
    s2SI_le_S h.relIndex_SI
    (IsGamma0.pCore_centralizer_le_of_charTwo h.cs.setting h.cs.gamma0 h.cs.sylow_inf
      h.cs.charTwo hQR)

theorem pCore_ne_bot_of_phi (hφ : s2Phi S L ≠ ⊥) :
    pCoreOf 2 (Subgroup.normalizer (s2Phi S L : Set G)) ≠ ⊥ := by
  intro hbot
  apply hφ
  have : s2Phi S L ≤ pCoreOf 2 (Subgroup.normalizer (s2Phi S L : Set G)) :=
    le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl c.phi_isPGroup
  rw [hbot] at this
  exact le_bot_iff.1 this

theorem SI_pair {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) :
    IsWitnessPair M (s2SI S L) (H ⊓ Subgroup.normalizer (s2Phi S L : Set G)) := by
  have h := c.data
  have hφ := c.phi_ne hE hI
  have hSIphi : s2SI S L ≤ Subgroup.normalizer (s2Phi S L : Set G) :=
    (c.SI_phi hE hI).le.trans inf_le_right
  have hSIH : s2SI S L ≤ H := s2SI_le_S.trans h.cs.sylow.1
  refine ⟨c.SI_conf, le_inf hSIH hSIphi, ?_, ?_, ?_⟩
  · intro hbot
    apply hφ
    have : s2Phi S L ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (s2Phi S L : Set G)) :=
      le_pCoreOf_of_normalizes (le_inf c.phi_le_H Subgroup.le_normalizer) inf_le_right
        c.phi_isPGroup
    rw [hbot] at this
    exact le_bot_iff.1 this
  · exact CharTwo.inf_normalizer h.cs.charTwo c.phi_le_H c.phi_isPGroup
  · intro hle
    exact h.cs.not_le (fun l hl => (hle ⟨C56.le_H h.cs hl, L_le_normalizer_phi hl⟩))

theorem GI_gamma {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) : IsGamma M (Subgroup.normalizer (s2Phi S L : Set G)) :=
  ⟨c.pCore_ne_bot_of_phi (c.phi_ne hE hI), s2SI S L, H ⊓ Subgroup.normalizer (s2Phi S L : Set G),
    c.SI_pair hE hI, inf_le_right⟩

end Ctx

end S2

end CFSG.QuasithinUnique.A5
