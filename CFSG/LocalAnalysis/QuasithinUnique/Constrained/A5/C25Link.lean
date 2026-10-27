module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Star
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem setting_of_A5 (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block)
    (hP2 : NoProperA5Block) (cfg : A5Cfg2 G T M H S L) {x : G} (hxT : x ∈ T)
    (hxU : ¬ conjR (blockU L) x ≤ s2Q1 S L) (hB : A5s2B T M H S L x) :
    Setting (Subgroup.normalizer (s2Phi S L : Set G)) L (s2SI S L) (blockU L) := by
  obtain ⟨t, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  obtain ⟨P₂, hE, hI⟩ := c.exists_P₂
  obtain ⟨P₁, -, -⟩ := c.std₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gi : Subgroup G := Subgroup.normalizer (s2Phi S L : Set G)
  have hSIGi : s2SI S L ≤ Gi := hB.SI_phi.le.trans inf_le_right
  have hxGi : x ∈ Gi := hB.x_phi
  have hQL : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hxSI : x ∉ s2SI S L := by
    intro hx
    apply hxU
    have hxU' : x⁻¹ ∈ Subgroup.normalizer (blockU L : Set G) :=
      Subgroup.inv_mem _ (C1.mem_normalizer_blockU hx.2)
    rw [conjR_eq_cj, mem_normalizer_iff_cj.1 hxU']
    exact c.u₁q
  have hD2 : IsPGroup 2 ↥(s2SI S L ⊔ Subgroup.zpowers x) := by
    have hxz : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      cfg.cs.setting.sylow.2.1.to_le (Subgroup.zpowers_le.2 hxT)
    exact IsPGroup.to_sup_of_normal_left' c.isPGroup_SI hxz (Subgroup.zpowers_le.2 hB.x_SI)
  have hDGi : s2SI S L ⊔ Subgroup.zpowers x ≤ Gi :=
    sup_le hSIGi (Subgroup.zpowers_le.2 hxGi)
  obtain ⟨TI, hDTI, hTI⟩ := exists_isSylowTwoOf_of_le hDGi hD2
  have hSITI : s2SI S L ≤ TI := le_sup_left.trans hDTI
  have hxTI : x ∈ TI := Subgroup.zpowers_le.1 (le_sup_right.trans hDTI)
  have hUinf : blockU L ⊓ pCoreOf 2 Gi = ⊥ := by
    have h2 := congrArg (cj x) hB.Ux_inf
    rw [conjR_eq_cj, cj_inf, cj_cj, mul_inv_cancel, cj_one,
      mem_normalizer_iff_cj.1 (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Gi
        (Subgroup.le_normalizer hxGi))] at h2
    exact h2.trans (Subgroup.map_bot _)
  exact
    { qtke := cfg.cs.setting.qtke.1
      gi_core := c.pCore_ne_bot_of_phi hB.phi_ne
      L_le := L_le_normalizer_phi
      SI_le := hSIGi
      local_SI := c.local_SI
      U_le := Subgroup.le_normalizer_iff_commutator_le_left.mp hQL
      short := h.isShort
      alt5 := h.alt5
      U_elem := isElemAbelian_blockU h.isShort
      U_card := P₁.toPiData.card_blockU.ge
      L_norm := fun l hl => C1.mem_normalizer_blockU (Subgroup.le_normalizer hl)
      U_inf := hUinf
      big := ⟨TI, hTI, lt_of_le_of_ne hSITI fun heq => hxSI (by rw [heq]; exact hxTI)⟩
      star := fun H₁ S₁ hc hLSI hH₁ hS₁ hlt =>
        star_gen c hE hI h37 h39 hP1 hP2 H₁ S₁ hc hLSI hH₁ hS₁ hlt }

end CFSG.QuasithinUnique.A5.C25
