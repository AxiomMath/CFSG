module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

theorem comm_ne_bot_of_not_le {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {t : G}
    (c : S2.Ctx T M H S L t) {x : G} (hxN : x ∈ Subgroup.normalizer (S : Set G))
    (hxU : ¬ conjR (blockU L) x ≤ s2Q1 S L) : ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥ := by
  intro hbot
  apply hxU
  have hxR : x⁻¹ ∈ Subgroup.normalizer (baum S : Set G) :=
    inv_mem (normalizer_le_normalizer_baum S hxN)
  have hRx : conjR (baum S) x = baum S := mem_normalizer_iff_cj.1 hxR
  have hUx_R : conjR (blockU L) x ≤ baum S := by
    have := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) c.u₁R
    rwa [show Subgroup.map (MulAut.conj x⁻¹).toMonoidHom (baum S) = baum S from hRx] at this
  have hUxC : conjR (blockU L) x ≤ Subgroup.centralizer (blockU L : Set G) := by
    rw [Subgroup.commutator_comm] at hbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  rw [c.q₁]
  exact le_inf hUx_R hUxC

theorem lemma2_4_25_A (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7) (hC56 : LemmaC56_14_s2) :
    Lemma2_4_25_A := by
  intro G _ _ T M H S L cfg x hxT hxN hxU
  obtain ⟨t, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  obtain ⟨P₂, hE, hI⟩ := c.exists_P₂
  have hcomm := comm_ne_bot_of_not_le c hxN hxU
  obtain ⟨-, -, -, hfrat⟩ := hC56 G T M H S L cfg.cs cfg.alt5 cfg.double x hxT hxN hcomm
  have hxΦ : x ∈ Subgroup.normalizer (frattiniOf (s2I S L) : Set G) := by
    have : x⁻¹ ∈ Subgroup.normalizer (frattiniOf (s2I S L) : Set G) :=
      mem_normalizer_iff_cj.2 hfrat
    simpa using inv_mem this
  have hSI : s2SI S L = S ⊓ Subgroup.normalizer (frattiniOf (s2I S L) : Set G) :=
    c.SI_frat hE hI
  have hxSI : x ∈ Subgroup.normalizer (s2SI S L : Set G) := by
    refine mem_normalizer_iff_cj.2 ?_
    rw [hSI, cj_inf, mem_normalizer_iff_cj.1 hxN, cj_normalizer, mem_normalizer_iff_cj.1 hxΦ]
  have hxφ : x ∈ Subgroup.normalizer (s2Phi S L : Set G) := by
    refine mem_normalizer_iff_cj.2 ?_
    unfold s2Phi
    rw [cj_inf, mem_normalizer_iff_cj.1 hxΦ, cj_centralizer, mem_normalizer_iff_cj.1 hxSI]
  exact
    { frat_x := hfrat
      x_SI := hxSI
      x_phi := hxφ
      phi_ne := c.phi_ne hE hI
      o3_cent := c.o3_cent hE hI
      SI_frat := hSI
      SI_phi := c.SI_phi hE hI
      SI_index := h.relIndex_SI
      SI_conf := c.SI_conf
      SI_pair := c.SI_pair hE hI
      GI_gamma := c.GI_gamma hE hI }

end CFSG.QuasithinUnique.A5
