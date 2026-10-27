module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem cj_s2Q1 {g : G} (hg : g ∈ S) (L : Subgroup G) : cj g (s2Q1 S L) = s2Q1 S (cj g L) := by
  have hb : cj g (baum S) = baum S :=
    mem_normalizer_iff_cj.1 (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg))
  have h1 := pCoreOf_map_equiv 2 (MulAut.conj g) (L ⊔ baum S)
  rw [Subgroup.map_sup] at h1
  unfold s2Q1 cj
  rw [← h1]
  have : (baum S).map (MulAut.conj g).toMonoidHom = baum S := hb
  rw [this]

end CFSG.QuasithinUnique.A5.S2

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem lemma2_4_25_Q (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7) : Lemma2_4_25_Q := by
  intro G _ _ T M H S L cfg t ht htL
  obtain ⟨t₀, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  rcases h.conj_cases (S.inv_mem ht) with h1 | h1
  · exact absurd h1 htL
  · show s2Q1 S L ⊓ cj t⁻¹ (s2Q1 S L) ≤ pCoreOf 2 H
    rw [cj_s2Q1 (S.inv_mem ht), h1]
    exact c.Q_inf_le

end CFSG.QuasithinUnique.A5
