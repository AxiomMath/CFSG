module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6

public section

namespace CFSG.QuasithinUnique.Vol2Native

theorem lemma256Embedding_of_a3 (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) :
    Lemma256Embedding := by
  intro G _ _ T M hs N _ E hE1 hEc hES
  have hE2 : IsPGroup 2 E := N.tuple.sylow.isPGroup.to_le (hEc.trans N.SC_le_S)
  have hHX : N.H ≤ Subgroup.normalizer (E : Set G) :=
    N.H_le_normalizer_of (N.K0_le_centralizer_of_le_SC hEc) hES
  have hΓ : IsGamma M (Subgroup.normalizer (E : Set G)) :=
    N.isGamma_of_le hE1 hE2 Subgroup.le_normalizer le_rfl hHX
  obtain ⟨htupX, -⟩ := N.tuple_of_overgroup hΓ hHX
  obtain ⟨KE, hKEX, hKKE⟩ := exists_isComponentIn_of_gamma0_overgroup h37 h39 hs.setting
    N.tuple.gamma0 N.tuple.sylow_inf hs.setting.isSylowTwoOf_M N.tuple.lt.le N.tuple.z_mem
    N.tuple.z_ne_one N.tuple.z_sq htupX.gamma0 htupX.sylow htupX.sylow_inf hHX N.isComp
  exact ⟨KE, hKKE, hKEX⟩

end CFSG.QuasithinUnique.Vol2Native
