module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.BetaBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.SylowPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_permuting_elemAbelian_conj
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ B : Subgroup G, (∃ g ∈ H ⊓ M, B = A.map (MulAut.conj g).toMonoidHom) ∧
      B ≤ H ⊓ M ∧ IsElemAbelian 3 B ∧ Nat.card B = 9 ∧
      B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := GLBPrimeCore 3 (H ⊓ M) with hQdef
  set U := T ⊓ Q with hUdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hQHM : Q ≤ H ⊓ M := glbPrimeCore_le 3 _
  have hHMQ : H ⊓ M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_glbPrimeCore 3 _
  have hQ3 : Nat.Coprime 3 (Nat.card Q) := glbPrimeCore_coprime 3 _
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := hTHM.trans hHMQ
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf Subgroup.le_normalizer hTQ
  have hUsyl : IsSylowTwoOf U Q :=
    ⟨inf_le_right, hT.2.1.to_le inf_le_left,
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.not_two_dvd_relIndex_inf_of_normalizes
        hTHM hQHM hTQ hT.2.2⟩
  obtain ⟨V, hVsyl, hAV⟩ := D2L34BetaConf3.exists_isSylowTwoOf_glbPrimeCore_inf hc
  obtain ⟨q, hqQ, hUV⟩ := CFSG.Quasithin.B1.sylowTwo_conj hVsyl hUsyl
  have hAHM : A ≤ H ⊓ M := le_inf (hc.esc.A_le.trans hc.esc.le_H) (hc.esc.A_le.trans hc.esc.le_M)
  have hqHM : q ∈ H ⊓ M := hQHM hqQ
  set A' := A.map (MulAut.conj q).toMonoidHom with hA'def
  have hA'HM : A' ≤ H ⊓ M := by
    rintro _ ⟨a, ha, rfl⟩
    exact (H ⊓ M).mul_mem ((H ⊓ M).mul_mem hqHM (hAHM ha)) ((H ⊓ M).inv_mem hqHM)
  have hA'U : A' ≤ Subgroup.normalizer (U : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_normalizer_of_map_conj_eq_self
    have e : (MulAut.conj q).toMonoidHom a = q * a * q⁻¹ := rfl
    rw [hUV, ← map_conj_mul', e, show q * a * q⁻¹ * q = q * a by group, map_conj_mul',
      map_conj_eq_self_of_mem_normalizer (hAV ha)]
  have hA'c : Nat.card A' = 9 := by
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj q).injective, hc.esc.card_A]
    norm_num
  have hA'el : IsElemAbelian 3 A' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hc.esc.elem _
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hNX₀ : ∀ g (hg : g ∈ H ⊓ M), π ⟨g, hg.1⟩ ∈
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    intro g hg
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hWQ : GLBPrimeCore 3 H ≤ Q :=
    le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le)
      (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H)) (glbPrimeCore_coprime 3 H)
  have hAQ : ∀ g (hg : g ∈ H ⊓ M), ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ Q := by
    intro g hg a ha
    have hgH := hg.1
    have hmem : π ⟨g, hgH⟩ * π ⟨a, (hAHM ha).1⟩ * (π ⟨g, hgH⟩)⁻¹ ∈ (A.subgroupOf H).map π :=
      (Subgroup.mem_normalizer_iff.mp (hNX₀ g hg) _).mp
        ⟨⟨a, (hAHM ha).1⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    obtain ⟨⟨a₁, ha₁H⟩, ha₁, he⟩ := hmem
    have h1 : π ((⟨a₁, ha₁H⟩ : H)⁻¹ * (⟨g, hgH⟩ * ⟨a, (hAHM ha).1⟩ * (⟨g, hgH⟩ : H)⁻¹)) = 1 := by
      rw [map_mul, map_inv, he, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hw := (mk'_primeComplementCore_eq_one_iff 3 _).mp h1
    have e : g * a * g⁻¹ = a₁ * (a₁⁻¹ * (g * a * g⁻¹)) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha₁))
      (Subgroup.mem_sup_right (hWQ ?_))
    simpa using hw
  have hA'Q : A' ≤ Subgroup.normalizer (Q : Set G) := hA'HM.trans hHMQ
  have hAA'Q : A ≤ A' ⊔ Q := by
    intro a ha
    have hqa : q * a * q⁻¹ ∈ A' := ⟨a, ha, rfl⟩
    have e : a = q⁻¹ * (q * a * q⁻¹) * q := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Q.inv_mem hqQ))
      (Subgroup.mem_sup_left hqa)) (Subgroup.mem_sup_right hqQ)
  have hTA' : ∀ t ∈ T, A'.map (MulAut.conj t).toMonoidHom ≤
      A' ⊔ (Q ⊓ Subgroup.normalizer (U : Set G)) := by
    intro t ht
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hx
    have h1 : t * (q * a * q⁻¹) * t⁻¹ ∈ A' ⊔ Q := by
      have e : t * (q * a * q⁻¹) * t⁻¹ = (t * q) * a * (t * q)⁻¹ := by group
      rw [e]
      have htq : t * q ∈ H ⊓ M := (H ⊓ M).mul_mem (hTHM ht) hqHM
      have h2 := hAQ (t * q) htq a ha
      have hle : A ⊔ Q ≤ A' ⊔ Q := sup_le hAA'Q le_sup_right
      exact hle h2
    have h2 : t * (q * a * q⁻¹) * t⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).mul_mem ((Subgroup.normalizer (U : Set G)).mul_mem
        (hTU ht) (hA'U ⟨a, ha, rfl⟩)) ((Subgroup.normalizer (U : Set G)).inv_mem (hTU ht))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A' Q hA'Q,
      Set.mem_mul] at h1
    obtain ⟨a', ha', q', hq', he⟩ := h1
    have hq'N : q' ∈ Subgroup.normalizer (U : Set G) := by
      have : q' = a'⁻¹ * (t * (q * a * q⁻¹) * t⁻¹) := by rw [← he]; group
      rw [this]
      exact (Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).inv_mem (hA'U ha')) h2
    show (MulAut.conj t).toMonoidHom (q * a * q⁻¹) ∈ _
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← he]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right ⟨hq', hq'N⟩)
  have hUN₁ : U ≤ Q ⊓ Subgroup.normalizer (U : Set G) := le_inf inf_le_right Subgroup.le_normalizer
  have hodd : ¬ 2 ∣ (U.subgroupOf (Q ⊓ Subgroup.normalizer (U : Set G))).index := by
    intro h
    apply hUsyl.2.2
    have := Subgroup.relIndex_mul_relIndex U (Q ⊓ Subgroup.normalizer (U : Set G)) Q hUN₁
      inf_le_left
    exact h.trans ⟨_, this.symm⟩
  have hN₁3 : Nat.Coprime 3 (Nat.card (Q ⊓ Subgroup.normalizer (U : Set G) : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hQ3
  have hA'N₁ : A' ≤ Subgroup.normalizer ((Q ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) :
      Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf hA'Q (hA'U.trans Subgroup.le_normalizer)
  have hTN₁ : T ≤ Subgroup.normalizer ((Q ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) :
      Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf hTQ (hTU.trans Subgroup.le_normalizer)
  obtain ⟨m, hm, hTm⟩ := exists_conj_le_normalizer_sup (N₁ := Q ⊓ Subgroup.normalizer (U : Set G))
    (V := U) inf_le_right hodd hN₁3 hA'c hA'N₁ hT.2.1 hTU hTN₁ hTA'
  refine ⟨A'.map (MulAut.conj m).toMonoidHom,
    ⟨m * q, (H ⊓ M).mul_mem (hQHM hm.1) hqHM, by rw [map_conj_mul']⟩, ?_, ?_, ?_, ?_, hTm⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hmHM : m ∈ H ⊓ M := hQHM hm.1
    exact (H ⊓ M).mul_mem ((H ⊓ M).mul_mem hmHM (hA'HM hx)) ((H ⊓ M).inv_mem hmHM)
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hA'el _
  · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hA'c]
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.normalizer (U : Set G)).mul_mem ((Subgroup.normalizer (U : Set G)).mul_mem
      hm.2 (hA'U hx)) ((Subgroup.normalizer (U : Set G)).inv_mem hm.2)

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_permuting_elemAbelian
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ B : Subgroup G, B ≤ H ⊓ M ∧ IsElemAbelian 3 B ∧ Nat.card B = 9 ∧
      B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G) := by
  obtain ⟨B, -, h⟩ := D2L34BetaConf3.exists_permuting_elemAbelian_conj hc hT
  exact ⟨B, h⟩

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
