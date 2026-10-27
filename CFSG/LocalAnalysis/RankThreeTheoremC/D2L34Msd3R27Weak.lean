module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.BetaBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.TwoOfThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2NonExtremalL34At.exists_weakConf [D2Amb3 G] {T : Subgroup G}
    (hNE : D2NonExtremalL34At P M T) {E N : Subgroup G} (hesc : D2Escape 3 P M E N E)
    (hTN : Subgroup.normalizer (T : Set G) ≤ N) :
    ∃ (d' : TauCeti.ValidLieTypeIndex) (Ebar : Sylow 3 (N ⧸ primeComplementCore (G := N) 3))
      (K' : Subgroup (N ⧸ primeComplementCore (G := N) 3)),
      D2L34WeakConf3 d' P M E N E Ebar K' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ebar, K', hEbar, hK'⟩ := hesc.almostSimple (D2Amb3.glob (G := G))
  obtain ⟨d', hd', hi⟩ := hNE E N hesc hTN Ebar K' hEbar hK'
  have := hK'.normal
  have hK'c : Nat.card K' = 20160 :=
    (kFactSmallThreeOrders K').2.1 (isLinThreeFour_of_l34Index hd' hi)
  have hEN : E ≤ N := hesc.le_H
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hesc.card_A
  have hEp' : IsPGroup 3 (E.subgroupOf N) := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
  have hEb : Nat.card (Ebar : Subgroup (N ⧸ primeComplementCore (G := N) 3)) = 3 ^ 2 := by
    rw [hEbar, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hEp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hesc.card_A]
  have hfac : (Nat.card (N ⧸ primeComplementCore (G := N) 3)).factorization 3 = 2 := by
    have h1 := Ebar.card_eq_multiplicity
    rw [hEb] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hidx3 : ¬ 3 ∣ K'.index := by
    intro h3
    have hmul := K'.index_mul_card
    rw [hK'c] at hmul
    have hidx0 : K'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : (K'.index * 20160).factorization 3 = 2 := by rw [hmul, hfac]
    rw [Nat.factorization_mul hidx0 (by norm_num), Finsupp.add_apply,
      factorization_20160_three] at h2
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hidx0).mp h3
    omega
  have hEK' : (E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) ≤ K' := by
    rw [← hEbar]
    exact le_of_isPGroup_of_not_dvd_index Nat.prime_three hidx3 Ebar.isPGroup'
  exact ⟨d', Ebar, K', hd', hesc, hEbar, hK', hi, hEK'⟩

private theorem D2L34WeakConf3.exists_isSylowTwoOf_glbPrimeCore_inf
    (hw : D2L34WeakConf3 d P M A H R Rbar K) :
    ∃ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)) ∧
      A ≤ Subgroup.normalizer (V : Set G) := by
  have hAHM : A ≤ H ⊓ M :=
    le_inf (hw.esc.A_le.trans hw.esc.le_H) (hw.esc.A_le.trans hw.esc.le_M)
  obtain ⟨V, hV, hVA⟩ := CFSG.DihedralBlueprint.normalized_exists_sylow 3 2 Nat.prime_three
    Nat.prime_two A (GLBPrimeCore 3 (H ⊓ M)) (IsPGroup.of_card (n := 2) hw.esc.card_A)
    (hAHM.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M))) (glbPrimeCore_coprime 3 (H ⊓ M))
  exact ⟨V, isSylowTwoOf_of_isSylowIn hV, hVA⟩

private theorem D2L34WeakConf3.isSylowTwoOf_map
    (hw : D2L34WeakConf3 d P M A H R Rbar K)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (Subgroup.normalizer (((A.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) : Subgroup _) : Set _)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hw.almostSimple.eq_normalizer_of_l34 kFactL34Inner hw.l34 hw.iso hw.le_K
  set α : ↥(H ⊓ M) →* (H ⧸ primeComplementCore (G := H) 3) :=
    π.comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H)) with hα
  have hαr : α.range = ((H ⊓ M).subgroupOf H).map π := by
    ext z
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hα, MonoidHom.comp_apply]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left u, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hαT : (T.subgroupOf (H ⊓ M)).map α = (T.subgroupOf H).map π := by
    ext z
    simp only [Subgroup.mem_map, hα, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left u, hu, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hT.1 hh⟩, hh, rfl⟩
  have h := isSylowTwoOf_map_range α hT
  rw [hαT, hαr, hX₀N] at h
  exact h

private theorem D2L34WeakConf3.map_eq_of_conj
    (hw : D2L34WeakConf3 d P M A H R Rbar K) {g : G}
    (hg : g ∈ H ⊓ M) :
    ((A.map (MulAut.conj g).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hw.almostSimple.eq_normalizer_of_l34 kFactL34Inner hw.l34 hw.iso hw.le_K
  have hgN : π ⟨g, hg.1⟩ ∈
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hAH : A ≤ H := hw.esc.A_le.trans hw.esc.le_H
  ext z
  constructor
  · rintro ⟨⟨x, hxH⟩, hx, rfl⟩
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_subgroupOf.mp hx
    have e : (⟨x, hxH⟩ : H) = ⟨g, hg.1⟩ * ⟨a, hAH ha⟩ * (⟨g, hg.1⟩ : H)⁻¹ := by
      apply Subtype.ext
      rw [← hax]
      rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp
      ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  · intro hz
    obtain ⟨⟨a, haH⟩, ha, he⟩ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z).mp hz
    refine ⟨⟨g, hg.1⟩ * ⟨a, haH⟩ * (⟨g, hg.1⟩ : H)⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    · rw [map_mul, map_mul, map_inv, he]
      group

private theorem D2L34WeakConf3.exists_permuting_elemAbelian_conj
    (hw : D2L34WeakConf3 d P M A H R Rbar K) {T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) :
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
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := hTHM.trans hHMQ
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf Subgroup.le_normalizer hTQ
  have hUsyl : IsSylowTwoOf U Q :=
    ⟨inf_le_right, hT.2.1.to_le inf_le_left,
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.not_two_dvd_relIndex_inf_of_normalizes
        hTHM hQHM hTQ hT.2.2⟩
  obtain ⟨V, hVsyl, hAV⟩ := hw.exists_isSylowTwoOf_glbPrimeCore_inf
  obtain ⟨q, hqQ, hUV⟩ := CFSG.Quasithin.B1.sylowTwo_conj hVsyl hUsyl
  have hAHM : A ≤ H ⊓ M := le_inf (hw.esc.A_le.trans hw.esc.le_H) (hw.esc.A_le.trans hw.esc.le_M)
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
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj q).injective, hw.esc.card_A]
    norm_num
  have hA'el : IsElemAbelian 3 A' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hw.esc.elem _
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hw.almostSimple.eq_normalizer_of_l34 kFactL34Inner hw.l34 hw.iso hw.le_K
  have hNX₀ : ∀ g (hg : g ∈ H ⊓ M), π ⟨g, hg.1⟩ ∈
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    intro g hg
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hWQ : GLBPrimeCore 3 H ≤ Q :=
    le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le 3 H) hw.esc.primeCore_le)
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
    have hw' := (mk'_primeComplementCore_eq_one_iff 3 _).mp h1
    have e : g * a * g⁻¹ = a₁ * (a₁⁻¹ * (g * a * g⁻¹)) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha₁))
      (Subgroup.mem_sup_right (hWQ ?_))
    simpa using hw'
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

theorem D2L34WeakConf3.exists_permuting_elemAbelian_map_eq
    (hw : D2L34WeakConf3 d P M A H R Rbar K) {T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ B : Subgroup G, (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
        (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ∧
      B ≤ H ⊓ M ∧ IsElemAbelian 3 B ∧ Nat.card B = 9 ∧
      B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G) := by
  obtain ⟨B, ⟨g, hg, rfl⟩, h⟩ := hw.exists_permuting_elemAbelian_conj hT
  exact ⟨_, hw.map_eq_of_conj hg, h⟩

theorem D2L34WeakConf3.cover_of_isSylowTwoOf_of_map_eq
    (hw : D2L34WeakConf3 d P M A H R Rbar K)
    {T B Y : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hTY : T ≤ Y) (hBY : B ≤ Y) (hNTY : H ⊓ Subgroup.normalizer (T : Set G) ≤ Y) :
    ∀ k ∈ K, ∃ a ∈ Y, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hTbar := hw.isSylowTwoOf_map hT
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    rw [hw.almostSimple.card_A]
    norm_num
  have hNY : Subgroup.normalizer (((T.subgroupOf H).map π : Subgroup _) : Set _) ≤
      (Y.subgroupOf H).map π :=
    (normalizer_map_le_map_normalizer hw.esc.primeCore_le hT).trans
      (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
        (hNTY (Subgroup.mem_subgroupOf.mp hx))))
  have hAY : (A.subgroupOf H).map π ≤ (Y.subgroupOf H).map π := by
    rw [← hBA]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBY (Subgroup.mem_subgroupOf.mp hx)))
  have hKY := le_of_normalizer_sylowTwo_le hw.l34 hw.almostSimple.normal
    hw.almostSimple.centralizer_eq_bot hw.iso hw.le_K hw.almostSimple.elem hAbar9 hTbar
    (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hTY (Subgroup.mem_subgroupOf.mp hx)))) hAY hNY
  intro k hk
  obtain ⟨y, hy, rfl⟩ := hKY hk
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, rfl⟩

private theorem D2L34WeakConf3.exists_quaternion_le_autIn_of_map_eq
    (hw : D2L34WeakConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) (hBH : B ≤ H)
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    ∃ Q : Subgroup (MulAut B),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set W := GLBPrimeCore 3 (H ⊓ M)
  set Abar := (A.subgroupOf H).map π with hAbar
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hAH : A ≤ H := hw.esc.A_le.trans hw.esc.le_H
  have hAHM : A ≤ H ⊓ M := le_inf hAH (hw.esc.A_le.trans hw.esc.le_M)
  have hX₀N : ((H ⊓ M).subgroupOf H).map π = Subgroup.normalizer (Abar : Set _) :=
    hw.almostSimple.eq_normalizer_of_l34 kFactL34Inner hw.l34 hw.iso hw.le_K
  have hNA : ∀ g (hg : g ∈ H ⊓ M), π ⟨g, hg.1⟩ ∈ Subgroup.normalizer (Abar : Set _) := by
    intro g hg
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hAbar9 : Nat.card Abar = 9 := by
    rw [hAbar, hw.almostSimple.card_A]
    norm_num
  have hAbarc : ∀ x ∈ Abar, ∀ y ∈ Abar, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hw.almostSimple.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hWHM : W ≤ H ⊓ M := glbPrimeCore_le 3 _
  have hHMW : H ⊓ M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glbPrimeCore 3 _
  have hAW : Abar ⊓ (W.subgroupOf H).map π = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hAbar9]
    have h1 : Nat.Coprime 9 (Nat.card (W.subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWHM.trans inf_le_left)).toEquiv]
      exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸
        Nat.Coprime.pow_left 2 (glbPrimeCore_coprime 3 _)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ π) h1
  have hcomm : ∀ (w : G) (hw : w ∈ W) (y : H ⧸ primeComplementCore (G := H) 3), y ∈ Abar →
      π ⟨w, (hWHM hw).1⟩ * y = y * π ⟨w, (hWHM hw).1⟩ := by
    intro w hw y hy
    obtain ⟨⟨a, haH⟩, ha, rfl⟩ := hy
    have haA : a ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hwN := hNA w (hWHM hw)
    have hc1 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ ∈
        Abar :=
      Abar.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN _).mp ⟨⟨a, haH⟩, ha, rfl⟩)
        (Abar.inv_mem ⟨⟨a, haH⟩, ha, rfl⟩)
    have hc2 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ ∈
        (W.subgroupOf H).map π := by
      have h1 : a * w⁻¹ * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHMW (hAHM haA)) _).mp (W.inv_mem hw)
      have hmem : w * (a * w⁻¹ * a⁻¹) ∈ W := W.mul_mem hw h1
      refine ⟨⟨w * (a * w⁻¹ * a⁻¹), (hWHM hmem).1⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
      have e : (⟨w * (a * w⁻¹ * a⁻¹), (hWHM hmem).1⟩ : H) =
          ⟨w, (hWHM hw).1⟩ * ⟨a, haH⟩ * (⟨w, (hWHM hw).1⟩ : H)⁻¹ * (⟨a, haH⟩ : H)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ =
        1 := by
      have := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
      rw [hAW, Subgroup.mem_bot] at this
      exact this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hψmem : ∀ b : B, (π.comp (Subgroup.inclusion hBH)) b ∈ Abar := by
    intro b
    rw [← hBA]
    exact ⟨⟨b, hBH b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  let ψ : B →* Abar := (π.comp (Subgroup.inclusion hBH)).codRestrict Abar hψmem
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hBA] at hy
    obtain ⟨⟨b, hbH⟩, hb, rfl⟩ := hy
    exact ⟨⟨b, Subgroup.mem_subgroupOf.mp hb⟩, Subtype.ext rfl⟩
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hB9, hAbar9])
  let φ : B ≃* Abar := MulEquiv.ofBijective ψ hψb
  have hφ : ∀ b : B, ((φ b : Abar) : H ⧸ primeComplementCore (G := H) 3) = π ⟨b, hBH b.2⟩ :=
    fun _ => rfl
  let Ψ : MulAut B ≃* MulAut Abar := MulAut.congr φ
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hw.l34 hw.iso
  obtain ⟨Q₈, hQ₈le, ⟨eQ⟩⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_quaternion_le_automizer hL hw.le_K
      hAbar9
  have hTbar := hw.isSylowTwoOf_map hT
  obtain ⟨hNKeq, -, -⟩ := normalizer_inf_eq_sup_of_l34 hw.l34 hw.almostSimple.normal hw.iso
    hw.le_K hAbar9 hTbar
  refine ⟨Q₈.map Ψ.symm.toMonoidHom, ?_,
    ⟨(Subgroup.equivMapOfInjective Q₈ Ψ.symm.toMonoidHom Ψ.symm.injective).symm.trans eQ⟩⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := hQ₈le hσ
  have hkK' : k ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hk : k ∈ Subgroup.normalizer (Abar : Set _) ⊓ K := ⟨hkN, hkK'⟩
  rw [← hNKeq, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hTbar.1), Set.mem_mul]
    at hk
  obtain ⟨tbar, htbar, a, ha, rfl⟩ := hk
  obtain ⟨⟨t, htH⟩, ht, rfl⟩ := htbar.1
  have htT : t ∈ T := Subgroup.mem_subgroupOf.mp ht
  obtain ⟨u, hu, hut⟩ := exists_mul_mem_normalizer_of_sup (hT.2.1.to_le inf_le_left) hB9 hBU
    (hTBU htT)
  refine ⟨⟨u * t, hut⟩, Subgroup.mem_subgroupOf.mpr (T.mul_mem hu.1 htT), ?_⟩
  show B.normalizerMonoidHom ⟨u * t, hut⟩ = Ψ.symm _
  rw [MulEquiv.eq_symm_apply]
  ext y
  obtain ⟨b, rfl⟩ := φ.surjective y
  have huH : u ∈ H := hTH hu.1
  have hy1 : π ⟨t, htH⟩ * π ⟨b, hBH b.2⟩ * (π ⟨t, htH⟩)⁻¹ ∈ Abar := by
    have hbA : π ⟨b, hBH b.2⟩ ∈ Abar := (φ b).2
    exact (Subgroup.mem_normalizer_iff.mp (hNA t (hTHM htT)) _).mp hbA
  have hL1 : (((Ψ (B.normalizerMonoidHom ⟨u * t, hut⟩)) (φ b) : Abar) :
      H ⧸ primeComplementCore (G := H) 3) =
      π ⟨u, huH⟩ * (π ⟨t, htH⟩ * π ⟨b, hBH b.2⟩ * (π ⟨t, htH⟩)⁻¹) * (π ⟨u, huH⟩)⁻¹ := by
    show ((φ (B.normalizerMonoidHom ⟨u * t, hut⟩ (φ.symm (φ b))) : Abar) :
      H ⧸ primeComplementCore (G := H) 3) = _
    rw [MulEquiv.symm_apply_apply, hφ]
    have e : (⟨((B.normalizerMonoidHom ⟨u * t, hut⟩ b : B) : G),
        hBH (B.normalizerMonoidHom ⟨u * t, hut⟩ b).2⟩ : H) =
        ⟨u, huH⟩ * (⟨t, htH⟩ * ⟨b, hBH b.2⟩ * (⟨t, htH⟩ : H)⁻¹) * (⟨u, huH⟩ : H)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv,
        CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe]
      group
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [hL1, hcomm u hu.2 _ hy1, mul_inv_cancel_right]
  show _ = ((Abar.normalizerMonoidHom ⟨π ⟨t, htH⟩ * a, hkN⟩ (φ b) : Abar) :
    H ⧸ primeComplementCore (G := H) 3)
  rw [CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe, hφ]
  have hbA : π ⟨b, hBH b.2⟩ ∈ Abar := (φ b).2
  rw [mul_inv_rev, show π ⟨t, htH⟩ * a * π ⟨b, hBH b.2⟩ * (a⁻¹ * (π ⟨t, htH⟩)⁻¹) =
    π ⟨t, htH⟩ * (a * π ⟨b, hBH b.2⟩ * a⁻¹) * (π ⟨t, htH⟩)⁻¹ by group,
    hAbarc a ha _ hbA, mul_inv_cancel_right]

theorem D2L34WeakConf3.two_of_three_normalized_of_map_eq [D2Amb3 G]
    (hw : D2L34WeakConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) (hBH : B ≤ H)
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hBel : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hHc : CharTwo H := (D2Amb3.glob (G := G)).charTwo H hw.esc.maxTwoLocal_H.1
  have hO2 : pCoreOf 2 H ≤ T := by
    have hO2p : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    have hO2W : pCoreOf 2 H ≤ GLBPrimeCore 3 H := by
      refine le_glbPrimeCore (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) ?_
      obtain ⟨k, hk⟩ := hO2p.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hO2HM : pCoreOf 2 H ≤ H ⊓ M :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hO2W.trans hw.esc.primeCore_le)
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HM
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hO2p
    exact hle.trans (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hchar : CharTwo (T ⊔ B) :=
    charTwo_of_le_of_pCoreOf_le (sup_le hTH hBH) hHc (hO2.trans le_sup_left)
  exact CFSG.AGLEmbeddingD2.Tits.MsidePrelim.two_of_three_normalized hT.2.1 hBel hB9 inf_le_left
    hBU hTBU hchar
    (hw.exists_quaternion_le_autIn_of_map_eq hT hBH hBA hB9 hBU hTBU)

end CFSG.LocalAnalysis.RankThreeTheoremC
