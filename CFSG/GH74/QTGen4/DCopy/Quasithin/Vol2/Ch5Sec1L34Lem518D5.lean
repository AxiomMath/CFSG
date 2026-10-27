module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.A3Structure314Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement Pointwise

section Bar

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem a314Statement_bar_F4 (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts_F4) {X T₀ B L : Subgroup G}
    (hO : pCoreOf 2 X ≠ ⊥) (hsyl : IsSylowTwoOf T₀ X) (hBX : B ≤ X) (hB : B ∈ lFamily T₀)
    (hL : L ∈ cComp X) (hBL : B < L) (hT₀B : T₀ ≤ Subgroup.normalizer (B : Set G))
    (hA : Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5))) :
    modO2Image X B < modO2Image X L ∧
      A314Statement (o2Img X T₀) (modO2Image X B) (modO2Image X L) := by
  have hne : modO2Image X B ≠ modO2Image X L := fun h =>
    hBL.ne (Vol2.Ch11.SecA.eq_of_modO2Image_eq hsyl (le_of_mem_cComp hL) hBL.le
      (perfect_of_mem_cComp hL) hT₀B h)
  have hlt : modO2Image X B < modO2Image X L :=
    lt_of_le_of_ne (Subgroup.map_mono fun _ hx => hBL.le hx) hne
  refine ⟨hlt, ?_⟩
  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hO
  have hsylbar : IsSylowTwoOf (o2Img X T₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hL' : modO2Image X L ∈ cComp (⊤ : Subgroup (O2Q X)) := modO2Image_mem_cComp hL
  have hBbar : modO2Image X B ∈ lFamily (o2Img X T₀) := modO2Image_mem_lFamily hsyl hBX hB
  have hTL : IsSylowTwoOf (o2Img X T₀ ⊓ modO2Image X L) (modO2Image X L) :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL') hsylbar
  have hB1 : modO2Image X B ∈ lFamily (o2Img X T₀ ⊓ modO2Image X L) :=
    cComp_mem_of_le hBbar le_sup_left (sup_le_sup_left inf_le_left _)
  have hAbar : IsAlt 5 (↥(modO2Image X B) ⧸ CFSG.solvableRadical ↥(modO2Image X B)) :=
    A7.isAlt_quot_solvableRadical_of_surj hA (barMap_surjective hBX) (isPGroup_ker_barMap _)
  rcases lemma_1_2_4_list hQ hs hnab h312 hO hsyl hBX hB hL hBL.le with h1 | h1 | h1
  · exact absurd h1 hne
  · exact A314.of_case_F4 h314 ⟨hBbar, hlt, hTL, hB1, hAbar⟩ h1
  · rcases A314.nonquasi_case (h36 _ hQbar _ hL') (A312.not_quasisimple_of_nonquasi h1) hlt
      hAbar h1 with h13 | h14
    · unfold A314Statement
      iterate 12 right
      left
      exact h13
    · unfold A314Statement
      iterate 13 right
      exact h14

end Bar

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem le_Mp_of_conj_F4 (h5114 : Stmt5_1_14_first_F4) {Y : Subgroup G} {a : G}
    (haMp : a ∈ Subgroup.normalizer (oTwoUpper H : Set G)) (hKY : oTwoUpper H ≤ Y)
    (hTY : ∀ y ∈ T, a * y * a⁻¹ ∈ Y) (hO : pCoreOf 2 Y ≠ ⊥) :
    Y ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  have hYQ : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
  have hHQ' : H ≤ Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf (hh.isSylowTwoOf h.hyp.hStar.1.1)]
    refine sup_le (fun k hk => mem_normalizer_map_conj_inv (hYQ (hKY ?_)))
      (fun y hy => mem_normalizer_map_conj_inv (hYQ (hTY y hy)))
    exact (Subgroup.mem_normalizer_iff.mp haMp k).mp hk
  have hQ'1 : (pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom ≠ ⊥ := fun h0 =>
    hO ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj a⁻¹).injective).mp h0)
  have hloc : IsTwoLocal (Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G)) :=
    ⟨_, hQ'1, (pCoreOf_isPGroup 2 Y).map _, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := (h.isUniqueM_F4 h5114).2 M' ⟨hM', hHQ'.trans hle⟩
  intro y hy
  have h1 : a⁻¹ * y * a⁻¹⁻¹ ∈ Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨y, hYQ hy, rfl⟩
  have h2 : a⁻¹ * y * a⁻¹⁻¹ ∈ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [← hM'eq]
    exact hle h1
  have h3 := (Subgroup.normalizer (oTwoUpper H : Set G)).mul_mem
    ((Subgroup.normalizer (oTwoUpper H : Set G)).mul_mem haMp h2)
    ((Subgroup.normalizer (oTwoUpper H : Set G)).inv_mem haMp)
  simpa [mul_assoc] using h3

theorem isSylowTwoOf_T₀_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) {U U' : Subgroup G}
    (hUU' : U ≠ U') (hU : ParData518 T H B D U)
    (hK : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)))
    (hperm : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (U.map (MulAut.conj g).toMonoidHom = U ∨ U.map (MulAut.conj g).toMonoidHom = U') ∧
        (U'.map (MulAut.conj g).toMonoidHom = U ∨ U'.map (MulAut.conj g).toMonoidHom = U'))
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≠ ⊥) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (U : Set G))
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
        (T ⊓ Subgroup.normalizer (U : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hST, -, hTKS, hOMS, -, hSN⟩ := s.S_facts_F4 h510 h331 hR
  obtain ⟨-, -, hUN, -⟩ := hU
  have hTMp := h.T_le_Mp
  have hTTK := s.T_le_normalizer_inf_K
  have hfix : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (g ∈ Subgroup.normalizer (U : Set G) ↔ g ∈ Subgroup.normalizer (U' : Set G)) := by
    intro g hgK hgT
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_eq_iff_of_perm hUU' (hperm g hgK hgT)
  have hswap : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        g ∉ Subgroup.normalizer (U : Set G) → U.map (MulAut.conj g).toMonoidHom = U' := by
    intro g hgK hgT hgU
    rcases (hperm g hgK hgT).1 with h1 | h1
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hgU
    · exact h1
  have hswap' : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        g ∉ Subgroup.normalizer (U : Set G) → U'.map (MulAut.conj g).toMonoidHom = U := by
    intro g hgK hgT hgU
    rcases (hperm g hgK hgT).2 with h1 | h1
    · exact h1
    · exact absurd ((hfix g hgK hgT).mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1)) hgU

  have hST₀ : s518 T H B D ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf hST (le_sup_right.trans hUN)
  have hTKT₀ : T ⊓ oTwoUpper H ≤ T ⊓ Subgroup.normalizer (U : Set G) := hTKS.trans hST₀
  have hT₀2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) :=
    hh.sylow.1.to_le inf_le_left
  have hTT₀ := le_normalizer_inf_normalizer_of_swap (U := U) (U' := U')
    (fun t ht => hfix t (hTMp ht) (hTTK ht)) (fun t ht => hswap t (hTMp ht) (hTTK ht))
  have hT₀1 : T ⊓ Subgroup.normalizer (U : Set G) ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    have hle := hOMS.trans hST₀
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hNT₀ := s.normalizer_le_Mp_F4 h311 h5114 hT₀1 inf_le_left hTKT₀ hTT₀

  have hT₀X : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅ :
        Subgroup G) : Set G) :=
    le_normalizer_sup_of_le
      (fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2)
      (inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN)))
  have hOX : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≤ pCoreOf 2 ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
        sd5 T L H B D D₅) ⊔ (T ⊓ Subgroup.normalizer (U : Set G))) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hT₀X).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  set X₁ := (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
    (T ⊓ Subgroup.normalizer (U : Set G)) with hX₁def
  clear_value X₁
  have hT₀X₁ : T ⊓ Subgroup.normalizer (U : Set G) ≤ X₁ := by rw [hX₁def]; exact le_sup_right
  have hK₂X₁ : oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ≤ X₁ := by
    rw [hX₁def]; exact le_sup_left.trans le_sup_left
  have hD₅X₁ : D₅ ≤ X₁ := by
    rw [hX₁def]
    exact (le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans
      (le_sup_right.trans le_sup_left)
  have hOX₁ : pCoreOf 2 X₁ ≠ ⊥ := by
    intro h0
    apply hO
    rw [h0] at hOX
    exact le_bot_iff.mp hOX

  by_contra hns
  obtain ⟨T₁, hT₁, hT₀T₁⟩ := A4.exists_isSylowTwoOf_ge hT₀X₁ hT₀2
  have hlt : T ⊓ Subgroup.normalizer (U : Set G) < T₁ := by
    refine lt_of_le_of_ne hT₀T₁ (fun heq => hns ?_)
    rw [← heq] at hT₁
    exact hT₁
  obtain ⟨t, htT, htU⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (U : Set G) := by
    by_contra hall
    push Not at hall
    have hTeq : T ⊓ Subgroup.normalizer (U : Set G) = T :=
      le_antisymm inf_le_left (fun x hx => ⟨hx, hall x hx⟩)
    apply hns
    have hTX₁ : T ≤ X₁ := by rw [← hTeq]; exact hT₀X₁
    rw [hTeq]
    exact hh.isSylowTwoOf hTX₁
  have hcT := card_eq_two_mul_of_swap (fun t ht => hswap t (hTMp ht) (hTTK ht))
    (fun t ht => hswap' t (hTMp ht) (hTTK ht)) htT htU
  have hcT₁le : Nat.card T₁ ≤ 2 * Nat.card (T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) := by
    rw [← hcT]
    exact card_le_of_quasithinIsSylowTwo hh.sylow hT₁.2.1
  obtain ⟨hrel2, hcT₁⟩ := relIndex_eq_two_of_lt hlt hT₁.2.1 hcT₁le
  have hT₁N : T₁ ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T₁).mp
      (Subgroup.normal_of_index_eq_two hrel2)
  have hT₁Mp := hT₁N.trans hNT₀
  have hT₀K : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hTKT₀ inf_le_right)
  have hT₁TK : T₁ ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hT₀K]
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hT₁N hx, hT₁Mp hx⟩

  have hTA := hh.isSylowTwoOf (le_inf hTMp hTTK)
  have hT₁A := isSylowTwoOf_of_card_eq hTA (le_inf hT₁Mp hT₁TK) hT₁.2.1 (hcT₁.trans hcT.symm)
  obtain ⟨a, haA, ha⟩ := A4.exists_conj_of_isSylowTwoOf hTA hT₁A
  have hconjT : ∀ y ∈ T, a * y * a⁻¹ ∈ T₁ := fun y hy =>
    (ha _).mpr (by simpa [mul_assoc] using hy)

  have hnot : ¬ T₁ ≤ Subgroup.normalizer (U : Set G) := by
    intro hT₁U
    have hTUa : T ≤ Subgroup.normalizer
        ((U.map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_map_conj_inv (hT₁U (hconjT y hy))
    rcases (hperm a⁻¹ (inv_mem haA.1) (inv_mem haA.2)).1 with h1 | h1
    · rw [h1] at hTUa
      exact htU (hTUa htT)
    · rw [h1] at hTUa
      exact htU ((hfix t (hTMp htT) (hTTK htT)).mpr (hTUa htT))
  obtain ⟨t₁, ht₁T₁, ht₁U⟩ := Set.not_subset.mp hnot

  have hKX₁ := K_le_of_swap (hT₁Mp ht₁T₁) (hT₁.1 ht₁T₁)
    (hswap t₁ (hT₁Mp ht₁T₁) (hT₁TK ht₁T₁) ht₁U) hK hK₂X₁
  have hX₁Mp := s.le_Mp_of_conj_F4 h5114 haA.1 hKX₁ (fun y hy => hT₁.1 (hconjT y hy)) hOX₁
  exact s.D₅_not_le (hD₅X₁.trans hX₁Mp)

theorem D₅_le_normalizer_of_sylow_F4 (hF : L2TorusFact)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts_F4) (hFive : A314FiveNormFact) {U X₁ : Subgroup G}
    (hU : ParData518 T H B D U)
    (hX₁ : X₁ = (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ⊔ (T ⊓ Subgroup.normalizer (U : Set G)))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (U : Set G)) X₁) (hO : pCoreOf 2 X₁ ≠ ⊥) :
    D₅ ≤ Subgroup.normalizer
      (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hT₀K₂, hlfam, hA5, hBK₂, hBT₀⟩ := s.parabolic_facts_F4 h510 h331 hR hU
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  set T₀ := T ⊓ Subgroup.normalizer (U : Set G) with hT₀def
  have hK₂X₁ : K₂ ≤ X₁ := by rw [hX₁]; exact le_sup_left.trans le_sup_left
  have hT₀X₁ : T₀ ≤ X₁ := hsyl.1
  have hD₅X₁ : D₅ ≤ X₁ := by
    rw [hX₁]
    exact (le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans
      (le_sup_right.trans le_sup_left)
  have hperf : ⁅K₂, K₂⁆ = K₂ := perfect_of_mem_cComp hlfam
  have hOT₀ : pCoreOf 2 X₁ ≤ T₀ := F7.isSylowTwoOf_pCoreOf_le hsyl

  obtain ⟨KX, hKX, hK₂KX⟩ := lemma_1_2_4_exists hh.qtke hh.simple hh.nonabelian h37 h39 hO hsyl
    hK₂X₁ hlfam
  have hnorm := lemma_1_2_4_normal hh.qtke hh.simple hh.nonabelian h37 h38 hO hsyl hlfam hK₂KX
    hKX hT₀K₂
  have hX₁KX : X₁ ≤ Subgroup.normalizer (KX : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKX)).mp hnorm
  rcases eq_or_lt_of_le hK₂KX with heq | hlt
  · rw [heq]
    exact hD₅X₁.trans hX₁KX
  obtain ⟨hltbar, h314bar⟩ := a314Statement_bar_F4 hh.qtke hh.simple hh.nonabelian h36 h312 h314
    hO hsyl hK₂X₁ hlfam hKX hlt hT₀K₂ hA5

  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hh.qtke hh.simple hh.nonabelian hO
  have hsylbar : IsSylowTwoOf (o2Img X₁ T₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hBbar := modO2Image_mem_lFamily hsyl hK₂X₁ hlfam
  have hA5bar : IsAlt 5 (ModO2 (modO2Image X₁ K₂)) := by
    obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hK₂X₁
    obtain ⟨e2⟩ := hA5
    exact ⟨e1.symm.trans e2⟩
  have hLbar := modO2Image_mem_cComp hKX

  have hD5card : Nat.card (modO2Image X₁ D₅) = 5 := by
    have hker : (barMap hD₅X₁).ker = ⊥ := by
      have h2 := isPGroup_ker_barMap hD₅X₁
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      have hdvd : 2 ^ k ∣ 5 := hk ▸ s.card_D₅ ▸ Subgroup.card_subgroup_dvd_card _
      have hk0 : k = 0 := by
        rcases k with _ | k
        · rfl
        · exfalso
          rw [pow_succ] at hdvd
          have : 2 ∣ 5 := (dvd_mul_left 2 (2 ^ k)).trans hdvd
          omega
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hinj : Function.Injective (barMap hD₅X₁) := (MonoidHom.ker_eq_bot_iff _).mp hker
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, barMap_surjective hD₅X₁⟩), s.card_D₅]
  have hD5N : modO2Image X₁ D₅ ≤
      Subgroup.normalizer ((modO2Image X₁ KX : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨d, -, rfl⟩
    exact o2Map_mem_normalizer (hX₁KX d.2)
  have hT0N : o2Img X₁ T₀ ≤
      Subgroup.normalizer ((modO2Image X₁ KX : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨t, -, rfl⟩
    exact o2Map_mem_normalizer (hX₁KX t.2)
  have hT0B : o2Img X₁ T₀ ≤
      Subgroup.normalizer ((modO2Image X₁ K₂ : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (hT₀K₂ (Subgroup.mem_subgroupOf.mp ht))

  obtain ⟨hST, hTLS, -, -, -, -⟩ := s.S_facts_F4 h510 h331 hR
  have hTLT₀ : T ⊓ L ≤ T₀ := hTLS.trans (le_inf hST (le_sup_right.trans hU.2.2.1))
  have hZT := s.T_le_normalizer_z518 hF
  have hDN := s.D₅_le_normalizer_inf
  have hset1 : ((z518 T L D₅ : Subgroup G) : Set G) =
      (D₅ : Set G) * ((T ⊓ L : Subgroup G) : Set G) := by
    rw [z518, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D₅ (T ⊓ L) hDN
  have hset2 : ((z518 T L D₅ : Subgroup G) : Set G) =
      ((T ⊓ L : Subgroup G) : Set G) * (D₅ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) D₅ hDN
  have h₁ : ∀ a ∈ D₅, ∀ c ∈ T₀, ∃ a' ∈ D₅, ∃ c' ∈ T₀, c * a = a' * c' := by
    intro a ha c hc
    have hca : c * a * c⁻¹ ∈ ((z518 T L D₅ : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hZT hc.1) a).mp (Subgroup.mem_sup_right ha)
    rw [hset1] at hca
    obtain ⟨a', ha', l, hl, hal⟩ := hca
    have hal' : a' * l = c * a * c⁻¹ := hal
    refine ⟨a', ha', l * c, T₀.mul_mem (hTLT₀ hl) hc, ?_⟩
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = (a' * l) * c := by rw [← hal']
      _ = a' * (l * c) := by group
  have h₂ : ∀ a ∈ D₅, ∀ c ∈ T₀, ∃ c' ∈ T₀, ∃ a' ∈ D₅, a * c = c' * a' := by
    intro a ha c hc
    have hca : c⁻¹ * a * c⁻¹⁻¹ ∈ ((z518 T L D₅ : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hZT (T.inv_mem hc.1)) a).mp (Subgroup.mem_sup_right ha)
    rw [hset2] at hca
    obtain ⟨l, hl, a', ha', hla⟩ := hca
    have hla' : l * a' = c⁻¹ * a * c⁻¹⁻¹ := hla
    refine ⟨c * l, T₀.mul_mem hc (hTLT₀ hl), a', ha', ?_⟩
    calc a * c = c * (c⁻¹ * a * c⁻¹⁻¹) := by group
      _ = c * (l * a') := by rw [← hla']
      _ = c * l * a' := by group
  have hDT := modO2Image_set_mul_comm hD₅X₁ hT₀X₁ h₁ h₂

  have hB3 : Nat.card B = 3 := h.card_B_eq_three_F4 h510
  obtain ⟨⟨b, hbB⟩, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  have hb3' : orderOf b = 3 := by rw [← Subgroup.orderOf_mk b hbB]; exact hb3
  have hbX₁ : b ∈ X₁ := hK₂X₁ (hBK₂ hbB)
  have hBD : B ≤ Subgroup.normalizer (D₅ : Set G) := fun x hx =>
    mem_normalizer_of_le_isCyclic (s.isCyclic_D hF) s.D₅_le (h.notation59.2.2 hx)
  have hBC := le_centralizer_of_card_three_of_card_five hB3 s.card_D₅ hBD
  have hb : ∃ y ∈ modO2Image X₁ K₂, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer ((o2Img X₁ T₀ ⊓ modO2Image X₁ K₂ : Subgroup (O2Q X₁)) :
        Set (O2Q X₁)) ∧ ∀ d ∈ modO2Image X₁ D₅, d * y = y * d := by
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩, ⟨⟨b, hbX₁⟩, hBK₂ hbB, rfl⟩, ?_,
      ?_, ?_⟩
    · have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨b, hbX₁⟩ : ↥X₁) ^ 3 = 1 := Subtype.ext (by simp [← hb3', pow_orderOf_eq_one])
        rw [this, map_one]
      have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩ ≠ 1 := by
        intro h0
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X₁)) ⟨_, h0⟩
        have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val (congrArg Subtype.val hk)
        have := orderOf_dvd_of_pow_eq_one hbk
        rw [hb3'] at this
        have h3 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
        omega
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hne
      · exact h'
    · show _ ∈ Subgroup.normalizer ((modO2Image X₁ T₀ ⊓ modO2Image X₁ K₂ :
        Subgroup (O2Q X₁)) : Set (O2Q X₁))
      rw [← modO2Image_inf_eq hOT₀]
      exact o2Map_mem_normalizer (hBT₀ hbB)
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hc := hBC hbB
      exact (Subgroup.mem_centralizer_iff.mp hc d (Subgroup.mem_subgroupOf.mp hd))
  have hDK := hFive (O2Q X₁) hQbar (o2Img X₁ T₀) (modO2Image X₁ K₂) (modO2Image X₁ KX)
    (modO2Image X₁ D₅) hsylbar hBbar hA5bar hLbar hltbar h314bar hD5card hD5N hT0N hT0B hDT hb
  intro d hd
  exact mem_normalizer_of_mk_mem_normalizer hK₂X₁ hperf (hOT₀.trans hT₀K₂) (hD₅X₁ hd)
    (hDK ⟨⟨d, hD₅X₁ hd⟩, hd, rfl⟩)

theorem D₅_le_normalizer_parabolic_F4 (hF : L2TorusFact)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hDSC : DSCStatement_F4) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts_F4)
    (hFive : A314FiveNormFact) {U U' : Subgroup G} (hUU' : U ≠ U')
    (hU : ParData518 T H B D U)
    (hK : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)))
    (hperm : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (U.map (MulAut.conj g).toMonoidHom = U ∨ U.map (MulAut.conj g).toMonoidHom = U') ∧
        (U'.map (MulAut.conj g).toMonoidHom = U ∨ U'.map (MulAut.conj g).toMonoidHom = U')) :
    D₅ ≤ Subgroup.normalizer
      (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) := by
  by_cases hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) = ⊥
  · exact (s.false_of_pCoreOf_eq_bot_F4 hF h311 h5114 h510 h331 hR hDSC hU hO).elim
  · exact s.D₅_le_normalizer_of_sylow_F4 hF h510 h331 hR h36 h37 h38 h39 h312 h314 hFive hU rfl
      (s.isSylowTwoOf_T₀_F4 hF h311 h5114 h510 h331 hR hUU' hU hK hperm hO)
      (s.pCoreOf_X₁_ne_bot_F4 hF h510 h331 hR hO)

theorem false_of_setting_F4 (hTP : L34TwoParabolicFact)
    (hTA : L34TwoAutFact) (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hDSC : DSCStatement_F4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts_F4) (hFive : A314FiveNormFact) : False := by
  obtain ⟨U₂, U₃, hne, hpar, hK, hperm⟩ := s.exists_two_parabolics_F4 hTP hTA h510 h331 hR
  have h2 := s.D₅_le_normalizer_parabolic_F4 hF h311 h5114 h510 h331 hR hDSC h36 h37 h38 h39 h312
    h314 hFive hne (hpar U₂ (Or.inl rfl)) hK hperm
  have hK' : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) := by
    rw [sup_comm]
    exact hK
  have h3 := s.D₅_le_normalizer_parabolic_F4 hF h311 h5114 h510 h331 hR hDSC h36 h37 h38 h39 h312
    h314 hFive hne.symm (hpar U₃ (Or.inr rfl)) hK'
    (fun g hg1 hg2 => ⟨(hperm g hg1 hg2).2.symm, (hperm g hg1 hg2).1.symm⟩)
  have hJ : oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) = oTwoUpper H :=
    le_antisymm (sup_le ((oTwoUpper_le _).trans inf_le_left)
      ((oTwoUpper_le _).trans inf_le_left)) hK
  apply s.D₅_not_le
  have h23 := le_normalizer_sup_of_le h2 h3
  rw [hJ] at h23
  exact h23

end Setting518D5

theorem stmt5_1_18_D5_of_inputs_F4 (hTP : L34TwoParabolicFact)
    (hTA : L34TwoAutFact) (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_16_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hDSC : DSCStatement_F4) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts_F4) (hFive : A314FiveNormFact) :
    Stmt5_1_18_D5_F4 := by
  intro G _ _ T M L V H B D n h _ D₃ hD₃ h3 hD₃M hne _ D₅ hD₅ h5
  by_contra hD5
  by_cases hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)
  · exact hne (h.eq_B_of_inner_F4 hF h510 h516 hD₃ h3 hD₃M hin)
  · push Not at hin
    exact (Setting518D5.mk h hD₃ h3 hD₃M hin hD₅ h5 hD5).false_of_setting_F4 hTP hTA hF h311 h5114
      h510 h331 hR hDSC h36 h37 h38 h39 h312 h314 hFive

end Setting

end CFSG.Quasithin.H13
