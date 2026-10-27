module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5TS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5SS331
public import CFSG.Quasithin.Background.C2PushY

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem D₅_not_le_normalizer_S_F4 (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    ¬ D₅ ≤ Subgroup.normalizer (s518 T H B D : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨hST, -, hTKS, hOMS, -, hSN⟩ := s.S_facts_F4 h510 h331 hR
  have hS1 : s518 T H B D ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    exact le_bot_iff.mp (h0 ▸ hOMS)
  have hNS := s.normalizer_le_Mp_F4 h311 h5114 hS1 hST hTKS (le_sup_right.trans hSN)
  exact fun h => s.D₅_not_le (h.trans hNS)

theorem sd5_facts_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    IsSylowTwoOf (s518 T H B D) (sd5 T L H B D D₅) ∧
      (s518 T H B D).relIndex (sd5 T L H B D D₅) = 5 ∧
      (Nonempty (OTwoQuot (sd5 T L H B D D₅) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (sd5 T L H B D D₅) ≃* ↥(CFSG.Open.Sz 0))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hST, hTLS, -, -, -, -⟩ := s.S_facts_F4 h510 h331 hR
  have hS2 : IsPGroup 2 (s518 T H B D) := pCoreOf_isPGroup 2 _
  have hSZ : s518 T H B D ≤ Subgroup.normalizer (z518 T L D₅ : Set G) :=
    hST.trans (s.T_le_normalizer_z518 hF)
  have hO := s.pCoreOf_z518
  refine He9.oTwoQuot_sup_iso hS2 hSZ (by rw [hO]; exact s.relIndex_z518)
    (by rw [hO]; exact hTLS) ?_
  by_contra hcon
  push Not at hcon
  apply s.D₅_not_le_normalizer_S_F4 h311 h5114 h510 h331 hR
  intro d hd
  have hdZ : d ∈ z518 T L D₅ := Subgroup.mem_sup_right hd
  have hconj : ∀ d ∈ z518 T L D₅, ∀ x ∈ s518 T H B D, d * x * d⁻¹ ∈ s518 T H B D := by
    intro d hd x hx
    have h1 : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ ∈ s518 T H B D := by
      have := hcon x⁻¹ ((s518 T H B D).inv_mem hx) d hd
      rw [hO] at this
      exact hTLS this
    have h2 := (s518 T H B D).mul_mem hx h1
    simpa [mul_assoc] using h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj d hdZ x hx, fun hx => ?_⟩
  have := hconj d⁻¹ ((z518 T L D₅).inv_mem hdZ) _ hx
  simpa [mul_assoc] using this

theorem borelOf_sd5_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    borelOf (sd5 T L H B D D₅) (s518 T H B D) = s518 T H B D := by
  obtain ⟨-, hidx, -⟩ := s.sd5_facts_F4 hF h311 h5114 h510 h331 hR
  have hSY : s518 T H B D ≤ sd5 T L H B D D₅ := le_sup_right
  have hinf : s518 T H B D ⊓ sd5 T L H B D D₅ = s518 T H B D := inf_eq_left.mpr hSY
  unfold borelOf
  rw [hinf]
  set Nn := sd5 T L H B D D₅ ⊓ Subgroup.normalizer (s518 T H B D : Set G) with hNn
  have hSN : s518 T H B D ≤ Nn := le_inf hSY Subgroup.le_normalizer
  have hNY : Nn ≤ sd5 T L H B D D₅ := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hSN hNY
  rw [hidx] at hmul
  have hdvd : (s518 T H B D).relIndex Nn ∣ 5 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSN
  · exfalso
    rw [h5] at hmul
    have h1 : Nn.relIndex (sd5 T L H B D D₅) = 1 := by omega
    have hYN := Subgroup.relIndex_eq_one.mp h1
    apply s.D₅_not_le_normalizer_S_F4 h311 h5114 h510 h331 hR
    exact ((le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans hYN).trans
      inf_le_right

theorem false_of_pCoreOf_eq_bot_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt)
    (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hDSC : DSCStatement_F4) {U : Subgroup G} (hU : ParData518 T H B D U)
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set S := s518 T H B D with hSdef
  set Y := sd5 T L H B D D₅ with hYdef
  obtain ⟨hST, -, hTKS, hOMS, hOMpS, hSN⟩ := s.S_facts_F4 h510 h331 hR
  obtain ⟨-, hUTK, hUN, φ, hφs, hφk⟩ := hU
  have hTK := h.isSylowTwoOf_inf_K
  have hTKN : T ⊓ K ≤ Subgroup.normalizer (U : Set G) := hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, hnsK₂, -, hTK₂, hBorK₂⟩ := oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  set K₂ := oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  have hK₂K : K₂ ≤ K := (oTwoUpper_le _).trans inf_le_left
  have hTMp := h.T_le_Mp
  have hSMp : S ≤ Subgroup.normalizer (K : Set G) := hST.trans hTMp
  have hSK₂ : S ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hSMp hx) (hUN (Subgroup.mem_sup_right hx))
  have hSK₂eq : S ⊓ K₂ = T ⊓ K₂ :=
    le_antisymm (inf_le_inf_right _ hST)
      (le_inf ((inf_le_inf_left T hK₂K).trans hTKS) inf_le_right)

  obtain ⟨hSY, -, hiso⟩ := s.sd5_facts_F4 hF h311 h5114 h510 h331 hR
  have hborY := s.borelOf_sd5_F4 hF h311 h5114 h510 h331 hR
  have hSYle : S ≤ Y := le_sup_right
  have hSYeq : S ⊓ Y = S := inf_eq_left.mpr hSYle

  obtain ⟨-, -, hBorel, hBhall, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTKM : IsSylowTwoOf (T ⊓ K) (M ⊓ K) :=
    A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ hh.T_le) inf_le_right
  have hMKeq : B ⊔ (T ⊓ K) = M ⊓ K := sup_eq_of_isHall_isSylow hBhall hTKM
  have hYN : M ⊓ K ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hMKeq]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_le (s.B_le_normalizer_z518_F4 hF h331 hR)
        ((le_sup_right.trans le_sup_left).trans hSN)
    · exact inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN))
  have hBorK₂M : borelOf K₂ S ≤ M ⊓ K := by
    intro x hx
    have hx2 : x ∈ Subgroup.normalizer ((T ⊓ K₂ : Subgroup G) : Set G) := by
      have hx' := hx.2
      rw [hSK₂eq] at hx'
      exact hx'
    rw [hMK]
    exact ⟨hK₂K hx.1, hBorK₂ ⟨hx.1, hx2⟩⟩

  have hcharM : CharTwo M :=
    charTwo_of_inH' hh.qtke hh.sylow ⟨hh.T_le, pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1⟩
  have hcharMp := h.charTwo_Mp_F4 h5114
  have hDM : D₅ ≤ M := s.D₅_le.trans (s.hyp.notation59.2.1.1.trans (inf_le_left.trans hh.L_le))
  have hYM : Y ≤ M :=
    sup_le (sup_le (inf_le_left.trans hh.T_le) hDM) (hST.trans hh.T_le)
  have hc1 : CharTwo (K₂ ⊔ S ⊔ borelOf Y S) := by
    rw [hborY]
    refine C2Push.charTwo_of_pCoreOf_le hcharMp (hOMpS.trans (le_sup_right.trans le_sup_left)) ?_
    exact sup_le (sup_le (hK₂K.trans Subgroup.le_normalizer) hSMp) hSMp
  have hc2 : CharTwo (Y ⊔ S ⊔ borelOf K₂ S) :=
    C2Push.charTwo_of_pCoreOf_le hcharM (hOMS.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le hYM (hST.trans hh.T_le)) (hBorK₂M.trans inf_le_left))

  have hlistK₂ : IsRankOneListed (oTwoQuot ↥K₂) := Or.inl ⟨2, by norm_num, hL2K₂⟩
  have hiso' : Nonempty (oTwoQuot ↥Y ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥Y ≃* ↥(Sz 0)) :=
    hiso
  have hlistY : IsRankOneListed (oTwoQuot ↥Y) := by
    rcases hiso' with h1 | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
    · exact Or.inr (Or.inl ⟨0, h1⟩)
  have hhyp : Hyp111 K₂ Y S := by
    refine ⟨⟨inferInstance, pCoreOf_isPGroup 2 _, hSK₂, by rw [hSK₂eq]; exact hTK₂, hlistK₂, ?_,
      hc1⟩, ⟨inferInstance, pCoreOf_isPGroup 2 _, hSYle.trans Subgroup.le_normalizer,
        by rw [hSYeq]; exact hSY, hlistY, hBorK₂M.trans hYN, hc2⟩, ?_⟩
    · rw [hborY]
      exact hSK₂
    · rw [sup_eq_left.mpr (hSYle.trans le_sup_right)]
      exact hO
  have hqt : IsQuasithinSub (K₂ ⊔ Y ⊔ S) := by
    intro p hp hp2 R _ hR' hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR', hR2, rfl⟩)
  have hnorm : (S.subgroupOf (S ⊔ borelOf Y S)).Normal := by
    rw [hborY, sup_idem, Subgroup.subgroupOf_self]
    infer_instance
  exact hDSC G K₂ Y S hhyp hqt (Or.inr hnorm) hnsK₂ hiso'

end Setting518D5

end Setting

end CFSG.Quasithin.H13
