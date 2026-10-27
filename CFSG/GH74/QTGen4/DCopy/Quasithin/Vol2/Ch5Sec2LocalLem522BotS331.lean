module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem524
public import CFSG.Quasithin.Background.Harris.F112S3Big.Defs
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522Bot

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.Background.Harris.F112S3Big

@[expose] def Stmt5_2_2_bot_list_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    ∀ L1' L2' : Subgroup G,
      ((L1' = L₂ ∧ L2' = Dp ⊔ sec52S M H) ∨ (L1' = Dp ⊔ sec52S M H ∧ L2' = L₂)) →
      Hyp111 L1' L2' (sec52S M H) →
      (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
          centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
        centerOf (sec52S M H) ≤ Subgroup.centralizer (L1' : Set G)) →
      F112ListBLoc L1' L2' (sec52S M H) → False

namespace Hyp5_2_2p

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}
  (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
include hyp

theorem S_facts_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    sec52S M H ≤ T ∧ T ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
      B ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
      sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H ∧ sec52S M H ⊓ L = T ⊓ L ∧
      sec52S M H ⊓ L₂ = T ⊓ L₂ ∧ pCoreOf 2 M ≤ sec52S M H ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ sec52S M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨-, -, hBorel, -, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  set S := sec52S M H with hSdef
  have hTMH : T ≤ M ⊓ H := le_inf h.T_le hH.1.1
  have hST : S ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTMH)
  have hMHN : M ⊓ H ≤ Subgroup.normalizer (S : Set G) := le_normalizer_pCoreOf 2 _
  have hSK : S ⊓ oTwoUpper H = T ⊓ oTwoUpper H := hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hL₂K := hyp.choice.le_oTwoUpper
  have hSL₂ : S ⊓ L₂ = T ⊓ L₂ := by
    rw [← inf_eq_right.mpr hL₂K, ← inf_assoc, hSK, inf_assoc]
  have hO2le : ∀ X : Subgroup G, T ≤ X → M ⊓ H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) →
      pCoreOf 2 X ≤ S := by
    intro X hTX hMHX
    have hXT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTX)
    exact le_pCoreOf_of_le_normalizer 2 (hXT.trans hTMH) hMHX (pCoreOf_isPGroup 2 X)
  have hHMp : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  refine ⟨hST, hTMH.trans hMHN, hyp.notation59.1.1.trans hMHN, hSK, h.inf_L_eq_F4 h331 hR hH,
    hSL₂, hO2le M h.T_le (inf_le_left.trans (le_normalizer_pCoreOf 2 M)), ?_⟩
  exact hO2le _ (hH.1.1.trans hHMp) ((inf_le_right.trans hHMp).trans (le_normalizer_pCoreOf 2 _))

theorem B_le_normalizer_Y_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) :
    B ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := by
  have hh := hyp.toHyp5_0_1
  obtain ⟨-, -, hBS, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
  have hBL : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [← hSL]
    exact fun b hb =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hBS hb, hh.normal (hBM hb)⟩
  have hBD : B ≤ Subgroup.normalizer (Dp : Set G) := fun b hb =>
    mem_normalizer_of_le_of_isCyclic (hyp.isCyclic_D hF) hyp.Dp_le (hyp.notation59.2.2 hb)
  exact le_normalizer_sup_of_le_of_le hBL hBD

theorem Dp_not_le_normalizer_F4 (h311 : Theorem311Stmt) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    ¬ Dp ≤ Subgroup.normalizer (sec52S M H : Set G) := by
  intro hDpS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hST, hTS, -, hSK, -, -, hOMS, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hS1 : S ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    exact le_bot_iff.mp (h0 ▸ hOMS)
  have hO' : pCoreOf 2 (Subgroup.normalizer (S : Set G)) ≠ ⊥ := by
    intro h0
    apply hS1
    have hle : S ≤ pCoreOf 2 (Subgroup.normalizer (S : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hS2
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hM₀ : InH T (Subgroup.normalizer (S : Set G)) := ⟨hTS, hO'⟩
  have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
    obtain ⟨P, hP⟩ := exists_sylow_coe_eq hh.sylow
    have hstar : IsHStar (P : Subgroup G) M H := hP ▸ hyp.hStar
    have hTM : (P : Subgroup G) ≤ M := hP ▸ hh.T_le
    exact ⟨H ⊓ M, hP ▸ hstar.isUniqueMaxOver P hTM⟩
  have hTKn : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hTS' : IsSylowTwoOf T (oTwoUpper H ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hRS : IsSylowTwoOf S (oTwoUpper H ⊔ S) :=
    isSylowTwoOf_sup_of_inf_le hST hTKn (by rw [inf_comm, ← hSK]; exact inf_le_left) hTS'
  obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := h311 G T hh.simple hh.nonabelian hh.qtke hh.sylow _ H S
    hM₀ hyp.hStar.1 hu hS1 hST hRS le_rfl
  apply hR₀1
  have hHN : H ≤ Subgroup.normalizer (R₀ : Set G) := le_sup_right.trans hR₀N
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hG₀N : Dp ⊔ (L₂ ⊔ S) ≤ Subgroup.normalizer (R₀ : Set G) :=
    sup_le (hDpS.trans (le_sup_left.trans hR₀N))
      (sup_le ((hyp.choice.le_oTwoUpper.trans (oTwoUpper_le H)).trans hHN) (hSH.trans hHN))
  have hle : R₀ ≤ pCoreOf 2 (Dp ⊔ (L₂ ⊔ S)) :=
    le_pCoreOf_of_le_normalizer 2 (hR₀R.trans (le_sup_right.trans le_sup_right)) hG₀N
      (hS2.to_le hR₀R)
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem sup_Y_eq_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    (T ⊓ L) ⊔ Dp ⊔ sec52S M H = Dp ⊔ sec52S M H := by
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hTLS : T ⊓ L ≤ sec52S M H := hSL ▸ inf_le_left
  apply le_antisymm
  · exact sup_le (sup_le (hTLS.trans le_sup_right) le_sup_left) le_sup_right
  · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem SDp_facts_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    IsSylowTwoOf (sec52S M H) (Dp ⊔ sec52S M H) ∧ (sec52S M H).relIndex (Dp ⊔ sec52S M H) = p ∧
      (p = 3 → Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3))) ∧
      (p = 5 → Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* DihedralGroup 5) ∨
        Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* ↥(Sz 0))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec52S M H with hSdef
  set Y := (T ⊓ L) ⊔ Dp with hYdef
  obtain ⟨hST, hTS, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hST.trans (hyp.T_le_normalizer_Y hF)
  have hOY := hyp.pCoreOf_Y
  have hYidx : (pCoreOf 2 Y).relIndex Y = p := by rw [hOY]; exact hyp.relIndex_Y
  have hOS : pCoreOf 2 Y ≤ S := by rw [hOY]; exact hTLS
  have hnt : ∃ r ∈ S, ∃ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
    by_contra hcon
    push Not at hcon
    apply hyp.Dp_not_le_normalizer_F4 h311 h510 h331 hR hO
    intro d hd
    have hdY : d ∈ Y := Subgroup.mem_sup_right hd
    have hconj : ∀ d ∈ Y, ∀ x ∈ S, d * x * d⁻¹ ∈ S := by
      intro d hd x hx
      have h1 : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ ∈ S := hOS (hcon x⁻¹ (S.inv_mem hx) d hd)
      have h2 := S.mul_mem hx h1
      simpa [mul_assoc] using h2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj d hdY x hx, fun hx => ?_⟩
    have := hconj d⁻¹ (Y.inv_mem hdY) _ hx
    simpa [mul_assoc] using this
  have heq := hyp.sup_Y_eq_F4 h510 h331 hR
  rw [← hYdef] at heq
  rcases hyp.p_cases with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := oTwoQuot_sup_iso_three hS2 hSY hYidx hOS hnt
    rw [heq] at h1 h2 h3
    exact ⟨h1, h2, fun _ => h3, fun h => absurd h (by norm_num)⟩
  · obtain ⟨h1, h2, h3⟩ := He9.oTwoQuot_sup_iso hS2 hSY hYidx hOS hnt
    rw [heq] at h1 h2 h3
    exact ⟨h1, h2, fun h => absurd h (by norm_num), fun _ => h3⟩

theorem hyp111_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) (hLie : Stmt5_2_L2Lie_F4)
    (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) ∧ borelOf (Dp ⊔ sec52S M H) (sec52S M H) =
      sec52S M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  have hN := hyp.notation59
  set S := sec52S M H with hSdef
  set Q₁ := Dp ⊔ S with hQ₁def
  obtain ⟨hST, hTS, hBS, -, hSL, hSL₂, hOMS, hOMpS⟩ := hyp.S_facts_F4 h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  obtain ⟨hsyl, hidx, h3, h5⟩ := hyp.SDp_facts_F4 hF h311 h510 h331 hR hO
  have hnn : ¬ Q₁ ≤ Subgroup.normalizer (S : Set G) := fun hle =>
    hyp.Dp_not_le_normalizer_F4 h311 h510 h331 hR hO (le_sup_left.trans hle)
  have hborQ : borelOf Q₁ S = S :=
    borelOf_eq_of_relIndex_prime le_sup_right hyp.prime_p hidx hnn
  obtain ⟨hlist, hbor, -⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  obtain ⟨hTL₂, -⟩ := hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hL₂K := hyp.choice.le_oTwoUpper
  have hborL₂ : borelOf L₂ S = borelOf L₂ T := by
    unfold borelOf
    rw [hSL₂]
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  have hHMp : H ≤ Mp := le_normalizer_oTwoUpper H
  have hMchar : CharTwo M :=
    charTwo_of_inH' h.qtke h.sylow (inH_of_inM ⟨h.maxTwoLocal, h.T_le⟩)
  have hMpO : pCoreOf 2 Mp ≠ ⊥ := by
    intro h0
    apply hyp.toHyp5_1_8.pCoreOf_oTwoUpper_ne_bot
    have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 Mp :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans Subgroup.le_normalizer)
        (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)) (pCoreOf_isPGroup 2 _)
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hMpchar : CharTwo Mp := charTwo_of_inH' h.qtke h.sylow ⟨hH.1.1.trans hHMp, hMpO⟩
  obtain ⟨-, -, hBorel, hBhall, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf hH.1.1) (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hTKM : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ h.T_le) inf_le_right
  have hMKeq : B ⊔ (T ⊓ oTwoUpper H) = M ⊓ oTwoUpper H := sup_eq_of_isHall_isSylow hBhall hTKM
  have hQeq : (T ⊓ L) ⊔ Dp ⊔ S = Q₁ := hyp.sup_Y_eq_F4 h510 h331 hR
  have hTQ : T ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hQeq]
    exact le_normalizer_sup_of_le_of_le (hyp.T_le_normalizer_Y hF) hTS
  have hBQ : B ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hQeq]
    exact le_normalizer_sup_of_le_of_le (hyp.B_le_normalizer_Y_F4 hF h510 h331 hR) hBS
  have hMKQ : M ⊓ oTwoUpper H ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hMKeq]
    exact sup_le hBQ (inf_le_left.trans hTQ)
  have hborL₂M : borelOf L₂ S ≤ M ⊓ oTwoUpper H := by
    rw [hborL₂]
    exact le_inf hbor (inf_le_left.trans hL₂K)
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hDpM : Dp ≤ M := hyp.Dp_le.trans (hN.2.1.1.trans (inf_le_left.trans h.L_le))
  have hc1 : CharTwo (L₂ ⊔ S ⊔ borelOf Q₁ S) := by
    rw [hborQ]
    refine charTwo_of_pCore_centralizer_le hMpchar ?_
      (inf_le_left.trans (hOMpS.trans (le_sup_right.trans le_sup_left)))
    exact sup_le (sup_le (hL₂K.trans Subgroup.le_normalizer) (hSH.trans hHMp)) (hSH.trans hHMp)
  have hc2 : CharTwo (Q₁ ⊔ S ⊔ borelOf L₂ S) := by
    refine charTwo_of_pCore_centralizer_le hMchar ?_
      (inf_le_left.trans (hOMS.trans (le_sup_right.trans le_sup_left)))
    exact sup_le (sup_le (sup_le hDpM hSM) hSM) (hborL₂M.trans inf_le_left)
  have hlistQ : IsRankOneListed (oTwoQuot ↥Q₁) := by
    rcases hyp.p_cases with hp | hp
    · obtain ⟨e⟩ := h3 hp
      exact isRankOneListed_perm_three e
    · rcases h5 hp with he | he
      · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
      · exact Or.inr (Or.inl ⟨0, he⟩)
  have hSQ : S ≤ Q₁ := le_sup_right
  have hSQeq : S ⊓ Q₁ = S := inf_eq_left.mpr hSQ
  refine ⟨⟨⟨inferInstance, hS2, hyp.S_le, by rw [hSL₂]; exact hTL₂, hlist, ?_, hc1⟩,
    ⟨inferInstance, hS2, hSQ.trans Subgroup.le_normalizer, by rw [hSQeq]; exact hsyl, hlistQ,
      hborL₂M.trans hMKQ, hc2⟩, ?_⟩, hborQ⟩
  · rw [hborQ]
    exact hyp.S_le
  · have e : L₂ ⊔ Q₁ ⊔ S = Dp ⊔ (L₂ ⊔ S) := by
      rw [hQ₁def]
      apply le_antisymm
      · exact sup_le (sup_le (le_sup_left.trans le_sup_right)
          (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
          (le_sup_right.trans le_sup_right)
      · exact sup_le (le_sup_left.trans (le_sup_right.trans le_sup_left))
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    rw [e]
    exact hO

end Hyp5_2_2p

end CFSG.Quasithin.H13
