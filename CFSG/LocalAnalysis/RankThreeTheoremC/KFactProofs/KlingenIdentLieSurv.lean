module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.RankThree.PartOne.K1214.SylowShape
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieRows
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Emb
import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
import CFSG.RankThree.PartOne.K1214.SylowSp4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.RankThree.PartOne.K1214

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y} {K : Subgroup Y}

theorem comm_inf_of_sylowShape {r e : ℕ} (hsh : SylowShape p r e K) (T : Sylow p K)
    (hT : (T : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K) :
    ∀ a ∈ (Rb : Subgroup Y) ⊓ K, ∀ b ∈ (Rb : Subgroup Y) ⊓ K, a * b = b * a := by
  obtain ⟨f⟩ := hsh (T : Subgroup K) T.isPGroup' T.not_dvd_index
  intro a ha b hb
  rw [← hT] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have h : (⟨a', ha'⟩ : (T : Subgroup K)) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := by
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact congrArg (fun x : (T : Subgroup K) => ((x : K) : Y)) h

theorem sylowShape_sp48 {X : Type} [Group X] [Finite X] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpFourEightIndex d) (e : X ≃* CatGroup d) : SylowShape 3 2 2 X := by
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  simp only at hdq
  subst hdq
  have hm : StatedClassicalModel X .PSp 2 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hq2, hq3] at hm
  exact sylowShape_of_psp4Model (f := 3) (p := 3) (e := 2) (m := 1) Nat.prime_three
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm

theorem sp48_false (hSchur : KFactChevTwoSurvivorSchur) (hred : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hkl : HasKlingenData p Rb Y₀) (hp3 : p = 3) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpFourEightIndex d) (e₁ : K ⧸ Subgroup.center K ≃* CatGroup d) : False := by
  subst hp3
  have hZ : Subgroup.center K = ⊥ :=
    hSchur K 3 d (Or.inr (Or.inl ⟨rfl, hd⟩)) hK.2.2 (isPGroup_center hred hK) ⟨e₁⟩
  have eK : K ≃* CatGroup d :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e₁
  have hC := centralizer_eq_bot hred hKn hcent hZ
  obtain ⟨⟨eS⟩, -⟩ := KFactProofs.Sp48.exists_equiv_sp8 hd eK
  have h6 : K.index ≤ 6 := haveI := hKn; KFactProofs.Sp48.index_le_six (eK := eS) hC
  have hidx : ¬ 3 ^ 2 ∣ K.index := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h
    norm_num at this
    omega
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map_eq_inf (Rb := Rb) hK
  exact false_of_comm_of_klingen hKn (by rw [hC]; infer_instance)
    (by rw [hC, sup_bot_eq]; exact hidx) (comm_inf_of_sylowShape (sylowShape_sp48 hd eK) T₀ hT₀) hkl

theorem reeF4_false
    (hSchur : KFactChevTwoSurvivorSchur) (hred : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hkl : HasKlingenData p Rb Y₀) (hp5 : p = 5) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeFFourFiveIndex d) (e₁ : K ⧸ Subgroup.center K ≃* CatGroup d) : False := by
  subst hp5
  have hZ : Subgroup.center K = ⊥ :=
    hSchur K 5 d (Or.inr (Or.inr (Or.inr ⟨rfl, hd⟩))) hK.2.2 (isPGroup_center hred hK) ⟨e₁⟩
  have eK : K ≃* CatGroup d :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e₁
  have hC := centralizer_eq_bot hred hKn hcent hZ
  have h5 : K.index ∣ 5 := haveI := hKn
    index_dvd_of_card_mulAut_dvd K hC
      (CFSG.HardMathSupport.Malle.LocalAction.card_mulAut_dvd_five_mul hd ⟨eK⟩)
  have hidx : ¬ 5 ^ 2 ∣ K.index := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans h5)
    norm_num at this
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map_eq_inf (Rb := Rb) hK
  exact false_of_comm_of_klingen hKn (by rw [hC]; infer_instance)
    (by rw [hC, sup_bot_eq]; exact hidx)
    (comm_inf_of_sylowShape
      (CFSG.HardMathSupport.Malle.LocalAction.sylowShape_five_of_catGroup hd ⟨eK⟩) T₀ hT₀) hkl

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
