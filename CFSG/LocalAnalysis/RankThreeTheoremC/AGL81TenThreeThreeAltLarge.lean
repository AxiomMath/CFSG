module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltCore
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv Equiv.Perm
open CFSG.HardMathSupport.RichardWeiss.Coordinator (ConjSpec exists_action eq_of_conjSpec
  perm_mem_normalizer mk_mem_normalizer_barM pair_data_at_M quad_data_at_M
  mem_wN_of_mem_normalizer_wN wAction_surjective_d8 false_of_quotient_alt_seven)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem exists_odd_conjSpec {Q : Type} [Group Q] {Lb : Subgroup Q} {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (h5 : 5 ≤ Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6)
    (φ : ↥Lb ≃* ↥(alternatingGroup Ω)) {β : Q} (hβ : β ∈ normalizer (Lb : Set Q))
    (hodd : Odd (orderOf β)) :
    ∃ σ : Perm Ω, ConjSpec φ β σ ∧ σ ∈ alternatingGroup Ω ∧ Odd (orderOf σ) := by
  have hZ : zpowers β ≤ normalizer (Lb : Set Q) := zpowers_le.mpr hβ
  obtain ⟨π, hπ, -⟩ := exists_action h5 h6 φ (zpowers β).subtype fun h => hZ h.2
  set x : ↥(zpowers β) := ⟨β, mem_zpowers β⟩
  have hσodd : Odd (orderOf (π x)) := by
    refine hodd.of_dvd_nat ((orderOf_map_dvd π x).trans ?_)
    rw [Subgroup.orderOf_mk]
  exact ⟨π x, hπ x,
    CFSG.HardMathSupport.RichardWeiss.Coordinator.sign_eq_one_of_odd_orderOf hσodd, hσodd⟩

section Models

variable {Q : Type} [Group Q] [Finite Q] {Lb P : Subgroup Q} {β : Q}

theorem centralizes_pair (hPL : P ≤ Lb) {E : Subgroup Q} {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥Lb ≃* AltB (Fin n)) (hE : (E.subgroupOf Lb).map φ.toMonoidHom = EA (Fin n))
    (hB : (P.subgroupOf Lb).map φ.toMonoidHom = NA (Fin n))
    (hβL : β ∈ normalizer (Lb : Set Q)) (hβE : β ∈ normalizer (E : Set Q))
    (hodd : Odd (orderOf β))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  have hcard : Fintype.card (Fin n × Bool) = 2 * n := by simp [mul_comm]
  obtain ⟨σ, hσ, hσA, hσo⟩ := exists_odd_conjSpec (by omega) (by omega) φ hβL hodd
  have hσR : (⟨σ, hσA⟩ : AltB (Fin n)) ∈ NA (Fin n) := by
    have h1 := perm_mem_normalizer φ (EA (Fin n)) hE hβL hβE hσ hσA
    rwa [normalizer_EA (by simp; omega)] at h1
  have hker : IsPGroup 2 (blockAction (ι := Fin n)).ker := by
    rw [ker_blockAction]
    exact isPGroup_two_EA_subgroupOf
  exact centralizes_of_model hPL φ hB blockAction blockAction_surjective hker
    (pCore_perm_eq_bot (Or.inr (Or.inr hn))) (centralizer_wSup_perm (Or.inr (Or.inr hn))) hβL hσ
    hσA hσR hσo hW

theorem centralizes_quad (hPL : P ≤ Lb) {n : ℕ} (hn : n = 3 ∨ 5 ≤ n)
    (φ : ↥Lb ≃* AltW (Fin n) (Fin 4))
    (hB : (P.subgroupOf Lb).map φ.toMonoidHom = wN d8 (Fin n))
    (hβL : β ∈ normalizer (Lb : Set Q)) (hβP : β ∈ normalizer (P : Set Q))
    (hodd : Odd (orderOf β))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  have hcard : Fintype.card (Fin n × Fin 4) = 4 * n := by simp [mul_comm]
  have hι : 2 ≤ Fintype.card (Fin n) := by simp; omega
  obtain ⟨σ, hσ, hσA, hσo⟩ := exists_odd_conjSpec (by omega) (by omega) φ hβL hodd
  have hσR : (⟨σ, hσA⟩ : AltW (Fin n) (Fin 4)) ∈ wN d8 (Fin n) :=
    mem_wN_of_mem_normalizer_wN hn (perm_mem_normalizer φ (wN d8 (Fin n)) hB hβL hβP hσ hσA)
  exact centralizes_of_model hPL φ hB (wAction wreathHyp_d8 hι) (wAction_surjective_d8 hι)
    (isPGroup_ker_wAction wreathHyp_d8 hι) (pCore_perm_eq_bot (Or.inr hn))
    (centralizer_wSup_perm (Or.inr hn)) hβL hσ hσA hσR hσo hW

theorem centralizes_eight (hPL : P ≤ Lb) {r s : ℕ} (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : 6 ≤ s)
    (φ : ↥Lb ≃* AltE r s) (hB : (P.subgroupOf Lb).map φ.toMonoidHom = eightN r s)
    (hβL : β ∈ normalizer (Lb : Set Q))
    (hact : ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s), ConjSpec φ β (Perm.sumCongr σ₁ σ₂))
    (hodd : Odd (orderOf β))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  have hcard : Fintype.card (OmegaE r s) = 2 * r + s := by
    simp [OmegaE, Fintype.card_sum, Fintype.card_prod, mul_comm]
  have hr1 : 1 ≤ r := by omega
  haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨σ, hσ, hσA, hσo⟩ := exists_odd_conjSpec (by omega) (by omega) φ hβL hodd
  obtain ⟨σ₁, hσ₁, σ₂, hσ'⟩ := hact
  have heq : σ = Perm.sumCongr σ₁ σ₂ := eq_of_conjSpec (by omega) φ hβL hσ hσ'
  have hσR : (⟨σ, hσA⟩ : AltE r s) ∈ eightN r s := by
    refine ⟨(σ₁, σ₂), ?_, ?_⟩
    · show (σ₁, σ₂) ∈ pTilde (Fin r) (Fin s)
      rw [mem_pTilde]
      refine ⟨hσ₁, ?_⟩
      have h1 : sign σ = 1 := mem_alternatingGroup.1 hσA
      rwa [heq, sign_sumCongr] at h1
    · rw [Perm.sumCongrHom_apply]
      exact heq.symm
  have hker : IsPGroup 2 ((eightAction (Fin r) (Fin s)).comp (eightEquiv r s).toMonoidHom).ker := by
    rw [← MonoidHom.comap_ker]
    exact isPGroup_ker_eightAction.comap_of_injective _ (eightEquiv r s).injective
  have hs5 : 5 ≤ s := by omega
  exact centralizes_of_model hPL φ hB _ (eightAction_surjective.comp (eightEquiv r s).surjective)
    hker (pCore_prod_eq_bot (pCore_perm_eq_bot hr) (pCore_perm_eq_bot (Or.inr (Or.inr hs5))))
    (centralizer_wSup_perm_prod hr hs5) hβL hσ hσA hσR hσo hW

end Models

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_bar {M : Subgroup G} {b : G} (hb : b ∈ M) (hbo : Odd (orderOf b)) :
    Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)) := by
  refine hbo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
  rw [Subgroup.orderOf_mk]

theorem centralizes_large (h810 : Asc81bEightTen)
    {M S L : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX1 : ¬ InClassXBlock L) {m : ℕ} (hm : 10 ≤ m)
    (hdeg : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)))
    {b : G} (hb : b ∈ M) (hbS : b ∈ normalizer (S : Set G)) (hbo : Odd (orderOf b))
    (hbL : b ∈ normalizer (L : Set G))
    (hW : ∀ w (hw : w ∈ barM M (normalizer (S : Set G) ⊓ L)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (normalizer (S : Set G) ⊓ L))) ⟨w, hw⟩ ∈
        wSup (↥(barM M (normalizer (S : Set G) ⊓ L)) ⧸
          CFSG.pCore 2 ↥(barM M (normalizer (S : Set G) ⊓ L))) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * w *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ * w⁻¹ ∈
          pCoreOf 2 (barM M (normalizer (S : Set G) ⊓ L))) :
    ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ := by
  obtain ⟨e⟩ := hdeg
  have hSL : S ≤ normalizer (L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hK hA hL
  have hPL : barM M (normalizer (S : Set G) ⊓ L) ≤ barM M L := AGLEmbedding.barM_mono inf_le_right
  have hβL := mk_mem_normalizer_barM hb hbL
  have hβP := mk_mem_normalizer_barM hb
    (CFSG.HardMathSupport.RichardWeiss.Coordinator.mem_normalizer_inf
      (Subgroup.le_normalizer hbS) hbL)
  have hβE := mk_mem_normalizer_barM hb
    (CFSG.HardMathSupport.RichardWeiss.Coordinator.mem_normalizer_inf hbS hbL)
  have hodd := odd_orderOf_bar hb hbo
  have e' : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m) :=
    (CFSG.HardMathSupport.Cooperstein.Coordinator.barMSupCenterEquiv hA hL hSL).symm.trans e
  rcases h810 G M S L hK hA hL hSL m (Or.inr (by omega)) ⟨e'⟩ with h1 | ⟨h5, -⟩ |
    ⟨n, hn, hd, -⟩ | ⟨n, hn, hd, -⟩ | ⟨N, r, -, -, -, hr, hs, ⟨ψ, hB, hact⟩, -, -⟩
  · exact absurd h1 hX1
  · obtain ⟨-, ⟨e7⟩, -⟩ := h5
    exact (false_of_quotient_alt_seven hm e' e7).elim
  · obtain ⟨φ, hE, hB⟩ := pair_data_at_M hA hL hSL (by omega) hd
    exact centralizes_pair hPL hn φ hE hB hβL hβE hodd hW
  · obtain ⟨φ, hB⟩ := quad_data_at_M hA hL hSL hd
    exact centralizes_quad hPL hn φ hB hβL hβP hodd hW
  · refine centralizes_eight hPL hr hs ψ hB hβL ?_ hodd hW
    exact hact _ ((mem_barM _).2 ⟨⟨b, hb⟩, Subgroup.mem_inf.2 ⟨hbS, hbL⟩, rfl⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
