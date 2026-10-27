module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FRStruct
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCore610
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FClaimA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FConj
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FQuat

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isThreeOnePlusTwo_of_equiv {H : Type*} [Group H] {P : Subgroup G} {Q : Subgroup H}
    (e : ↥P ≃* ↥Q) (h : IsThreeOnePlusTwo Q) : IsThreeOnePlusTwo P := by
  obtain ⟨⟨r, hr, s, hs, hne⟩, hcard, hexp⟩ := h
  refine ⟨⟨(e.symm ⟨r, hr⟩ : G), (e.symm ⟨r, hr⟩).2, (e.symm ⟨s, hs⟩ : G), (e.symm ⟨s, hs⟩).2, ?_⟩,
    ?_, ?_⟩
  · intro hcon
    apply hne
    have h1 : e.symm ⟨r, hr⟩ * e.symm ⟨s, hs⟩ = e.symm ⟨s, hs⟩ * e.symm ⟨r, hr⟩ := Subtype.ext hcon
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv]; exact hcard
  · intro g hg
    have h1 := hexp (e ⟨g, hg⟩) (e ⟨g, hg⟩).2
    have h2 : (e ⟨g, hg⟩) ^ 3 = 1 := Subtype.ext (by simpa using h1)
    have h3 : (⟨g, hg⟩ : ↥P) ^ 3 = 1 := by
      apply e.injective; rw [map_pow, h2, map_one]
    exact congrArg Subtype.val h3

theorem lemma610 (hcov : CoverStmt) (iL3 : InputL3U3Facts) (i183 : Input18_3_4)
    (h515 : Lemma515) (hKT : InputKType) (hNoSL : InputNoSLSection) (h62 : Lemma62Stmt)
    (hSL34 : InputSL34Facts) (h2320 : Input23_20) (h65 : Lemma65) (h66 : Lemma66)
    (hS : GLStanding G 4 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsExtremal B)
    {K : Subgroup G} (hK : IsHSet B K) : ¬ IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
  intro hSL
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hxB, hx1, hcomp⟩, -, hKM⟩ := hK
  obtain ⟨hB1, b, L, A, hw⟩ := hB.exists_witness
  have e := exists_extCtx hS hC hB1 hw
  have env : Env 4 B b L A := ⟨hS, hC, hB1, hw, e⟩
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    rcases h62 G 4 hS hC B hB x hxB hx1 K hcomp with h | h
    · exact h
    · exact absurd h (not_isLTwoOddPow_slThreeFour hSL)
  have hxC : B ≤ Subgroup.centralizer ({x} : Set G) := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.Bel hc hxB
  have hB81 : Nat.card B = 81 := e.Bc
  have h20 := h2320 G _ K B hcomp (Or.inr hSL) hxC e.Bel hBN
  obtain ⟨hInn, hrel⟩ : (∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K,
      b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K) ∧ (dQ K).relIndex B = 9 := by
    rcases h20 with h | h
    · exact absurd (le_glbCore_of_gammaCl hS hB1 hBN h) hKM
    · exact h
  have hD9 : Nat.card ↥(B ⊓ dQ K) = 9 := by
    have hmul := Subgroup.relIndex_mul_card (dQ K) B
    rw [inf_comm, hrel, hB81] at hmul
    omega
  have hAB0 : A ⊓ (B ⊓ dQ K) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    by_contra ha1
    exact claimA hcov iL3 i183 h515 hKT hNoSL env hxB hx1 hcomp hBN hSL hD9 ha.1 ha1
      (Subgroup.mem_inf.1 ha.2).2
  have hβ : ¬ ∀ u ∈ B, ∀ v ∈ B, u ≠ 1 → v ≠ 1 → ∃ g ∈ Subgroup.normalizer (B : Set G),
      g * u * g⁻¹ = v := by
    intro htr
    obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
      have h1 := e.Ac
      rw [this, Subgroup.card_bot] at h1
      omega
    obtain ⟨g, hg, hgx⟩ := htr x hxB a (e.AB haA) hx1 ha1
    obtain ⟨hc', hBN', -, hSL', hD9', haD'⟩ :=
      conj_hsl hS hxB hcomp hBN hg hKM hB1 hSL hD9
    rw [hgx] at hc' haD'
    exact claimA hcov iL3 i183 h515 hKT hNoSL env (e.AB haA) ha1 hc' hBN' hSL' hD9' haA ha1 haD'
  have hBp : IsPGroup 3 ↥B := IsPGroup.of_card (n := 4) (by rw [hB81]; norm_num)
  obtain ⟨R, hBR, hRp, hRY, hR1c, hcommR, hdecR, hN1, hN2⟩ := exists_rStruct hBp hBN hInn
  obtain ⟨P', ⟨eP⟩⟩ := sylow_equiv_sylowBar (K := K) (P := R ⊓ K) inf_le_right
    (hRp.to_le inf_le_left) hR1c
  obtain ⟨hZ3, hSyl3⟩ := hSL34 _ hSL
  have h12 : IsThreeOnePlusTwo (R ⊓ K) := isThreeOnePlusTwo_of_equiv eP (hSyl3 P')
  have hZeq : (R ⊓ K) ⊓ (R ⊓ dQ K) = (R ⊓ K) ⊓ dQ K := by
    ext g; simp only [Subgroup.mem_inf]; tauto
  have hZc : Nat.card ↥((R ⊓ K) ⊓ (R ⊓ dQ K)) = 3 := by
    rw [hZeq, card_sylow_inf_dQ inf_le_right (hRp.to_le inf_le_left) hR1c, hZ3,
      Nat.Prime.factorization_self Nat.prime_three]; norm_num
  have hZle : (R ⊓ K) ⊓ (R ⊓ dQ K) ≤ Zc (R ⊓ K) := by
    intro z hz
    rw [mem_Zc]
    exact ⟨(Subgroup.mem_inf.1 hz).1, fun r hr => (hcommR r hr z (Subgroup.mem_inf.1 hz).2).symm⟩
  have hZC : (R ⊓ K) ⊓ (R ⊓ dQ K) = Zc (R ⊓ K) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZc, h12.card_Zc])
  refine core610 (B := B) (A := A) (R₁ := R ⊓ K) (R₂ := R ⊓ dQ K) (Z := Zc (R ⊓ K)) hB81 e.Bel
    (fun E hE hBE => e.SC.2.2 E le_top hE hBE) (e.AB) e.Ac h12.2.1 h12.2.2 (Zc_le _)
    h12.card_Zc (fun z hz r hr => (mem_Zc.1 hz).2 r hr) (fun z hz hzc => mem_Zc.2 ⟨hz, fun r hr => hzc r hr⟩)
    (fun a ha c hc => h12.comm_mem_Zc ha hc) hcommR hZC.symm.symm (fun b hb => hdecR b (hBR hb))
    (hBR.trans hN2) ?_ ?_ (fun U hUN hU3 hc => ?_)
  · have : B ⊓ (R ⊓ dQ K) = B ⊓ dQ K := by
      ext g; simp only [Subgroup.mem_inf]; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hBR h1, h3⟩
    rw [this]; exact hD9
  · have : B ⊓ (R ⊓ dQ K) = B ⊓ dQ K := by
      ext g; simp only [Subgroup.mem_inf]; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hBR h1, h3⟩
    rw [this]; exact hAB0
  · obtain ⟨hd, hcard⟩ := lemma66v_transport h65 h66 hS hC hB1 hw hβ U hUN hU3 hc
    refine ⟨?_, hcard⟩
    rcases hd with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact Or.inr h2
    · exact Or.inl h1


end CFSG.HardMathSupport.Solomon.UniquenessMaximal
