module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma6364Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma6364AutAux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

structure Lemma63Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i248 : I248At G p

namespace L63

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem mem_glaBeta {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {m : ℕ} (hlt : m < GLATwoLocalRank q G) :
    q ∈ GLABeta (m + 1) G := by
  refine ⟨hq, hq2, ?_, hlt⟩
  have hbdd := bddAbove_twoLocalPRanks (G := G) hq.one_lt
  have hne : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank q H = k}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : GLATwoLocalRank q G = 0 := by
      unfold GLATwoLocalRank twoLocalPrimeRank
      rw [h]
      exact csSup_empty
    omega
  obtain ⟨H, -, hH⟩ := Nat.sSup_mem hne hbdd
  have hpos : 0 < CFSG.Open.pRank q H := by
    have h1 : CFSG.Open.pRank q H = GLATwoLocalRank q G := hH
    omega
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  have hdvd : q ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self q hpos.ne'
  exact hdvd.trans (Subgroup.card_subgroup_dvd_card E)

theorem exists_sylow_pair {q : ℕ} (hq : q.Prime) (L : Subgroup G) :
    ∃ (Q₀ : Subgroup G) (Q : Sylow q G), Q₀ ≤ L ∧ IsPGroup q Q₀ ∧
      Nat.card Q₀ = q ^ (Nat.card L).factorization q ∧ Q₀ ≤ (Q : Subgroup G) := by
  haveI := Fact.mk hq
  obtain ⟨S⟩ : Nonempty (Sylow q ↥L) := inferInstance
  have hP : IsPGroup q ((S : Subgroup ↥L).map L.subtype) := S.isPGroup'.map L.subtype
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(S : Subgroup ↥L).map L.subtype, Q, Subgroup.map_subtype_le _, hP, ?_, hQ⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact S.card_eq_multiplicity

theorem normalizer_le_glaWeakCore {q : ℕ} (hq : q.Prime) {Q E : Subgroup G} (hEQ : E ≤ Q)
    (h3 : 3 ≤ CFSG.Open.pRank q E) : Subgroup.normalizer (E : Set G) ≤ GLAWeakCore q Q :=
  le_sSup ⟨E, hEQ, by omega,
    h3.trans (CFSG.SectionRank.pRank_mono hq.one_lt le_sup_left), rfl⟩

theorem coreIn_top_eq_glbCore (q k : ℕ) (P : Subgroup G) :
    CFSG.HardMathSupport.Solomon.Coordinator.coreIn q k P ⊤ = GLBCore q k P := by
  refine le_antisymm (iSup₂_le fun E hE => (top_inf_eq _).le.trans (le_sSup ⟨E, hE.1, hE.2, rfl⟩))
    (sSup_le ?_)
  rintro N ⟨E, hEP, hk, rfl⟩
  exact (top_inf_eq (Subgroup.normalizer (E : Set G))).ge.trans
    (le_iSup₂ (f := fun (E : Subgroup G) (_ : E ≤ P ∧ k ≤ CFSG.Open.pRank q E) =>
      (⊤ : Subgroup G) ⊓ Subgroup.normalizer (E : Set G)) E ⟨hEP, hk⟩)

theorem coreIn_le_glaWeakCore {q : ℕ} (hq : q.Prime) {Q₀ Q : Subgroup G} (hQ : Q₀ ≤ Q)
    (X : Subgroup G) :
    CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q₀ X ≤ GLAWeakCore q Q :=
  iSup₂_le fun E hE => inf_le_right.trans (normalizer_le_glaWeakCore hq (hE.1.trans hQ) hE.2)

theorem exists_mul_mem_normalizer {q : ℕ} (hq : q.Prime) {L Q₀ : Subgroup G} (hQ₀L : Q₀ ≤ L)
    (hcard : Nat.card Q₀ = q ^ (Nat.card L).factorization q) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, l * b ∈ Subgroup.normalizer (Q₀ : Set G) := by
  haveI := Fact.mk hq
  have hcard' : Nat.card (Q₀.subgroupOf L) = q ^ (Nat.card ↥L).factorization q := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀L).toEquiv
  let P₀ : Sylow q ↥L := Sylow.ofCard (Q₀.subgroupOf L) hcard'
  let σ : MulAut ↥L := L.normalizerMonoidHom ⟨b, hb⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L (σ • P₀) P₀
  have hP₀ : (P₀ : Subgroup ↥L) = Q₀.subgroupOf L := rfl
  have hτ : ((MulAut.conj g * σ) • P₀ : Sylow q ↥L) = P₀ := by
    rw [mul_smul, ← Sylow.smul_def]
    exact hg
  have hsub : (MulAut.conj g * σ) • (P₀ : Subgroup ↥L) = (P₀ : Subgroup ↥L) := by
    rw [← Sylow.pointwise_smul_def, hτ]
  refine ⟨(g : G), g.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hn : (g : G) * b ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer g.2) hb
  by_cases hyL : y ∈ L
  · have h1 := Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj g * σ)
      (S := (P₀ : Subgroup ↥L)) (x := ⟨y, hyL⟩)
    rw [hsub] at h1
    have h2 : (⟨y, hyL⟩ : ↥L) ∈ (P₀ : Subgroup ↥L) ↔ y ∈ Q₀ := by
      rw [hP₀, Subgroup.mem_subgroupOf]
    have h3 : (MulAut.conj g * σ) • (⟨y, hyL⟩ : ↥L) ∈ (P₀ : Subgroup ↥L) ↔
        (g : G) * b * y * ((g : G) * b)⁻¹ ∈ Q₀ := by
      rw [hP₀, Subgroup.mem_subgroupOf]
      have : (((MulAut.conj g * σ) • (⟨y, hyL⟩ : ↥L) : ↥L) : G) =
          (g : G) * b * y * ((g : G) * b)⁻¹ := by
        show (g : G) * (b * y * b⁻¹) * (g : G)⁻¹ = _
        group
      rw [this]
    rw [← h2, ← h3, h1]
  · have hy1 : y ∉ Q₀ := fun h => hyL (hQ₀L h)
    have hy2 : (g : G) * b * y * ((g : G) * b)⁻¹ ∉ Q₀ := fun h =>
      hyL ((Subgroup.mem_normalizer_iff.1 hn y).2 (hQ₀L h))
    exact ⟨fun h => absurd h hy1, fun h => absurd h hy2⟩

end L63

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma63_holds (hc : S6Ctx G p) (hin : Lemma63Inputs G p) (h62 : Lemma62At G p) :
    Lemma63At G p := by
  intro q hq hq2 hqp B x L hTq hlt
  obtain ⟨⟨hBmax, hxB, hx1, hLcomp, hBL, hcent⟩, hchev⟩ := hTq
  by_cases hU : IsU3Case p q L
  · exact Or.inl hU
  refine Or.inr fun D J hDJ => ?_
  have hβ := L63.mem_glaBeta hq hq2 hlt
  obtain ⟨Q₀, Q, hQ₀L, hQ₀q, hQ₀card, hQ₀Q⟩ := L63.exists_sylow_pair hq L
  obtain ⟨M, hM2, hMW⟩ := (hc.weakCore q hβ).2 Q
  have hcardC := L6364.card_inf_centModSubgroup hc.prime hBmax.1 hxB hx1 hcent
  have haut := L6364.exists_elemAbelian_aut (k := 3) (L := L) hBmax.1 hBL (by
    rw [hcardC, ← pow_succ]
    exact pow_four_le_card_of_bmax hc hBmax)
  have hCk := kGroup_centralizer hc hx1
  rcases hin.i248 hc.prime hc.odd q hq hq2 hqp _ L Q₀ hCk hLcomp hchev haut hQ₀L hQ₀q hQ₀card with
    ⟨h3, hcore⟩ | hU'
  swap
  · exact absurd hU' hU
  have hLM : L ≤ M := hcore.le.trans ((L63.coreIn_le_glaWeakCore hq hQ₀Q L).trans hMW)
  have hNM : Subgroup.normalizer (Q₀ : Set G) ≤ M :=
    (L63.normalizer_le_glaWeakCore hq hQ₀Q h3).trans hMW
  have hBM : B ≤ M := by
    intro b hb
    obtain ⟨l, hl, hln⟩ := L63.exists_mul_mem_normalizer hq hQ₀L hQ₀card (hBL hb)
    have hb' : b = l⁻¹ * (l * b) := by group
    rw [hb']
    exact M.mul_mem (M.inv_mem (hLM hl)) (hNM hln)
  have hJM : J ≤ M := (hDJ.2.1.1.1.trans inf_le_left).trans hLM
  refine h62 q hq hq2 hqp B x L ⟨⟨hBmax, hxB, hx1, hLcomp, hBL, hcent⟩, hchev⟩ D J
    ⟨hDJ, M, hM2, hDJ.1.1.trans hBM, ?_⟩
  show (M ⊓ J) ⊔ GLAPPrimeCoreOf p J = J
  rw [inf_eq_right.2 hJM]
  exact sup_eq_left.2 (Subgroup.map_subtype_le _)

end CFSG.LocalAnalysis.GLTheoremA
