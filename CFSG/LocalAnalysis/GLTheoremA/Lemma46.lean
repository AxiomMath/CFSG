module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma45
public import CFSG.LocalAnalysis.GLTheoremA.PartIInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem lemma46 {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hS3 : Stage3 G p) (hS4 : Stage4Order G p) (h113 : I113UsedAt G p)
    {B L K₁ : Subgroup G} {x : G} (hBxL : IsSMax p B x L) (hL : L ≤ MxB p Club B x)
    (hK₁ : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K₁)
    (hBK₁ : ¬ B ≤ Subgroup.normalizer (K₁ : Set G)) :
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G),
      Relation.ReflTransGen (PumpRel p) (B, x, L) (B', x', L') ∧ L' ≤ MxB p Club B' x' ∧
      mxB p Club B x < mxB p Club B' x' ∧
      ¬ IsCyclic (B' ⊓ centModSubgroup p L' : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Cx := Subgroup.centralizer ({x} : Set G)
  have hS : IsSTriple p B x L := hBxL.1
  have hB : GLAIsBmax p B := hS.1
  have hx : IsEssential p B x := hS.2.1
  have hLc : GLAPComponent p Cx L := hS.2.2
  have hLg : IsGoodComp p Club B x L := isGoodComp_of_le_MxB hp hLc hL
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hB.1 hx.1
  obtain ⟨A, hA, hBA, hAnorm, hdecA, hAnc⟩ := h113 B x K₁ hB hx hK₁ hBK₁
  have hxK₁ : x ∈ centModSubgroup p K₁ := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hK₁.1 hk)
  have hxA : x ∈ A := hBA ⟨hx.1, hxK₁⟩
  have hKgood : ∀ L', IsGoodComp p Club B x L' → closureIn K₁ B ≤ centModSubgroup p L' :=
    fun L' hL' => closureIn_le_centModSubgroup hp hBCx hK₁ hL'.1 hL'.2.1 hBK₁
  have hKL := hKgood L hLg
  obtain ⟨N, hN, hAN⟩ := GLAIsBmax.exists_maxTwoLocal hA
  obtain ⟨D₀, hD₀D, hD₀card, hD₀e, -⟩ :=
    hS3.2.2.1 A _ N hA (inf_le_left.trans inf_le_left) hAnc hN hAN
  obtain ⟨x', hx'D₀, hx'1⟩ : ∃ a ∈ D₀, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 h
    rw [hbot, Subgroup.card_bot, one_mul] at hD₀card
    exact hAnc (isCyclic_of_prime_card hD₀card.symm)
  have hx'E : IsEssential p A x' := hD₀e x' hx'D₀ hx'1
  have hx'D := hD₀D hx'D₀
  have hx'L : CentMod p L x' := centMod_iff.2 (hKL hx'D.1.2)
  have hAdec : ∀ b ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ b = u * v := by
    intro b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := hdecA b hb
    exact ⟨u, ⟨hu.2, hu.1⟩, v, hv.1, centMod_iff.2 (hKL hv.2), rfl⟩
  obtain ⟨L', -, hL'c, hrel, -, hAL', ⟨eLL'⟩, -, -, -, hcm⟩ :=
    pump_step h183 hp hS4 hKP hsimple hnonab hBxL hLg.2.1 hA hxA hAdec hx'E hx'L
  have hL'g : IsGoodComp p Club A x' L' :=
    ⟨hL'c, hAL', fun h => hLg.2.2 ((hEC.club_congr L L' ⟨eLL'⟩).2 h)⟩
  refine ⟨A, x', L', Relation.ReflTransGen.single hrel, le_MxB hL'g, ?_, ?_⟩
  ·
    have hMdef : MxB p Club B x = sSup {K | IsGoodComp p Club B x K} := rfl
    have hcov : Nat.card (PQuot p (K₁ ⊔ MxB p Club B x)) ≤ mxB p Club A x' := by
      rw [hMdef, ← sSup_insert]
      refine card_pQuot_sSup_le_mxB hp hEC h183 hKP hsimple hnonab hA hx'E hxA _ ?_
      rintro L'' (rfl | hL'')
      · refine ⟨hK₁, ?_, centMod_iff.2 hx'D.2,
          hEC.not_club_of_exc _ (hEC.exc_of_not_le B x L'' hB hx hK₁ hBK₁)⟩
        have := hAnorm 1 (Subgroup.one_mem B)
        rwa [gLBConj_one] at this
      · refine ⟨hL''.1, fun b hb => ?_, centMod_iff.2 (hKgood L'' hL'' hx'D.1.2), hL''.2.2⟩
        obtain ⟨u, hu, v, hv, rfl⟩ := hdecA b hb
        exact Subgroup.mul_mem _ (hL''.2.1 hu.2) (centMod_iff.2 (hKgood L'' hL'' hv.2)).1
    have hNX : K₁ ⊔ MxB p Club B x ≤ Cx := sup_le hK₁.1 (sSup_le fun L'' hL'' => hL''.1.1)
    have hstrict : Nat.card (PQuot p (MxB p Club B x)) <
        Nat.card (PQuot p (K₁ ⊔ MxB p Club B x)) := by
      refine card_pQuot_lt_of_le_normalizer hp le_sup_right
        (sup_le (fun k hk => ?_) Subgroup.le_normalizer) fun hle => ?_
      · refine mem_normalizer_sSup fun L'' hL'' => ?_
        have hne : L'' ≠ K₁ := fun h => hBK₁ (h ▸ hL''.2.1)
        exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hL''.1 hK₁ hne hk
      · have hK₁M : K₁ ≤ sSup {K | IsGoodComp p Club B x K} ⊔
            GLAPPrimeCoreOf p (K₁ ⊔ MxB p Club B x) := le_sup_left.trans hle
        have hmem := mem_of_le_sSup_sup_glaPComponent hp {K | IsGoodComp p Club B x K}
          (fun L'' hL'' => glaPComponent_of_le hp hL''.1 (le_sup_of_le_right (le_sSup hL'')) hNX)
          (glaPComponent_of_le hp hK₁ le_sup_left hNX) hK₁M
        exact hBK₁ hmem.2.1
    exact hstrict.trans_le hcov
  ·
    intro hcyc
    apply hAnc
    have hle : (A ⊓ closureIn K₁ B ⊓ centModSubgroup p K₁ : Subgroup G) ≤
        A ⊓ centModSubgroup p L' := fun d hd =>
      ⟨hd.1.1, centMod_iff.1 (hcm d hd.1.1 (centMod_iff.2 (hKL hd.1.2)))⟩
    exact Subgroup.isCyclic_of_le hle

end CFSG.LocalAnalysis.GLTheoremA
