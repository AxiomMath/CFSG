module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks
public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PFixedLineDimension

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem Bstar_eq_map (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Bstar P B = B.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) :=
  (FaithfulPImageVocabulary.image_eq P hc.faithfulBinaryIrreducibleAction.normal B).symm

theorem mem_Qline_iff (hc : BinaryActionRankCounterexample G p P T B e ρ) (v : Space hc) :
    v ∈ Qline hc ↔ (v.val : G) ∈ Subgroup.centralizer (B : Set G) := by
  unfold Qline E
  rw [BinaryRepresentations.mem_fixedSpace_iff, Bstar_eq_map hc]
  constructor
  · intro h b hb
    have hmem : conjOnP P hc.faithfulBinaryIrreducibleAction.normal b ∈ B.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) := ⟨b, hb, rfl⟩
    have h1 := congrArg Space.val (h _ hmem)
    rw [sigma_apply, Subtype.ext_iff, conjOnP_apply] at h1
    have : b * (v.val : G) * b⁻¹ = v.val := h1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro h d hd
    obtain ⟨b, hb, rfl⟩ := hd
    have hbc : (v.val : G) * b = b * v.val := ((Subgroup.mem_centralizer_iff.mp h) b hb).symm
    refine Additive.toMul.injective ?_
    show (sigma hc _ v).val = v.val
    rw [sigma_apply]
    apply Subtype.ext
    rw [conjOnP_apply, mul_inv_eq_iff_eq_mul, hbc.symm]

@[expose] noncomputable def QlineEquiv (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Qline hc ≃ ↥(P ⊓ Subgroup.centralizer (B : Set G)) where
  toFun v := ⟨((v.1.val : P) : G), (v.1.val).2, (mem_Qline_iff hc v.1).mp v.2⟩
  invFun x := ⟨Space.mk hc ⟨x.1, x.2.1⟩, (mem_Qline_iff hc _).mpr x.2.2⟩
  left_inv v := rfl
  right_inv x := rfl

theorem card_cyclic (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    IsCyclic ↥(P ⊓ Subgroup.centralizer (B : Set G)) ∧
      P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  obtain ⟨hne, heq⟩ := (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.1
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc.oddPrimeClassTwoAction.actor_ne_bot
  have hb' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  refine ⟨?_, hne⟩
  rw [← heq b b.2 hb']
  exact hc.oddPrimeClassTwoAction.cyclic_centralizer b b.2 hb'

theorem card_eq (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Nat.card ↥(P ⊓ Subgroup.centralizer (B : Set G)) = p := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  obtain ⟨hcyc, hne⟩ := card_cyclic hc
  set C := P ⊓ Subgroup.centralizer (B : Set G) with hC
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    have := (elemAbelian hc).2 (g : G) (g.2.1)
    simpa using this
  have hg1 : g ≠ 1 := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := hg ⟨x, hx⟩
    rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rcases (Nat.dvd_prime (Fact.out)).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · rw [← hord, h]

theorem finrank_eq_one (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Module.finrank (ZMod p) (Qline hc) = 1 := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  have h1 : Nat.card (Qline hc) = p := (Nat.card_congr (QlineEquiv hc)).trans (card_eq hc)
  have h2 : Nat.card (Qline hc) = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Qline hc) :=
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := Qline hc)
  rw [Nat.card_zmod, h1] at h2
  have hp1 : 1 < p := (prime hc).one_lt
  have : p ^ 1 = p ^ Module.finrank (ZMod p) (Qline hc) := by rw [pow_one]; exact h2
  exact (Nat.pow_right_injective hp1 this).symm

end CFSG.LocalAnalysis.RankThreeUC.Section5.PFixedLineDimension
