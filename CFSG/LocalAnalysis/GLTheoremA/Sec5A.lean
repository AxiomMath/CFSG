module

public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure Sec5Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  stage3 : Stage3 G p
  stage4Order : Stage4Order G p
  stage4 : Stage4 G p
  input18_3_4 : Input18_3_4

@[expose] def Prop51At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0Max p B x L → CentModEqZpowers p B L x

variable {G : Type} [Group G] [Finite G]

theorem IsSTriple.mem_centralizer {p : ℕ} {B L : Subgroup G} {x : G} (h : IsSTriple p B x L) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.1 (h.2.2.1 hl)

theorem card_zpowers_eq_of_pow {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]

theorem mem_zpowers_of_card_sup_le {p : ℕ} (hp : p.Prime) {x b : G} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) (h : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) ≤ p) :
    b ∈ Subgroup.zpowers x := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers b := le_sup_left
  have heq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_zpowers_eq_of_pow hp hx hx1]; exact h)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem card_le_of_isCyclic_of_pow {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : IsCyclic D)
    (hexp : ∀ d ∈ D, d ^ p = 1) : Nat.card D ≤ p := by
  obtain ⟨g, hg⟩ := hD.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hexp g g.2)
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)

theorem lemma52 {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) {B A L : Subgroup G} {x : G}
    (hBxL : IsS0Max p B x L) (hA : GLAIsBmax p A) (hxA : x ∈ A)
    (hAdec : ∀ b ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ b = u * v) :
    CentModEqZpowers p A L x := by
  have hp := hc.prime
  have hxS : IsSTriple p B x L := hBxL.1.1
  have hx1 : x ≠ 1 := hxS.2.1.2.1
  have hxp : x ^ p = 1 := hA.1.2 x hxA
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := IsSTriple.mem_centralizer hxS
  intro b hbA
  constructor
  · intro hbL
    by_contra hbx
    set D := Subgroup.zpowers x ⊔ Subgroup.zpowers b with hDdef
    have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.2 hxA) (Subgroup.zpowers_le.2 hbA)
    have hDexp : ∀ d ∈ D, d ^ p = 1 := fun d hd => hA.1.2 d (hDA hd)
    have hDcm : D ≤ centModSubgroup p L := sup_le
      (Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer hxC)))
      (Subgroup.zpowers_le.2 (centMod_iff.1 hbL))
    have hDnc : ¬ IsCyclic D := fun hcyc => hbx (mem_zpowers_of_card_sup_le hp hxp hx1
      (card_le_of_isCyclic_of_pow hp hcyc hDexp))
    obtain ⟨N, hN, hAN⟩ := GLAIsBmax.exists_maxTwoLocal hA
    obtain ⟨D₀, hD₀D, hD₀card, hD₀e, -⟩ := hc.stage3.2.2.1 A D N hA hDA hDnc hN hAN
    obtain ⟨a, haD₀, ha1⟩ : ∃ a ∈ D₀, a ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 h
      rw [hbot, Subgroup.card_bot, one_mul] at hD₀card
      exact hbx (mem_zpowers_of_card_sup_le hp hxp hx1 hD₀card.symm.le)
    have haE : IsEssential p A a := hD₀e a haD₀ ha1
    have haL : CentMod p L a := centMod_iff.2 (hDcm (hD₀D haD₀))
    obtain ⟨K, -, -, hrel, -, -, -, -, -, -, hcm⟩ :=
      pump_step hc.input18_3_4 hp hc.stage4Order hc.kProper hc.simple hc.nonabelian
        hBxL.2.1 hBxL.2.2 hA hxA hAdec haE haL
    have hS0 : IsS0Max p A a K :=
      (hc.stage4Order.2.2.2.2.2.2.1 (B, x, L) (A, a, K)
        (pumpLe_of_reflTransGen hBxL.1.1 (Relation.ReflTransGen.single hrel))).2 hBxL
    have h51' := h51 A a K hS0
    have hxa : x ∈ Subgroup.zpowers a := (h51' x hxA).1 (hcm x hxA (centMod_of_mem_centralizer hxC))
    have hba : b ∈ Subgroup.zpowers a := (h51' b hbA).1 (hcm b hbA hbL)
    have hap : a ^ p = 1 := hA.1.2 a (hDA (hD₀D haD₀))
    have hxa' : Subgroup.zpowers x = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxa)
        (by rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hap ha1])
    exact hbx (hxa' ▸ hba)
  · intro hb
    exact centMod_of_mem_centralizer ((Subgroup.zpowers_le.2 hxC) hb)

end CFSG.LocalAnalysis.GLTheoremA
