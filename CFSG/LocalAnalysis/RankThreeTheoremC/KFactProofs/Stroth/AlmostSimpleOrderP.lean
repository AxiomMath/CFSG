module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
public import CFSG.HardMathSupport.Lang.Coordinator.ONanOuterSylowCyc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

private theorem ordP_center_eq_bot {E : Type} [Group E] [IsSimpleGroup E]
    (hnab : ∃ a b : E, a * b ≠ b * a) : Subgroup.center E = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center E := by
      rw [h]
      exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

private theorem ordP_commutator_eq_top {E : Type} [Group E] [IsSimpleGroup E]
    (hnab : ∃ a b : E, a * b ≠ b * a) : commutator E = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator E) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hab
  · exact h

private theorem ordP_quasisimple {E : Type} [Group E] [IsSimpleGroup E]
    (hnab : ∃ a b : E, a * b ≠ b * a) : CFSG.Open.IsQuasisimple E :=
  ⟨ordP_commutator_eq_top hnab,
    ((QuotientGroup.quotientMulEquivOfEq (ordP_center_eq_bot hnab)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem ordP_isComponentOf {X : Type} [Group X] {L : Subgroup X} [L.Normal]
    [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsComponentOf L ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤),
    ordP_quasisimple hnab⟩

private theorem ordP_catalog_quot {E : Type} [Group E] (hZ : Subgroup.center E = ⊥)
    (hcat : IsCatalogGroup E) : IsCatalogGroup (E ⧸ Subgroup.center E) := by
  obtain ⟨i, ⟨f⟩⟩ := hcat
  exact ⟨i, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans f⟩⟩

private theorem ordP_le_normalizer {X : Type} [Group X] (L D : Subgroup X) [L.Normal] :
    D ≤ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.normalizer_eq_top]
  exact le_top

private noncomputable def ordP_conjOuter {X : Type} [Group X] (L D : Subgroup X) [L.Normal] :
    D →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp
    ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion (ordP_le_normalizer L D)))

private theorem ordP_conjOuter_injective {X : Type} [Group X] {L D : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hDL : D ⊓ L = ⊥) :
    Function.Injective (ordP_conjOuter L D) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, hd⟩ h1
  have h1' : (Subgroup.normalizerMonoidHom L
      (Subgroup.inclusion (ordP_le_normalizer L D) ⟨d, hd⟩) : MulAut ↥L) ∈ inner ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp h1'
  have key : ∀ m : ↥L, (l : X) * (m : X) * (l : X)⁻¹ = d * (m : X) * d⁻¹ := by
    intro m
    have h2 : (MulAut.conj l) m = (Subgroup.normalizerMonoidHom L
        (Subgroup.inclusion (ordP_le_normalizer L D) ⟨d, hd⟩)) m := by
      rw [hl]
    exact congrArg Subtype.val h2
  have hc : (l : X)⁻¹ * d ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have e : (l : X) * h * (l : X)⁻¹ = d * h * d⁻¹ := key ⟨h, hh⟩
    apply mul_left_cancel (a := (l : X))
    calc (l : X) * (h * ((l : X)⁻¹ * d)) = ((l : X) * h * (l : X)⁻¹) * d := by group
      _ = (d * h * d⁻¹) * d := by rw [e]
      _ = d * h := by group
      _ = (l : X) * ((l : X)⁻¹ * d * h) := by group
  rw [hC] at hc
  have h3 : (l : X)⁻¹ * d = 1 := Subgroup.mem_bot.mp hc
  have hld : (l : X) = d := inv_mul_eq_one.mp h3
  have hdL : d ∈ L := by
    rw [← hld]
    exact l.2
  have hdbot : d ∈ D ⊓ L := Subgroup.mem_inf.mpr ⟨hd, hdL⟩
  rw [hDL, Subgroup.mem_bot] at hdbot
  exact Subtype.ext hdbot

private theorem ordP_isElemAbelian_range {G H : Type} [Group G] [Group H] {p : ℕ}
    {D : Subgroup G} (hD : CFSG.Open.IsElemAbelian p D) (f : D →* H) :
    CFSG.Open.IsElemAbelian p f.range := by
  have hcomm : ∀ a b : f.range, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
    apply Subtype.ext
    have hxy : x * y = y * x := hD.1.is_comm.comm x y
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hxy]
  refine ⟨⟨⟨fun a b => hcomm a b⟩⟩, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [← map_pow]
  have hx : x ^ p = 1 := Subtype.ext (by simpa using hD.2 x.1 x.2)
  rw [hx, map_one]

private theorem ordP_two_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  unfold CFSG.Open.pRank
  refine le_csSup ?_ ⟨E, le_top, hE, hcard⟩
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨F, -, -, hk⟩
  have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ k ≤ Nat.card G := by
    rw [← hk]
    exact Subgroup.card_le_card_group F
  exact le_trans h1.le h2

section Certificates


theorem false_of_inf_eq_bot_of_cyclic {X : Type} [Group X] [Finite X] {p : ℕ}
    {L D : Subgroup X} [L.Normal] (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a)
    (hcat : IsCatalogGroup L) (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hF : ThompsonFrame p D) (P₀ : Sylow p L) (hcyc : IsCyclic (P₀ : Subgroup L))
    (hD0 : D ⊓ L = ⊥) : False := by
  have hinj := ordP_conjOuter_injective hC hD0
  have hEcard : Nat.card (ordP_conjOuter L D).range = p ^ 2 := by
    rw [← hF.card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hEel := ordP_isElemAbelian_range hF.elem (ordP_conjOuter L D)
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Outer ↥L)) :=
    ordP_two_le_pRank hF.prime hEel hEcard
  have hK3 := kFactOutCyclic_holds ↥L hs hnab hcat p hF.prime hF.odd P₀ hcyc
  have h4 := le_trans h2 hK3
  omega

theorem false_of_sylow_card_eq_prime {X : Type} [Group X] [Finite X] {p : ℕ}
    {L D : Subgroup X} [L.Normal] (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a)
    (hcat : IsCatalogGroup L) (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hF : ThompsonFrame p D) (P₀ : Sylow p L) (hP : Nat.card (P₀ : Subgroup L) = p) : False := by
  haveI : Fact p.Prime := ⟨hF.prime⟩
  haveI : IsSimpleGroup L := hs
  have hp0 : 0 < p := hF.prime.pos
  have hp2 : 2 ≤ p := hF.prime.two_le
  have hLcard : Nat.card L = p * (P₀ : Subgroup L).index := by
    have h := Subgroup.card_mul_index (P₀ : Subgroup L)
    rw [hP] at h
    exact h.symm
  have hidx : ¬ p ∣ (P₀ : Subgroup L).index := Sylow.not_dvd_index P₀
  have hcomD : ∀ x y : D, x * y = y * x := fun x y => hF.elem.1.is_comm.comm x y
  have hDL : ¬ D ≤ L := by
    intro h
    have h1 := Subgroup.card_dvd_of_le h
    rw [hF.card, hLcard] at h1
    have h2 : p * p ∣ p * (P₀ : Subgroup L).index := by
      rw [← sq]
      exact h1
    exact hidx (Nat.dvd_of_mul_dvd_mul_left hp0 h2)
  have hA : D ⊓ L = ⊥ → False := fun hD0 =>
    false_of_inf_eq_bot_of_cyclic hs hnab hcat hC hF P₀ (isCyclic_of_prime_card hP) hD0
  have hB : Nat.card (D ⊓ L : Subgroup X) = p → False := by
    intro hS
    have hSL : D ⊓ L ≤ L := inf_le_right
    have hSp : IsPGroup p (D ⊓ L : Subgroup X) :=
      IsPGroup.of_card (n := 1) (by rw [hS, pow_one])
    have hScyc : IsCyclic (D ⊓ L : Subgroup X) := isCyclic_of_prime_card hS
    have hcardS : Nat.card ((D ⊓ L).subgroupOf L) = p :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).trans hS
    have hSidx : ¬ p ∣ ((D ⊓ L).subgroupOf L).index := by
      have h := Subgroup.card_mul_index ((D ⊓ L).subgroupOf L)
      rw [hcardS, hLcard] at h
      have h' : ((D ⊓ L).subgroupOf L).index = (P₀ : Subgroup L).index :=
        Nat.eq_of_mul_eq_mul_left hp0 h
      rw [h']
      exact hidx
    have hDS : ¬ D ≤ D ⊓ L := by
      intro h
      have h1 := Subgroup.card_le_of_le h
      rw [hF.card, hS] at h1
      nlinarith
    obtain ⟨d, hdD, hdS⟩ := SetLike.not_le_iff_exists.mp hDS
    have hdL : d ∉ L := fun h => hdS (Subgroup.mem_inf.mpr ⟨hdD, h⟩)
    have hcomp : CFSG.Open.IsComponentOf L ⊤ := ordP_isComponentOf hnab
    have hcatQ : IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
      ordP_catalog_quot (ordP_center_eq_bot hnab) hcat
    have hdvd : p ∣ Nat.card L := ⟨_, hLcard⟩
    have hdN : d ∈ Subgroup.normalizer (L : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top d
    have hdp : d ^ p = 1 := hF.elem.2 d hdD
    have hcommS : ∀ s ∈ D ⊓ L, d * s = s * d := by
      intro s hs'
      have hsD : s ∈ D := (Subgroup.mem_inf.mp hs').1
      exact congrArg Subtype.val (hcomD ⟨d, hdD⟩ ⟨s, hsD⟩)
    have hmem := CFSG.AGLEmbedding.OuterSylow.kFactOuterSylowInner_holds_cyc X L p hF.odd hcomp
      hcatQ hdvd (D ⊓ L) hSL hSp hSidx hScyc d hdN hdp hcommS
    rw [hC, sup_bot_eq] at hmem
    exact hdL hmem
  by_cases hD0 : D ⊓ L = ⊥
  · exact hA hD0
  · have hdvd' : Nat.card (D ⊓ L : Subgroup X) ∣ p ^ 2 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ L ≤ D)
      rwa [hF.card] at h
    obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow hF.prime).mp hdvd'
    interval_cases i
    · exact hD0 (by rw [Subgroup.eq_bot_iff_card]; simpa using hiS)
    · exact hB (by simpa using hiS)
    · have hDeq : D ⊓ L = D :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hF.card, hiS]))
      exact hDL (inf_eq_left.mp hDeq)

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
