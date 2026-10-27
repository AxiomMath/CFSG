module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemma129_of_printed (h : Lemma129PrintedStatement) : Lemma129Statement := by
  intro G _ _ m p B M E A N D hcex
  obtain ⟨K, hK, hcase⟩ := h hcex
  refine ⟨K, hK.1, hK.2.1, hK.2.2.1, hK.2.2.2, ?_⟩
  rcases hcase with ⟨h3, h5, hA, hAK, -⟩ | ⟨hb, hdata⟩
  · exact Or.inl ⟨h3, h5, hA, hAK⟩
  · obtain ⟨D, _, _, e, F, hF, -, a, ha, hA, -⟩ := hdata
    exact Or.inr ⟨hb, F, hF, a, ha, hA⟩

namespace Lemma129

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)

section Generation

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_hyperplane_centralizer {p : ℕ} [Fact p.Prime] {A S T : Subgroup G}
    (hA : IsElemAbelian p A) (hA2 : p ^ 2 ≤ Nat.card A)
    (hSA : A ≤ Subgroup.normalizer (S : Set G)) (hS : ¬ p ∣ Nat.card S)
    (hT : ∀ B : Subgroup G, B ≤ A → (B.subgroupOf A).index = p →
      S ⊓ Subgroup.centralizer (B : Set G) ≤ T) : S ≤ T := by
  classical
  haveI : IsElementaryAbelian p A := isElemAbelian_iff_isElementaryAbelian.mp hA
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : Nontrivial A := by
    have h1 : 1 < Nat.card A := lt_of_lt_of_le (by nlinarith) hA2
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  letI : MulDistribMulAction A S := Subgroup.conjMulDistribMulActionOfLeNormalizer A S hSA
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := S) hS
  set T' : Subgroup S := T.comap S.subtype with hT'
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B S) ≤ T' := by
    refine iSup₂_le fun B hB => ?_
    set R : Subgroup G := B.map A.subtype with hR
    have hRA : R ≤ A := Subgroup.map_subtype_le B
    have hRi : (R.subgroupOf A).index = p := by
      rw [hR, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
      exact hB
    intro x hx
    have hxR : (x : G) ∈ S ⊓ Subgroup.centralizer (R : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
      calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hbx]
    exact hT R hRA hRi hxR
  rw [hgen, top_le_iff] at hle
  intro x hx
  have : (⟨x, hx⟩ : S) ∈ T' := hle ▸ Subgroup.mem_top _
  exact this

end Generation

section Basics

variable {G : Type} [Group G] [Finite G]

theorem card_eq_pow_pRank {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE.isPGroup
  have h1 : n ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hn
  obtain ⟨F, hFE, -, hF⟩ := CFSG.SectionRank.exists_pRank hp.one_lt E
  have h2 : Nat.card F ≤ Nat.card E := Subgroup.card_le_of_le hFE
  rw [hF, hn] at h2
  have h3 : CFSG.Open.pRank p E ≤ n := (pow_le_pow_iff_right₀ hp.one_lt).1 h2
  rw [hn, le_antisymm h1 h3]

theorem pRank_le_pRank_add_one {p : ℕ} (hp : p.Prime) {A F : Subgroup G} (hA : IsElemAbelian p A)
    (hFA : F ≤ A) (hidx : (F.subgroupOf A).index ≤ p) : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p F + 1 := by
  have hF : IsElemAbelian p F := hA.mono hFA
  have h1 := card_eq_pow_pRank hp hA
  have h2 := card_eq_pow_pRank hp hF
  have h3 : Nat.card A = Nat.card F * (F.subgroupOf A).index := by
    have := Subgroup.card_mul_index (F.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv] at this
    exact this.symm
  have h4 : p ^ CFSG.Open.pRank p A ≤ p ^ (CFSG.Open.pRank p F + 1) := by
    rw [← h1, h3, pow_succ, ← h2]
    exact Nat.mul_le_mul_left _ hidx
  exact (pow_le_pow_iff_right₀ hp.one_lt).1 h4

theorem pRank_le_of_le {p : ℕ} (hp : p.Prime) {A F : Subgroup G} (hFA : F ≤ A) :
    CFSG.Open.pRank p F ≤ CFSG.Open.pRank p A := CFSG.SectionRank.pRank_mono hp.one_lt hFA

end Basics

section Setup

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem prime_of (h : Cex127 G m p B M E A N D) : p.Prime := h.standing.prime

theorem ne_two_of (h : Cex127 G m p B M E A N D) : p ≠ 2 := h.standing.ne_two

theorem A_le_M (h : Cex127 G m p B M E A N D) : A ≤ M := h.pair.1.2.1.1.1.1

theorem A_el (h : Cex127 G m p B M E A N D) : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1

theorem three_le_rank_A (h : Cex127 G m p B M E A N D) : 3 ≤ CFSG.Open.pRank p A :=
  h.pair.1.2.1.1.2

theorem E_le_M (h : Cex127 G m p B M E A N D) : E ≤ M := h.pair.1.1.1.1.1

theorem E_el (h : Cex127 G m p B M E A N D) : IsElemAbelian p E := h.pair.1.1.1.1.2.1

theorem three_le_rank_E (h : Cex127 G m p B M E A N D) : 3 ≤ CFSG.Open.pRank p E :=
  h.pair.1.1.1.2

theorem uniq_E (h : Cex127 G m p B M E A N D) : IsUniquenessTwoLocal p E M := h.pair.1.1.2

theorem not_uniq_A (h : Cex127 G m p B M E A N D) : ¬ IsUniquenessTwoLocal p A M :=
  h.pair.1.2.1.2

theorem two_le_rank_inf (h : Cex127 G m p B M E A N D) :
    2 ≤ CFSG.Open.pRank p (E ⊓ A) := h.pair.1.2.2

theorem A_le_N (h : Cex127 G m p B M E A N D) : A ≤ N := by
  refine le_trans ?_ h.hD
  intro a ha
  have hc : ∀ x ∈ D, ∀ b ∈ A, b * x * b⁻¹ = x := fun x hx b hb => by
    have := elemAbelian_comm (A_el h) hb (h.plane.1 hx)
    rw [this]; group
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd; rw [hc d hd a ha]; exact hd
  · intro hd
    have h1 := hc _ hd a⁻¹ (A.inv_mem ha)
    have h2 : a⁻¹ * (a * d * a⁻¹) * a⁻¹⁻¹ = d := by group
    rw [h2] at h1
    rw [h1]; exact hd

theorem N_ne_top (h : Cex127 G m p B M E A N D) : N ≠ ⊤ := isTwoLocal_ne_top h.standing h.twoLocal

end Setup

section Step1

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

structure IsMinS (M N A S : Subgroup G) : Prop where
  le : S ≤ pCoreOf 2 M
  norm : A ≤ Subgroup.normalizer (S : Set G)
  not_le : ¬ S ≤ pCoreOf 2 N
  min : ∀ T : Subgroup G, T ≤ pCoreOf 2 M → A ≤ Subgroup.normalizer (T : Set G) →
    ¬ T ≤ pCoreOf 2 N → Nat.card S ≤ Nat.card T

omit [Finite G] in
theorem A_le_normalizer_pCoreOf_two {M A : Subgroup G} (hA : A ≤ M) :
    A ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := fun a ha =>
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hA ha)

theorem exists_minS (h : Cex127 G m p B M E A N D) : ∃ S, IsMinS M N A S := by
  classical
  obtain ⟨S, ⟨hS1, hS2, hS3⟩, hSmin⟩ := Set.exists_min_image
    {S : Subgroup G | S ≤ pCoreOf 2 M ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ pCoreOf 2 N} (fun S => Nat.card S) (Set.toFinite _)
    ⟨pCoreOf 2 M, le_rfl, A_le_normalizer_pCoreOf_two (A_le_M h), h.fails⟩
  exact ⟨S, hS1, hS2, hS3, fun T hT1 hT2 hT3 => hSmin T ⟨hT1, hT2, hT3⟩⟩

theorem not_dvd_card_S (h : Cex127 G m p B M E A N D) {S : Subgroup G} (hS : S ≤ pCoreOf 2 M) :
    ¬ p ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := prime_of h
  have h2 : IsPGroup 2 ↥S := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  rw [hk]
  intro hd
  have := (Nat.Prime.dvd_of_dvd_pow hp hd)
  exact ne_two_of h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

omit [Finite G] in
theorem le_normalizer_of_conj_mem {A H : Subgroup G}
    (h : ∀ a ∈ A, ∀ x ∈ H, a * x * a⁻¹ ∈ H) : A ≤ Subgroup.normalizer (H : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h a ha y hy, fun hy => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hy
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [e] at this

omit [Finite G] in
theorem normalizer_inf_centralizer {p : ℕ} {A S B' : Subgroup G} (hA : IsElemAbelian p A)
    (hB' : B' ≤ A) (hSA : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (B' : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun a ha x hx => ?_
  refine ⟨(Subgroup.mem_normalizer_iff.1 (hSA ha) x).1 hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro b hb
  have hbx := Subgroup.mem_centralizer_iff.1 hx.2 b hb
  have hab : a * b = b * a := elemAbelian_comm hA ha (hB' hb)
  have hab' : a⁻¹ * b = b * a⁻¹ := by
    have := elemAbelian_comm hA (A.inv_mem ha) (hB' hb)
    exact this
  calc b * (a * x * a⁻¹) = (b * a) * x * a⁻¹ := by group
    _ = (a * b) * x * a⁻¹ := by rw [← hab]
    _ = a * (b * x) * a⁻¹ := by group
    _ = a * (x * b) * a⁻¹ := by rw [hbx]
    _ = a * x * (b * a⁻¹) := by group
    _ = a * x * (a⁻¹ * b) := by rw [hab']
    _ = a * x * a⁻¹ * b := by group

theorem exists_hyperplane_le_centralizer (h : Cex127 G m p B M E A N D) {S : Subgroup G}
    (hS : IsMinS M N A S) :
    ∃ B' : Subgroup G, B' ≤ A ∧ (B'.subgroupOf A).index = p ∧
      B' ≤ Subgroup.centralizer (S : Set G) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  have hrank : p ^ 2 ≤ Nat.card A := by
    have := card_eq_pow_pRank hp (A_el h)
    rw [this]
    exact Nat.pow_le_pow_right hp.pos (le_trans (by norm_num) (three_le_rank_A h))
  have hgen := le_of_forall_hyperplane_centralizer (p := p) (T := pCoreOf 2 N) (A_el h) hrank hS.norm
    (not_dvd_card_S h hS.le) (fun B' hB'A hB'i => by
      by_contra hnot
      have hnc : ¬ S ≤ Subgroup.centralizer (B' : Set G) := by
        intro hSB
        apply hcon B' hB'A hB'i
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have := Subgroup.mem_centralizer_iff.1 (hSB hs) b hb
        exact this.symm
      have hlt : (S ⊓ Subgroup.centralizer (B' : Set G)) < S :=
        lt_of_le_of_ne inf_le_left fun heq => hnc (heq ▸ inf_le_right)
      have h1 := hS.min (S ⊓ Subgroup.centralizer (B' : Set G)) (inf_le_left.trans hS.le)
        (normalizer_inf_centralizer (A_el h) hB'A hS.norm) hnot
      exact absurd h1 (not_le.2 (card_lt_of_lt' hlt)))
  exact hS.not_le hgen

end Step1

section Step2a

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

@[expose] def deltaTwo (X D : Subgroup G) : Subgroup G :=
  ⨅ (d : G) (_ : d ∈ D) (_ : d ≠ 1), pCoreOf 2 (X ⊓ Subgroup.centralizer ({d} : Set G))

theorem inf_pCoreOf_two_le (X C : Subgroup G) :
    X ⊓ pCoreOf 2 C ≤ pCoreOf 2 (X ⊓ C) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (inf_le_inf_left X (CFSG.LieType.BorelTits.pCoreOf_le 2 C)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C).to_le inf_le_right)
  intro g hg
  exact mem_normalizer_inf (Subgroup.le_normalizer hg.1)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hg.2)

theorem le_deltaTwo (h121 : Prop121_corStatement) (h : Cex127 G m p B M E A N D)
    {S F : Subgroup G} (hS : IsMinS M N A S) (hF : F ≤ A)
    (hFS : F ≤ Subgroup.centralizer (S : Set G)) : S ≤ deltaTwo N F := by
  refine le_iInf₂ fun d hd => le_iInf fun hd1 => ?_
  have hSN : S ≤ N := hS.le.trans h.hO
  have hSd : S ≤ Cg d := by
    intro s hs
    rw [Cg, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (hFS hd) s hs)
  have h1 : S ≤ pCoreOf 2 (Cg d) := (le_inf hS.le hSd).trans (h121 h.toSec11 (hF hd) hd1)
  exact (le_inf hSN h1).trans (inf_pCoreOf_two_le N (Cg d))

theorem barX_eq_bot_iff {p : ℕ} {X S : Subgroup G} (hSX : S ≤ X) :
    barX p X S = ⊥ ↔ S ≤ GLAPPrimeCoreOf p X := by
  constructor
  · intro hb s hs
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hSX hs⟩ ∈ barX p X S :=
      ⟨⟨s, hSX hs⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact ⟨_, hmem, rfl⟩
  · intro hS
    refine eq_bot_iff.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ GLAPPrimeCoreOf p X := hS ((Subgroup.mem_subgroupOf).1 hx)
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rw [this] at hy
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy

theorem not_le_primeCore (h191 : Input19_1_6) (h121 : Prop121_corStatement)
    (h : Cex127 G m p B M E A N D) {S F : Subgroup G} (hS : IsMinS M N A S) (hFA : F ≤ A)
    (hFS : F ≤ Subgroup.centralizer (S : Set G)) (hr : 2 ≤ CFSG.Open.pRank p F) :
    ¬ S ≤ GLAPPrimeCoreOf p N := by
  intro hSO
  have hp := prime_of h
  have hΔ := le_deltaTwo h121 h hS hFA hFS
  have key := h191 G h.standing.kProper p 2 hp Nat.prime_two (ne_two_of h) N (N_ne_top h) F
    (hFA.trans (A_le_N h)) ((A_el h).mono hFA) hr
  exact hS.not_le ((le_inf hΔ hSO).trans key)

end Step2a

section Inputs

@[expose] def Input19_1_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ (k : ℕ) (D : Subgroup G), 1 ≤ k → IsEkIn p k X D →
      ((∀ K : Subgroup G, GLAPComponent p X K →
          barX p X (deltaTwo X D) ≤
            Subgroup.normalizer (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X))) ∧
        barX p X (deltaTwo X D) ≤
          Subgroup.centralizer (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) : Set (↥X ⧸ GLAPPrimeCore p ↥X))) ∧
      ∀ K : Subgroup G, GLAPComponent p X K →
        ¬ barX p X (deltaTwo X D) ≤
            Subgroup.centralizer (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X)) →
          D ≤ Subgroup.normalizer (K : Set G) ∧ D ⊓ centBar p ⊤ K = ⊥ ∧
            ¬ IsCompLocallyOTwoBalanced p k D K ∧
            autBar p (deltaTwo X D) K ≤
              localDeltaTwoIn (innerAut (barOf p K) ⊔ autBar p (deltaTwo X D) K) (autBar p D K)

end Inputs

section Step2

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

omit [Finite G] in
theorem barX_mono129 {p : ℕ} {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

omit [Finite G] in
theorem isPGroup_barX {p q : ℕ} {X S : Subgroup G} (hS : IsPGroup q ↥S) (hSX : S ≤ X) :
    IsPGroup q ↥(barX p X S) :=
  (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map _

theorem exists_component (h191 : Input19_1_6) (h121 : Prop121_corStatement) (hI : Input19_1_two)
    (h : Cex127 G m p B M E A N D) {S F : Subgroup G} (hS : IsMinS M N A S) (hFA : F ≤ A)
    (hFS : F ≤ Subgroup.centralizer (S : Set G)) (hr : 2 ≤ CFSG.Open.pRank p F) :
    ∃ K : Subgroup G, GLAPComponent p N K ∧
      barX p N S ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) ∧
      ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) ∧
      F ≤ Subgroup.normalizer (K : Set G) ∧ F ⊓ centBar p ⊤ K = ⊥ ∧
      ¬ IsCompLocallyOTwoBalanced p (CFSG.Open.pRank p F) F K ∧
      autBar p (deltaTwo N F) K ≤
        localDeltaTwoIn (innerAut (barOf p K) ⊔ autBar p (deltaTwo N F) K) (autBar p F K) := by
  have hp := prime_of h
  have hFel : IsElemAbelian p F := (A_el h).mono hFA
  have hEk : IsEkIn p (CFSG.Open.pRank p F) N F :=
    ⟨hFA.trans (A_le_N h), hFel, card_eq_pow_pRank hp hFel⟩
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hI G h.standing.kProper p hp (ne_two_of h) N (N_ne_top h)
    (CFSG.Open.pRank p F) F (by omega) hEk
  have hSΔ := le_deltaTwo h121 h hS hFA hFS
  have hSbarΔ : barX p N S ≤ barX p N (deltaTwo N F) := barX_mono129 hSΔ
  have hSN : S ≤ N := hS.le.trans h.hO
  have hS2 : IsPGroup 2 ↥(barX p N S) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isPGroup_barX ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hS.le) hSN
  have hcop : Nat.Coprime p (Nat.card (barX p N S)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 (ne_two_of h))
  have hex : ∃ K : Subgroup G, GLAPComponent p N K ∧
      ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    by_contra hcon
    push Not at hcon
    have hbot : barX p N S = ⊥ :=
      eq_bot_of_centralizes_pCore_components hp (glaPPrimeCore_quotient_eq_bot hp) hcop
        (hSbarΔ.trans h1') fun Kb hKb => by
          obtain ⟨K, hK, rfl⟩ := exists_glaPComponent_barX_eq (p := p) N hKb
          exact hcon K hK
    exact not_le_primeCore h191 h121 h hS hFA hFS hr ((barX_eq_bot_iff hSN).1 hbot)
  obtain ⟨K, hK, hKc⟩ := hex
  have hKnc : ¬ barX p N (deltaTwo N F) ≤
      Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    fun hle => hKc (hSbarΔ.trans hle)
  obtain ⟨hFN, hFc, hbal, hW⟩ := h2 K hK hKnc
  exact ⟨K, hK, hSbarΔ.trans (h1 K hK), hKc, hFN, hFc, hbal, hW⟩

end Step2

section NoCover

theorem commutator_eq_bot_of_cover {Y : Type*} [Group Y] {Sb Kb Mb Ob : Subgroup Y}
    (hSK : Sb ≤ Subgroup.normalizer (Kb : Set Y)) (hKM : Kb ≤ Mb)
    (hcomm : ∀ s ∈ Sb, ∀ m ∈ Mb, s * m * s⁻¹ * m⁻¹ ∈ Ob) (hO : IsPGroup 2 ↥Ob)
    (htriv : ∀ T : Subgroup Y, T ≤ Kb → (T.subgroupOf Kb).Normal → IsPGroup 2 ↥T → T = ⊥) :
    ⁅Sb, Kb⁆ = ⊥ := by
  set T : Subgroup Y := ⁅Sb, Kb⁆ with hT
  have hTK : T ≤ Kb := by
    have := (Subgroup.le_normalizer_iff_commutator_le_left (H := Sb) (K := Kb)).1 hSK
    rwa [Subgroup.commutator_comm] at this
  have hTn : (T.subgroupOf Kb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTK).2
      (Subgroup.normalizer_commutator_ge_right Sb Kb)
  have hTO : T ≤ Ob := by
    rw [hT, Subgroup.commutator_def]
    refine (Subgroup.closure_le Ob).2 ?_
    rintro _ ⟨s, hs, k, hk, rfl⟩
    exact hcomm s hs k (hKM hk)
  exact htriv T hTK hTn (hO.to_le hTO)

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCoreOf_top_quotient {p : ℕ} (hp : p.Prime) {N : Subgroup G} :
    GLAPPrimeCoreOf p (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ := by
  have hO := glaPPrimeCore_quotient_eq_bot (Z := ↥N) hp
  have h5 := glaPPrimeCore_map_iso p
    (Subgroup.topEquiv : (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) ≃* (↥N ⧸ GLAPPrimeCore p ↥N))
  rw [hO] at h5
  have h6 : GLAPPrimeCore p ↥(⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h5
  unfold GLAPPrimeCoreOf
  rw [h6, Subgroup.map_bot]

theorem eq_bot_of_normal_two_group {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N K : Subgroup G}
    (hK : GLAPComponent p N K) {T : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    (hTK : T ≤ barX p N K) (hn : (T.subgroupOf (barX p N K)).Normal) (h2 : IsPGroup 2 ↥T) :
    T = ⊥ := by
  have hsn : IsSubnormal (barX p N K) ⊤ := by
    have := isSubnormal_barX (C := N) p hK.2.1
    rwa [barX_self] at this
  have hcop : Nat.Coprime p (Nat.card (T.subgroupOf (barX p N K))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h1 : T.subgroupOf (barX p N K) ≤ GLAPPrimeCore p ↥(barX p N K) := le_sSup ⟨hn, hcop⟩
  have h3 : T ≤ GLAPPrimeCoreOf p (barX p N K) := by
    have := Subgroup.map_mono (f := (barX p N K).subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hTK] at this
  have h4 := h3.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hsn)
  rw [glaPPrimeCoreOf_top_quotient hp] at h4
  exact eq_bot_iff.2 h4

theorem not_covers {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {S K : Subgroup G} (hS : IsMinS M N A S) (hK : GLAPComponent p N K)
    (hSK : barX p N S ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)))
    (hKc : ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) :
    ¬ Covers p N M K := by
  intro hcov
  apply hKc
  have hp := prime_of h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hON : pCoreOf 2 M ≤ N := h.hO
  have hcomm : ∀ s ∈ barX p N S, ∀ μ ∈ barX p N M,
      s * μ * s⁻¹ * μ⁻¹ ∈ barX p N (pCoreOf 2 M) := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨μ, hμ, rfl⟩
    have hσS : (σ : G) ∈ S := (Subgroup.mem_subgroupOf).1 hσ
    have hμM : (μ : G) ∈ M := (Subgroup.mem_subgroupOf).1 hμ
    refine ⟨σ * μ * σ⁻¹ * μ⁻¹, (Subgroup.mem_subgroupOf).2 ?_, by simp⟩
    have h1 : (σ : G) ∈ pCoreOf 2 M := hS.le hσS
    have h2 : (μ : G) * (σ : G)⁻¹ * (μ : G)⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hμM) _).1 ((pCoreOf 2 M).inv_mem h1)
    have h3 := (pCoreOf 2 M).mul_mem h1 h2
    have e : ((σ * μ * σ⁻¹ * μ⁻¹ : ↥N) : G) = (σ : G) * ((μ : G) * (σ : G)⁻¹ * (μ : G)⁻¹) := by
      simp [mul_assoc]
    rw [e]
    exact h3
  have hcomm0 : ⁅barX p N S, barX p N K⁆ = ⊥ :=
    commutator_eq_bot_of_cover hSK hcov hcomm
      (isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hON)
      fun T hTK hn h2 => eq_bot_of_normal_two_group hp (ne_two_of h) hK hTK hn h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm0

end NoCover

section Input1916

@[expose] def ActsAsPerm {K : Type*} [Group K] {n : ℕ} (B : Subgroup (MulAut K))
    (φ : K ≃* alternatingGroup (Fin n)) (ρ : ↥B →* Equiv.Perm (Fin n)) : Prop :=
  ∀ (b : ↥B) (x : K), ((φ ((b : MulAut K) x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
    ρ b * ((φ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * (ρ b)⁻¹

@[expose] def SemiregOutside {n : ℕ} {B : Type*} [Group B] (ρ : B →* Equiv.Perm (Fin n))
    (Ω₀ : Set (Fin n)) : Prop :=
  (∀ b : B, ∀ j ∈ Ω₀, ρ b j = j) ∧ ∀ b : B, b ≠ 1 → ∀ j : Fin n, j ∉ Ω₀ → ρ b j ≠ j

@[expose] def Alt1916 (p k : ℕ) {K : Type*} [Group K] (B : Subgroup (MulAut K)) : Prop :=
  ∃ m r : ℕ, 0 < m ∧ (r = 2 ∨ r = 4) ∧
    ∃ (φ : K ≃* alternatingGroup (Fin (m * p ^ k + r)))
      (ρ : ↥B →* Equiv.Perm (Fin (m * p ^ k + r))) (Ω₀ : Set (Fin (m * p ^ k + r))),
      ActsAsPerm B φ ρ ∧ Ω₀.ncard = r ∧ SemiregOutside ρ Ω₀

@[expose] def Spor1916 (p k : ℕ) {K : Type*} [Group K] (B : Subgroup (MulAut K)) : Prop :=
  p = 5 ∧ k = 2 ∧ IsSporType .Fi22 K ∧ B ≤ innerAut K ∧
    ∀ B' : Subgroup (MulAut K), IsElemAbelian p B' → p ^ 2 ≤ Nat.card B' →
      IsWeaklyLocallyOTwoBalanced p 2 B'

@[expose] def Lie1916 (p k : ℕ) {K : Type*} [Group K] (B : Subgroup (MulAut K)) : Prop :=
  k = 2 ∧ (∃ q : ℕ, p ∣ q - 1 ∧ IsLpType p q (K ⧸ Subgroup.center K)) ∧ B ≤ innerAut K ∧
    ∀ B' : Subgroup (MulAut K), IsElemAbelian p B' → p ^ 2 ≤ Nat.card B' →
      IsWeaklyLocallyOTwoBalanced p 2 B'

@[expose] def Input19_16 : Prop :=
  ∀ (p k : ℕ), p.Prime → p ≠ 2 → 2 ≤ k →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → CFSG.Open.IsQuasisimple K →
      GLAPPrimeCore p K = ⊥ →
      ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ k →
        (IsLocallyOTwoBalanced p k B ∨ Alt1916 p k B ∨ Spor1916 p k B ∨ Lie1916 p k B) ∧
        (¬ IsWeaklyLocallyOTwoBalanced p 2 B →
          p = 3 ∧ ∃ m : ℕ, 0 < m ∧ Nonempty (K ≃* alternatingGroup (Fin (m * 3 ^ k + 4))))

@[expose] def Input19_16Fixed : Prop :=
  ∀ (p k : ℕ), p.Prime → p ≠ 2 → 2 ≤ k →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → CFSG.Open.IsQuasisimple K →
      GLAPPrimeCore p K = ⊥ →
      ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ k →
        (IsLocallyOTwoBalanced p k B ∨ Alt1916 p k B ∨ Spor1916 p k B ∨ Lie1916 p k B) ∧
        (¬ IsWeaklyLocallyOTwoBalanced p 2 B →
          p = 3 ∧ ∃ m : ℕ, 0 < m ∧ Nonempty (K ≃* alternatingGroup (Fin (m * 3 ^ 2 + 4))))

@[expose] def Input19_16Main : Prop :=
  ∀ (p k : ℕ), p.Prime → p ≠ 2 → 2 ≤ k →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → CFSG.Open.IsQuasisimple K →
      GLAPPrimeCore p K = ⊥ →
      ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ k →
        IsLocallyOTwoBalanced p k B ∨ Alt1916 p k B ∨ Spor1916 p k B ∨ Lie1916 p k B

theorem input19_16Main_of_fixed (h : Input19_16Fixed) : Input19_16Main :=
  fun p k hp hp2 hk K _ _ hKG hKq hO B hB hBc => (h p k hp hp2 hk K hKG hKq hO B hB hBc).1

end Input1916

section Trichotomy

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def autHom (p : ℕ) {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G)) :
    ↥F →* MulAut (barOf p K) :=
  (barAut p K).comp (Subgroup.inclusion hFK)

theorem autHom_apply (p : ℕ) {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G)) (f : ↥F) :
    autHom p hFK f = barAut p K ⟨(f : G), hFK f.2⟩ := rfl

theorem autBar_eq_range (p : ℕ) {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G)) :
    autBar p F K = (autHom p hFK).range := by
  unfold autBar autHom
  rw [MonoidHom.range_comp, Subgroup.inclusion_range, inf_eq_left.2 hFK]

theorem autHom_injective (p : ℕ) {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G))
    (hF : F ⊓ centBar p ⊤ K = ⊥) : Function.Injective (autHom p hFK) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro f hf
  rw [MonoidHom.mem_ker] at hf
  have hmem : (f : G) ∈ F ⊓ centBar p ⊤ K := by
    refine ⟨f.2, ⟨Subgroup.inclusion hFK f, ?_, rfl⟩, Subgroup.mem_top _⟩
    exact (show (Subgroup.inclusion hFK f) ∈ MonoidHom.ker (barAut p K) from hf)
  rw [hF, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (Subtype.ext hmem)

theorem card_autBar (p : ℕ) {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G))
    (hF : F ⊓ centBar p ⊤ K = ⊥) : Nat.card (autBar p F K) = Nat.card F := by
  rw [autBar_eq_range p hFK]
  exact (Nat.card_congr (MonoidHom.ofInjective (autHom_injective p hFK hF)).toEquiv).symm

theorem isElemAbelian_autBar {p : ℕ} {F K : Subgroup G} (hFK : F ≤ Subgroup.normalizer (K : Set G))
    (hF : IsElemAbelian p F) : IsElemAbelian p (autBar p F K) := by
  unfold autBar
  rw [inf_eq_left.2 hFK]
  exact (hF.subgroupOf _).map _

omit [Finite G] in
theorem isQuasisimple_barOf129 {p : ℕ} (hp : p.Prime) {X L : Subgroup G} [Finite G]
    (h : GLAPComponent p X L) : CFSG.Open.IsQuasisimple (barOf p L) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv (quotEquivBarX hp h.1 h.2.1)
    h.2.2.1.2.2

theorem apply_input1916 (hI : Input19_16) {m p : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : GLAPComponent p N K)
    {Bb : Subgroup (MulAut (barOf p K))} {k : ℕ} (hk : 2 ≤ k) (hBel : IsElemAbelian p Bb)
    (hBc : Nat.card Bb = p ^ k) :
    (IsLocallyOTwoBalanced p k Bb ∨ Alt1916 p k Bb ∨ Spor1916 p k Bb ∨ Lie1916 p k Bb) ∧
      (¬ IsWeaklyLocallyOTwoBalanced p 2 Bb →
        p = 3 ∧ ∃ m : ℕ, 0 < m ∧ Nonempty (barOf p K ≃* alternatingGroup (Fin (m * 3 ^ k + 4)))) := by
  have hp := prime_of h
  have hKtop : K ≠ ⊤ := fun htop => N_ne_top h (top_le_iff.1 (htop ▸ hK.1))
  have hKG : CFSG.Open.IsKGroup (barOf p K) :=
    (h.standing.kProper.isKGroup K hKtop).quotient (GLAPPrimeCore p ↥K)
  exact hI p k hp (ne_two_of h) hk (barOf p K) hKG (isQuasisimple_barOf129 hp hK)
    (glaPPrimeCore_quotient_eq_bot hp) Bb hBel hBc

theorem apply_input1916Main (hI : Input19_16Main) {m p : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : GLAPComponent p N K)
    {Bb : Subgroup (MulAut (barOf p K))} {k : ℕ} (hk : 2 ≤ k) (hBel : IsElemAbelian p Bb)
    (hBc : Nat.card Bb = p ^ k) :
    IsLocallyOTwoBalanced p k Bb ∨ Alt1916 p k Bb ∨ Spor1916 p k Bb ∨ Lie1916 p k Bb := by
  have hp := prime_of h
  have hKtop : K ≠ ⊤ := fun htop => N_ne_top h (top_le_iff.1 (htop ▸ hK.1))
  have hKG : CFSG.Open.IsKGroup (barOf p K) :=
    (h.standing.kProper.isKGroup K hKtop).quotient (GLAPPrimeCore p ↥K)
  exact hI p k hp (ne_two_of h) hk (barOf p K) hKG (isQuasisimple_barOf129 hp hK)
    (glaPPrimeCore_quotient_eq_bot hp) Bb hBel hBc

end Trichotomy

section Weak

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

omit [Finite G] in
theorem mem_centBar_top_iff {p : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ centBar p ⊤ K ↔ barAut p K ⟨g, hg⟩ = 1 := by
  unfold centBar
  simp only [inf_top_eq, Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy, hyg⟩
    have : y = ⟨g, hg⟩ := Subtype.ext hyg
    rwa [this] at hy
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite G] in
theorem mem_normalizer_of_mem_centBar {p : ℕ} {K : Subgroup G} {x : G} (hx : x ∈ centBar p ⊤ K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  unfold centBar at hx
  simp only [inf_top_eq, Subgroup.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

omit [Finite G] in
theorem conj_mem_centBar {p : ℕ} {K : Subgroup G} {n x : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hx : x ∈ centBar p ⊤ K) : n * x * n⁻¹ ∈ centBar p ⊤ K := by
  have hxn := mem_normalizer_of_mem_centBar hx
  have hnxn : n * x * n⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hxn) (Subgroup.inv_mem _ hn)
  rw [mem_centBar_top_iff hnxn]
  have hx1 := (mem_centBar_top_iff hxn).1 hx
  have : (⟨n * x * n⁻¹, hnxn⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨n, hn⟩ * ⟨x, hxn⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, hx1]
  simp

theorem barX_le_centralizer_of_le_centBar {p : ℕ} (hp : p.Prime) {N K S : Subgroup G}
    (hK : GLAPComponent p N K) (hSN : S ≤ N) (hS : S ≤ centBar p ⊤ K) :
    barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have hsn := mem_normalizer_of_mem_centBar (hS hs)
  have h1 := (mem_centBar_top_iff hsn).1 (hS hs)
  have hmk : barAut p K ⟨s, hsn⟩ (QuotientGroup.mk ⟨t, ht⟩) = QuotientGroup.mk ⟨t, ht⟩ := by
    rw [h1]; rfl
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hmk
  have hker := QuotientGroup.eq.1 hmk
  have hu : (s * t * s⁻¹)⁻¹ * t ∈ GLAPPrimeCoreOf p K := by
    refine ⟨_, hker, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hconj := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p K ht) _).1
    ((GLAPPrimeCoreOf p K).inv_mem hu)
  have e : s * t * s⁻¹ * t⁻¹ = t * ((s * t * s⁻¹)⁻¹ * t)⁻¹ * t⁻¹ := by group
  rw [e]
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hK.2.1 hconj

theorem le_normalizer_of_barX {p : ℕ} (hp : p.Prime) {N K S : Subgroup G}
    (hK : GLAPComponent p N K) (hSN : S ≤ N)
    (hSK : barX p N S ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) :
    S ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
  mem_normalizer_of_barX_normalizes hp le_rfl hK (hSN hg) (Subgroup.le_normalizer (hSN hg))
    (hSK ⟨⟨g, hSN hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩)

theorem exists_comm_not_mem_centBar (h : Cex127 G m p B M E A N D) {S K : Subgroup G}
    (hS : IsMinS M N A S) (hK : GLAPComponent p N K)
    (hFne : A ⊓ Subgroup.centralizer (S : Set G) ≠ A)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKc : ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) :
    ∃ σ ∈ S, ∃ a ∈ A, σ * a * σ⁻¹ * a⁻¹ ∉ centBar p ⊤ K := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  have hSN : S ≤ N := hS.le.trans h.hO
  set R : Subgroup G := S ⊓ centBar p ⊤ K with hR
  have hRS : R < S := by
    refine lt_of_le_of_ne inf_le_left fun heq => hKc ?_
    exact barX_le_centralizer_of_le_centBar hp hK hSN (heq ▸ inf_le_right)
  have hCS : S ⊓ Subgroup.centralizer (A : Set G) < S := by
    refine lt_of_le_of_ne inf_le_left fun heq => hFne ?_
    refine le_antisymm inf_le_left fun a ha => Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro x hx
    have : x ∈ S ⊓ Subgroup.centralizer (A : Set G) := by rw [heq]; exact hx
    exact (Subgroup.mem_centralizer_iff.1 this.2 a ha).symm
  have hRN : R ≤ pCoreOf 2 N := by
    by_contra hn
    exact absurd (hS.min R (inf_le_left.trans hS.le) (le_normalizer_of_conj_mem fun a ha x hx =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hS.norm ha) x).1 hx.1,
        conj_mem_centBar (hAK ha) hx.2⟩) hn) (not_le.2 (card_lt_of_lt' hRS))
  have hCN : S ⊓ Subgroup.centralizer (A : Set G) ≤ pCoreOf 2 N := by
    by_contra hn
    exact absurd (hS.min _ (inf_le_left.trans hS.le)
      (normalizer_inf_centralizer (A_el h) le_rfl hS.norm) hn) (not_le.2 (card_lt_of_lt' hCS))
  have hSle : S ≤ pCoreOf 2 N := by
    intro x hx
    have hRn : A ≤ Subgroup.normalizer (R : Set G) :=
      le_normalizer_of_conj_mem fun a ha y hy =>
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hS.norm ha) y).1 hy.1,
          conj_mem_centBar (hAK ha) hy.2⟩
    have hSRn : x ∈ Subgroup.normalizer (R : Set G) :=
      (le_normalizer_of_conj_mem (A := S) (H := R) fun s hs y hy =>
        Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs),
          conj_mem_centBar (hSK hs) hy.2⟩) hx
    have hxcomm : ∀ u ∈ A, u * x * u⁻¹ * x⁻¹ ∈ R := by
      intro u hu
      have h1 : x * u * x⁻¹ * u⁻¹ ∈ centBar p ⊤ K := hcon x hx u hu
      have h1' := (centBar p ⊤ K).inv_mem h1
      have e : (x * u * x⁻¹ * u⁻¹)⁻¹ = u * x * u⁻¹ * x⁻¹ := by group
      rw [e] at h1'
      refine Subgroup.mem_inf.2 ⟨?_, h1'⟩
      exact S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hS.norm hu) x).1 hx) (S.inv_mem hx)
    have hVp : ¬ p ∣ Nat.card R := not_dvd_card_S h (inf_le_left.trans hS.le)
    obtain ⟨v, hvR, hfix⟩ := exists_fixed_in_coset' (p := p) (U := A) (V := R)
      (A_el h).isPGroup hVp hRn hSRn hxcomm
    have hyS : x * v ∈ S := S.mul_mem hx hvR.1
    have hyC : x * v ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hfix u hu
      calc u * (x * v) = u * (x * v) * u⁻¹ * u := by group
        _ = (x * v) * u := by rw [this]
    have e : x = (x * v) * v⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 N).mul_mem (hCN (Subgroup.mem_inf.2 ⟨hyS, hyC⟩))
      ((pCoreOf 2 N).inv_mem (hRN hvR))
  exact hS.not_le hSle

omit [Finite G] in
theorem autBar_mono (p : ℕ) {X Y K : Subgroup G} (h : X ≤ Y) : autBar p X K ≤ autBar p Y K :=
  Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf).2 (inf_le_inf_right _ h ((Subgroup.mem_subgroupOf).1 hx))

omit [Finite G] in
theorem barAut_mem_autBar {p : ℕ} {X K : Subgroup G} {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : barAut p K ⟨g, hg⟩ ∈ autBar p X K :=
  ⟨⟨g, hg⟩, (Subgroup.mem_subgroupOf).2 ⟨hgX, hg⟩, rfl⟩

theorem le_normalizer_deltaTwo {N F A : Subgroup G} (hA : ∃ p, IsElemAbelian p A) (hFA : F ≤ A)
    (hAN : A ≤ N) : A ≤ Subgroup.normalizer (deltaTwo N F : Set G) := by
  obtain ⟨p, hAel⟩ := hA
  refine le_normalizer_of_conj_mem fun a ha x hx => ?_
  unfold deltaTwo at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro d hd hd1
  have haCd : a ∈ N ⊓ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_inf.2 ⟨hAN ha, Subgroup.mem_centralizer_singleton_iff.2
      (elemAbelian_comm hAel ha (hFA hd))⟩
  have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ haCd
  exact (Subgroup.mem_normalizer_iff.1 hn x).1 (hx d hd hd1)

omit [Finite G] in
theorem mem_autBar_iff {p : ℕ} {X K : Subgroup G} {x : MulAut (barOf p K)} :
    x ∈ autBar p X K ↔ ∃ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)), g ∈ X ∧
      barAut p K ⟨g, hg⟩ = x := by
  unfold autBar
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨γ, ⟨hγX, -⟩, rfl⟩
    exact ⟨γ.1, γ.2, hγX, rfl⟩
  · rintro ⟨g, hg, hgX, rfl⟩
    exact ⟨⟨g, hg⟩, ⟨hgX, hg⟩, rfl⟩

theorem conj_mem_innerAut {K : Type*} [Group K] (φ : MulAut K) {x : MulAut K}
    (hx : x ∈ innerAut K) : φ * x * φ⁻¹ ∈ innerAut K := by
  obtain ⟨k, rfl⟩ := hx
  refine ⟨φ k, ?_⟩
  ext y
  simp [MulAut.conj_apply]

omit [Finite G] in
theorem localDeltaTwoIn_mono {M : Type*} [Group M] {H D D' : Subgroup M} (h : D' ≤ D) :
    localDeltaTwoIn H D ≤ localDeltaTwoIn H D' :=
  le_iInf₂ fun d hd => le_iInf fun hd1 => iInf₂_le d (h hd) |>.trans (iInf_le _ hd1)

theorem not_weakly_balanced (h121 : Prop121_corStatement) (h : Cex127 G m p B M E A N D)
    {S F K : Subgroup G} (hS : IsMinS M N A S) (hFdef : F = A ⊓ Subgroup.centralizer (S : Set G))
    (hFne : F ≠ A) (hK : GLAPComponent p N K) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFc : F ⊓ centBar p ⊤ K = ⊥)
    (hr : 2 ≤ CFSG.Open.pRank p F)
    (hKc : ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)))
    (hW : autBar p (deltaTwo N F) K ≤
      localDeltaTwoIn (innerAut (barOf p K) ⊔ autBar p (deltaTwo N F) K) (autBar p F K)) :
    ¬ IsWeaklyLocallyOTwoBalanced p 2 (autBar p A K) := by
  intro hweak
  have hp := prime_of h
  have hFA : F ≤ A := hFdef ▸ inf_le_left
  have hFS : F ≤ Subgroup.centralizer (S : Set G) := hFdef ▸ inf_le_right
  have hFK : F ≤ Subgroup.normalizer (K : Set G) := hFA.trans hAK
  obtain ⟨σ, hσS, a, haA, hnot⟩ :=
    exists_comm_not_mem_centBar h hS hK (hFdef ▸ hFne) hSK hAK hKc
  have hFel : IsElemAbelian p (autBar p F K) := isElemAbelian_autBar hFK ((A_el h).mono hFA)
  obtain ⟨D₂, hD₂le, hD₂el, hD₂c⟩ := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact exists_le_isElemAbelian_card hFel (n := 2) (by
      rw [card_autBar p hFK hFc, card_eq_pow_pRank hp ((A_el h).mono hFA)]
      exact pow_dvd_pow p hr)
  have hD : IsEkIn p 2 (autBar p A K) D₂ := ⟨hD₂le.trans (autBar_mono p hFA), hD₂el, hD₂c⟩
  set Δ := deltaTwo N F with hΔ
  set H := innerAut (barOf p K) ⊔ autBar p Δ K with hH
  have hAΔ := le_normalizer_deltaTwo (N := N) ⟨p, A_el h⟩ hFA (A_le_N h)
  have hBH : autBar p A K ≤ Subgroup.normalizer (H : Set (MulAut (barOf p K))) := by
    refine le_normalizer_of_conj_mem fun b hb x hx => ?_
    obtain ⟨a', ha'K, ha'A, hba⟩ := mem_autBar_iff.1 hb
    have hW' : ∀ y ∈ autBar p Δ K, b * y * b⁻¹ ∈ autBar p Δ K := by
      intro y hy
      obtain ⟨g, hgK, hgΔ, hyg⟩ := mem_autBar_iff.1 hy
      have hg' : a' * g * a'⁻¹ ∈ Δ := (Subgroup.mem_normalizer_iff.1 (hAΔ ha'A) g).1 hgΔ
      have hg'K : a' * g * a'⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ ha'K hgK) (Subgroup.inv_mem _ ha'K)
      refine mem_autBar_iff.2 ⟨a' * g * a'⁻¹, hg'K, hg', ?_⟩
      have : (⟨a' * g * a'⁻¹, hg'K⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨a', ha'K⟩ * ⟨g, hgK⟩ * ⟨a', ha'K⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hba, hyg]
    have key : H.map (MulAut.conj b).toMonoidHom ≤ H := by
      rw [hH, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact conj_mem_innerAut b hy
      · rintro _ ⟨y, hy, rfl⟩
        exact hW' y hy
    have := key ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hcomm := hweak _ hD H le_sup_left hBH
  have hW' := hW.trans (localDeltaTwoIn_mono (H := H) hD₂le)
  have hσΔ : σ ∈ Δ := le_deltaTwo h121 h hS hFA hFS hσS
  have h1 : barAut p K ⟨σ, hSK hσS⟩ ∈ autBar p Δ K := barAut_mem_autBar hσΔ (hSK hσS)
  have h2 : barAut p K ⟨a, hAK haA⟩ ∈ autBar p A K := barAut_mem_autBar haA (hAK haA)
  have h3 := Subgroup.commutator_mem_commutator (hW' h1) h2
  rw [hcomm, Subgroup.mem_bot] at h3
  apply hnot
  have hc : σ * a * σ⁻¹ * a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSK hσS) (hAK haA))
      (Subgroup.inv_mem _ (hSK hσS))) (Subgroup.inv_mem _ (hAK haA))
  rw [mem_centBar_top_iff hc]
  have : (⟨σ * a * σ⁻¹ * a⁻¹, hc⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨σ, hSK hσS⟩ * ⟨a, hAK haA⟩ * ⟨σ, hSK hσS⟩⁻¹ * ⟨a, hAK haA⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [commutatorElement_def] at h3
  exact h3

end Weak

section Cover

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem exists_isSylowIn_above {p : ℕ} [Fact p.Prime] {X P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup p ↥P) : ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem normalizer_le_of_rank_four (h : Cex127 G m p B M E A N D)
    (hA3 : CFSG.Open.pRank p A = 3) {Y X : Subgroup G} (hYM : Y ≤ M) (hYel : IsElemAbelian p Y)
    (hY4 : 4 ≤ CFSG.Open.pRank p Y) (hXY : X ≤ Y) (hX2 : 2 ≤ CFSG.Open.pRank p X) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR, hYR⟩ := exists_isSylowIn_above hYM hYel.isPGroup
  have h104 := lemma104_v_holds h.toSec11.toSec10Fails h.pair (Or.inr hA3) hR
  by_cases hX4 : 4 ≤ CFSG.Open.pRank p X
  · exact (le_sSup (show Subgroup.normalizer (X : Set G) ∈
      {N | ∃ Q : Subgroup G, Q ≤ R ∧ 4 ≤ CFSG.Open.pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)} from
      ⟨X, hXY.trans hYR, hX4, rfl⟩)).trans h104.2
  · push Not at hX4
    have hXel : IsElemAbelian p X := hYel.mono hXY
    have hXcard := card_eq_pow_pRank hp hXel
    have hYcard := card_eq_pow_pRank hp hYel
    obtain ⟨E4, hE4c, hXE4, hE4Y⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
      (show Nat.card X ∣ p ^ 4 by rw [hXcard]; exact pow_dvd_pow p (by omega))
      (show p ^ 4 ∣ Nat.card Y by rw [hYcard]; exact pow_dvd_pow p hY4) hXY
    have hE4R : E4 ≤ R := hE4Y.trans hYR
    have hE4 : IsEkIn p 4 R E4 := ⟨hE4R, hYel.mono hE4Y, hE4c⟩
    obtain ⟨-, -, E', hE', hE4E'⟩ := h104.1 E4 hE4
    have hcore : GLBCore p 2 E' ≤ M := hE'.2.clause_d
    exact (le_sSup (show Subgroup.normalizer (X : Set G) ∈
      {N | ∃ Q : Subgroup G, Q ≤ E' ∧ 2 ≤ CFSG.Open.pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)} from
      ⟨X, hXE4.trans hE4E', hX2, rfl⟩)).trans hcore

theorem exists_isSCp_top_above {p : ℕ} {W : Subgroup G} (hW : IsElemAbelian p W) :
    ∃ A₁ : Subgroup G, IsSCp p ⊤ A₁ ∧ W ≤ A₁ := by
  obtain ⟨A₁, hWA₁, hmax⟩ := (Set.toFinite {E : Subgroup G | W ≤ E ∧ IsElemAbelian p E}).exists_le_maximal
    ⟨le_rfl, hW⟩
  exact ⟨A₁, ⟨le_top, hmax.1.2, fun E' _ hE'el hle =>
    le_antisymm (hmax.2 ⟨hWA₁.trans hle, hE'el⟩ hle) hle⟩, hWA₁⟩

theorem ddKey_not_le_of_rank_lt {p : ℕ} {E A A' : Subgroup G}
    (h1 : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p (E ⊓ A'))
    (h3 : CFSG.Open.pRank p A < CFSG.Open.pRank p A') : ¬ ddKey p E A' ≤ ddKey p E A := by
  intro hle
  unfold ddKey at hle
  rcases Prod.Lex.toLex_le_toLex.1 hle with ha | ⟨e1, hb⟩
  · omega
  · rcases Prod.Lex.toLex_le_toLex.1 hb with hb' | ⟨e2, hc⟩
    · omega
    · rcases Prod.Lex.toLex_le_toLex.1 hc with hc' | ⟨e3, hd⟩
      · omega
      · rcases Prod.Lex.toLex_le_toLex.1 hd with hd' | ⟨e4, _⟩
        · omega
        · omega

theorem normalizer_le_of_rank_gt (h : Cex127 G m p B M E A N D) {W : Subgroup G}
    (hWel : IsElemAbelian p W) (hA0 : E ⊓ A ≤ W)
    (hrank : CFSG.Open.pRank p A < CFSG.Open.pRank p W) {X : Subgroup G} (hXW : X ≤ W)
    (hX2 : 2 ≤ CFSG.Open.pRank p X) : Subgroup.normalizer (X : Set G) ≤ M := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₁, hA₁sc, hWA₁⟩ := exists_isSCp_top_above hWel
  have hA₁el : IsElemAbelian p A₁ := hA₁sc.2.1
  have hcoreE : GLBCore p 2 E ≤ M := (uniq_E h).clause_d
  have hA₁M : A₁ ≤ M := by
    intro x hx
    have hc : ∀ z ∈ E ⊓ A, x * z * x⁻¹ = z := fun z hz => by
      have := elemAbelian_comm hA₁el hx (hWA₁ (hA0 hz))
      rw [this]; group
    have hxN : x ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy; rw [hc y hy]; exact hy
      · intro hy
        have hc' : ∀ z ∈ E ⊓ A, x⁻¹ * z * x⁻¹⁻¹ = z := fun z hz => by
          have := elemAbelian_comm hA₁el (A₁.inv_mem hx) (hWA₁ (hA0 hz))
          rw [this]; group
        have h1 := hc' _ hy
        have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
        have h3 := h2.symm.trans h1
        rw [h3]
        exact hy
    exact (le_sSup (show Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∈
      {N | ∃ Q : Subgroup G, Q ≤ E ∧ 2 ≤ CFSG.Open.pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)} from
      ⟨E ⊓ A, inf_le_left, two_le_rank_inf h, rfl⟩)).trans hcoreE hxN
  have hA₁rank : CFSG.Open.pRank p A < CFSG.Open.pRank p A₁ :=
    lt_of_lt_of_le hrank (CFSG.SectionRank.pRank_mono hp.one_lt hWA₁)
  have hA₁sc' : IsSCstar p M A₁ :=
    ⟨⟨hA₁M, hA₁el, fun E' hE'M hE'el hle => hA₁sc.2.2 E' le_top hE'el hle⟩,
      le_trans (three_le_rank_A h) hA₁rank.le⟩
  by_cases hU : IsUniquenessTwoLocal p A₁ M
  · have hcore : GLBCore p 2 A₁ ≤ M := hU.clause_d
    exact (le_sSup (show Subgroup.normalizer (X : Set G) ∈
      {N | ∃ Q : Subgroup G, Q ≤ A₁ ∧ 2 ≤ CFSG.Open.pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)} from
      ⟨X, hXW.trans hWA₁, hX2, rfl⟩)).trans hcore
  · exfalso
    have hfirst : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p (E ⊓ A₁) :=
      CFSG.SectionRank.pRank_mono hp.one_lt (le_inf inf_le_left (hA0.trans hWA₁))
    have hDD : inDDp p M E A₁ :=
      ⟨h.pair.1.1, ⟨hA₁sc', hU⟩, le_trans (two_le_rank_inf h) hfirst⟩
    exact ddKey_not_le_of_rank_lt (E := E) (A := A) (A' := A₁) hfirst hA₁rank (h.pair.2 E A₁ hDD)

end Cover

section Setup2Sec

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

structure Setup2 (M A N : Subgroup G) (p : ℕ) (S F K : Subgroup G) : Prop where
  hS : IsMinS M N A S
  hFdef : F = A ⊓ Subgroup.centralizer (S : Set G)
  hyp : ∃ B' : Subgroup G, B' ≤ F ∧ (B'.subgroupOf A).index = p
  hr : 2 ≤ CFSG.Open.pRank p F
  hK : GLAPComponent p N K
  hSK : barX p N S ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))
  hKc : ¬ barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))
  hFK : F ≤ Subgroup.normalizer (K : Set G)
  hFc : F ⊓ centBar p ⊤ K = ⊥
  hbal : ¬ IsCompLocallyOTwoBalanced p (CFSG.Open.pRank p F) F K
  hW : autBar p (deltaTwo N F) K ≤
    localDeltaTwoIn (innerAut (barOf p K) ⊔ autBar p (deltaTwo N F) K) (autBar p F K)
  hnc : ¬ Covers p N M K

theorem exists_setup2 (h191 : Input19_1_6) (h121 : Prop121_corStatement) (hI : Input19_1_two)
    (h : Cex127 G m p B M E A N D) : ∃ S F K : Subgroup G, Setup2 M A N p S F K := by
  have hp := prime_of h
  obtain ⟨S, hS⟩ := exists_minS h
  obtain ⟨B', hB'A, hB'i, hB'S⟩ := exists_hyperplane_le_centralizer h hS
  set F : Subgroup G := A ⊓ Subgroup.centralizer (S : Set G) with hFdef
  have hFA : F ≤ A := inf_le_left
  have hFS : F ≤ Subgroup.centralizer (S : Set G) := inf_le_right
  have hB'F : B' ≤ F := le_inf hB'A hB'S
  have hr : 2 ≤ CFSG.Open.pRank p F := by
    have h1 := pRank_le_pRank_add_one hp (A_el h) hB'A hB'i.le
    have h2 := three_le_rank_A h
    have h3 : CFSG.Open.pRank p B' ≤ CFSG.Open.pRank p F := CFSG.SectionRank.pRank_mono hp.one_lt hB'F
    omega
  obtain ⟨K, hK, hSK, hKc, hFK, hFc, hbal, hW⟩ := exists_component h191 h121 hI h hS hFA hFS hr
  exact ⟨S, F, K, hS, hFdef, ⟨B', hB'F, hB'i⟩, hr, hK, hSK, hKc, hFK, hFc, hbal, hW,
    not_covers h hS hK hSK hKc⟩

namespace Setup2

variable {S F K : Subgroup G}

theorem F_le_A (hs : Setup2 M A N p S F K) : F ≤ A := hs.hFdef ▸ inf_le_left

theorem F_le_cent (hs : Setup2 M A N p S F K) : F ≤ Subgroup.centralizer (S : Set G) :=
  hs.hFdef ▸ inf_le_right

theorem S_le_N (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) : S ≤ N :=
  hs.hS.le.trans h.hO

theorem S_le_normalizer (hp : p.Prime) (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) :
    S ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_barX hp hs.hK (hs.S_le_N h) hs.hSK

theorem index_le (hp : p.Prime) (hs : Setup2 M A N p S F K) : (F.subgroupOf A).index ≤ p := by
  obtain ⟨B', hB'F, hB'i⟩ := hs.hyp
  have h1 : (F.subgroupOf A).index ∣ (B'.subgroupOf A).index := Subgroup.relIndex_dvd_of_le_left A hB'F
  rw [hB'i] at h1
  exact Nat.le_of_dvd hp.pos h1

theorem pRank_A_le (hp : p.Prime) (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) :
    CFSG.Open.pRank p A ≤ CFSG.Open.pRank p F + 1 :=
  pRank_le_pRank_add_one hp (A_el h) hs.F_le_A (hs.index_le hp)

end Setup2

end Setup2Sec

end Lemma129

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
