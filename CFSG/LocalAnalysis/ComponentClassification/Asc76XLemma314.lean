module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma313

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def nbr (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | adj Ω K J}

@[expose] def orb (X P : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ x ∈ X, Q = rightConjugate P x}

theorem rightConjugate_injective (g : G) :
    Function.Injective (rightConjugate · g : Subgroup G → Subgroup G) := by
  intro J L h
  have h' := congrArg (rightConjugate · g⁻¹) h
  simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using h'

theorem image_rightConjugate_image (s : Set (Subgroup G)) (g h : G) :
    (rightConjugate · h) '' ((rightConjugate · g) '' s) = (rightConjugate · (g * h)) '' s := by
  rw [Set.image_image]
  simp only [rightConjugate_mul]

theorem ncard_image_rightConjugate (s : Set (Subgroup G)) (g : G) :
    ((rightConjugate · g) '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s (rightConjugate_injective g)

theorem sSup_nbr_le_normalizer (Ω : Set (Subgroup G)) (K : Subgroup G) :
    sSup (nbr Ω K) ≤ normalizer (K : Set G) :=
  sSup_le fun _ hJ => hJ.2.2

theorem adj_rightConjugate_of_mem_normalizer {Ω : Set (Subgroup G)}
    (hΩinv : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω) {K J : Subgroup G} (h : adj Ω K J) {g : G}
    (hg : g ∈ normalizer (K : Set G)) : adj Ω K (rightConjugate J g) := by
  have h' := adj_conj hΩinv h g
  rwa [(rightConjugate_eq_self_iff K g).mpr hg] at h'

theorem nbr_rightConjugate {Ω : Set (Subgroup G)}
    (hΩinv : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω) (K : Subgroup G) (g : G) :
    nbr Ω (rightConjugate K g) = (rightConjugate · g) '' nbr Ω K := by
  ext J
  constructor
  · intro hJ
    refine ⟨rightConjugate J g⁻¹, ?_, ?_⟩
    · show adj Ω K (rightConjugate J g⁻¹)
      have h := adj_conj hΩinv hJ g⁻¹
      simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using h
    · simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  · rintro ⟨L, hL, rfl⟩
    exact adj_conj hΩinv hL g

theorem mem_of_reach_of_closed {Ω C : Set (Subgroup G)} {K J : Subgroup G} (hK : K ∈ C)
    (hC : ∀ N ∈ C, ∀ N', adj Ω N N' → N' ∈ C) (h : reach Ω K J) : J ∈ C := by
  induction h with
  | refl => exact hK
  | tail _ hab ih => exact hC _ ih _ hab

theorem image_rightConjugate_eq_of_mem {α : Set (Subgroup G)}
    (hblock : ∀ g : G, (rightConjugate · g) '' α = α ∨ Disjoint ((rightConjugate · g) '' α) α)
    {x y : G} {M : Subgroup G} (hx : M ∈ (rightConjugate · x) '' α)
    (hy : M ∈ (rightConjugate · y) '' α) :
    (rightConjugate · x) '' α = (rightConjugate · y) '' α := by
  rcases hblock (x * y⁻¹) with h | h
  · conv_rhs => rw [← h]
    rw [image_rightConjugate_image, inv_mul_cancel_right]
  · exfalso
    have h1 : rightConjugate M y⁻¹ ∈ (rightConjugate · (x * y⁻¹)) '' α := by
      obtain ⟨N, hN, rfl⟩ := hx
      exact ⟨N, hN, (rightConjugate_mul N x y⁻¹).symm⟩
    have h2 : rightConjugate M y⁻¹ ∈ α := by
      obtain ⟨N, hN, rfl⟩ := hy
      simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using hN
    exact Set.disjoint_left.mp h h1 h2

theorem mem_normalizer_sSup [Finite G] {π : Set (Subgroup G)} {g : G}
    (h : ∀ J ∈ π, rightConjugate J g ∈ π) : g ∈ normalizer ((sSup π : Subgroup G) : Set G) := by
  have hle : rightConjugate (sSup π) g ≤ sSup π := by
    rw [rightConjugate, map_le_iff_le_comap]
    refine sSup_le fun J hJ x hx => ?_
    have h1 : (MulAut.conj g⁻¹) x ∈ rightConjugate J g := ⟨x, hx, rfl⟩
    exact le_sSup (h J hJ) h1
  exact (rightConjugate_eq_self_iff _ g).mp
    (eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))

theorem barMk_mem_normalizer {X J : Subgroup G} {x : X}
    (hx : (x : G) ∈ normalizer (J : Set G)) :
    barMk X x ∈ normalizer ((bar X J : Subgroup (BarGroup X)) : Set (BarGroup X)) := by
  rw [← rightConjugate_eq_self_iff, ← bar_rightConjugate, (rightConjugate_eq_self_iff J _).mpr hx]

theorem lemma28_nbr (h28 : Asc76Lemma28) {Ω : Set (Subgroup G)} {K₀ : Subgroup G} [Finite G]
    (hΩK : Ω = Set.range (rightConjugate K₀)) (hgen : sSup Ω = ⊤)
    (hsymm : ∀ K ∈ Ω, ∀ J, adj Ω K J → adj Ω J K) (hconn : ∀ K ∈ Ω, ∀ J ∈ Ω, reach Ω K J)
    (hcond : ∀ K ∈ Ω, ∀ J L, adj Ω K J → adj Ω K L →
      adj Ω L J ∨ ∃ x ∈ J ⊔ L, L = rightConjugate J x)
    {K P : Subgroup G} (hK : K ∈ Ω) (hP : adj Ω K P)
    (hmax : ∀ Q, adj Ω K Q → (orb (sSup (nbr Ω K)) Q).ncard ≤ (orb (sSup (nbr Ω K)) P).ncard) :
    (∀ Q ∈ orb (sSup (nbr Ω K)) P, ∀ Q' ∈ orb (sSup (nbr Ω K)) P,
      ∃ x ∈ sSup (orb (sSup (nbr Ω K)) P), Q' = rightConjugate Q x) ∧
    (∀ g : G, (rightConjugate · g) '' {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M} =
        {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M} ∨
      Disjoint ((rightConjugate · g) '' {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M})
        {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M}) ∧
    ∀ Q ∈ orb (sSup (nbr Ω K)) P, ∃ g : G,
      Q ∈ (rightConjugate · g) '' {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M} ∧
      (rightConjugate · g) '' {M | M ∈ Ω ∧ ∀ Q ∈ orb (sSup (nbr Ω K)) P, adj Ω Q M} ⊆
        orb (sSup (nbr Ω K)) P := by
  subst hΩK
  have hX : (⨆ (J : Subgroup G) (_ : adj (Set.range (rightConjugate K₀)) K J), J) =
      sSup (nbr (Set.range (rightConjugate K₀)) K) :=
    (sSup_eq_iSup (s := nbr (Set.range (rightConjugate K₀)) K)).symm
  have horb : ∀ Q, {Q' | ∃ x ∈ (⨆ (J : Subgroup G) (_ : adj (Set.range (rightConjugate K₀)) K J),
      J), Q' = rightConjugate Q x} = orb (sSup (nbr (Set.range (rightConjugate K₀)) K)) Q := by
    intro Q
    rw [hX]
    rfl
  obtain ⟨h1, h2, h3⟩ := h28 G K₀ hgen hsymm hconn hcond K hK
    (orb (sSup (nbr (Set.range (rightConjugate K₀)) K)) P) ⟨P, hP, (horb P).symm⟩
    (fun Q hQ => (congrArg Set.ncard (horb Q)).trans_le (hmax Q hQ))
  refine ⟨fun Q hQ Q' hQ' => ?_, h2, h3⟩
  obtain ⟨x, hx, e⟩ := h1 Q hQ Q' hQ'
  exact ⟨x, by rw [sSup_eq_iSup]; exact hx, e⟩

structure OrbitData (Ω : Set (Subgroup G)) (K : Subgroup G) (π : Set (Subgroup G)) : Prop where
  adj_of_mem : ∀ J ∈ π, adj Ω K J
  conj_mem : ∀ J ∈ π, ∀ x ∈ sSup π, rightConjugate J x ∈ π
  exists_conj : ∀ J ∈ π, ∀ L ∈ π, ∃ x ∈ sSup π, L = rightConjugate J x
  nontrivial : ∃ J ∈ π, ∃ L ∈ π, J ≠ L

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_bar_le (hΩ : Sec3Setting Ω) {X M M' T : Subgroup G} (hM : M ∈ Ω) (hM' : M' ∈ Ω)
    (hMX : M ≤ X) (hM'X : M' ≤ X) (hTM : T ≤ M) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (h : bar X T ≤ bar X M') : M = M' := by
  refine hΩ.eq_of_pGroup_le hM hM' hT2 hT1 hTM fun t ht => ?_
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact hΩ.mem_of_barMk_mem hM' hM'X (x := ⟨t, hMX (hTM ht)⟩) hk' (h (barMk_mem_bar ht))

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem OrbitData.not_adj (hΩ : Sec3Setting Ω) {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : OrbitData Ω K π)
    (hsyl : ∀ J ∈ π, ∀ T : Subgroup G, IsSylowOf 2 T J → IsSylowOf 2 (bar (sSup π) T) ⊤)
    {J L : Subgroup G} (hJ : J ∈ π) (hL : L ∈ π) (hne : J ≠ L) : ¬ adj Ω J L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, -, hLN⟩
  set A := sSup π with hAdef
  have hJA : J ≤ A := le_sSup hJ
  have hLA : L ≤ A := le_sSup hL
  obtain ⟨T, hT⟩ := Sec3Setting.exists_sylow J
  obtain ⟨U, hU⟩ := Sec3Setting.exists_sylow L
  have hT' := isSylowOf_iff_card.mp hT
  have hU' := isSylowOf_iff_card.mp hU
  set N := normalizer ((bar A J : Subgroup (BarGroup A)) : Set (BarGroup A)) with hNdef
  have hTN : bar A T ≤ N := (bar_mono hT'.1).trans le_normalizer
  have hUN : bar A U ≤ N := by
    rintro _ ⟨u, hu, rfl⟩
    exact barMk_mem_normalizer (hLN (hU'.1 (mem_subgroupOf.mp hu)))
  obtain ⟨n, hn, hnU⟩ := exists_conj_of_isSylowOf (isSylowOf_of_le hTN le_top (hsyl J hJ T hT))
    (isSylowOf_of_le hUN le_top (hsyl L hL U hU))
  have hle : bar A U ≤ bar A J := by
    rw [hnU]
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    exact (mem_normalizer_iff.mp hn y).mpr (bar_mono hT'.1 hy)
  exact hne (hΩ.eq_of_bar_le (hπ.adj_of_mem L hL).1 (hπ.adj_of_mem J hJ).1 hLA hJA hU'.1
    (IsPGroup.of_card hU'.2) (hΩ.sylow_ne_bot (hπ.adj_of_mem L hL).1 hU) hle).symm

theorem OrbitData.mem_of_le (hΩ : Sec3Setting Ω) {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : OrbitData Ω K π)
    (hsyl : ∀ J ∈ π, ∀ T : Subgroup G, IsSylowOf 2 T J → IsSylowOf 2 (bar (sSup π) T) ⊤)
    {L : Subgroup G} (hL : L ∈ Ω) (hLA : L ≤ sSup π) : L ∈ π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := sSup π with hAdef
  obtain ⟨J, hJ, -⟩ := hπ.nontrivial
  obtain ⟨T, hT⟩ := Sec3Setting.exists_sylow J
  obtain ⟨U, hU⟩ := Sec3Setting.exists_sylow L
  have hT' := isSylowOf_iff_card.mp hT
  have hU' := isSylowOf_iff_card.mp hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card hU'.2
  obtain ⟨P, hP, hUP⟩ := exists_isSylowOf_le (le_top : bar A U ≤ ⊤) (isPGroup_bar hU2)
  obtain ⟨q, -, hq⟩ := exists_conj_of_isSylowOf (hsyl J hJ T hT) hP
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore A) q
  have hJa := hπ.conj_mem J hJ a a.2
  have e : bar A (rightConjugate T a) = rightConjugate (bar A T) (barMk A a) :=
    bar_rightConjugate A T a
  have hPa : P = bar A (rightConjugate T a) := hq.trans e.symm
  have hTa : rightConjugate T a ≤ rightConjugate J a := map_mono hT'.1
  have hle : bar A U ≤ bar A (rightConjugate J a) := hUP.trans (hPa ▸ bar_mono hTa)
  have h := hΩ.eq_of_bar_le hL (hπ.adj_of_mem _ hJa).1 hLA (le_sSup hJa) hU'.1 hU2
    (hΩ.sylow_ne_bot hL hU) hle
  rw [h]
  exact hJa

theorem OrbitData.exists_fix_conj (hΩ : Sec3Setting Ω) (hB : BenderFacts) {K : Subgroup G}
    {π : Set (Subgroup G)} (hπ : OrbitData Ω K π) (hsz : IsSzOrU3 (BarGroup (sSup π)))
    (hsyl : ∀ J ∈ π, ∀ T : Subgroup G, IsSylowOf 2 T J → IsSylowOf 2 (bar (sSup π) T) ⊤)
    {P Q Q' : Subgroup G} (hP : P ∈ π) (hQ : Q ∈ π) (hQ' : Q' ∈ π) (hQP : Q ≠ P)
    (hQ'P : Q' ≠ P) :
    ∃ a ∈ sSup π, rightConjugate P a = P ∧ rightConjugate Q a = Q' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := sSup π with hAdef
  have hPA : P ≤ A := le_sSup hP
  have hQA : Q ≤ A := le_sSup hQ
  have hQ'A : Q' ≤ A := le_sSup hQ'
  have hPΩ := (hπ.adj_of_mem P hP).1
  have hQΩ := (hπ.adj_of_mem Q hQ).1
  have hQ'Ω := (hπ.adj_of_mem Q' hQ').1
  obtain ⟨T, hT⟩ := Sec3Setting.exists_sylow P
  obtain ⟨U, hU⟩ := Sec3Setting.exists_sylow Q
  obtain ⟨U', hU'⟩ := Sec3Setting.exists_sylow Q'
  have hT' := isSylowOf_iff_card.mp hT
  have hU₁ := isSylowOf_iff_card.mp hU
  have hU₂ := isSylowOf_iff_card.mp hU'
  have hszt : IsSzOrU3 ↥(⊤ : Subgroup (BarGroup A)) := isSzOrU3_of_mulEquiv Subgroup.topEquiv hsz
  obtain ⟨SP, hSP⟩ := hsyl P hP T hT
  obtain ⟨SQ, hSQ⟩ := hsyl Q hQ U hU
  obtain ⟨SQ', hSQ'⟩ := hsyl Q' hQ' U' hU'
  have h1 : SQ ≠ SP := by
    intro h
    apply hQP
    refine hΩ.eq_of_bar_le hQΩ hPΩ hQA hPA hU₁.1 (IsPGroup.of_card hU₁.2) (hΩ.sylow_ne_bot hQΩ hU)
      ?_
    rw [← hSQ, h, hSP]
    exact bar_mono hT'.1
  have h2 : SQ' ≠ SP := by
    intro h
    apply hQ'P
    refine hΩ.eq_of_bar_le hQ'Ω hPΩ hQ'A hPA hU₂.1 (IsPGroup.of_card hU₂.2)
      (hΩ.sylow_ne_bot hQ'Ω hU') ?_
    rw [← hSQ', h, hSP]
    exact bar_mono hT'.1
  obtain ⟨r, hr, hrS⟩ := hB.sylow_transitive _ hszt SP SQ SQ' h1 h2
  have hrS' := congrArg
    (fun S : Sylow 2 ↥(⊤ : Subgroup (BarGroup A)) =>
      (S : Subgroup ↥(⊤ : Subgroup (BarGroup A))).map (⊤ : Subgroup (BarGroup A)).subtype)
    hrS
  rw [map_subtype_smul_sylow, hSQ, hSQ'] at hrS'
  have hrT : ((r : ↥(⊤ : Subgroup (BarGroup A))) : BarGroup A) ∈ bar A T := by
    rw [← hSP]
    exact ⟨r, hr, rfl⟩
  obtain ⟨t, htT, htr⟩ := hrT
  have htP : (t : G) ∈ P := hT'.1 (mem_subgroupOf.mp htT)
  refine ⟨(t : G)⁻¹, inv_mem t.2, (rightConjugate_eq_self_iff P _).mpr
    (inv_mem (le_normalizer htP)), ?_⟩
  have e := bar_rightConjugate A U t⁻¹
  have h3 : bar A (rightConjugate U (t : G)⁻¹) = bar A U' := by
    rw [show ((t : G)⁻¹) = ((t⁻¹ : A) : G) from rfl, e, map_inv, htr, hrS']
  have hQt : rightConjugate Q (t : G)⁻¹ ∈ π := hπ.conj_mem Q hQ _ (inv_mem t.2)
  have hUt : IsSylowOf 2 (rightConjugate U (t : G)⁻¹) (rightConjugate Q (t : G)⁻¹) :=
    isSylowOf_rightConjugate hU _
  have hUt' := isSylowOf_iff_card.mp hUt
  exact hΩ.eq_of_bar_le (hπ.adj_of_mem _ hQt).1 hQ'Ω (le_sSup hQt) hQ'A hUt'.1
    (IsPGroup.of_card hUt'.2) (hΩ.sylow_ne_bot (hπ.adj_of_mem _ hQt).1 hUt)
    (h3.le.trans (bar_mono hU₂.1))

namespace MinCounter

theorem conc4_nbr (hM : MinCounter Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Conc4 (bar (sSup (nbr Ω K)) '' nbr Ω K) := by
  have hΩ := hM.setting
  refine hM.conc4_bar (fun J hJ => hJ.1) (fun J hJ x hx => ?_) (Or.inl ?_)
  · exact adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hJ (sSup_nbr_le_normalizer Ω K hx)
  · refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨fun J hJ => hJ.1, fun h => ?_⟩)
      (Set.toFinite Ω)
    have h1 : K ∈ nbr Ω K := by rw [h]; exact hK
    exact h1.2.1 rfl

theorem adj_of_not_mem_orb (hM : MinCounter Ω) {K P Q : Subgroup G} (hK : K ∈ Ω)
    (hP : adj Ω K P) (hQ : adj Ω K Q) (hQP : ∀ x ∈ sSup (nbr Ω K), Q ≠ rightConjugate P x) :
    adj Ω P Q := by
  have hΩ := hM.setting
  set X := sSup (nbr Ω K) with hXdef
  have hPX : P ≤ X := le_sSup hP
  have hQX : Q ≤ X := le_sSup hQ
  obtain ⟨hC1, -⟩ := hM.conc4_nbr hK (bar X P) ⟨P, hP, rfl⟩
  have hcomm := hC1 (bar X Q) ⟨Q, hQ, rfl⟩ fun q hq => by
    obtain ⟨x, hx, hxQ⟩ := hΩ.exists_conj_of_bar hP.1 hQ.1 hPX hQX hq
    exact hQP x hx hxQ
  refine ⟨hQ.1, fun h => hQP 1 (one_mem _) (by rw [rightConjugate_one]; exact h), fun y hy => ?_⟩
  have hQC : bar X Q ≤ centralizer ((bar X P : Subgroup (BarGroup X)) : Set (BarGroup X)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hyN : barMk X ⟨y, hQX hy⟩ ∈
      normalizer ((bar X P : Subgroup (BarGroup X)) : Set (BarGroup X)) :=
    centralizer_le_normalizer _ (hQC (barMk_mem_bar hy))
  exact hΩ.mem_normalizer_of_barMk hP.1 hPX hyN

theorem orbit_structure (hM : MinCounter Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {π : Set (Subgroup G)} (hπ : OrbitData Ω K π) :
    IsSzOrU3 (BarGroup (sSup π)) ∧
      ∀ J ∈ π, ∀ T : Subgroup G, IsSylowOf 2 T J → IsSylowOf 2 (bar (sSup π) T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  set A := sSup π with hAdef
  have hπΩ : π ⊆ Ω := fun J hJ => (hπ.adj_of_mem J hJ).1
  obtain ⟨J₀, hJ₀, L₀, hL₀, hne₀⟩ := hπ.nontrivial
  have hlt : π.ncard < Ω.ncard := by
    refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hπΩ, fun h => ?_⟩) (Set.toFinite Ω)
    have h1 : K ∈ π := by rw [h]; exact hK
    exact (hπ.adj_of_mem K h1).2.1 rfl
  have hC := hM.conc4_bar hπΩ hπ.conj_mem (Or.inl hlt)
  have hJA : ∀ J ∈ π, J ≤ A := fun J hJ => le_sSup hJ
  have hgen : sSup (bar A '' π) = ⊤ := (hΩ.barSetting hπΩ hπ.conj_mem).generates
  have hncl : ∀ J ∈ π,
      normalClosure ((bar A J : Subgroup (BarGroup A)) : Set (BarGroup A)) = ⊤ := by
    intro J hJ
    rw [eq_top_iff, ← hgen]
    refine sSup_le ?_
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hπ.exists_conj J hJ L hL
    have e : bar A (rightConjugate J x) = rightConjugate (bar A J) (barMk A ⟨x, hx⟩) :=
      bar_rightConjugate A J ⟨x, hx⟩
    rw [e]
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have h1 := normalClosure_normal.conj_mem _ (subset_normalClosure hy) (barMk A ⟨x, hx⟩)⁻¹
    simpa [mul_assoc] using h1
  have hnn : ∀ J ∈ π, ¬ (bar A J).Normal := by
    intro J hJ hn
    have hAN := hΩ.le_normalizer_of_bar_normal (hπΩ hJ) (hJA J hJ) hn
    obtain ⟨x, hx, rfl⟩ := hπ.exists_conj J hJ J₀ hJ₀
    obtain ⟨y, hy, rfl⟩ := hπ.exists_conj J hJ L₀ hL₀
    apply hne₀
    rw [(rightConjugate_eq_self_iff J x).mpr (hAN hx),
      (rightConjugate_eq_self_iff J y).mpr (hAN hy)]
  have key : ∀ J ∈ π, IsSzOrU3 (BarGroup A) ∧
      ∀ T : Subgroup G, IsSylowOf 2 T J → IsSylowOf 2 (bar A T) ⊤ := by
    intro J hJ
    obtain ⟨-, hC2⟩ := hC (bar A J) ⟨J, hJ, rfl⟩
    rcases hC2 with hn | ⟨hsz, hsyl⟩
    · exact absurd hn (hnn J hJ)
    rw [hncl J hJ] at hsz hsyl
    exact ⟨isSzOrU3_of_mulEquiv Subgroup.topEquiv.symm hsz, fun T hT =>
      hsyl _ (isSylowOf_bar (hJA J hJ) hT)⟩
  exact ⟨(key J₀ hJ₀).1, fun J hJ => (key J hJ).2⟩

theorem orbitData_nbr (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28) {K : Subgroup G} (hK : K ∈ Ω) :
    OrbitData Ω K (nbr Ω K) ∧ ∀ M ∈ Ω, (∀ J ∈ nbr Ω K, adj Ω J M) → M = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hΩK := hM.lemma312 h22 hB hK
  have hconn := hM.lemma313 h22 hB h26
  set X := sSup (nbr Ω K) with hXdef
  have hXN : X ≤ normalizer (K : Set G) := sSup_nbr_le_normalizer Ω K
  have hne : (nbr Ω K).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    apply hM.lemma36 h22 hK
    have hall : ∀ J ∈ Ω, J = K := by
      intro J hJ
      rcases Relation.ReflTransGen.cases_head (hconn K hK J hJ) with h | ⟨c, hc, -⟩
      · exact h.symm
      · have hc' : c ∈ nbr Ω K := hc
        rw [h0] at hc'
        exact absurd hc' (Set.notMem_empty c)
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hΩ.generates]
    refine sSup_le fun J hJ => ?_
    rw [hall J hJ]
    exact le_normalizer
  obtain ⟨P, hPn, hPmax⟩ := Set.exists_max_image (nbr Ω K) (fun P => (orb X P).ncard)
    (Set.toFinite _) hne
  have hcond : ∀ K' ∈ Ω, ∀ J L, adj Ω K' J → adj Ω K' L →
      adj Ω L J ∨ ∃ x ∈ J ⊔ L, L = rightConjugate J x := by
    intro K' hK' J L hJ hL
    by_cases hJL : J = L
    · exact Or.inr ⟨1, one_mem _, by rw [hJL, rightConjugate_one]⟩
    rcases hM.lemma37_two h22 hB hK' (hΩ.mem_perp_of_le_normalizer hJ.1 hJ.2.2)
        (hΩ.mem_perp_of_le_normalizer hL.1 hL.2.2) hJL with h | h
    · exact Or.inl (hΩ.adj_of_even h22 hL.1 hJ.1 hJL h.2)
    · exact Or.inr h
  obtain ⟨hT1, hT2, hT3⟩ := lemma28_nbr h28 hΩK hΩ.generates
    (fun K' hK' J h => hΩ.adj_symm h22 hK' h) hconn hcond hK hPn hPmax
  set π := orb X P with hπdef
  set α := {M | M ∈ Ω ∧ ∀ Q ∈ π, adj Ω Q M} with hαdef
  have hπsub : ∀ Q ∈ π, adj Ω K Q := by
    rintro Q ⟨x, hx, rfl⟩
    exact adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hPn (hXN hx)
  have hPπ : P ∈ π := ⟨1, one_mem _, (rightConjugate_one P).symm⟩
  have hπX : sSup π ≤ X := sSup_le fun Q hQ => le_sSup (hπsub Q hQ)
  have hπinv : ∀ J ∈ π, ∀ x ∈ sSup π, rightConjugate J x ∈ π := by
    rintro J ⟨y, hy, rfl⟩ x hx
    exact ⟨y * x, mul_mem hy (hπX hx), rightConjugate_mul P y x⟩
  have hKα : K ∈ α := ⟨hK, fun Q hQ => hΩ.adj_symm h22 hK (hπsub Q hQ)⟩
  have hA : ∀ Q, adj Ω K Q → Q ∉ π → Q ∈ α := by
    intro Q hQ hQπ
    refine ⟨hQ.1, fun J hJ => ?_⟩
    refine hM.adj_of_not_mem_orb hK (hπsub J hJ) hQ fun x hx hQx => hQπ ?_
    obtain ⟨y, hy, rfl⟩ := hJ
    exact ⟨y * x, mul_mem hy hx, by rw [hQx, rightConjugate_mul]⟩
  by_cases htwo : ∃ J ∈ π, ∃ L ∈ π, J ≠ L
  swap
  ·
    push Not at htwo
    exfalso
    obtain ⟨g, hPg, hgπ⟩ := hT3 P hPπ
    have hαg : (rightConjugate · g) '' α = {P} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hPg, fun Q hQ => htwo Q (hgπ hQ) P hPπ⟩
    have hα1 : α.ncard = 1 := by
      rw [← ncard_image_rightConjugate α g, hαg, Set.ncard_singleton]
    have hαK : α = {K} := by
      obtain ⟨M, hM'⟩ := Set.ncard_eq_one.mp hα1
      have h1 : K ∈ ({M} : Set (Subgroup G)) := hM' ▸ hKα
      rw [hM', Set.mem_singleton_iff.mp h1]
    have hnP : nbr Ω P = {K} := by
      rw [← hαK]
      ext M
      constructor
      · intro hM'
        exact ⟨hM'.1, fun Q hQ => (htwo Q hQ P hPπ) ▸ hM'⟩
      · intro hM'
        exact hM'.2 P hPπ
    have hnK : nbr Ω K = {P} := by
      have hP' : P ∈ Set.range (rightConjugate K) := hΩK ▸ hPn.1
      obtain ⟨h, hh⟩ := hP'
      have h1 : (nbr Ω K).ncard = 1 := by
        rw [← ncard_image_rightConjugate (nbr Ω K) h, ← nbr_rightConjugate hΩ.conj_mem, hh, hnP,
          Set.ncard_singleton]
      obtain ⟨M, hM'⟩ := Set.ncard_eq_one.mp h1
      have h2 : P ∈ ({M} : Set (Subgroup G)) := hM' ▸ hPn
      rw [hM', Set.mem_singleton_iff.mp h2]
    have hall : ∀ N ∈ Ω, N ∈ ({K, P} : Set (Subgroup G)) := by
      intro N hN
      refine mem_of_reach_of_closed (Or.inl rfl) (fun N₁ hN₁ N₂ h => ?_) (hconn K hK N hN)
      rcases hN₁ with h1 | h1
      · have h2 : N₂ ∈ nbr Ω N₁ := h
        rw [h1, hnK] at h2
        exact Or.inr h2
      · have h1' : N₁ = P := h1
        have h2 : N₂ ∈ nbr Ω N₁ := h
        rw [h1', hnP] at h2
        exact Or.inl h2
    apply hM.lemma36 h22 hK
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hΩ.generates]
    refine sSup_le fun N hN => ?_
    rcases hall N hN with h1 | h1
    · rw [h1]
      exact le_normalizer
    · have h1' : N = P := h1
      rw [h1']
      exact hPn.2.2
  have hπ : OrbitData Ω K π := ⟨hπsub, hπinv, hT1, htwo⟩
  obtain ⟨hsz, hsyl⟩ := hM.orbit_structure hK hπ
  have hαK : ∀ M ∈ α, M = K := by
    obtain ⟨g, hPg, hgπ⟩ := hT3 P hPπ
    have case2 : π ⊆ (rightConjugate · g) '' α → False := by
      intro hall
      have hβπ : (rightConjugate · g) '' α = π := Set.Subset.antisymm hgπ hall
      have hαind : ∀ M ∈ α, ∀ M' ∈ α, M ≠ M' → ¬ adj Ω M M' := by
        intro M hMα M' hM'α hne' h
        have h1 := adj_conj hΩ.conj_mem h g
        have hMg : rightConjugate M g ∈ π := hβπ ▸ Set.mem_image_of_mem _ hMα
        have hM'g : rightConjugate M' g ∈ π := hβπ ▸ Set.mem_image_of_mem _ hM'α
        exact hπ.not_adj hΩ hsyl hMg hM'g (fun h' => hne' (rightConjugate_injective g h')) h1
      have hnK : nbr Ω K = π := by
        refine Set.Subset.antisymm (fun Q hQ => ?_) hπsub
        by_contra hQπ
        exact hαind K hKα Q (hA Q hQ hQπ) (Ne.symm hQ.2.1) hQ
      have hcardα : α.ncard = π.ncard := by rw [← hβπ, ncard_image_rightConjugate]
      have hcard : ∀ N ∈ Ω, (nbr Ω N).ncard = π.ncard := by
        intro N hN
        have hN' : N ∈ Set.range (rightConjugate K) := hΩK ▸ hN
        obtain ⟨h, rfl⟩ := hN'
        rw [nbr_rightConjugate hΩ.conj_mem, ncard_image_rightConjugate, hnK]
      have hnJ : ∀ J ∈ π, nbr Ω J = α := by
        intro J hJ
        symm
        refine Set.eq_of_subset_of_ncard_le (fun M hM => hM.2 J hJ) ?_ (Set.toFinite _)
        rw [hcard J (hπsub J hJ).1, hcardα]
      have hnα : ∀ M ∈ α, nbr Ω M = π := by
        intro M hM
        symm
        refine Set.eq_of_subset_of_ncard_le
          (fun J hJ => hΩ.adj_symm h22 (hπsub J hJ).1 (hM.2 J hJ)) ?_ (Set.toFinite _)
        rw [hcard M hM.1]
      have hall' : ∀ N ∈ Ω, N ∈ α ∪ π := by
        intro N hN
        refine mem_of_reach_of_closed (Or.inl hKα) (fun N₁ hN₁ N₂ h => ?_) (hconn K hK N hN)
        have h2 : N₂ ∈ nbr Ω N₁ := h
        rcases hN₁ with h1 | h1
        · rw [hnα N₁ h1] at h2
          exact Or.inr h2
        · rw [hnJ N₁ h1] at h2
          exact Or.inl h2
      have hAn : (sSup π).Normal := by
        rw [← normalizer_eq_top_iff, eq_top_iff, ← hΩ.generates]
        refine sSup_le fun N hN => ?_
        rcases hall' N hN with h1 | h1
        · intro n hn
          refine mem_normalizer_sSup fun J hJ => ?_
          rw [(rightConjugate_eq_self_iff J n).mpr ((h1.2 J hJ).2.2 hn)]
          exact hJ
        · exact (le_sSup h1).trans le_normalizer
      have hKg : rightConjugate K g ∈ π := hβπ ▸ Set.mem_image_of_mem _ hKα
      have hKA : K ≤ sSup π := by
        intro k hk
        have h1 : g⁻¹ * k * g ∈ rightConjugate K g := by
          rw [mem_rightConjugate_iff]
          simpa [mul_assoc] using hk
        have h3 := hAn.conj_mem _ (le_sSup hKg h1) g
        simpa [mul_assoc] using h3
      exact (hπsub K (hπ.mem_of_le hΩ hsyl hK hKA)).2.1 rfl
    have hβ : ∀ Q ∈ (rightConjugate · g) '' α, Q = P := by
      intro Q hQ
      by_contra hQP
      by_cases hall : π ⊆ (rightConjugate · g) '' α
      · exact case2 hall
      obtain ⟨Q', hQ'π, hQ'β⟩ := Set.not_subset.mp hall
      have hQ'P : Q' ≠ P := fun h => hQ'β (h ▸ hPg)
      obtain ⟨a, -, haP, haQ⟩ := hπ.exists_fix_conj hΩ hB hsz hsyl hPπ (hgπ hQ) hQ'π hQP hQ'P
      have hPa : P ∈ (rightConjugate · a) '' ((rightConjugate · g) '' α) := ⟨P, hPg, haP⟩
      rw [image_rightConjugate_image] at hPa
      have hβa := image_rightConjugate_eq_of_mem hT2 hPa hPg
      have hQ'a : Q' ∈ (rightConjugate · a) '' ((rightConjugate · g) '' α) := ⟨Q, hQ, haQ⟩
      rw [image_rightConjugate_image, hβa] at hQ'a
      exact hQ'β hQ'a
    intro M hMα
    have hMg : rightConjugate M g ∈ (rightConjugate · g) '' α := Set.mem_image_of_mem _ hMα
    have hKg : rightConjugate K g ∈ (rightConjugate · g) '' α := Set.mem_image_of_mem _ hKα
    exact rightConjugate_injective g ((hβ _ hMg).trans (hβ _ hKg).symm)
  have hnK : nbr Ω K = π := by
    refine Set.Subset.antisymm (fun Q hQ => ?_) hπsub
    by_contra hQπ
    exact hQ.2.1 (hαK Q (hA Q hQ hQπ))
  rw [hnK]
  exact ⟨hπ, fun M hM hMα => hαK M ⟨hM, hMα⟩⟩

theorem lemma314 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28) {K : Subgroup G} (hK : K ∈ Ω) :
    (∀ L ∈ Ω, L ≤ sSup (nbr Ω K) ↔ L ∈ nbr Ω K) ∧ IsSzOrU3 (BarGroup (sSup (nbr Ω K))) ∧
      ∀ M ∈ Ω, (∀ J ∈ nbr Ω K, adj Ω J M) → M = K := by
  obtain ⟨hπ, hα⟩ := hM.orbitData_nbr h22 hB h26 h28 hK
  obtain ⟨hsz, hsyl⟩ := hM.orbit_structure hK hπ
  exact ⟨fun L hL => ⟨hπ.mem_of_le hM.setting hsyl hL, fun h => le_sSup h⟩, hsz, hα⟩

end MinCounter

end CFSG.ComponentClassification.Asc76X
