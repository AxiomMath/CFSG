module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma37
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_frattini_eq_bot {T : Subgroup G} (hT : IsPGroup 2 T)
    (h : frattini T = ⊥) : IsElemAbelian 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 T) := ⟨hT⟩
  have hF := CFSG.frattini_eq_closure_commutator_union_powers (R := T) (p := 2)
  rw [h] at hF
  have hsq : ∀ y : T, y ^ 2 = 1 := fun y => by
    have : y ^ 2 ∈ (⊥ : Subgroup T) := hF ▸ subset_closure (Or.inr ⟨y, rfl⟩)
    rwa [mem_bot] at this
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by simpa using congrArg Subtype.val (hsq ⟨x, hx⟩)⟩
  have hc : ⁅a, b⁆ ∈ (⊥ : Subgroup T) :=
    hF ▸ subset_closure (Or.inl (commutator_mem_commutator (mem_top a) (mem_top b)))
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem eq_of_isSylowOf_le {T P J : Subgroup G} (hT : IsSylowOf 2 T J) (hP : IsPGroup 2 P)
    (hPJ : P ≤ J) (hTP : T ≤ P) : P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff_card] at hT
  symm
  refine eq_of_le_of_card_ge hTP ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hT.2, hk]
  apply Nat.pow_le_pow_right (by norm_num)
  have h := card_dvd_of_le hPJ
  rw [hk] at h
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h

theorem isSylowOf_rightConjugate {T J : Subgroup G} (hT : IsSylowOf 2 T J) (g : G) :
    IsSylowOf 2 (rightConjugate T g) (rightConjugate J g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff_card] at hT ⊢
  refine ⟨fun x hx => ?_, by rw [rightConjugate_card, rightConjugate_card, hT.2]⟩
  rw [mem_rightConjugate_iff] at hx ⊢
  exact hT.1 hx

omit [Finite G] in
theorem bar_self (X : Subgroup G) : bar X X = ⊤ := by
  rw [bar, subgroupOf_self]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem frattini_sylow_ne_bot (hΩ : Sec3Setting Ω) {J T : Subgroup G} (hJ : J ∈ Ω)
    (hT : IsSylowOf 2 T J) : frattini T ≠ ⊥ := fun h =>
  (hΩ.rank J hJ T hT).2 (isElemAbelian_of_frattini_eq_bot
    (IsPGroup.of_card (isSylowOf_iff_card.mp hT).2) h)

theorem commute_of_sylow (hΩ : Sec3Setting Ω) {S T₁ T₂ J₁ J₂ : Subgroup G} (hS : IsPGroup 2 S)
    (hJ₁ : J₁ ∈ Ω) (hJ₂ : J₂ ∈ Ω) (hT₁ : IsSylowOf 2 T₁ J₁) (hT₂ : IsSylowOf 2 T₂ J₂)
    (hT₁S : T₁ ≤ S) (hT₂S : T₂ ≤ S) (hne : T₁ ≠ T₂) : ⁅T₁, T₂⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ : Set (Subgroup G) := {T | T ≤ S ∧ ∃ J ∈ Ω, IsSylowOf 2 T J}
  have hcard' : ∀ J ∈ Ω, ∀ J' ∈ Ω, (Nat.card J).factorization 2 = (Nat.card J').factorization 2 :=
    fun J hJ J' hJ' => by
      by_cases h : J = J'
      · rw [h]
      · exact (hΩ.twoPart J hJ J' hJ' h).1
  refine lemma25 (Δ := Δ) hS (fun T hT => hT.1) ?_ ?_ ?_ ?_ T₁ ⟨hT₁S, J₁, hJ₁, hT₁⟩ T₂
    ⟨hT₂S, J₂, hJ₂, hT₂⟩ hne
  · rintro T ⟨hTS, J, hJ, hT⟩ s hs
    refine ⟨fun x hx => ?_, rightConjugate J s, hΩ.conj_mem J hJ s, isSylowOf_rightConjugate hT s⟩
    rw [mem_rightConjugate_iff] at hx
    have h1 := hTS hx
    have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs) h1) hs
  · rintro T ⟨-, J, hJ, hT⟩ T' ⟨-, J', hJ', hT'⟩
    rw [(isSylowOf_iff_card.mp hT).2, (isSylowOf_iff_card.mp hT').2, hcard' J hJ J' hJ']
  · rintro T ⟨-, J, hJ, hT⟩
    exact hΩ.frattini_sylow_ne_bot hJ hT
  · rintro T ⟨hTS, J, hJ, hT⟩ T' ⟨hT'S, J', hJ', hT'⟩ hTT'
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (isSylowOf_iff_card.mp hT).2
    by_cases hJJ' : J = J'
    · subst hJJ'
      exfalso
      have hP : IsPGroup 2 ↥(S ⊓ J) := hS.to_le inf_le_left
      have h1 := eq_of_isSylowOf_le hT hP inf_le_right (le_inf hTS (isSylowOf_iff_card.mp hT).1)
      have h2 := eq_of_isSylowOf_le hT' hP inf_le_right
        (le_inf hT'S (isSylowOf_iff_card.mp hT').1)
      exact hTT' (h1.symm.trans h2)
    · exact two_subgroup_of_odd_eq_bot _ _ (hT2.to_le inf_le_left)
        (hΩ.twoPart J hJ J' hJ' hJJ').2
        (inf_le_inf (isSylowOf_iff_card.mp hT).1 (isSylowOf_iff_card.mp hT').1)

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X.MinCounter

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_good (hM : MinCounter Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) : ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ R ≤ S ∧
      IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := sSup (perp Ω K)
  have hR' := isSylowOf_iff_card.mp hR
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hR'.2
  have hRX : R ≤ X := hR'.1.trans (le_sSup (hM.setting.mem_perp_self hK))
  obtain ⟨SX, hSX, hRSX⟩ := exists_isSylowOf_le hRX hR2
  have hSX' := isSylowOf_iff_card.mp hSX
  obtain ⟨S, hS, hSXS⟩ := exists_isSylowOf_le (le_top : SX ≤ ⊤) (IsPGroup.of_card hSX'.2)
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have heq := eq_of_isSylowOf_le hSX (hS2.to_le inf_le_left) inf_le_right (le_inf hSXS hSX'.1)
  exact ⟨S, hS, hRSX.trans hSXS, heq ▸ hSX⟩

theorem isSylowOf_inf_of_conc4 (hΩ : Sec3Setting Ω) (hB : BenderFacts) {α : Set (Subgroup G)}
    (hαΩ : α ⊆ Ω) (hC : Conc4 (bar (sSup α) '' α)) {S J : Subgroup G}
    (hS : IsSylowOf 2 (S ⊓ sSup α) (sSup α)) (hJ : J ∈ α) (hSJ : S ⊓ J ≠ ⊥) :
    IsSylowOf 2 (S ⊓ J) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := sSup α with hXdef
  have hJX : J ≤ X := le_sSup hJ
  set SX := S ⊓ X with hSXdef
  have hSX := isSylowOf_iff_card.mp hS
  have hSX2 : IsPGroup 2 SX := IsPGroup.of_card hSX.2
  have hSXbar : IsSylowOf 2 (bar X SX) (bar X X) := isSylowOf_bar le_rfl hS
  have hSJ' : S ⊓ J = SX ⊓ J := by
    rw [hSXdef, inf_assoc, inf_of_le_right hJX]
  have hSJ2 : IsPGroup 2 ↥(S ⊓ J) := hSJ' ▸ hSX2.to_le inf_le_left
  have hinter : bar X SX ⊓ bar X J ≤ bar X (S ⊓ J) := by
    rintro _ ⟨⟨s, hs, rfl⟩, hsJ⟩
    obtain ⟨k, hk⟩ := hSX2 ⟨(s : G), hs⟩
    have hk' : (s : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hsJ' : (s : G) ∈ J := hΩ.mem_of_barMk_mem (hαΩ hJ) hJX hk' hsJ
    exact ⟨s, mem_inf.mpr ⟨(mem_inf.mp hs).1, hsJ'⟩, rfl⟩
  obtain ⟨P, hPJ, hPS⟩ : ∃ P : Subgroup (BarGroup X), IsSylowOf 2 P (bar X J) ∧
      P ≤ bar X SX := by
    obtain ⟨-, hC2⟩ := hC (bar X J) ⟨J, hJ, rfl⟩
    rcases hC2 with hn | ⟨hsz, hsyl⟩
    · refine ⟨bar X SX ⊓ bar X J, ?_, inf_le_left⟩
      exact isSylowOf_inf (bar_mono hJX) (by rw [normalizer_eq_top_iff.mpr hn]; exact le_top)
        hSXbar
    · obtain ⟨R', hR', hSJR'⟩ := exists_isSylowOf_le (inf_le_right : S ⊓ J ≤ J) hSJ2
      have hR'bar := isSylowOf_bar hJX hR'
      have hR'M := hsyl _ hR'bar
      set Mb := normalClosure ((bar X J : Subgroup (BarGroup X)) : Set (BarGroup X))
      have hMn : Mb.Normal := normalClosure_normal
      have hSM : IsSylowOf 2 (bar X SX ⊓ Mb) Mb :=
        isSylowOf_inf (by rw [bar_self]; exact le_top)
          (by rw [normalizer_eq_top_iff.mpr hMn]; exact le_top) hSXbar
      have heq : bar X R' = bar X SX ⊓ Mb := by
        by_contra hne
        have h1 := hB.inf_eq_bot_of_isSylowOf hsz hR'M hSM hne
        apply hSJ
        rw [eq_bot_iff]
        intro y hy
        have hyX : y ∈ X := hJX (mem_inf.mp hy).2
        have hyb : barMk X ⟨y, hyX⟩ ∈ bar X R' ⊓ (bar X SX ⊓ Mb) := by
          refine mem_inf.mpr ⟨⟨⟨y, hyX⟩, hSJR' hy, rfl⟩, mem_inf.mpr ⟨⟨⟨y, hyX⟩,
            ?_, rfl⟩, ?_⟩⟩
          · rw [hSJ'] at hy
            exact (mem_inf.mp hy).1
          · exact subset_normalClosure ⟨⟨y, hyX⟩, (mem_inf.mp hy).2, rfl⟩
        rw [h1, mem_bot] at hyb
        obtain ⟨k, hk⟩ := hSJ2 ⟨y, hy⟩
        have hk1 : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have hk' : (⟨y, hyX⟩ : X) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk1)
        have := eq_one_of_two_element_of_ker (barMk X) (odd_card_ker_barMk X) hk' hyb
        rw [mem_bot]
        exact congrArg Subtype.val this
      exact ⟨bar X R', hR'bar, heq ▸ inf_le_left⟩
  rw [isSylowOf_iff_card]
  refine ⟨inf_le_right, ?_⟩
  have hle : P ≤ bar X (S ⊓ J) := le_trans (le_inf hPS (isSylowOf_iff_card.mp hPJ).1) hinter
  have h1 : Nat.card P ≤ Nat.card (S ⊓ J : Subgroup G) := by
    rw [← card_bar_of_pGroup (inf_le_right.trans hJX) hSJ2]
    exact card_le_of_le hle
  rw [(isSylowOf_iff_card.mp hPJ).2, factorization_card_bar hJX] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSJ2
  rw [hk] at h1 ⊢
  congr 1
  apply le_antisymm
  · have h := card_dvd_of_le (inf_le_right : S ⊓ J ≤ J)
    rw [hk] at h
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h
  · exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem isSylowOf_inf_of_mem_perp (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K S J : Subgroup G} (hK : K ∈ Ω) (hS : IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K)))
    (hJ : J ∈ perp Ω K) (hSJ : S ⊓ J ≠ ⊥) : IsSylowOf 2 (S ⊓ J) J :=
  isSylowOf_inf_of_conc4 hM.setting hB (Sec3Setting.perp_subset Ω K) (hM.lemma37_one h22 hK) hS
    hJ hSJ

theorem lemma39 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K R S J : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hS : IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K))) (hJ : J ∈ Ω) {u : G}
    (huJ : u ∈ J) (huS : u ∈ S) (huR : u ∈ normalizer (R : Set G)) (hu1 : u ≠ 1) {k : ℕ}
    (huk : u ^ (2 ^ k) = 1) : IsSylowOf 2 (S ⊓ J) J ∧ u ∈ S ⊓ J := by
  have hΩ := hM.setting
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (isSylowOf_iff_card.mp hR).2
  have huK : u ∈ normalizer (K : Set G) := hΩ.normalizer_le_normalizer hK hR2
    (hΩ.sylow_ne_bot hK hR) (isSylowOf_iff_card.mp hR).1 huR
  have hJK : J ∈ perp Ω K := ⟨hJ, even_card_of_two_element (mem_inf.mpr ⟨huJ, huK⟩) hu1 huk⟩
  have hSJ : S ⊓ J ≠ ⊥ := fun h => hu1 (by
    have : u ∈ S ⊓ J := mem_inf.mpr ⟨huS, huJ⟩
    rwa [h, mem_bot] at this)
  exact ⟨hM.isSylowOf_inf_of_mem_perp h22 hB hK hS hJK hSJ, mem_inf.mpr ⟨huS, huJ⟩⟩

theorem lemma310 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K R S J U : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hS2 : IsPGroup 2 S)
    (hRS : R ≤ S) (hS : IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K))) (hJ : J ∈ Ω)
    (hUJ : U ≤ S ⊓ J) (hU : IsElemAbelian 2 U) (hU4 : Nat.card U = 4) :
    IsSylowOf 2 (S ⊓ J) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (isSylowOf_iff_card.mp hR).2
  have hRK : R ≤ K := (isSylowOf_iff_card.mp hR).1
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hU1 : U ≠ ⊥ := fun h => by rw [h, card_bot] at hU4; norm_num at hU4
  have hcomm : ∀ g ∈ S, rightConjugate R g ≠ R → ⁅R, rightConjugate R g⁆ = ⊥ := by
    intro g hg hne
    refine hΩ.commute_of_sylow hS2 hK (hΩ.conj_mem K hK g) hR (isSylowOf_rightConjugate hR g)
      hRS (fun x hx => ?_) (Ne.symm hne)
    rw [mem_rightConjugate_iff] at hx
    have h1 := hRS hx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hg) h1) hg
  obtain ⟨-, h24⟩ := lemma24In hRS (hUJ.trans inf_le_left) hR2 hU hU4 hcomm
    (hΩ.frattini_sylow_ne_bot hK hR)
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h24
  obtain ⟨hzΓ, hzR⟩ := mem_inf.mp hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hΓJ : gammaOneOn U S ≤ normalizer (J : Set G) := by
    refine iSup_le fun U₀ => iSup_le fun hU₀ => iSup_le fun hU₀1 => ?_
    exact inf_le_right.trans (hΩ.normalizer_le_normalizer hJ (hU2.to_le hU₀) hU₀1
      (hU₀.trans (hUJ.trans inf_le_right)))
  obtain ⟨k, hk⟩ := hR2 ⟨z, (mem_inf.mp hzR).1⟩
  have hk' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have heven : Even (Nat.card (K ⊓ normalizer (J : Set G) : Subgroup G)) :=
    even_card_of_two_element (mem_inf.mpr ⟨hRK (mem_inf.mp hzR).1, hΓJ hzΓ⟩) hz1' hk'
  have hJK : J ∈ perp Ω K := by
    by_cases hJK : J = K
    · rw [hJK]
      exact hΩ.mem_perp_self hK
    · exact ⟨hJ, hΩ.even_inf_normalizer_symm hJ hK (Ne.symm hJK) heven⟩
  have hSJ : S ⊓ J ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUJ))
  exact hM.isSylowOf_inf_of_mem_perp h22 hB hK hS hJK hSJ

end CFSG.ComponentClassification.Asc76X.MinCounter
