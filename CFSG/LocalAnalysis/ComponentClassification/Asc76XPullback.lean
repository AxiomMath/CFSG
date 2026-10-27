module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XCounter

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_bar {X J L : Subgroup G} (hJX : J ≤ X) (hLX : L ≤ X)
    (h : ⁅bar X J, bar X L⁆ = ⊥) : ⁅J, L⁆ ≤ oddCoreIn X := by
  have h1 : (⁅J.subgroupOf X, L.subgroupOf X⁆).map (barMk X) = ⊥ := by
    rw [map_commutator]
    exact h
  rw [Subgroup.map_eq_bot_iff, ker_barMk] at h1
  have h2 : (⁅J.subgroupOf X, L.subgroupOf X⁆).map X.subtype = ⁅J, L⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hJX, map_subgroupOf_eq_of_le hLX]
  rw [← h2]
  exact map_mono h1

theorem isSylowOf_bar {X K R : Subgroup G} (hKX : K ≤ X) (hR : IsSylowOf 2 R K) :
    IsSylowOf 2 (bar X R) (bar X K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff_card] at hR ⊢
  refine ⟨bar_mono hR.1, ?_⟩
  rw [card_bar_of_pGroup (hR.1.trans hKX) (IsPGroup.of_card hR.2), hR.2,
    factorization_card_bar hKX]

omit [Finite G] in
theorem normal_sSup_of_invariant {α : Set (Subgroup G)}
    (hα : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α) : (sSup α).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : sSup α ≤ (sSup α).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun J hJ x hx => ?_
    have h1 : g * x * g⁻¹ ∈ rightConjugate J g⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      simpa [mul_assoc] using hx
    exact le_sSup (hα J hJ g⁻¹) h1
  exact hle hn

theorem oddCore_eq_bot_of_normal' (hO : standardComponentOddCore G = ⊥) {X : Subgroup G}
    (hX : X.Normal) : CFSG.oddCore X = ⊥ := by
  have hnorm : (oddCoreIn X).Normal := ⟨fun n hn g => by
    have := normalizer_le_normalizer_oddCoreIn X (show g ∈ normalizer (X : Set G) from
      mem_normalizer_iff.mpr fun h => ⟨fun hh => hX.conj_mem h hh g, fun hh => by
        have := hX.conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
    exact (mem_normalizer_iff.mp this n).mp hn⟩
  have hle : oddCoreIn X ≤ standardComponentOddCore G := le_sSup ⟨hnorm, odd_card_oddCoreIn X⟩
  rw [hO, le_bot_iff] at hle
  rwa [oddCoreIn, map_eq_bot_iff_of_injective _ X.subtype_injective] at hle

@[expose] def nclIn (X K : Subgroup G) : Subgroup G :=
  (normalClosure ((K.subgroupOf X : Subgroup X) : Set X)).map X.subtype

theorem isSzOrU3_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsSzOrU3 B) : IsSzOrU3 A := by
  rcases h with ⟨a, ha, ⟨f⟩⟩ | ⟨a, ha, ⟨f⟩⟩
  · exact Or.inl ⟨a, ha, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨a, ha, ⟨e.trans f⟩⟩

noncomputable def nclInEquiv {X K : Subgroup G} (hO : CFSG.oddCore X = ⊥) :
    nclIn X K ≃* normalClosure ((bar X K : Subgroup (BarGroup X)) : Set (BarGroup X)) := by
  have hinj : Function.Injective (barMk X) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_barMk, hO]
  have hmap : (normalClosure ((K.subgroupOf X : Subgroup X) : Set X)).map (barMk X) =
      normalClosure ((bar X K : Subgroup (BarGroup X)) : Set (BarGroup X)) := by
    rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective _), bar, coe_map]
  exact ((normalClosure ((K.subgroupOf X : Subgroup X) : Set X)).equivMapOfInjective _
    X.subtype_injective).symm.trans
    (((normalClosure ((K.subgroupOf X : Subgroup X) : Set X)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr hmap))

omit [Finite G] in
theorem le_nclIn {X K : Subgroup G} (hKX : K ≤ X) : K ≤ nclIn X K := by
  intro k hk
  exact ⟨⟨k, hKX hk⟩, subset_normalClosure (show (⟨k, hKX hk⟩ : X) ∈ K.subgroupOf X from hk),
    rfl⟩

omit [Finite G] in
theorem normalClosure_eq_nclIn {X Y K : Subgroup G} (hY : Y.Normal)
    (hXY : Y ≤ centralizer (X : Set G)) (hG : X ⊔ Y = ⊤) (hKX : K ≤ X) :
    normalClosure (K : Set G) = nclIn X K := by
  apply le_antisymm
  · have hn : (nclIn X K).Normal := by
      refine ⟨fun z hz g => ?_⟩
      have hg : g ∈ ((X ⊔ Y : Subgroup G) : Set G) := by rw [hG]; exact mem_top g
      rw [mul_normal] at hg
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      obtain ⟨w, hw, rfl⟩ := hz
      show x * y * (w : G) * (x * y)⁻¹ ∈ nclIn X K
      have hyw : y * (w : G) * y⁻¹ = w := by
        rw [← mem_centralizer_iff.mp (hXY hy) w w.2, mul_inv_cancel_right]
      have e : x * y * (w : G) * (x * y)⁻¹ = x * (y * (w : G) * y⁻¹) * x⁻¹ := by group
      rw [e, hyw]
      exact ⟨⟨x, hx⟩ * w * ⟨x, hx⟩⁻¹, normalClosure_normal.conj_mem w hw _, by simp⟩
    exact normalClosure_le_normal (le_nclIn hKX)
  · rw [nclIn, map_le_iff_le_comap]
    exact normalClosure_le_normal fun k hk => subset_normalClosure (show (k : G) ∈ K from hk)

theorem card_barGroup_le (X : Subgroup G) : Nat.card (BarGroup X) ≤ Nat.card G :=
  (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.oddCore X))).trans
    (card_le_card_group X)

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_of_bar (hΩ : Sec3Setting Ω) {X J L : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω)
    (hJX : J ≤ X) (hLX : L ≤ X) {q : BarGroup X} (h : bar X L = rightConjugate (bar X J) q) :
    ∃ x ∈ X, L = rightConjugate J x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) q
  have hJx : rightConjugate J x ≤ X := fun y hy => by
    rw [mem_rightConjugate_iff] at hy
    have h2 : (x : G) * y * (x : G)⁻¹ ∈ X := hJX hy
    have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem x.2) h2) x.2
  refine ⟨x, x.2, hΩ.eq_of_bar_eq hL (hΩ.conj_mem J hJ x) hLX hJx ?_⟩
  rw [bar_rightConjugate]
  exact h

theorem le_normalizer_of_bar_normal (hΩ : Sec3Setting Ω) {X J : Subgroup G} (hJ : J ∈ Ω)
    (hJX : J ≤ X) (h : (bar X J).Normal) : X ≤ normalizer (J : Set G) := by
  intro x hx
  have hq : barMk X ⟨x, hx⟩ ∈ normalizer ((bar X J : Subgroup _) : Set _) :=
    mem_normalizer_iff.mpr fun y => ⟨fun hy => h.conj_mem y hy _, fun hy => by
      have := h.conj_mem _ hy (barMk X ⟨x, hx⟩)⁻¹
      simpa [mul_assoc] using this⟩
  exact hΩ.mem_normalizer_of_barMk hJ hJX hq

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conc4_clause_of_split (hΩ : Sec3Setting Ω) {α β : Set (Subgroup G)} (hαβ : Ω = α ∪ β)
    (hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α)
    (hβinv : ∀ J ∈ β, ∀ g : G, rightConjugate J g ∈ β)
    (hcomm : ∀ A ∈ α, ∀ B ∈ β, ⁅A, B⁆ = ⊥) (hC : Conc4 (bar (sSup α) '' α)) {K : Subgroup G}
    (hK : K ∈ α) :
    (∀ J ∈ Ω, (∀ g : G, J ≠ rightConjugate K g) → ⁅K, J⁆ = ⊥) ∧
      (K.Normal ∨ (IsSzOrU3 (normalClosure (K : Set G)) ∧
        ∀ R : Subgroup G, IsSylowOf 2 R K → IsSylowOf 2 R (normalClosure (K : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := sSup α with hXdef
  set Y := sSup β with hYdef
  have hαΩ : α ⊆ Ω := hαβ ▸ Set.subset_union_left
  have hXn : X.Normal := normal_sSup_of_invariant hαinv
  have hYn : Y.Normal := normal_sSup_of_invariant hβinv
  have hO : CFSG.oddCore X = ⊥ := oddCore_eq_bot_of_normal' hΩ.oddCore hXn
  have hOX : oddCoreIn X = ⊥ := by
    show (CFSG.oddCore X).map X.subtype = ⊥
    rw [hO, Subgroup.map_bot]
  have hJX : ∀ J ∈ α, J ≤ X := fun J hJ => le_sSup hJ
  have hKX := hJX K hK
  have hXY : Y ≤ centralizer (X : Set G) := by
    refine sSup_le fun B hB => ?_
    rw [← le_centralizer_iff]
    refine sSup_le fun A hA => ?_
    rw [← commutator_eq_bot_iff_le_centralizer]
    exact hcomm A hA B hB
  have hG : X ⊔ Y = ⊤ := by
    rw [hXdef, hYdef, ← sSup_union, ← hαβ]
    exact hΩ.generates
  obtain ⟨hC1, hC2⟩ := hC (bar X K) ⟨K, hK, rfl⟩
  refine ⟨fun J hJ hJK => ?_, ?_⟩
  · rw [hαβ] at hJ
    rcases hJ with hJα | hJβ
    · have h1 := hC1 (bar X J) ⟨J, hJα, rfl⟩ fun q hq => by
        obtain ⟨x, -, hx⟩ := hΩ.exists_conj_of_bar (hαΩ hK) (hαΩ hJα) hKX (hJX J hJα) hq
        exact hJK x hx
      have h2 := commutator_le_of_bar hKX (hJX J hJα) h1
      rwa [hOX, le_bot_iff] at h2
    · exact hcomm K hK J hJβ
  · rcases hC2 with hn | ⟨hsz, hsyl⟩
    ·
      left
      have hXK := hΩ.le_normalizer_of_bar_normal (hαΩ hK) hKX hn
      refine ⟨fun n hn' g => ?_⟩
      have hg : g ∈ ((X ⊔ Y : Subgroup G) : Set G) := by rw [hG]; exact mem_top g
      rw [mul_normal] at hg
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      show x * y * n * (x * y)⁻¹ ∈ K
      have hyn : y * n * y⁻¹ = n := by
        rw [← mem_centralizer_iff.mp (hXY hy) n (hKX hn'), mul_inv_cancel_right]
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e, hyn]
      exact (mem_normalizer_iff.mp (hXK hx) n).mp hn'
    · right
      have heq := normalClosure_eq_nclIn hYn hXY hG hKX
      refine ⟨?_, fun R hR => ?_⟩
      · rw [heq]
        exact isSzOrU3_of_mulEquiv (nclInEquiv hO) hsz
      · have h1 := hsyl _ (isSylowOf_bar hKX hR)
        rw [isSylowOf_iff_card] at h1 hR ⊢
        refine ⟨hR.1.trans (heq ▸ le_nclIn hKX), ?_⟩
        rw [heq, Nat.card_congr (nclInEquiv (K := K) hO).toEquiv, ← h1.2,
          card_bar_of_pGroup (hR.1.trans hKX) (IsPGroup.of_card hR.2)]

theorem conc4_of_split (hΩ : Sec3Setting Ω) {α β : Set (Subgroup G)} (hαβ : Ω = α ∪ β)
    (hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α)
    (hβinv : ∀ J ∈ β, ∀ g : G, rightConjugate J g ∈ β)
    (hcomm : ∀ A ∈ α, ∀ B ∈ β, ⁅A, B⁆ = ⊥) (hCα : Conc4 (bar (sSup α) '' α))
    (hCβ : Conc4 (bar (sSup β) '' β)) : Conc4 Ω := by
  intro K hK
  have hK' := hK
  rw [hαβ] at hK'
  rcases hK' with hKα | hKβ
  · exact hΩ.conc4_clause_of_split hαβ hαinv hβinv hcomm hCα hKα
  · exact hΩ.conc4_clause_of_split (hαβ.trans (Set.union_comm α β)) hβinv hαinv
      (fun B hB A hA => by rw [commutator_comm]; exact hcomm A hA B hB) hCβ hKβ

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X.MinCounter

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conc4_bar (hM : MinCounter Ω) {α : Set (Subgroup G)} (hαΩ : α ⊆ Ω)
    (hαinv : ∀ J ∈ α, ∀ x ∈ sSup α, rightConjugate J x ∈ α)
    (hlt : α.ncard < Ω.ncard ∨ Nat.card ↥(sSup α) < Nat.card G) :
    Conc4 (bar (sSup α) '' α) := by
  refine hM.ih _ _ (hM.setting.barSetting hαΩ hαinv) ?_
  rcases (card_barGroup_le (sSup α)).lt_or_eq with h | h
  · exact Or.inl h
  · rcases hlt with hlt | hlt
    · exact Or.inr ⟨h, (Set.ncard_image_le (Set.toFinite α)).trans_lt hlt⟩
    · exact absurd h ((Nat.card_le_card_of_surjective _
        (QuotientGroup.mk'_surjective (CFSG.oddCore ↥(sSup α)))).trans_lt hlt).ne

theorem lemma36 (hM : MinCounter Ω) (h22 : Lemma22Four) {K : Subgroup G} (hK : K ∈ Ω) :
    ¬ K.Normal := by
  intro hKn
  have hΩ := hM.setting
  set α : Set (Subgroup G) := {K} with hα
  set β : Set (Subgroup G) := Ω \ {K} with hβ
  have hαβ : Ω = α ∪ β := by
    rw [hα, hβ, Set.union_sdiff_self, Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hK)]
  have hKconj : ∀ g : G, rightConjugate K g = K := fun g =>
    (rightConjugate_eq_self_iff K g).mpr (by rw [normalizer_eq_top_iff.mpr hKn]; exact mem_top g)
  have hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α := by
    intro J hJ g
    have hJK : J = K := hJ
    rw [hJK, hKconj]
    exact Set.mem_singleton K
  have hβinv : ∀ J ∈ β, ∀ g : G, rightConjugate J g ∈ β := by
    rintro J ⟨hJ, hJK⟩ g
    refine ⟨hΩ.conj_mem J hJ g, fun h => hJK ?_⟩
    have h1 : rightConjugate J g = K := h
    have : J = rightConjugate (rightConjugate J g) g⁻¹ := by
      rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    rw [this, h1, hKconj]
    rfl
  have hOK : oddCoreIn K = ⊥ := by
    show (CFSG.oddCore K).map K.subtype = ⊥
    rw [oddCore_eq_bot_of_normal' hΩ.oddCore hKn, Subgroup.map_bot]
  have hcomm : ∀ A ∈ α, ∀ B ∈ β, ⁅A, B⁆ = ⊥ := by
    intro A hA B hB'
    have hAK : A = K := hA
    subst hAK
    obtain ⟨hB, hBK⟩ := hB'
    have heven : Even (Nat.card (B ⊓ normalizer (A : Set G) : Subgroup G)) := by
      rw [normalizer_eq_top_iff.mpr hKn, inf_top_eq]
      exact (hΩ.tightlyEmbedded hB).1
    have h := (hΩ.lemma35 h22 hK hB hBK heven).2
    rw [hOK, le_bot_iff] at h
    rw [commutator_comm]
    exact h
  have hCα : Conc4 (bar (sSup α) '' α) := by
    rintro _ ⟨K', hK', rfl⟩
    rw [hα, Set.mem_singleton_iff] at hK'
    subst hK'
    have htop : bar (sSup α) K' = ⊤ := by
      rw [hα, sSup_singleton, bar, subgroupOf_self]
      exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    refine ⟨fun J hJ hJK => absurd ?_ (hJK 1), Or.inl ?_⟩
    · obtain ⟨J', hJ', rfl⟩ := hJ
      rw [hα, Set.mem_singleton_iff] at hJ'
      rw [hJ', rightConjugate_one]
    · rw [htop]
      infer_instance
  have hCβ : Conc4 (bar (sSup β) '' β) :=
    hM.conc4_bar Set.sdiff_subset (fun J hJ x _ => hβinv J hJ x)
      (Or.inl (Set.ncard_sdiff_singleton_lt_of_mem hK (Set.toFinite Ω)))
  exact hM.not_conc (hΩ.conc4_of_split hαβ hαinv hβinv hcomm hCα hCβ)

end CFSG.ComponentClassification.Asc76X.MinCounter
