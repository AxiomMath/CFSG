module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionLocal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly CFSG.Semidihedral.Principal.PrimewiseScalar

variable {X : Type} [Group X] [Finite X]

@[expose] def CentralizerCovered (t : X) (P : Subgroup X) : Prop :=
  ∀ m ∈ centralizer ({t} : Set X), ∃ n ∈ normalizer (P : Set X),
    n ∈ centralizer ({t} : Set X) ∧ n⁻¹ * m ∈ oddCentralizer t

structure IsCandidate (S : Subgroup X) (t : X) (p : ℕ) (P : Subgroup X) : Prop where
  isPGroup : IsPGroup p P
  ne_bot : P ≠ ⊥
  le_normalizer : S ≤ normalizer (P : Set X)
  covered : CentralizerCovered t P

theorem exists_isCandidate {S : Sylow 2 X} {t : X} (ht : IsCentralInvolution (S : Subgroup X) t)
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card (oddCentralizer t)) :
    ∃ P, IsCandidate S t p P := by
  have hSN := (le_centralizer_of_isCentralInvolution ht).trans
    (centralizer_le_normalizer_oddCentralizer t)
  obtain ⟨P, hP, hSP⟩ :=
    exists_isSylowOf_le_normalizer (p := p) (odd_card_oddCentralizer t) S.isPGroup' hSN
  refine ⟨P, ⟨isPGroup_of_isSylowOf hP, fun hbot => ?_, hSP, fun m hm => ?_⟩⟩
  · have h := card_isSylowOf hP
    rw [hbot, Subgroup.card_bot] at h
    have hk : (Nat.card (oddCentralizer t)).factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hp).ne'
    exact absurd h.symm (Nat.one_lt_pow hk (Fact.out : p.Prime).one_lt).ne'
  · obtain ⟨k, hk, hkn⟩ :=
      exists_mem_inv_mul_mem_normalizer hP (centralizer_le_normalizer_oddCentralizer t hm)
    refine ⟨k⁻¹ * m, hkn, (centralizer {t}).mul_mem
      ((centralizer {t}).inv_mem (oddCentralizer_le t hk)) hm, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (centralizer_le_normalizer_oddCentralizer t
      ((centralizer {t}).inv_mem hm)) k).mp hk
    rwa [inv_inv, show m⁻¹ * k * m = (k⁻¹ * m)⁻¹ * m by group] at h

theorem exists_isCandidate_max {S : Subgroup X} {t : X} {p : ℕ} {P₀ : Subgroup X}
    (h₀ : IsCandidate S t p P₀) :
    ∃ P, IsCandidate S t p P ∧ ∀ Q, IsCandidate S t p Q → Nat.card Q ≤ Nat.card P :=
  Set.exists_max_image {P | IsCandidate S t p P} (fun P => Nat.card P) (Set.toFinite _) ⟨P₀, h₀⟩

theorem IsCandidate.normalizer_ne_top {S : Sylow 2 X} {t : X} {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsCandidate S t p P) (hX : MinimalCounterexample X S t)
    (hp2 : p ≠ 2) : normalizer (P : Set X) ≠ ⊤ := by
  intro htop
  have hle := le_pPrimeCore_of_normal (Subgroup.normalizer_eq_top_iff.mp htop)
    (odd_card_of_isPGroup hp2 hP.isPGroup)
  rw [hX.oddCore_eq_bot, le_bot_iff] at hle
  exact hP.ne_bot hle

omit [Finite X] in
theorem conj_mem_map_conj_of_mem_centralizer {t : X} {P₀ : Subgroup X}
    (hP₀ : ∀ x ∈ P₀, t * x * t⁻¹ ∈ P₀) {n : X} (hn : n ∈ centralizer ({t} : Set X)) :
    ∀ x ∈ P₀.map (MulAut.conj n).toMonoidHom, t * x * t⁻¹ ∈ P₀.map (MulAut.conj n).toMonoidHom :=
  fun x hx => by
    rw [mem_map_conj_iff] at hx ⊢
    have hnt : n⁻¹ * t * n = t := by
      rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hn, inv_mul_cancel_left]
    have h := hP₀ _ hx
    rwa [show t * (n⁻¹ * x * n) * t⁻¹ = (n⁻¹ * t * n) * (n⁻¹ * x * n) * (n⁻¹ * t * n)⁻¹ by
      rw [hnt], show (n⁻¹ * t * n) * (n⁻¹ * x * n) * (n⁻¹ * t * n)⁻¹ = n⁻¹ * (t * x * t⁻¹) * n
      by group] at h

namespace MinimalCounterexample

variable {S : Sylow 2 X} {t : X} (hX : MinimalCounterexample X S t) {p : ℕ} [Fact p.Prime]
  (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsCandidate S t p P)
  (hmax : ∀ Q, IsCandidate S t p Q → Nat.card Q ≤ Nat.card P)
include hX hp2 hP hmax

theorem card_le_of_le_oddCoreOf {Q : Subgroup X} (hQ : IsPGroup p Q)
    (hQK : Q ≤ oddCoreOf (normalizer (P : Set X))) : Nat.card Q ≤ Nat.card P := by
  set H := normalizer (P : Set X)
  set K := oddCoreOf H
  have hKodd := odd_card_oddCoreOf H
  have hSK : (S : Subgroup X) ≤ normalizer (K : Set X) :=
    hP.le_normalizer.trans (le_normalizer_oddCoreOf H)
  obtain ⟨P₀, hP₀, hSP₀⟩ := exists_isSylowOf_le_normalizer (p := p) hKodd S.isPGroup' hSK
  have hPK : P ≤ K :=
    le_oddCoreOf Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup hp2 hP.isPGroup)
  have hPP₀ : P ≤ P₀ := le_isSylowOf_of_le_normalizer hP₀ hP.isPGroup hPK (oddCoreOf_le H)
  have htS := hX.central.1
  have hinv₀ : ∀ x ∈ P₀, t * x * t⁻¹ ∈ P₀ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hSP₀ htS) x).mp hx
  refine (card_le_of_isSylowOf hP₀ hQ hQK).trans (hmax _ ⟨isPGroup_of_isSylowOf hP₀,
    fun h => hP.ne_bot (le_bot_iff.mp (h ▸ hPP₀)), hSP₀, fun m hm => ?_⟩)
  obtain ⟨n₁, hn₁H, hn₁t, hn₁m⟩ := hP.covered m hm
  have hP₁K : P₀.map (MulAut.conj n₁).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf H hn₁H) x).mp
      (le_of_isSylowOf hP₀ hx)
  obtain ⟨c, hcK, hct, hc⟩ := exists_conj_of_invariant_sylow K hKodd (hSK htS) hX.central.2.1
    (Fact.out : p.Prime) (isSylowOf_of_card_eq hP₀ hP₁K
      (Subgroup.card_map_of_injective (MulAut.conj n₁).injective)) hP₀
    (conj_mem_map_conj_of_mem_centralizer hinv₀ hn₁t) hinv₀
  have hcC : c ∈ centralizer ({t} : Set X) := Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc c * t = t * c * t⁻¹ * t := by rw [hct]
      _ = t * c := by group)
  have hcO : c ∈ oddCentralizer t := hX.oddCoreOf_inf_centralizer_le hP.covered ⟨hcK, hcC⟩
  have hN : n₁⁻¹ * c ∈ normalizer (P₀ : Set X) := Subgroup.mem_normalizer_iff.mpr fun y =>
    (hc y).trans (by
      rw [mem_map_conj_iff, show n₁⁻¹ * (c * y * c⁻¹) * n₁ = n₁⁻¹ * c * y * (n₁⁻¹ * c)⁻¹ by
        group])
  refine ⟨c⁻¹ * n₁, by simpa using (normalizer (P₀ : Set X)).inv_mem hN,
    (centralizer {t}).mul_mem ((centralizer {t}).inv_mem hcC) hn₁t, ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (centralizer_le_normalizer_oddCentralizer t
    ((centralizer {t}).inv_mem hn₁t)) c).mp hcO
  rw [inv_inv] at h1
  rw [show (c⁻¹ * n₁)⁻¹ * m = n₁⁻¹ * c * n₁ * (n₁⁻¹ * m) by group]
  exact (oddCentralizer t).mul_mem h1 hn₁m

theorem eq_of_le_of_isPGroup {R : Subgroup X} (hR : IsPGroup p R) (hPR : P ≤ R)
    (hSR : (S : Subgroup X) ≤ normalizer (R : Set X)) : R = P := by
  set H := normalizer (P : Set X)
  have hSH : (S : Subgroup X) ≤ H := hP.le_normalizer
  have hQ := hX.isTwoANine_quotient hSH hP.covered (hP.normalizer_ne_top hX hp2)
  have hPR₀ : P ≤ R ⊓ H := le_inf hPR Subgroup.le_normalizer
  have hbar : ((R ⊓ H).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)) = ⊥ := by
    refine hQ.eq_bot_of_odd_of_sylow_le_normalizer
      ((S.subtype hSH).mapSurjective (QuotientGroup.mk'_surjective _)) ?_ ?_
    · exact (odd_card_of_isPGroup hp2 (hR.to_le inf_le_left)).of_dvd_nat
        ((Subgroup.card_map_dvd _ _).trans
          (Subgroup.card_comap_dvd_of_injective _ _ H.subtype_injective))
    · rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
      refine (Subgroup.map_mono fun s hs => mem_normalizer_subgroupOf_of_mem
        (inf_mem_normalizer (hSR (Subgroup.mem_subgroupOf.mp hs))
          (Subgroup.le_normalizer s.2))).trans (Subgroup.le_normalizer_map _)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbar
  have hR₀K : R ⊓ H ≤ oddCoreOf H := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : R ⊓ H ≤ H)]
    exact Subgroup.map_mono hbar
  have hR₀ : P = R ⊓ H := Subgroup.eq_of_le_of_card_ge hPR₀
    (hX.card_le_of_le_oddCoreOf hp2 hP hmax (hR.to_le inf_le_left) hR₀K)
  by_contra hne
  have h := lt_inf_normalizer_of_lt hR (lt_of_le_of_ne hPR (Ne.symm hne))
  rw [← hR₀] at h
  exact lt_irrefl _ h

end MinimalCounterexample

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
