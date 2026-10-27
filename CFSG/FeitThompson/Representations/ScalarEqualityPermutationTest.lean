module

public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.HallCosetInDetectedCoreSupport
import CFSG.FeitThompson.Representations.CoordinateKernelPermutationCharacterNorm
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L]

def autFixer {V : Type*} [Group V] (ρ : L →* MulAut V) (S : Set V) : Subgroup L where
  carrier := {g | ∀ v ∈ S, ρ g v = v}
  one_mem' := by intro v _; simp
  mul_mem' {a b} ha hb := by
    intro v hv
    rw [map_mul]
    change ρ a (ρ b v) = v
    rw [hb v hv, ha v hv]
  inv_mem' {a} ha := by
    intro v hv
    rw [map_inv]
    change ((ρ a)⁻¹ : MulAut V) v = v
    rw [show ((ρ a)⁻¹ : MulAut V) v = (ρ a).symm v from rfl, MulEquiv.symm_apply_eq, ha v hv]

theorem mem_autFixer {V : Type*} [Group V] {ρ : L →* MulAut V} {S : Set V} {g : L} :
    g ∈ autFixer ρ S ↔ ∀ v ∈ S, ρ g v = v := Iff.rfl

def lineFixer (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    (Ei : Subgroup (↥H ⧸ H0.subgroupOf H)) : Subgroup L :=
  U ⊓ autFixer (conjQuotientAut H H0) (Ei : Set (↥H ⧸ H0.subgroupOf H))

theorem lineFixer_le (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    (Ei : Subgroup (↥H ⧸ H0.subgroupOf H)) : lineFixer H H0 U Ei ≤ U := inf_le_left

theorem mem_lineFixer {H H0 U : Subgroup L} [H.Normal] [H0.Normal]
    {Ei : Subgroup (↥H ⧸ H0.subgroupOf H)} {x : L} :
    x ∈ lineFixer H H0 U Ei ↔ x ∈ U ∧ ∀ v ∈ Ei, conjQuotientAut H H0 x v = v :=
  Subgroup.mem_inf

def lineFixerInf (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) : Subgroup L :=
  ⨅ i, lineFixer H H0 U (Eline i)

theorem lineFixerInf_le_lineFixer (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (i : ZMod q) :
    lineFixerInf H H0 U Eline ≤ lineFixer H H0 U (Eline i) := iInf_le _ i

theorem lineFixerInf_le (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (i : ZMod q) :
    lineFixerInf H H0 U Eline ≤ U :=
  (lineFixerInf_le_lineFixer H H0 U Eline i).trans (lineFixer_le H H0 U (Eline i))

theorem le_lineFixerInf {H H0 U : Subgroup L} [H.Normal] [H0.Normal] {q : ℕ}
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {X : Subgroup L}
    (h : ∀ i, X ≤ lineFixer H H0 U (Eline i)) : X ≤ lineFixerInf H H0 U Eline :=
  le_iInf h

theorem mem_lineFixerInf {H H0 U : Subgroup L} [H.Normal] [H0.Normal] {q : ℕ}
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {x : L} :
    x ∈ lineFixerInf H H0 U Eline ↔ ∀ i, x ∈ lineFixer H H0 U (Eline i) :=
  Subgroup.mem_iInf

structure IsScalarEqualityConfig (p q : ℕ) (K H U B H0 : Subgroup L) [H.Normal] [H0.Normal]
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (A : Set L) : Prop where
  solvable : Group.IsSolvable L
  odd_card : Odd (Nat.card L)
  q_prime : q.Prime
  p_prime : p.Prime
  p_odd : Odd p
  p_ne_q : p ≠ q
  isComplement_K_B : K.IsComplement' B
  H_le_K : H ≤ K
  U_le_K : U ≤ K
  disjoint_H_U : Disjoint H U
  sup_H_U : H ⊔ U = K
  card_B : Nat.card B = q
  exists_gen_B : ∃ b ∈ B, B = Subgroup.zpowers b ∧
    ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)
  B_le_normalizer_U : B ≤ Subgroup.normalizer (U : Set L)
  coprime_H_U : (Nat.card H).Coprime (Nat.card U)
  coprime_q_K : q.Coprime (Nat.card K)
  inf_centralizer_U_B : U ⊓ Subgroup.centralizer (B : Set L) = ⊥
  H0_le_H : H0 ≤ H
  card_quotient : Nat.card (↥H ⧸ H0.subgroupOf H) = p ^ q
  indep_Eline : iSupIndep Eline
  iSup_Eline : ⨆ i, Eline i = ⊤
  card_Eline : ∀ i, Nat.card (Eline i) = p
  map_U_Eline : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i
  lineFixer_ne : ∀ i, lineFixer H H0 U (Eline i) ≠ U
  A_subset : A ⊆ (K : Set L) \ {1}
  A_invariant : ∀ g : L, ∀ x ∈ A, g⁻¹ * x * g ∈ A
  centralizer_subset_A : ∀ h ∈ H, h ≠ 1 →
    ((K ⊓ Subgroup.centralizer ({h} : Set L) : Subgroup L) : Set L) \ {1} ⊆ A
  commutator_eq : lineFixerInf H H0 U Eline = ⁅U, U⁆
  sub_one_eq : p - 1 = 2 * (lineFixer H H0 U (Eline 0)).relIndex U
  lt_relIndex : (lineFixer H H0 U (Eline 0)).relIndex U
    < (lineFixerInf H H0 U Eline).relIndex U
  inf_lineFixer : ∀ i j, i ≠ j →
    lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) = lineFixerInf H H0 U Eline

namespace IsScalarEqualityConfig

variable {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal] [H0.Normal]
  {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}

theorem isCyclic_B (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) : IsCyclic B := by
  obtain ⟨b, hbB, hB, -⟩ := hc.exists_gen_B
  refine ⟨⟨⟨b, hbB⟩, fun x => ?_⟩⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hB ▸ x.2 : (x : L) ∈ Subgroup.zpowers b)
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem q_odd (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) : Odd q := by
  have hdvd : q ∣ Nat.card L := hc.card_B ▸ Subgroup.card_subgroup_dvd_card B
  rcases Nat.even_or_odd q with he | ho
  · exact absurd (he.two_dvd.trans hdvd)
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.1 hc.odd_card)
  · exact ho

end IsScalarEqualityConfig

noncomputable def scalarEqualityFamily [Fintype L] (K H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) : Set (L → ℂ) :=
  indFam K (irrKer ℂ (H.subgroupOf K)
    ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K))

theorem mem_scalarEqualityFamily [Fintype L] {K H H0 U : Subgroup L} [H.Normal] [H0.Normal]
    {q : ℕ} {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {f : L → ℂ} :
    f ∈ scalarEqualityFamily K H H0 U Eline ↔
      ∃ θ ∈ irrKer ℂ (H.subgroupOf K)
        ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K),
        indClassFun K θ = f :=
  mem_indFam K

theorem scalarEqualityFamily_subset_indFam [Fintype L] {K H H0 U : Subgroup L} [H.Normal]
    [H0.Normal] {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) :
    scalarEqualityFamily K H H0 U Eline ⊆ indFam K (Irr ↥K) := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hf
  exact indClassFun_mem_indFam K (mem_Irr.2 (mem_irrChar.1 (mem_irrKer.1 hθ).1))

theorem cfInner_eq_zero_of_mem_scalarEqualityFamily [Fintype L] {K H H0 U : Subgroup L} [H.Normal]
    [H0.Normal] [K.Normal] {q : ℕ} {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {f g : L → ℂ} (hf : f ∈ scalarEqualityFamily K H H0 U Eline)
    (hg : g ∈ scalarEqualityFamily K H H0 U Eline) (hne : f ≠ g) : cfInner f g = 0 :=
  NormalInducedFamily.cfInner_eq_zero_of_mem_indFam K
    (scalarEqualityFamily_subset_indFam Eline hf)
    (scalarEqualityFamily_subset_indFam Eline hg) hne

noncomputable def scalarPermChar [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) : L → ℂ :=
  indClassFun (H ⊔ lineFixer H H0 U (Eline 0)) 1

theorem scalarPermChar_eq [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) :
    scalarPermChar H H0 U Eline = indClassFun (H ⊔ lineFixer H H0 U (Eline 0)) 1 := (rfl)

noncomputable def scalarTestChar [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (psi : L → ℂ) : L → ℂ :=
  scalarPermChar H H0 U Eline - psi

theorem scalarTestChar_eq [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (psi : L → ℂ) :
    scalarTestChar H H0 U Eline psi = scalarPermChar H H0 U Eline - psi := (rfl)

theorem scalarTestChar_apply [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (psi : L → ℂ) (x : L) :
    scalarTestChar H H0 U Eline psi x = scalarPermChar H H0 U Eline x - psi x := (rfl)

theorem indClassFun_one_mem_virtualChars [Fintype L] (X : Subgroup L) :
    indClassFun X (1 : X → ℂ) ∈ virtualChars L := by
  obtain ⟨V, -, hV⟩ := mem_Irr.1 (one_mem_Irr (G := ↥X))
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_indClassFun X V
  rw [hV] at hW
  exact span_Irr_le_virtualChars (hW ▸ InducedCharacterConstruction.fdRepCharacter_mem_span_Irr W)

theorem scalarTestChar_mem_virtualChars [Fintype L] (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {q : ℕ} (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) {psi : L → ℂ}
    (hpsi : psi ∈ Irr L) : scalarTestChar H H0 U Eline psi ∈ virtualChars L :=
  Submodule.sub_mem _ (indClassFun_one_mem_virtualChars _) (Irr_subset_virtualChars hpsi)

theorem card_sup_eq_mul_of_disjoint [Finite L] (H X : Subgroup L) [H.Normal]
    (hd : Disjoint H X) : Nat.card ↥H * Nat.card ↥X = Nat.card ↥(H ⊔ X) := by
  have h : (H.subgroupOf (H ⊔ X)).IsComplement' (X.subgroupOf (H ⊔ X)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hz
      have h2 := Subgroup.mem_inf.2 hz
      rw [disjoint_iff.1 hd, Subgroup.mem_bot] at h2
      exact Subgroup.mem_bot.2 (Subtype.ext h2)
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self]
      simp
  have h2 := h.card_mul_card
  rwa [Nat.card_eq_of_bijective _
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ X)).bijective,
    Nat.card_eq_of_bijective _
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : X ≤ H ⊔ X)).bijective] at h2

theorem scalarPermChar_apply_one [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal]
    [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) :
    scalarPermChar H H0 U Eline 1
      = (q : ℂ) * ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) := by
  set U0 := lineFixer H H0 U (Eline 0)
  have hU0U : U0 ≤ U := lineFixer_le H H0 U (Eline 0)
  have hLcard : Nat.card ↥K * Nat.card ↥B = Nat.card L := hc.isComplement_K_B.card_mul_card
  have hKcard : Nat.card ↥H * Nat.card ↥U = Nat.card ↥K := by
    rw [card_sup_eq_mul_of_disjoint H U hc.disjoint_H_U, hc.sup_H_U]
  have hXcard : Nat.card ↥H * Nat.card ↥U0 = Nat.card ↥(H ⊔ U0) :=
    card_sup_eq_mul_of_disjoint H U0 (hc.disjoint_H_U.mono_right hU0U)
  have hrel : Nat.card ↥U0 * U0.relIndex U = Nat.card ↥U :=
    ScalarComplementPermutationNorm.card_mul_relIndex hU0U
  rw [scalarPermChar_eq, indClassFun_one]
  have hH : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hU0' : (Nat.card ↥U0 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e1 : (Nat.card L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card ↥U : ℂ) * (Nat.card ↥B : ℂ) := by
    rw [← hLcard, ← hKcard]; push_cast; ring
  have e2 : (Nat.card ↥(H ⊔ U0) : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card ↥U0 : ℂ) := by
    rw [← hXcard]; push_cast; ring
  have e3 : (Nat.card ↥U : ℂ) = (Nat.card ↥U0 : ℂ) * (U0.relIndex U : ℂ) := by
    rw [← hrel]; push_cast; ring
  rw [e1, e2, e3, Pi.one_apply, mul_one, hc.card_B]
  field_simp

theorem exists_fix_of_mem_lineFixer (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    {Ei : Subgroup (↥H ⧸ H0.subgroupOf H)} (hEi : Ei ≠ ⊥) {i : L}
    (hi : i ∈ lineFixer H H0 U Ei) : ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0 := by
  obtain ⟨⟨v, hvEi⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEi
  have hvne : v ≠ 1 := fun hcon => hv1 (Subtype.ext hcon)
  induction v using QuotientGroup.induction_on with
  | _ h =>
    have hfix := (mem_lineFixer.1 hi).2 _ hvEi
    rw [conjQuotientAut_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfix
    refine ⟨(h : L), h.2, ?_, ?_⟩
    · intro hcon
      exact hvne (by rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hcon)
    · push_cast at hfix
      have hcoe : ((MulAut.conjNormal i (h : ↥H) : ↥H) : L) = i * (h : L) * i⁻¹ := by
        simp [MulAut.conjNormal_apply]
      rw [hcoe] at hfix
      have hmem := ‹H0.Normal›.conj_mem _ hfix i⁻¹
      convert hmem using 1
      group

theorem sup_lineFixer_sdiff_subset [Finite L] {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal]
    [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) :
    ((H ⊔ lineFixer H H0 U (Eline 0) : Subgroup L) : Set L) \ {1} ⊆ A := by
  have _hsolv := hc.solvable
  set U0 := lineFixer H H0 U (Eline 0)
  have hU0U : U0 ≤ U := lineFixer_le H H0 U (Eline 0)
  have hHK : H ≤ K := hc.H_le_K
  have hU0K : U0 ≤ K := hU0U.trans hc.U_le_K
  set Xs : Subgroup ↥K := (H ⊔ U0).subgroupOf K with hXs
  have hHX : H.subgroupOf K ≤ Xs := Subgroup.subgroupOf_mono K le_sup_left
  have hIX : U0.subgroupOf K ≤ Xs := Subgroup.subgroupOf_mono K le_sup_right
  have hdisj : Disjoint (H.subgroupOf K) (U0.subgroupOf K) := by
    rw [disjoint_iff, eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hz
    have h2 := Subgroup.mem_inf.2 hz
    rw [disjoint_iff.1 (hc.disjoint_H_U.mono_right hU0U), Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  have hsup : H.subgroupOf K ⊔ U0.subgroupOf K = Xs := (Subgroup.subgroupOf_sup hHK hU0K).symm
  have hcardH : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hHK).bijective
  have hcardU0 : Nat.card ↥(U0.subgroupOf K) = Nat.card ↥U0 :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hU0K).bijective
  have hcop : (Nat.card ↥(H.subgroupOf K)).Coprime (Nat.card ↥(U0.subgroupOf K)) := by
    rw [hcardH, hcardU0]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hU0U) hc.coprime_H_U
  have hE0 : Eline 0 ≠ ⊥ := by
    intro hcon
    have hcard := hc.card_Eline 0
    rw [hcon] at hcard
    simp only [Subgroup.card_bot] at hcard
    exact hc.p_prime.one_lt.ne hcard
  have hfix : ∀ i ∈ U0.subgroupOf K, ∃ h ∈ H.subgroupOf K, h ∉ H0.subgroupOf K ∧
      h⁻¹ * (i⁻¹ * h * i) ∈ H0.subgroupOf K := by
    intro i hi
    obtain ⟨h, hh, hhH0, hcon⟩ :=
      exists_fix_of_mem_lineFixer H H0 U hE0 (Subgroup.mem_subgroupOf.1 hi)
    refine ⟨⟨h, hHK hh⟩, Subgroup.mem_subgroupOf.2 hh, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hhH0
    · rw [Subgroup.mem_subgroupOf]; push_cast; exact hcon
  have hA : ∀ h ∈ H.subgroupOf K, h ≠ 1 →
      (Subgroup.centralizer ({h} : Set ↥K) : Set ↥K) \ {1} ⊆ {z : ↥K | (z : L) ∈ A} := by
    intro h hh hh1
    rintro z ⟨hzc, hz1⟩
    have hhL : (h : L) ∈ H := Subgroup.mem_subgroupOf.1 hh
    have hhL1 : (h : L) ≠ 1 := fun hcon => hh1 (Subtype.ext hcon)
    have hzc' : (z : L) ∈ Subgroup.centralizer ({(h : L)} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hzc))
    refine hc.centralizer_subset_A (h : L) hhL hhL1 ⟨Subgroup.mem_inf.2 ⟨z.2, hzc'⟩, ?_⟩
    intro hcon
    exact hz1 (Subtype.ext (by simpa using hcon))
  have hHn : ((H.subgroupOf K).subgroupOf Xs).Normal := by infer_instance
  have hH0n : ((H0.subgroupOf K).subgroupOf Xs).Normal := by infer_instance
  have key := sdiff_singleton_one_subset_of_centralizer_sdiff_subset
    (Xs := Xs) (H := H.subgroupOf K) (I := U0.subgroupOf K) (H0 := H0.subgroupOf K)
    hHn hH0n hHX hIX hdisj hsup hcop hfix hA
  rintro x ⟨hx, hx1⟩
  rw [Set.mem_singleton_iff] at hx1
  have hxK : x ∈ K := (sup_le hHK hU0K) hx
  exact key (a := (⟨x, hxK⟩ : ↥K)) ⟨Subgroup.mem_subgroupOf.2 hx, by
    simp only [Set.mem_singleton_iff]
    intro hcon
    exact hx1 (by simpa using congrArg Subtype.val hcon)⟩

theorem indClassFun_one_eq_zero_of_notMem [Fintype L] {X : Subgroup L} {A : Set L}
    (hXA : (X : Set L) \ {1} ⊆ A) (hAinv : ∀ g : L, ∀ x ∈ A, g⁻¹ * x * g ∈ A)
    {y : L} (hy1 : y ≠ 1) (hyA : y ∉ A) : indClassFun X (1 : ↥X → ℂ) y = 0 := by
  classical
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hmem : t⁻¹ * y * t ∈ X
  · exfalso
    have hne : t⁻¹ * y * t ≠ 1 := by
      intro hcon
      refine hy1 ?_
      have h2 : t * (t⁻¹ * y * t) * t⁻¹ = t * 1 * t⁻¹ := by rw [hcon]
      simpa [mul_assoc] using h2
    have hA := hXA ⟨hmem, by simpa using hne⟩
    have h3 := hAinv t⁻¹ _ hA
    simp only [inv_inv] at h3
    exact hyA (by simpa [show t * (t⁻¹ * y * t) * t⁻¹ = y from by group] using h3)
  · rw [dif_neg hmem]

theorem scalarPermChar_eq_zero_of_notMem [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {y : L} (hy1 : y ≠ 1) (hyA : y ∉ A) :
    scalarPermChar H H0 U Eline y = 0 :=
  indClassFun_one_eq_zero_of_notMem (sup_lineFixer_sdiff_subset hc) hc.A_invariant hy1 hyA

theorem inf_centralizer_eq_bot_of_notMem {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal]
    [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {x : L} (hxK : x ∈ K) (hx1 : x ≠ 1)
    (hxA : x ∉ A) : H ⊓ Subgroup.centralizer ({x} : Set L) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro h hh
  obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.1 hh
  by_contra hh1
  refine hxA (hc.centralizer_subset_A h hhH hh1 ⟨Subgroup.mem_inf.2 ⟨hxK, ?_⟩, hx1⟩)
  exact Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hhc).symm

theorem inf_centralizer_subgroupOf_eq_bot_of_notMem {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {z : ↥K} (hz1 : (z : L) ≠ 1)
    (hzA : (z : L) ∉ A) :
    (H.subgroupOf K) ⊓ Subgroup.centralizer ({z} : Set ↥K) = ⊥ := by
  have hbot := inf_centralizer_eq_bot_of_notMem hc z.2 hz1 hzA
  rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
  intro w hw
  obtain ⟨hwH, hwc⟩ := Subgroup.mem_inf.1 hw
  have hcomm : (w : L) * (z : L) = (z : L) * (w : L) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hwc)
  exact Subtype.ext (hbot (w : L) (Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.1 hwH, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩))

theorem eq_zero_of_mem_scalarEqualityFamily [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] [K.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {A : Set L} (hc : IsScalarEqualityConfig p q K H U B H0 Eline A)
    {chi : L → ℂ} (hchi : chi ∈ scalarEqualityFamily K H H0 U Eline) {y : L} (hy1 : y ≠ 1)
    (hyA : y ∉ A) : chi y = 0 := by
  classical
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hchi
  obtain ⟨hirr, -, hdet⟩ := mem_irrKer.1 hθ
  have _hHn : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hmem : t⁻¹ * y * t ∈ K
  · rw [dif_pos hmem]
    set z : ↥K := ⟨t⁻¹ * y * t, hmem⟩ with hzdef
    have hzcoe : (z : L) = t⁻¹ * y * t := rfl
    have hz1 : (z : L) ≠ 1 := by
      intro hcon
      refine hy1 ?_
      have h2 : t * (t⁻¹ * y * t) * t⁻¹ = t * 1 * t⁻¹ := by rw [← hzcoe, hcon]
      simpa [mul_assoc] using h2
    have hzA : (z : L) ∉ A := by
      intro hcon
      have h2 := hc.A_invariant t⁻¹ _ hcon
      simp only [inv_inv, hzcoe] at h2
      exact hyA (by simpa [show t * (t⁻¹ * y * t) * t⁻¹ = y from by group] using h2)
    exact eq_zero_of_inf_centralizer_eq_bot hirr hdet
      (inf_centralizer_subgroupOf_eq_bot_of_notMem hc hz1 hzA)
  · rw [dif_neg hmem]

theorem scalarTestChar_eq_zero_of_notMem [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] [K.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {A : Set L} (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {psi : L → ℂ}
    (hpsiS : psi ∈ scalarEqualityFamily K H H0 U Eline)
    (hdeg : psi 1 = (q : ℂ) * ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ))
    {y : L} (hyA : y ∉ A) : scalarTestChar H H0 U Eline psi y = 0 := by
  by_cases hy1 : y = 1
  · subst hy1
    rw [scalarTestChar_apply, scalarPermChar_apply_one hc, hdeg, sub_self]
  · rw [scalarTestChar_apply, scalarPermChar_eq_zero_of_notMem hc hy1 hyA,
      eq_zero_of_mem_scalarEqualityFamily hc hpsiS hy1 hyA, sub_zero]

theorem scalarTestChar_apply_one [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal]
    [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {psi : L → ℂ}
    (hdeg : psi 1 = (q : ℂ) * ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)) :
    scalarTestChar H H0 U Eline psi 1 = 0 := by
  rw [scalarTestChar_apply, scalarPermChar_apply_one hc, hdeg, sub_self]

theorem sum_character_mul_eq_zero {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    {N : Subgroup G} [N.Normal] [Fintype ↥N]
    (hN : ∃ h ∈ N, ρ.character h ≠ ρ.character 1) (g : G) :
    ∑ h : ↥N, ρ.character ((h : G) * g) = 0 := by
  have hinv := Representation.invariants_comp_subtype_eq_bot ρ hρ hN
  have hzero : ∀ v : V, ∑ h : ↥N, ρ (h : G) v = 0 := by
    intro v
    have h1 := Representation.sum_mem_invariants_comp_subtype ρ N v
    rw [hinv] at h1
    simpa using h1
  have hP : (∑ h : ↥N, ρ ((h : G) * g)) = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.sum_apply]
    have h2 : ∀ h : ↥N, ρ ((h : G) * g) v = ρ (h : G) (ρ g v) := fun h => by rw [map_mul]; rfl
    simp only [h2]
    simpa using hzero (ρ g v)
  have h3 := congrArg (LinearMap.trace ℂ V) hP
  rwa [map_sum, map_zero] at h3

theorem sum_apply_mul_eq_zero {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G)
    (hdet : ¬ (N : Set G) ⊆ charValueKernel χ) (g : G) : ∑ h : ↥N, χ ((h : G) * g) = 0 := by
  obtain ⟨W, hW, rfl⟩ := mem_irrChar.1 hχ
  have hN : ∃ h ∈ N, Representation.character W.ρ h ≠ Representation.character W.ρ 1 := by
    simp only [Set.subset_def, SetLike.mem_coe, mem_charValueKernel, not_forall] at hdet
    obtain ⟨x, hx, hne⟩ := hdet
    exact ⟨x, hx, hne⟩
  exact sum_character_mul_eq_zero W.ρ hW hN g

theorem sum_extendByZero_mul_eq_zero {K H : Subgroup L} [H.Normal] [Fintype ↥H] [Finite ↥K]
    (hHK : H ≤ K) {θ : ↥K → ℂ} (hθ : θ ∈ irrChar ℂ ↥K)
    (hdet : ¬ ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ) (z : L) :
    ∑ h : ↥H, extendByZero K θ ((h : L) * z) = 0 := by
  classical
  have _hHKn : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  have _hfinHK : Fintype ↥(H.subgroupOf K) := Fintype.ofFinite _
  by_cases hz : z ∈ K
  · have hcoe : ∀ h : ↥H, extendByZero K θ ((h : L) * z)
        = θ (⟨(h : L), hHK h.2⟩ * ⟨z, hz⟩) :=
      fun h => extendByZero_of_mem θ (K.mul_mem (hHK h.2) hz)
    rw [Finset.sum_congr rfl fun h _ => hcoe h]
    refine Eq.trans ?_ (sum_apply_mul_eq_zero (N := H.subgroupOf K) hθ hdet (⟨z, hz⟩ : ↥K))
    refine Fintype.sum_bijective
      (fun h : ↥H => (⟨⟨(h : L), hHK h.2⟩, Subgroup.mem_subgroupOf.2 h.2⟩ :
        ↥(H.subgroupOf K))) ?_ _ _ (fun _ => rfl)
    constructor
    · intro a b hab
      exact Subtype.ext (congrArg (fun x : ↥K => (x : L)) (congrArg Subtype.val hab))
    · intro w
      exact ⟨⟨((w : ↥K) : L), Subgroup.mem_subgroupOf.1 w.2⟩, Subtype.ext (Subtype.ext rfl)⟩
  · refine Finset.sum_eq_zero fun h _ => ?_
    refine extendByZero_of_notMem K θ ?_
    intro hmem
    refine hz ?_
    have hzz : z = (h : L)⁻¹ * ((h : L) * z) := by group
    rw [hzz]
    exact K.mul_mem (K.inv_mem (hHK h.2)) hmem

theorem sum_indClassFun_mul_eq_zero [Fintype L] {K H : Subgroup L} [H.Normal] [Fintype ↥H]
    (hHK : H ≤ K) {θ : ↥K → ℂ} (hθ : θ ∈ irrChar ℂ ↥K)
    (hdet : ¬ ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ) (g : L) :
    ∑ h : ↥H, indClassFun K θ ((h : L) * g) = 0 := by
  classical
  simp only [indClassFun_eq_sum_extendByZero]
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  have hbij : ∑ h : ↥H, extendByZero K θ (t⁻¹ * ((h : L) * g) * t)
      = ∑ h : ↥H, extendByZero K θ ((h : L) * (t⁻¹ * g * t)) := by
    refine Fintype.sum_bijective (fun h : ↥H => (⟨t⁻¹ * (h : L) * t, by
      simpa [mul_assoc] using ‹H.Normal›.conj_mem (h : L) h.2 t⁻¹⟩ : ↥H)) ?_ _ _ ?_
    · constructor
      · intro a b hab
        have h2 : t⁻¹ * (a : L) * t = t⁻¹ * (b : L) * t := congrArg Subtype.val hab
        exact Subtype.ext (by
          have h3 := congrArg (fun x => t * x * t⁻¹) h2
          simpa [mul_assoc] using h3)
      · intro w
        refine ⟨⟨t * (w : L) * t⁻¹, by simpa [mul_assoc] using ‹H.Normal›.conj_mem (w : L) w.2 t⟩,
          Subtype.ext ?_⟩
        change t⁻¹ * (t * (w : L) * t⁻¹) * t = (w : L)
        group
    · intro h
      congr 1
      change t⁻¹ * ((h : L) * g) * t = (t⁻¹ * (h : L) * t) * (t⁻¹ * g * t)
      group
  rw [hbij]
  exact sum_extendByZero_mul_eq_zero hHK hθ hdet (t⁻¹ * g * t)

theorem sum_subgroup_eq_zero_of_sum_coset {X H : Subgroup L} [Fintype ↥H] [Fintype ↥X]
    (hHX : H ≤ X) {f : L → ℂ} (hf : ∀ g : L, ∑ h : ↥H, f ((h : L) * g) = 0) :
    ∑ x : ↥X, f (x : L) = 0 := by
  classical
  have hT : ∑ h : ↥H, ∑ x : ↥X, f ((h : L) * (x : L)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun x _ => hf (x : L)
  have hS : ∀ h : ↥H, ∑ x : ↥X, f ((h : L) * (x : L)) = ∑ x : ↥X, f (x : L) := by
    intro h
    refine Fintype.sum_bijective (fun x : ↥X => (⟨(h : L) * (x : L), X.mul_mem (hHX h.2) x.2⟩ : ↥X))
      ?_ _ _ (fun _ => rfl)
    constructor
    · intro a b hab
      have h2 := congrArg Subtype.val hab
      exact Subtype.ext (by simpa using h2)
    · intro w
      exact ⟨⟨(h : L)⁻¹ * (w : L), X.mul_mem (X.inv_mem (hHX h.2)) w.2⟩, Subtype.ext (by simp)⟩
  rw [Finset.sum_congr rfl fun h _ => hS h, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hT
  have hcard : (Fintype.card ↥H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := ↥H)
  exact (mul_eq_zero.1 hT).resolve_left hcard

theorem cfInner_indClassFun_one_eq_zero_of_sum [Fintype L] {X : Subgroup L} [Fintype ↥X]
    {χ : L → ℂ} (hχ : χ ∈ classFun L) (hsum : ∑ x : ↥X, χ (x : L) = 0) :
    cfInner (indClassFun X (1 : ↥X → ℂ)) χ = 0 := by
  rw [cfInner_indClassFun X _ hχ, cfInner_def]
  refine mul_eq_zero_of_right _ ?_
  have h : ∀ x : ↥X, (1 : ↥X → ℂ) x * (starRingEnd ℂ) (resClassFun X χ x)
      = (starRingEnd ℂ) (χ (x : L)) := fun x => by
    rw [resClassFun_apply, Pi.one_apply, one_mul]
  rw [Finset.sum_congr rfl fun x _ => h x, ← map_sum, hsum, map_zero]

theorem cfInner_scalarPermChar_eq_zero [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A)
    {chi : L → ℂ} (hchi : chi ∈ scalarEqualityFamily K H H0 U Eline) :
    cfInner (scalarPermChar H H0 U Eline) chi = 0 := by
  classical
  have _hfH : Fintype ↥H := Fintype.ofFinite _
  have _hfX : Fintype ↥(H ⊔ lineFixer H H0 U (Eline 0) : Subgroup L) := Fintype.ofFinite _
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hchi
  obtain ⟨hirr, -, hdet⟩ := mem_irrKer.1 hθ
  rw [scalarPermChar_eq]
  refine cfInner_indClassFun_one_eq_zero_of_sum
    (X := (H ⊔ lineFixer H H0 U (Eline 0) : Subgroup L)) (indClassFun_mem_classFun K θ) ?_
  exact sum_subgroup_eq_zero_of_sum_coset (H := H) le_sup_left
    fun g => sum_indClassFun_mul_eq_zero hc.H_le_K hirr hdet g

section Norm

open Pointwise ScalarComplementPermutationNorm

private theorem conj_smul_eq_iff_mem_normalizer {X : Subgroup L} {g : L} :
    g ∈ Subgroup.normalizer (X : Set L) ↔ MulAut.conj g • X = X := by
  simp only [Subgroup.mem_normalizer_iff, SetLike.ext_iff, mem_conj_smul_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · have h1 := h (g⁻¹ * x * g)
    simp only [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group] at h1
    exact h1
  · have h1 := h (g * x * g⁻¹)
    simp only [show g⁻¹ * (g * x * g⁻¹) * g = x from by group] at h1
    exact h1

private theorem conj_smul_normal_eq {H : Subgroup L} [H.Normal] (g : L) :
    MulAut.conj g • H = H := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => mem_conj_smul_iff.2 ?_)
  · simpa [mul_assoc] using ‹H.Normal›.conj_mem _ (mem_conj_smul_iff.1 hz) g
  · simpa [mul_assoc] using ‹H.Normal›.conj_mem z hz g⁻¹

private theorem conj_smul_self_eq {X : Subgroup L} {x : L} (hx : x ∈ X) :
    MulAut.conj x • X = X := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => mem_conj_smul_iff.2 ?_)
  · have h2 : x * (x⁻¹ * z * x) * x⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem hx (mem_conj_smul_iff.1 hz)) (X.inv_mem hx)
    simpa [mul_assoc] using h2
  · exact X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx

private theorem conj_smul_eq_of_commutator_le {U Y : Subgroup L} (hYU : Y ≤ U) (hc : ⁅U, U⁆ ≤ Y)
    {u : L} (hu : u ∈ U) : MulAut.conj u • Y = Y := by
  have key : ∀ v ∈ U, ∀ y ∈ Y, v⁻¹ * y * v ∈ Y := by
    intro v hv y hy
    have hcomm : y⁻¹ * v⁻¹ * y * v ∈ ⁅U, U⁆ := by
      simpa [commutatorElement_def, mul_assoc] using
        Subgroup.commutator_mem_commutator (hYU (Y.inv_mem hy)) (U.inv_mem hv)
    have h2 := Y.mul_mem hy (hc hcomm)
    rwa [show y * (y⁻¹ * v⁻¹ * y * v) = v⁻¹ * y * v from by group] at h2
  refine le_antisymm (fun z hz => ?_) (fun z hz => mem_conj_smul_iff.2 (key u hu z hz))
  have h1 : u⁻¹ * z * u ∈ Y := mem_conj_smul_iff.1 hz
  have h2 := key u⁻¹ (U.inv_mem hu) _ h1
  rwa [show u⁻¹⁻¹ * (u⁻¹ * z * u) * u⁻¹ = z from by group] at h2

private theorem card_conj_smul_subgroup (σ : MulAut L) (S : Subgroup L) :
    Nat.card (σ • S : Subgroup L) = Nat.card S := by
  refine Nat.card_congr (Equiv.subtypeEquiv σ.toEquiv fun x => ?_).symm
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]

private theorem sup_inf_sup_of_disjoint {H U U0 Y : Subgroup L} [H.Normal] (hd : Disjoint H U)
    (hU0 : U0 ≤ U) (hY : Y ≤ U) : (H ⊔ U0) ⊓ (H ⊔ Y) = H ⊔ (U0 ⊓ Y) := by
  refine le_antisymm ?_ (le_inf (sup_le le_sup_left (le_sup_right.trans' inf_le_left))
    (sup_le le_sup_left (le_sup_right.trans' inf_le_right)))
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨h1, hh1, v, hv, hzv⟩ := exists_mul_of_mem_sup_normal hz1
  obtain ⟨h2, hh2, w, hw, hzw⟩ := exists_mul_of_mem_sup_normal hz2
  have hprod : h1 * v = h2 * w := by rw [hzv, hzw]
  have heq : h2⁻¹ * h1 = w * v⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hprod, inv_mul_cancel_left]
  have hmem : w * v⁻¹ ∈ H ⊓ U := Subgroup.mem_inf.2
    ⟨heq ▸ H.mul_mem (H.inv_mem hh2) hh1, U.mul_mem (hY hw) (U.inv_mem (hU0 hv))⟩
  rw [disjoint_iff.1 hd, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  subst hmem
  exact hzv ▸ Subgroup.mul_mem_sup hh1 (Subgroup.mem_inf.2 ⟨hv, hw⟩)

private theorem conj_smul_autFixer {V : Type*} [Group V] (ρ : L →* MulAut V) (S : Set V) (g : L) :
    MulAut.conj g • autFixer ρ S = autFixer ρ (ρ g '' S) := by
  have key : ∀ (x : L) (v : V), ρ (g⁻¹ * x * g) v = v ↔ ρ x (ρ g v) = ρ g v := fun x v => by
    rw [map_mul, map_mul, map_inv]
    change (ρ g).symm ((ρ x) ((ρ g) v)) = v ↔ _
    rw [MulEquiv.symm_apply_eq]
  ext x
  rw [mem_conj_smul_iff, mem_autFixer, mem_autFixer]
  exact ⟨fun h w hw => by obtain ⟨v, hv, rfl⟩ := hw; exact (key x v).1 (h v hv),
    fun h v hv => (key x v).2 (h (ρ g v) ⟨v, hv, rfl⟩)⟩

private theorem lineFixer_eq_inf_autFixer (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    (Ei : Subgroup (↥H ⧸ H0.subgroupOf H)) :
    lineFixer H H0 U Ei
      = U ⊓ autFixer (conjQuotientAut H H0) (Ei : Set (↥H ⧸ H0.subgroupOf H)) := by
  ext x; rw [mem_lineFixer, Subgroup.mem_inf, mem_autFixer]; rfl

private theorem conj_smul_lineFixer {H H0 U : Subgroup L} [H.Normal] [H0.Normal]
    {Ei Ej : Subgroup (↥H ⧸ H0.subgroupOf H)} {g : L}
    (hU : MulAut.conj g • U = U) (hE : Subgroup.map (conjQuotientAut H H0 g) Ei = Ej) :
    MulAut.conj g • lineFixer H H0 U Ei = lineFixer H H0 U Ej := by
  rw [lineFixer_eq_inf_autFixer, lineFixer_eq_inf_autFixer, Subgroup.smul_inf, hU,
    conj_smul_autFixer]
  congr 2
  rw [← hE, Subgroup.coe_map]
  rfl

private theorem map_coe_mulAut_mul {Q : Type*} [Group Q] (σ τ : MulAut Q) (S : Subgroup Q) :
    Subgroup.map ((σ * τ : MulAut Q) : Q →* Q) S
      = Subgroup.map ((σ : Q →* Q)) (Subgroup.map ((τ : Q →* Q)) S) := by
  rw [Subgroup.map_map]
  exact congrFun (congrArg Subgroup.map (MonoidHom.ext fun x => rfl)) S

private theorem map_coe_mulAut_one {Q : Type*} [Group Q] (S : Subgroup Q) :
    Subgroup.map ((1 : MulAut Q) : Q →* Q) S = S := by
  ext x
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

private theorem map_conjQuotientAut_pow_Eline {q : ℕ} {H H0 : Subgroup L} [H.Normal] [H0.Normal]
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} (b : L)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) (n : ℕ)
    (i : ZMod q) :
    Subgroup.map (conjQuotientAut H H0 (b ^ n)) (Eline i) = Eline (i + n) := by
  induction n with
  | zero => rw [pow_zero, map_one, map_coe_mulAut_one]; simp
  | succ k ih =>
    rw [pow_succ', map_mul, map_coe_mulAut_mul, ih, hb]
    push_cast
    ring_nf

private theorem extendByZero_eq_it [Finite L] (X : Subgroup L) (f : X → ℂ) (y : L) :
    InductionTransitivity.extendByZero X f y = extendByZero X f y := by
  by_cases h : y ∈ X
  · lift y to X using h with z
    rw [InductionTransitivity.extendByZero_apply_coe, extendByZero_apply_coe]
  · rw [InductionTransitivity.extendByZero_of_notMem _ _ h, extendByZero_of_notMem _ _ h]

private theorem indClassFun_eq_it [Fintype L] (X : Subgroup L) (f : X → ℂ) :
    InductionTransitivity.indClassFun X f = indClassFun X f := by
  funext g
  rw [InductionTransitivity.indClassFun_apply, indClassFun_eq_sum_extendByZero]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => extendByZero_eq_it X f _)

private theorem cfInner_indClassFun_one_self_eq_sum [Fintype L] (I : Subgroup L) :
    cfInner (indClassFun I (1 : I → ℂ)) (indClassFun I (1 : I → ℂ))
      = (Nat.card L : ℂ)⁻¹ * ((Nat.card I : ℂ)⁻¹ ^ 2 * ((Nat.card L : ℂ)
        * ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ))) := by
  rw [cfInner_def, ← indClassFun_eq_it, sum_mul_conj_indClassFun_one]

private theorem sum_card_inf_conj_of_normalizing [Fintype L] {K B I N : Subgroup L}
    (hKB : K.IsComplement' B) (hKI : ∀ k ∈ K, MulAut.conj k • I = I)
    (hI : ∀ b ∈ B, b ≠ 1 → I ⊓ MulAut.conj b⁻¹ • I = N) :
    ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)
      = (Nat.card K : ℂ) * ((Nat.card I : ℂ) + ((Nat.card B : ℂ) - 1) * (Nat.card N : ℂ)) := by
  classical
  have hbij := Fintype.sum_bijective (fun p : K × B => (p.1 : L) * (p.2 : L)) hKB
    (fun p => (Nat.card (I ⊓ MulAut.conj ((p.1 : L) * (p.2 : L)) • I : Subgroup L) : ℂ))
    (fun g => (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)) fun _ => rfl
  rw [← hbij, Fintype.sum_prod_type]
  have hterm : ∀ (k : K) (b : B),
      (Nat.card (I ⊓ MulAut.conj ((k : L) * (b : L)) • I : Subgroup L) : ℂ)
        = (Nat.card (I ⊓ MulAut.conj (b : L) • I : Subgroup L) : ℂ) := by
    intro k b
    rw [map_mul, mul_smul]
    have heq : I ⊓ MulAut.conj (k : L) • (MulAut.conj (b : L) • I)
        = MulAut.conj (k : L) • (I ⊓ MulAut.conj (b : L) • I) := by
      rw [Subgroup.smul_inf, hKI (k : L) k.2]
    rw [heq, card_conj_smul_subgroup]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => hterm k b,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  congr 1
  have hinv : ∑ b : B, (Nat.card (I ⊓ MulAut.conj (b : L) • I : Subgroup L) : ℂ)
      = ∑ b : B, (Nat.card (I ⊓ MulAut.conj ((b : L)⁻¹) • I : Subgroup L) : ℂ) :=
    Fintype.sum_equiv (Equiv.inv B) _ _ fun b => by simp
  rw [hinv, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : B))]
  have h1 : ∀ b ∈ Finset.univ.erase (1 : B),
      (Nat.card (I ⊓ MulAut.conj ((b : L)⁻¹) • I : Subgroup L) : ℂ) = (Nat.card N : ℂ) := by
    intro b hb
    have hb' : (b : L) ≠ 1 := fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h)
    rw [hI (b : L) b.2 hb']
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card]
  simp only [OneMemClass.coe_one, inv_one, map_one, one_smul, inf_idem]
  rw [Nat.cast_sub Nat.card_pos]
  push_cast
  ring

private theorem conj_smul_sup_lineFixer_eq {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {A : Set L} (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {k : L} (hk : k ∈ K) :
    MulAut.conj k • (H ⊔ lineFixer H H0 U (Eline 0)) = H ⊔ lineFixer H H0 U (Eline 0) := by
  set U0 := lineFixer H H0 U (Eline 0) with hU0def
  have hU0U : U0 ≤ U := lineFixer_le H H0 U (Eline 0)
  have hcomm : ⁅U, U⁆ ≤ U0 := hc.commutator_eq ▸ lineFixerInf_le_lineFixer H H0 U Eline 0
  have hKn : K ≤ Subgroup.normalizer ((H ⊔ U0 : Subgroup L) : Set L) := by
    rw [← hc.sup_H_U]
    refine sup_le (fun h hh => ?_) (fun u hu => ?_)
    · exact conj_smul_eq_iff_mem_normalizer.2 (conj_smul_self_eq ((le_sup_left : H ≤ H ⊔ U0) hh))
    · refine conj_smul_eq_iff_mem_normalizer.2 ?_
      rw [Subgroup.smul_sup, conj_smul_normal_eq, conj_smul_eq_of_commutator_le hU0U hcomm hu]
  exact conj_smul_eq_iff_mem_normalizer.1 (hKn hk)

private theorem inf_conj_smul_sup_lineFixer [Finite L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {A : Set L} (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {b : L} (hb : b ∈ B)
    (hb1 : b ≠ 1) :
    (H ⊔ lineFixer H H0 U (Eline 0)) ⊓ MulAut.conj b • (H ⊔ lineFixer H H0 U (Eline 0))
      = H ⊔ lineFixerInf H H0 U Eline := by
  obtain ⟨b0, hb0B, hB, hshift⟩ := hc.exists_gen_B
  have hord : orderOf b0 = q := by rw [← Nat.card_zpowers, ← hB, hc.card_B]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b0 ^ n = b :=
    mem_powers_iff_mem_zpowers.2 (hB ▸ hb : b ∈ Subgroup.zpowers b0)
  have hndvd : ¬ (q ∣ n) := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, hn]
    exact hb1
  have hn0 : (0 : ZMod q) ≠ ((n : ℕ) : ZMod q) := fun hcon =>
    hndvd ((ZMod.natCast_eq_zero_iff n q).1 hcon.symm)
  have hUb : MulAut.conj b • U = U :=
    conj_smul_eq_iff_mem_normalizer.1 (hc.B_le_normalizer_U hb)
  have hE : Subgroup.map (conjQuotientAut H H0 b) (Eline 0) = Eline ((n : ℕ) : ZMod q) := by
    rw [← hn]
    simpa using map_conjQuotientAut_pow_Eline b0 hshift n 0
  rw [Subgroup.smul_sup, conj_smul_normal_eq, conj_smul_lineFixer hUb hE,
    sup_inf_sup_of_disjoint hc.disjoint_H_U (lineFixer_le H H0 U (Eline 0))
      (lineFixer_le H H0 U (Eline _)),
    hc.inf_lineFixer 0 _ hn0]

theorem cfInner_scalarPermChar_self [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L}
    [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
    {A : Set L} (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) :
    cfInner (scalarPermChar H H0 U Eline) (scalarPermChar H H0 U Eline)
      = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)
        + ((q : ℂ) - 1) * ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) ^ 2
          / ((lineFixerInf H H0 U Eline).relIndex U : ℂ) := by
  set U0 := lineFixer H H0 U (Eline 0) with hU0def
  set C := lineFixerInf H H0 U Eline with hCdef
  have hU0U : U0 ≤ U := lineFixer_le H H0 U (Eline 0)
  have hCU : C ≤ U := lineFixerInf_le H H0 U Eline 0
  have hIcard : Nat.card ↥H * Nat.card ↥U0 = Nat.card ↥(H ⊔ U0) :=
    card_sup_eq_mul_of_disjoint H U0 (hc.disjoint_H_U.mono_right hU0U)
  have hNcard : Nat.card ↥H * Nat.card ↥C = Nat.card ↥(H ⊔ C) :=
    card_sup_eq_mul_of_disjoint H C (hc.disjoint_H_U.mono_right hCU)
  have hKcard : Nat.card ↥H * Nat.card ↥U = Nat.card ↥K := by
    rw [card_sup_eq_mul_of_disjoint H U hc.disjoint_H_U, hc.sup_H_U]
  have hLcard : Nat.card ↥K * Nat.card ↥B = Nat.card L := hc.isComplement_K_B.card_mul_card
  have hrelU0 : Nat.card ↥U0 * U0.relIndex U = Nat.card ↥U :=
    ScalarComplementPermutationNorm.card_mul_relIndex hU0U
  have hrelC : Nat.card ↥C * C.relIndex U = Nat.card ↥U :=
    ScalarComplementPermutationNorm.card_mul_relIndex hCU
  have hsum := sum_card_inf_conj_of_normalizing (I := H ⊔ U0) (N := H ⊔ C) hc.isComplement_K_B
    (fun k hk => conj_smul_sup_lineFixer_eq hc hk)
    (fun b hb hb1 => inf_conj_smul_sup_lineFixer hc (B.inv_mem hb) (inv_ne_one.2 hb1))
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.q_prime.pos.ne'
  have hh : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hi0 : (Nat.card ↥U0 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have ha : (U0.relIndex U : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun hcon => ?_
    rw [hcon, mul_zero] at hrelU0
    exact Nat.card_pos.ne' hrelU0.symm
  have hu : (C.relIndex U : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun hcon => ?_
    rw [hcon, mul_zero] at hrelC
    exact Nat.card_pos.ne' hrelC.symm
  have eI : (Nat.card ↥(H ⊔ U0) : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card ↥U0 : ℂ) := by
    rw [← hIcard]; push_cast; ring
  have eN : (Nat.card ↥(H ⊔ C) : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card ↥C : ℂ) := by
    rw [← hNcard]; push_cast; ring
  have eV : (Nat.card ↥U : ℂ) = (Nat.card ↥U0 : ℂ) * (U0.relIndex U : ℂ) := by
    rw [← hrelU0]; push_cast; ring
  have eK : (Nat.card ↥K : ℂ)
      = (Nat.card ↥H : ℂ) * ((Nat.card ↥U0 : ℂ) * (U0.relIndex U : ℂ)) := by
    rw [← eV, ← hKcard]; push_cast; ring
  have eL : (Nat.card L : ℂ)
      = (Nat.card ↥H : ℂ) * ((Nat.card ↥U0 : ℂ) * (U0.relIndex U : ℂ)) * (q : ℂ) := by
    rw [← eK, ← hLcard, hc.card_B]; push_cast; ring
  have eC : (Nat.card ↥C : ℂ)
      = (Nat.card ↥U0 : ℂ) * (U0.relIndex U : ℂ) / (C.relIndex U : ℂ) := by
    rw [eq_div_iff hu, ← eV, ← hrelC]; push_cast; ring
  rw [scalarPermChar_eq, cfInner_indClassFun_one_self_eq_sum, hsum, hc.card_B, eI, eN, eK, eL, eC]
  field_simp

end Norm

theorem scalarTestChar_norm_and_inner [Fintype L] {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal]
    [H0.Normal] [K.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
    (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) {psi : L → ℂ}
    (hpsiS : psi ∈ scalarEqualityFamily K H H0 U Eline) (hpsi : psi ∈ Irr L) :
    cfInner (scalarTestChar H H0 U Eline psi) (scalarTestChar H H0 U Eline psi)
        = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) + 1
          + ((q : ℂ) - 1) * ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) ^ 2
            / ((lineFixerInf H H0 U Eline).relIndex U : ℂ) ∧
      cfInner (scalarTestChar H H0 U Eline psi) psi = -1 ∧
      (∀ chi ∈ scalarEqualityFamily K H H0 U Eline, chi ≠ psi →
        cfInner (scalarTestChar H H0 U Eline psi) chi = 0) := by
  have hnorm := cfInner_scalarPermChar_self hc
  have hgp : cfInner (scalarPermChar H H0 U Eline) psi = 0 :=
    cfInner_scalarPermChar_eq_zero hc hpsiS
  have hpg : cfInner psi (scalarPermChar H H0 U Eline) = 0 := by
    rw [← conj_cfInner, hgp, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [scalarTestChar_eq, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hnorm, hgp, hpg,
      cfInner_self_of_mem_Irr hpsi]
    ring
  · rw [scalarTestChar_eq, cfInner_sub_left, hgp, cfInner_self_of_mem_Irr hpsi]
    ring
  · intro chi hchi hne
    rw [scalarTestChar_eq, cfInner_sub_left, cfInner_scalarPermChar_eq_zero hc hchi,
      cfInner_eq_zero_of_mem_scalarEqualityFamily hpsiS hchi (Ne.symm hne)]
    ring

end CFSG.FeitThompson
