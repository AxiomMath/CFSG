module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
public import CFSG.ClassicalInvolution.Asc77.WP3LayerLie
import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStmt
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace FrameVertex

section Uniqueness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem oddQuotMk_mem_exactImage {b : G} (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    {M : Subgroup G} (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) :
    oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c (exactCore c M) :=
  oddQuotMk_mem_modOdd (mem_exactCore hMb hc2 (mem_tqMembers_iff.mp hM).2) hbC

theorem movedComponent_eq (hΩ : ConjInvariant Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (D : LieDecomposition (exactImages Ω c) (exactJoin Ω c)) :
    ∃ j₀ : D.ι, ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = D.Q j₀ := by
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have hbmem := oddQuotMk_mem_exactImage hbC hc2 hM hMb
  have hMfam : exactCore c M ∈ exactFamily Ω c := exactCore_mem_exactFamily hM
  obtain ⟨j₀, hj₀⟩ := D.exists_le (modOdd c (exactCore c M))
    ⟨exactCore c M, ⟨hMfam, exactCore_le_centralizer c M⟩, rfl⟩
  have hbJ : oddQuotMk c ⟨b, hbC⟩ ∈ exactJoin Ω c := modOdd_le_exactJoin hMfam hbmem
  refine ⟨j₀, fun L hL hmov => ?_⟩
  have hbBar : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c B := oddQuotMk_mem_modOdd hbB hbC
  have hnot : oddQuotMk c ⟨b, hbC⟩ ∉ modOdd c (Subgroup.zpowers c) :=
    Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC
  obtain ⟨y, hyL, hy⟩ := hmov _ hbBar hnot
  have := exactJoin_normal (c := c) hΩ
  rcases D.eq_or_commutes_of_isComponentOf ((CFSG.isComponent_iff_open L).mp hL) with
    ⟨i, rfl⟩ | hcomm
  · by_cases hi : i = j₀
    · rw [hi]
    · exact absurd (D.commute i j₀ hi y hyL _ (hj₀ hbmem)).symm hy
  · exact absurd (hcomm y hyL _ hbJ).symm hy

theorem uniq_of_witness (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) :
    ∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      MovedByAll B c L₁ → MovedByAll B c L₂ → L₁ = L₂ := by
  obtain ⟨D⟩ := lieDecomposition_exactFamily hp2 CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    fundamentalWholeA1 hq hΩ hcls hc2 hBelow hnc
  obtain ⟨j₀, hj₀⟩ := movedComponent_eq hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D
  intro L₁ L₂ h1 h2 m1 m2
  rw [hj₀ L₁ h1 m1, hj₀ L₂ h2 m2]

theorem modOdd_le_normalizer (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L)
    (hmov : MovedByAll B c L) : modOdd c B ≤ Subgroup.normalizer (L : Set (OddQuot c)) := by
  intro x hx
  rw [mem_normalizer_iff_conjSub_eq]
  have hcomp : CFSG.IsComponent (conjSub x L) :=
    (isComponent_map_equiv_iff (MulAut.conj x) L).mpr hL
  have hmov' : MovedByAll B c (conjSub x L) := by
    intro y hy hyZ
    obtain ⟨w, hwL, hw⟩ := hmov y hy hyZ
    refine ⟨x * w * x⁻¹, conj_mem_conjSub hwL, fun h => hw ?_⟩
    have hxy : x * y = y * x := Lemma52Proof.modOdd_comm hB x hx y hy
    have hxy' : x⁻¹ * y = y * x⁻¹ := by
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [hxy]
        _ = y * x⁻¹ := by group
    have h2 : x * (y * w) * x⁻¹ = x * (w * y) * x⁻¹ := by
      calc x * (y * w) * x⁻¹ = (x * y) * w * x⁻¹ := by group
        _ = (y * x) * w * x⁻¹ := by rw [hxy]
        _ = y * (x * w * x⁻¹) := by group
        _ = (x * w * x⁻¹) * y := h
        _ = x * w * (x⁻¹ * y) := by group
        _ = x * w * (y * x⁻¹) := by rw [hxy']
        _ = x * (w * y) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  exact uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb _ _ hcomp hL
    hmov' hmov

end Uniqueness

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hyp51At_of_system (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G}
    (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hD : ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, ∀ j : Fin D.card,
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        p ^ D.exp j ≠ 3 ∧ StrongLocalTwoBalanceToralPowOn 2 (D.tag j) (fun _ _ _ => True) ∧
          ToralOnComponent c B (secComponentHom (normalizesLayer_exactFamily hΩ) D j)) :
    Hyp51At B c := by
  refine ⟨uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb, ?_⟩
  intro L hL hmov
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨Dsys, hDsys⟩ := hD
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hj₀⟩ := movedComponent_eq hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  have hBN := modOdd_le_normalizer hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb hL
    hmov
  subst hLeq
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j with hψ
  obtain ⟨hF3, hSB', P, hPc, hPact⟩ := hDsys j hmov
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ) Dsys j
  have hperf : Group.IsPerfect (compModel Dsys j).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _
      (Dsys.isFundTag j) (Dsys.admissible j)).1.1
  have h5 : 5 ≤ p ^ Dsys.exp j :=
    five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) hF3
  have hmemZ := fun x => Lemma52Proof.mem_modOdd_zpowers_iff hB hcB hc1 x
  have hself : Lemma52Proof.oddQuotSelf c ∈ modOdd c (Subgroup.zpowers c) :=
    (hmemZ _).mpr (Or.inr rfl)
  have hZcard : Nat.card (modOdd c (Subgroup.zpowers c)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨Lemma52Proof.oddQuotSelf c, hself⟩, fun h =>
      Lemma52Proof.oddQuotSelf_ne_one hB hcB hc1 (congrArg Subtype.val h).symm, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hmemZ z).mp z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hZB : modOdd c (Subgroup.zpowers c) ≤ modOdd c B := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    exact ⟨k, Subgroup.zpowers_le.mpr hcB hk, rfl⟩
  have hZ : ∀ z ∈ modOdd c (Subgroup.zpowers c), ∀ y ∈ ψ.range, z * y = y * z := by
    intro z hz y _
    rcases (hmemZ z).mp hz with rfl | rfl
    · simp
    · exact (Lemma52Proof.oddQuotSelf_central c y).symm
  have hZ' : ∀ b' ∈ modOdd c B, (∀ y ∈ ψ.range, b' * y = y * b') →
      b' ∈ modOdd c (Subgroup.zpowers c) := by
    intro b' hb' hcomm
    by_contra hnot
    obtain ⟨y, hy, hne'⟩ := hmov b' hb' hnot
    exact hne' (hcomm y hy)
  refine alphaOf_inducedImage_eq_bot_of_toral Fact.out (Dsys.isFundTag j) (Dsys.admissible j) hp2
    h5 hSB' ψ hker (Lemma52Proof.modOdd_sq hB) (Lemma52Proof.card_modOdd_eq_eight hB hB8 hcB) hBN
    hZcard hZB hZ hZ' ⟨P, hPc, fun b' hb' => ?_⟩
  obtain ⟨k, hkB, rfl⟩ := mem_modOdd_iff.mp hb'
  exact hPact k hkB k.2

theorem hyp51At_of_witness (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f (exactFamily Ω c) c) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hSB : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        StrongLocalTwoBalanceToralPowOn 2 (D.tag j) fun _ _ _ => True)
    (htoral : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        ToralOnComponent c B (secComponentHom (normalizesLayer_exactFamily hΩ) D j)) :
    Hyp51At B c := by
  obtain ⟨Dsys⟩ := lieSystemAt_exactFamily hΩ hcls hc2 hBelow hnc ⟨M, hM⟩
  exact hyp51At_of_system hp2 hq hΩ hcls hBelow hc2 hnc hB hB8 hcB hc1 hbB hb1 hbc hM hMb
    ⟨Dsys, fun j hmov => ⟨hF3 Dsys j, hSB Dsys j hmov, htoral Dsys j hmov⟩⟩

theorem hyp51At_of_system_lin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G}
    (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hD : ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, ∀ j : Fin D.card,
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralOnComponent c B (secComponentHom (normalizesLayer_exactFamily hΩ) D j)) :
    Hyp51At B c := by
  obtain ⟨D, hDj⟩ := hD
  refine hyp51At_of_system hp2 hq hΩ hcls hBelow hc2 hnc hB hB8 hcB hc1 hbB hb1 hbc hM hMb
    ⟨D, fun j hmov => ?_⟩
  obtain ⟨htag, htor⟩ := hDj j hmov
  have hexp : D.exp j = f := by
    rcases D.exp_eq j with h | ⟨h, -⟩
    · exact h
    · rcases htag with h' | h' <;> rw [h'] at h <;> cases h
  refine ⟨by rw [hexp]; omega, ?_, htor⟩
  rcases htag with h | h
  · rw [h]
    exact Linear.strongLocalTwoBalanceToralPowOn_PSL_two
  · rw [h]
    exact Unitary.strongLocalTwoBalanceToralPowOn_PSU_two

end Vertex

end FrameVertex

end CFSG.ClassicalInvolution.Asc77
