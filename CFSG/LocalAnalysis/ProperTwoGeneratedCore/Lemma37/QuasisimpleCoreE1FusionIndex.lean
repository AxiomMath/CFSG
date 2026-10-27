module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionNormalizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1_stab_reps : ∀ w : Fin 64, e1E w → w ≠ 0 → w ≠ 40 → w ≠ 32 → w ≠ 8 →
    ∃ s : Fin 64, c3Conj s 32 = 32 ∧ c3Conj s 2 = w := by decide +kernel

@[expose] def e1Pair (vw : Fin 64 × Fin 64) : Prop :=
  e1EStar vw.1 ∧ e1EStar vw.2 ∧ vw.2 ≠ vw.1 ∧ vw.2 ≠ c3Mul vw.1 40

instance : DecidablePred e1Pair := fun vw => by unfold e1Pair; infer_instance

theorem card_e1Pair : (Finset.univ.filter e1Pair).card = 24 := by decide +kernel

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem mem_centralizer_of_conj_eq {n : J ⧸ Subgroup.center J}
    (hn : n ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    (hnu : n * (u : J ⧸ Subgroup.center J) * n⁻¹ = u)
    (hny : n * (y : J ⧸ Subgroup.center J) * n⁻¹ = y) :
    n ∈ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  have h := d.conj_caseC3Word_of_e1E (wa := 32) (we := 2)
    (by rw [hnu, CaseC3BCD.caseC3Word_thirtytwo]) (by rw [hny, CaseC3BCD.caseC3Word_two])
    (conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hn)) hv
  rw [e1Act_facts.2.2 v hv] at h
  nth_rewrite 1 [← h]
  group

theorem exists_normalizer_conj_pair (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s)
    {A B' : J ⧸ Subgroup.center J} (hA : A ∈ e1EBar (Subgroup.center J) u m y x) (hA1 : A ≠ 1)
    (hAz : A ≠ caseC3Word (Subgroup.center J) u m y x 40)
    (hB : B' ∈ e1EBar (Subgroup.center J) u m y x) (hB1 : B' ≠ 1)
    (hBz : B' ≠ caseC3Word (Subgroup.center J) u m y x 40) (hBA : B' ≠ A)
    (hBAz : B' ≠ A * caseC3Word (Subgroup.center J) u m y x 40) :
    ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      n * (u : J ⧸ Subgroup.center J) * n⁻¹ = A ∧ n * (y : J ⧸ Subgroup.center J) * n⁻¹ = B' := by
  have hb := d.caseC3BCD
  obtain ⟨n₁, hn₁, hn₁u⟩ := d.exists_normalizer_conj_of_mem_e1EBar htype hA hA1 hAz
  have hn₁z := conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hn₁)
  have hu : (u : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 32 :=
    CaseC3BCD.caseC3Word_thirtytwo.symm
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  have hB'E : n₁⁻¹ * B' * n₁ ∈ e1EBar (Subgroup.center J) u m y x := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn₁) B').mp hB
    rwa [inv_inv] at h
  obtain ⟨w, hw, hwB⟩ := hb.mem_e1EBar_iff.mp hB'E
  have hback : ∀ {a : J ⧸ Subgroup.center J}, caseC3Word (Subgroup.center J) u m y x w = a →
      B' = n₁ * a * n₁⁻¹ := fun {a} h => by rw [← h, hwB]; group
  obtain ⟨s, hs32, hs2⟩ := e1_stab_reps w hw
    (fun h => hB1 (by rw [hback (a := 1) (by rw [h, CaseC3BCD.caseC3Word_zero])]; group))
    (fun h => hBz (by rw [hback (by rw [h])]; exact hn₁z))
    (fun h => hBA (by rw [hback (a := u) (by rw [h, hu]), hn₁u]))
    (fun h => hBAz (by
      rw [hback (a := (u : J ⧸ Subgroup.center J) * caseC3Word (Subgroup.center J) u m y x 40)
        (by rw [h, hu, hb.caseC3Word_mul, e1Act_facts.1]), ← hn₁u]
      nth_rewrite 2 [← hn₁z]
      group))
  refine ⟨n₁ * caseC3Word (Subgroup.center J) u m y x s,
    Subgroup.mul_mem _ hn₁ (d.map_le_normalizer_e1EBar (hb.caseC3Word_mem s)), ?_, ?_⟩
  · rw [show n₁ * caseC3Word (Subgroup.center J) u m y x s * (u : J ⧸ Subgroup.center J) *
      (n₁ * caseC3Word (Subgroup.center J) u m y x s)⁻¹ = n₁ * (caseC3Word (Subgroup.center J)
        u m y x s * (u : J ⧸ Subgroup.center J) * (caseC3Word (Subgroup.center J) u m y x s)⁻¹) *
          n₁⁻¹ by group, hu, hb.caseC3Word_conj, hs32, ← hu, hn₁u]
  · rw [show n₁ * caseC3Word (Subgroup.center J) u m y x s * (y : J ⧸ Subgroup.center J) *
      (n₁ * caseC3Word (Subgroup.center J) u m y x s)⁻¹ = n₁ * (caseC3Word (Subgroup.center J)
        u m y x s * (y : J ⧸ Subgroup.center J) * (caseC3Word (Subgroup.center J) u m y x s)⁻¹) *
          n₁⁻¹ by group, hy, hb.caseC3Word_conj, hs2, hback rfl]

theorem relIndex_centralizer_normalizer_e1EBar (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s) :
    (Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))).relIndex
        (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) =
          24 := by
  have hb := d.caseC3BCD
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set N := Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) with hN
  set C := Subgroup.centralizer (E : Set (J ⧸ Subgroup.center J)) with hC
  set zb := caseC3Word (Subgroup.center J) u m y x 40 with hzb
  obtain ⟨huE, hyE, hzE⟩ := d.mem_e1EBar_gens
  have hu1 : (u : J ⧸ Subgroup.center J) ≠ 1 := hb.mk_ne_one.1
  have hy1 : (y : J ⧸ Subgroup.center J) ≠ 1 := by
    rw [← CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (x := x), Ne,
      hb.caseC3Word_eq_one_iff]
    decide
  have huz : (u : J ⧸ Subgroup.center J) ≠ zb := by
    rw [hzb, ← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y)
      (x := x), Ne, hb.caseC3Word_inj]
    decide
  have hyz : (y : J ⧸ Subgroup.center J) ≠ zb := by
    rw [hzb, ← CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (x := x), Ne,
      hb.caseC3Word_inj]
    decide
  have hyu : (y : J ⧸ Subgroup.center J) ≠ u := by
    rw [← CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (x := x),
      ← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x), Ne,
      hb.caseC3Word_inj]
    decide
  have hyuz : (y : J ⧸ Subgroup.center J) ≠ u * zb := by
    rw [hzb, ← CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (x := x),
      ← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
      hb.caseC3Word_mul, Ne, hb.caseC3Word_inj]
    decide
  let X : (J ⧸ Subgroup.center J) × (J ⧸ Subgroup.center J) → Prop := fun p =>
    (p.1 ∈ E ∧ p.1 ≠ 1 ∧ p.1 ≠ zb) ∧ (p.2 ∈ E ∧ p.2 ≠ 1 ∧ p.2 ≠ zb) ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1 * zb
  have hconj : ∀ {n : J ⧸ Subgroup.center J}, n ∈ N → ∀ {a : J ⧸ Subgroup.center J}, a ∈ E →
      a ≠ 1 → a ≠ zb → (n * a * n⁻¹ ∈ E ∧ n * a * n⁻¹ ≠ 1 ∧ n * a * n⁻¹ ≠ zb) :=
    fun {n} hn {a} ha ha1 haz => by
      have hnz : n * zb * n⁻¹ = zb :=
        conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hn)
      refine ⟨(Subgroup.mem_normalizer_iff.mp hn a).mp ha, fun h => ha1 ?_, fun h => haz ?_⟩
      · rw [show a = n⁻¹ * (n * a * n⁻¹) * n by group, h]
        group
      · rw [show a = n⁻¹ * (n * a * n⁻¹) * n by group, h]
        nth_rewrite 1 [← hnz]
        group
  have hφ : ∀ n : N, X ((n : J ⧸ Subgroup.center J) * u * (n : J ⧸ Subgroup.center J)⁻¹,
      (n : J ⧸ Subgroup.center J) * y * (n : J ⧸ Subgroup.center J)⁻¹) := fun n => by
    have hnz : (n : J ⧸ Subgroup.center J) * zb * (n : J ⧸ Subgroup.center J)⁻¹ = zb :=
      conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le n.2)
    refine ⟨hconj n.2 huE hu1 huz, hconj n.2 hyE hy1 hyz, fun h => hyu (mul_left_cancel
      (mul_right_cancel h)), fun h => hyuz (mul_left_cancel (mul_right_cancel (h.trans ?_)))⟩
    show (n : J ⧸ Subgroup.center J) * u * (n : J ⧸ Subgroup.center J)⁻¹ * zb =
      (n : J ⧸ Subgroup.center J) * (u * zb) * (n : J ⧸ Subgroup.center J)⁻¹
    nth_rewrite 1 [← hnz]
    group
  let φ : N → {p // X p} := fun n => ⟨_, hφ n⟩
  have hφeq : ∀ a b : N, φ a = φ b ↔ a⁻¹ * b ∈ C.subgroupOf N := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 := congrArg (fun p => p.1.1) h
      have h2 := congrArg (fun p => p.1.2) h
      simp only [φ] at h1 h2
      refine d.mem_centralizer_of_conj_eq (a⁻¹ * b).2 ?_ ?_
      · rw [Subgroup.coe_mul, Subgroup.coe_inv,
          show (a : J ⧸ Subgroup.center J)⁻¹ * b * u * ((a : J ⧸ Subgroup.center J)⁻¹ * b)⁻¹ =
            (a : J ⧸ Subgroup.center J)⁻¹ * (b * u * (b : J ⧸ Subgroup.center J)⁻¹) * a by group,
          ← h1]
        group
      · rw [Subgroup.coe_mul, Subgroup.coe_inv,
          show (a : J ⧸ Subgroup.center J)⁻¹ * b * y * ((a : J ⧸ Subgroup.center J)⁻¹ * b)⁻¹ =
            (a : J ⧸ Subgroup.center J)⁻¹ * (b * y * (b : J ⧸ Subgroup.center J)⁻¹) * a by group,
          ← h2]
        group
    · intro h
      have hc := Subgroup.mem_centralizer_iff.mp h
      apply Subtype.ext
      simp only [φ, Prod.mk.injEq]
      have key : ∀ {s}, s ∈ E → (b : J ⧸ Subgroup.center J) * s * (b : J ⧸ Subgroup.center J)⁻¹ =
          (a : J ⧸ Subgroup.center J) * s * (a : J ⧸ Subgroup.center J)⁻¹ := by
        intro s hs
        have h' := hc s hs
        rw [Subgroup.coe_mul, Subgroup.coe_inv] at h'
        calc (b : J ⧸ Subgroup.center J) * s * (b : J ⧸ Subgroup.center J)⁻¹ =
              a * (s * ((a : J ⧸ Subgroup.center J)⁻¹ * b)) * (b : J ⧸ Subgroup.center J)⁻¹ := by
                rw [h']; group
          _ = a * s * (a : J ⧸ Subgroup.center J)⁻¹ := by group
      exact ⟨(key huE).symm, (key hyE).symm⟩
  have e : (N ⧸ C.subgroupOf N) ≃ {p // X p} := by
    refine Equiv.ofBijective (Quotient.lift φ fun a b hab =>
      (hφeq a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨fun q₁ q₂ h => ?_, fun p => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
      exact QuotientGroup.eq.mpr ((hφeq a b).mp h)
    · obtain ⟨⟨A, B'⟩, ⟨hA, hA1, hAz⟩, ⟨hB, hB1, hBz⟩, hBA, hBAz⟩ := p
      obtain ⟨n, hn, hnu, hny⟩ := d.exists_normalizer_conj_pair htype hA hA1 hAz hB hB1 hBz hBA hBAz
      exact ⟨QuotientGroup.mk ⟨n, hn⟩, Subtype.ext (Prod.ext hnu hny)⟩
  have e2 : {vw : Fin 64 × Fin 64 // e1Pair vw} ≃ {p // X p} := by
    refine Equiv.ofBijective (fun vw => ⟨(caseC3Word (Subgroup.center J) u m y x vw.1.1,
      caseC3Word (Subgroup.center J) u m y x vw.1.2), ?_⟩) ⟨fun vw vw' h => ?_, fun p => ?_⟩
    · obtain ⟨⟨hv, hv0, hv40⟩, ⟨hw, hw0, hw40⟩, hwv, hwvz⟩ := vw.2
      simp only [X]
      refine ⟨⟨hb.caseC3Word_mem_e1EBar_iff.mpr hv, ?_, ?_⟩,
        ⟨hb.caseC3Word_mem_e1EBar_iff.mpr hw, ?_, ?_⟩, ?_, ?_⟩
      · rw [Ne, hb.caseC3Word_eq_one_iff]; exact hv0
      · rw [hzb, Ne, hb.caseC3Word_inj]; exact hv40
      · rw [Ne, hb.caseC3Word_eq_one_iff]; exact hw0
      · rw [hzb, Ne, hb.caseC3Word_inj]; exact hw40
      · rw [Ne, hb.caseC3Word_inj]; exact hwv
      · rw [hzb, hb.caseC3Word_mul, Ne, hb.caseC3Word_inj]; exact hwvz
    · have h1 := congrArg (fun p => p.1.1) h
      have h2 := congrArg (fun p => p.1.2) h
      simp only [hb.caseC3Word_inj] at h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · obtain ⟨⟨A, B'⟩, ⟨hA, hA1, hAz⟩, ⟨hB, hB1, hBz⟩, hBA, hBAz⟩ := p
      obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hA
      obtain ⟨w, hw, rfl⟩ := hb.mem_e1EBar_iff.mp hB
      refine ⟨⟨(v, w), ⟨hv, fun h => hA1 ?_, fun h => hAz ?_⟩, ⟨hw, fun h => hB1 ?_,
        fun h => hBz ?_⟩, fun h => hBA ?_, fun h => hBAz ?_⟩, rfl⟩ <;> dsimp only at h ⊢
      · rw [h, CaseC3BCD.caseC3Word_zero]
      · rw [h]
      · rw [h, CaseC3BCD.caseC3Word_zero]
      · rw [h]
      · rw [h]
      · rw [h, hzb, hb.caseC3Word_mul]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr e, ← Nat.card_congr e2,
    Nat.card_eq_fintype_card, Fintype.card_subtype, card_e1Pair]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
