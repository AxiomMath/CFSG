module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIEmb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.D4T CFSG.StandardType CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Odd

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_nine_mul [IsCyclic (K ≃+* K)] {A : Subgroup (MulAut (Om8 K))}
    (hA : IsElemAbelian 3 A) {α : MulAut (Om8 K)} (hαA : α ∈ A)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    Nat.card A ≤ 9 * Nat.card ↥(A ⊓ Inn (Om8 K)) := by
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) :=
    NbrGraphD4.card_le_three_mul hαA fun a ha =>
      NbrGraphD4.exists_mul_pow_mem_sup (hA.2 a ha) hα3 hα
  have h2 : Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) ≤
      3 * Nat.card ↥(A ⊓ Inn (Om8 K)) := by
    by_cases hc : ∃ c ∈ A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range), c ∉ Inn (Om8 K)
    · obtain ⟨c, hcAS, hcI⟩ := hc
      have h := NbrGraphD4.card_le_three_mul (S := Inn (Om8 K)) hcAS fun a ha =>
        NbrGraphD4.exists_mul_pow_mem_inner ha.2 hcAS.2 (hA.2 a ha.1) (hA.2 c hcAS.1) hcI
      refine h.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le ?_))
      intro a ha
      exact ⟨ha.1.1, ha.2⟩
    · push Not at hc
      calc Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range))
          ≤ Nat.card ↥(A ⊓ Inn (Om8 K)) :=
            Subgroup.card_le_of_le fun a ha => ⟨ha.1, hc a ha⟩
        _ ≤ 3 * Nat.card ↥(A ⊓ Inn (Om8 K)) := Nat.le_mul_of_pos_left _ (by norm_num)
  omega

end Odd

section Data

variable {H : Type} [Group H] [Finite H] {K B : Subgroup H}

theorem rest2_data (hK : catalogIs ↥K isD4any) (hn : ¬ catalogIs ↥K S9.isD4two)
    (hB : IsElemAbelian 3 B) (hBK : B ≤ Subgroup.normalizer (K : Set H))
    (hout : ∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (K : Set H), NotCentralOut (conjAut K b hb))
    (hU : D4Unhandled2 K B) :
    ∃ (c : H) (hcN : c ∈ Subgroup.normalizer (K : Set H)), c ∈ B ∧ conjAut K c hcN ∉ innerAut ↥K ∧
      Nat.card B ≤ 81 * Nat.card (Bo K B) ∧
      (∃ E : Subgroup H, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ ∀ y ∈ E, c * y = y * c) ∧
      (∃ E W : Subgroup H, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ (∀ y ∈ E, c * y = y * c) ∧
        IsPGroup 2 W ∧ W ≠ ⊥ ∧ E ≤ Subgroup.normalizer (W : Set H) ∧
        c ∈ Subgroup.normalizer (W : Set H) ∧ W ≤ K) ∧
      ((∃ E W : Subgroup H, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ (∀ y ∈ E, c * y = y * c) ∧
        IsPGroup 2 W ∧ W ≠ ⊥ ∧ E ≤ Subgroup.normalizer (W : Set H) ∧
        c ∈ Subgroup.normalizer (W : Set H) ∧ W ≤ K) ∨
       ∀ T : Subgroup H, IsPGroup 2 T → T ≠ ⊥ → B ≤ Subgroup.normalizer (T : Set H) →
         T ≤ Subgroup.normalizer (K : Set H) → ¬ T ≤ Subgroup.centralizer (K : Set H) →
           Nat.card B ≤ 27 * Nat.card (Bo K B)) := by
  classical
  obtain ⟨n, hn2, hKn⟩ := exists_isD4pow2 hK hn
  obtain ⟨K₀, _, _, _, hK₀, ⟨Φ⟩⟩ := exists_om8_of_isD4pow2 hn2 hKn
  haveI : IsCyclic (K₀ ≃+* K₀) := CFSG.RankThree.PartOne.KFOUT3.isCyclic_aut (by omega) hK₀
  have hcomm : ∀ σ τ : K₀ ≃+* K₀, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.commGroup (α := K₀ ≃+* K₀)).mul_comm σ τ
  set N : Subgroup H := Subgroup.normalizer (K : Set H) with hN
  set ρ : ↥N →* MulAut ↥K := conjHom K with hρ
  have hB'el : IsElemAbelian 3 (B.subgroupOf N) := hB.comap N.subtype_injective
  have hAel : IsElemAbelian 3 (Bbar K B) :=
    CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ρ hB'el
  obtain ⟨b, hb, hbN, hnc⟩ := hout
  have hαA : conjAut K b hbN ∈ Bbar K B :=
    Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hb : (⟨b, hbN⟩ : ↥N) ∈ B.subgroupOf N)
  set Ψ : MulAut ↥K ≃* MulAut (Om8 K₀) := MulAut.congr Φ with hΨ
  set A' : Subgroup (MulAut (Om8 K₀)) := (Bbar K B).map Ψ.toMonoidHom with hA'
  have hA'el : IsElemAbelian 3 A' :=
    CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map _ hAel
  have hα'A' : Ψ (conjAut K b hbN) ∈ A' := Subgroup.mem_map_of_mem Ψ.toMonoidHom hαA
  have hα' : Ψ (conjAut K b hbN) ∉ Inn (Om8 K₀) ⊔ (AutOm.fieldAutP (K := K₀) 4).range :=
    not_mem_sup_of_notCentral Φ hcomm hnc
  have hA'card : Nat.card A' = Nat.card ↥(Bbar K B) :=
    Subgroup.card_map_of_injective Ψ.injective
  have hidx : 3 * Nat.card ↥(A' ⊓ Inn (Om8 K₀)) < Nat.card A' := by
    rw [hA'card]
    have := inf_inner_card_eq Φ (Bbar K B)
    rw [← hA'] at this
    rw [this]
    exact hU
  obtain ⟨c', hc'A', hc'S, hc'I⟩ := CFSG.LocalAnalysis.GLTheoremA.D4YH.exists_pure_field hA'el hα'A' hα' hidx
  have hc'3 : c' ^ 3 = 1 := hA'el.2 c' hc'A'
  obtain ⟨cb, hcb, hcbeq⟩ := hc'A'
  obtain ⟨⟨c, hcN⟩, hcB', rfl⟩ := hcb
  have hcB : c ∈ B := Subgroup.mem_subgroupOf.1 hcB'
  have hcout : conjAut K c hcN ∉ innerAut ↥K := by
    intro hin
    apply hc'I
    rw [← hcbeq]
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr Φ]
    exact ⟨_, hin, rfl⟩
  obtain ⟨h3n, k, hk, hj⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.D4YH.fixed_sub_om8 (by omega) hK₀ hc'3 hc'S hc'I
  have hemb : ∀ k₁ : Subfield K₀, k₁ ≤ k →
      FixEmb K c (matrixDerived (coordinateQuadPlus 4 ↥k₁)) := by
    intro k₁ hk₁
    obtain ⟨j, hjinj, hjfix⟩ := hj k₁ hk₁
    refine fixEmb_transport Φ hcN j hjinj (fun x => ?_)
    have : MulAut.congr Φ (conjAut K c hcN) = c' := hcbeq
    rw [this]
    exact hjfix x
  have hbot2 : Nat.card ↥(⊥ : Subfield K₀) = 2 := Subfield.card_bot K₀ 2
  have hembbot := hemb ⊥ bot_le
  have hE4 := hembbot.rank4 (rank4_om8_two hbot2)
  have hE3 := hembbot.rankW (m := 3) (rank3_om8_two hbot2)
  have hcardB := card_B_eq hBK
  have h81 : Nat.card ↥(Bbar K B) ≤ 81 := by
    rw [← hA'card]
    exact NbrGraphD4.card_le_81 hA'el hα'A' hα'
  have hB81 : Nat.card B ≤ 81 * Nat.card (Bo K B) := by
    rw [hcardB, mul_comm]
    exact Nat.mul_le_mul_right _ h81
  refine ⟨c, hcN, hcB, hcout, hB81, hE4, hE3, ?_⟩
  by_cases hev : Even n
  · left
    obtain ⟨m, hm⟩ := h3n
    have hnm : n / 3 = m := by omega
    rw [hnm] at hk
    have hmev : Even m := by
      have : Even (3 * m) := hm ▸ hev
      rcases Nat.even_mul.1 this with h | h
      · exact absurd h (by decide)
      · exact h
    have hm1 : 1 ≤ m := by omega
    have hm2 : 2 ≤ m := by
      obtain ⟨r, hr⟩ := hmev
      omega
    have hJ : catalogIs (matrixDerived (coordinateQuadPlus 4 ↥k)) (isD4pow2 m) :=
      catalogIs_matrixDerived hm1 hk
    have hJtop : catalogIs ↥(⊤ : Subgroup (matrixDerived (coordinateQuadPlus 4 ↥k)))
        (isD4pow2 m) := (catalogIs_congr Subgroup.topEquiv).2 hJ
    obtain ⟨E, W, -, -, hEel, hEc, hW2, hWne, hEW⟩ := hasE4W_of_even hmev hm2 hJtop
    exact (hemb k le_rfl).rankW ⟨E, W, hEel, hEc, hW2, hWne, hEW⟩
  · right
    intro T hT2 hTne hBT hTK hTnc
    have hodd : Odd n := Nat.not_even_iff_odd.1 hev
    set T' : Subgroup ↥N := T.subgroupOf N with hT'
    set Th : Subgroup (MulAut ↥K) := T'.map ρ with hTh
    have hT'2 : IsPGroup 2 T' := hT2.comap_subtype
    have hTh2 : IsPGroup 2 Th := hT'2.map ρ
    have hρcoe : ∀ (b : ↥N) (k : ↥K), ((ρ b k : ↥K) : H) = (b : H) * k * (b : H)⁻¹ :=
      fun b k => rfl
    have hThne : Th ≠ ⊥ := by
      intro hbot
      obtain ⟨t, ht, htk⟩ := (SetLike.not_le_iff_exists.1 hTnc)
      obtain ⟨k, hk, hkt⟩ : ∃ k ∈ K, k * t ≠ t * k := by
        by_contra hh
        push Not at hh
        exact htk (Subgroup.mem_centralizer_iff.2 hh)
      have hmem : ρ ⟨t, hTK ht⟩ ∈ Th := Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 ht)
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hkt
      have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : H)) hmem
      simp only [hρcoe, MulAut.one_apply] at h3
      calc k * t = (t * k * t⁻¹) * t := by rw [h3]
        _ = t * k := by group
    have hBT' : B.subgroupOf N ≤ Subgroup.normalizer (T' : Set ↥N) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb)) (y : H)
      simp only [hT', Subgroup.mem_subgroupOf, SetLike.mem_coe, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1 ⊢
      exact h1
    have hnorm : Bbar K B ≤ Subgroup.normalizer (Th : Set (MulAut ↥K)) := fun σ hσ => by
      obtain ⟨b, hb, rfl⟩ := hσ
      exact Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem _ (hBT' hb))
    have h3 := inf_inner_le_three_odd Φ (by omega) hK₀ hodd hAel hαA hnc hTh2 hThne hnorm
    have h9 := card_le_nine_mul hA'el hα'A' hα'
    have h4 := inf_inner_card_eq Φ (Bbar K B)
    rw [← hA'] at h4
    have hBb : Nat.card ↥(Bbar K B) ≤ 27 := by omega
    rw [hcardB, mul_comm]
    exact Nat.mul_le_mul_right _ hBb

end Data

end CFSG.LocalAnalysis.GLTheoremA.D4Y
