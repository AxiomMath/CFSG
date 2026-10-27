module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Hall

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J W : Subgroup G}

omit [Finite G] in
theorem pCoreIn_eq_self_of_isPGroup {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) :
    pCoreIn p X = X := by
  have htop : CFSG.pCore p X = ⊤ := by
    refine eq_top_iff.mpr (le_sSup ⟨inferInstance, ?_⟩)
    exact hX.of_equiv Subgroup.topEquiv.symm
  rw [pCoreIn, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite G] in
theorem commutator_le_of_le_normalizer {R T : Subgroup G}
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) : ⁅R, T⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro r hr t ht
  rw [commutatorElement_def, show r * t * r⁻¹ * t⁻¹ = r * (t * r⁻¹ * t⁻¹) by group]
  exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hTR ht) r⁻¹).mp (R.inv_mem hr))

theorem lemmaV45 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (h46 : LemmaII46Input σ J) (h49 : LemmaII49Input σ J)
    (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p) (hQF : Sec10.QGroupFourFusion G) :
    σ.LemmaV45 J := by
  intro W hW X hDX hWX hprimes
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have hWodd := odd_card_W hσ hJ hW
  have hWp := h31.coprime W hW
  have hXodd : Odd (Nat.card X) := by
    by_contra h
    have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)
    rcases hprimes 2 Nat.prime_two h2 with h | h
    · exact hσ.p_ne_two h.symm
    · exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h)
  have hD2 : IsPGroup 2 σ.D := isPGroup_D
  obtain ⟨R, hR, hDR⟩ := exists_isSylowOf_normalized_of_odd hσ.p_prime hD2 hDX hXodd
  have hTD := σ.T_le_D hσ
  have hTX : σ.T ≤ Subgroup.normalizer (X : Set G) := hTD.trans hDX
  have hTR : σ.T ≤ Subgroup.normalizer (R : Set G) := hTD.trans hDR
  have hRodd : Odd (Nat.card R) := odd_card_of_le hR.le hXodd
  have hXWodd : Odd (Nat.card (X ⊔ W : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hWX hXodd hWodd
  have hYWodd : ∀ {Y : Subgroup G}, Y ≤ X → Odd (Nat.card (Y ⊔ W : Subgroup G)) :=
    fun {Y} hYX => odd_card_of_le (sup_le (hYX.trans le_sup_left) le_sup_right) hXWodd
  have hRT : ⁅R, σ.T⁆ ≤ pCoreIn σ.p X := by
    apply commutator_le_pCore_of_local hXodd (isPGroup_T hσ) hTX hR hTR
    intro q hq hq2 hqp
    have : Fact q.Prime := ⟨hq⟩
    by_cases hqX : q ∣ Nat.card X
    · have hqW : q ∣ Nat.card W := (hprimes q hq hqX).resolve_left hqp
      obtain ⟨Z, hZX, hRZ, hDZ, hZπ, hZidx⟩ := exists_invariant_hall hD2 hDX hXodd hR.le hDR
        {d | (d : ℕ) = σ.p ∨ (d : ℕ) = q} (fun d hd => by
          left
          obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR.isPGroup
          rw [ha] at hd
          exact (Nat.prime_dvd_prime_iff_eq d.2 hσ.p_prime).mp (d.2.dvd_of_dvd_pow hd))
      have hZodd : Odd (Nat.card Z) := odd_card_of_le hZX hXodd
      obtain ⟨Y, hY, hDY⟩ := exists_isSylowOf_normalized_of_odd hq hD2 hDZ hZodd
      have hRZ' : IsSylowOf σ.p R Z := hR.of_le hRZ hZX
      have hZprimes : ∀ d : ℕ, d.Prime → d ∣ Nat.card Z → d = σ.p ∨ d = q :=
        fun d hd hdZ => hZπ ⟨d, hd⟩ hdZ
      obtain ⟨hZRY, hZYR⟩ := coe_eq_mul_of_isSylowOf (Ne.symm hqp) hRZ' hY hZprimes
      have hRY : (R : Set G) * Y = Y * R := hZRY.symm.trans hZYR
      have hYX : IsSylowOf q Y X := by
        rw [isSylowOf_iff] at hY ⊢
        refine ⟨hY.1.trans hZX, hY.2.1, ?_⟩
        rw [← Subgroup.relIndex_mul_relIndex Y Z X hY.1 hZX]
        exact hq.not_dvd_mul hY.2.2 (hZidx ⟨q, hq⟩ (Or.inr rfl))
      refine ⟨Y, hYX, hTD.trans hDY, hRY, ?_⟩
      exact lemmaV44 hσ hII hJ h31 hN' h42 h46 h21 hQF hW hR.isPGroup hDR hq hqW hY.isPGroup
        hDY hRY (hYWodd hYX.le)
    · refine ⟨⊥, DataConstruction.isSylowOf_bot hqX, fun t _ => ?_, ?_, ?_⟩
      · rw [Subgroup.mem_normalizer_iff]
        intro y
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl; group
        · intro h
          calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
            _ = 1 := by rw [h]; group
      · rw [Subgroup.coe_bot, Set.mul_singleton, Set.singleton_mul]
        simp
      · rw [sup_bot_eq]
        show ⁅R, σ.T⁆ ≤ pCoreIn σ.p R
        rw [pCoreIn_eq_self_of_isPGroup hR.isPGroup]
        exact commutator_le_of_le_normalizer hTR
  have hYN : ∀ q : ℕ, q.Prime → q ≠ σ.p → ∀ Y : Subgroup G, IsSylowOf q Y X →
      σ.D ≤ Subgroup.normalizer (Y : Set G) → Y ≤ σ.N := by
    intro q hq hqp Y hY hDY
    have : Fact q.Prime := ⟨hq⟩
    by_cases hqX : q ∣ Nat.card X
    · have hqW : q ∣ Nat.card W := (hprimes q hq hqX).resolve_left hqp
      obtain ⟨i, hYi⟩ := lemmaV43_ii hσ hII hJ h31 hN' h42 h46 h21 hQF hW hq hqW hY.isPGroup
        (hTD.trans hDY) (hYWodd hY.le)
      exact le_N_of_le_Ns hσ hII hDY hYi
    · have hY1 : Y = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        rw [hY.card_eq, Nat.factorization_eq_zero_of_not_dvd hqX, pow_zero]
      rw [hY1]
      exact bot_le
  have hXRN : R ⊔ (X ⊓ σ.N) = X := by
    apply eq_of_forall_exists_isSylowOf_le (sup_le hR.le inf_le_left)
    intro q hq hqX
    by_cases hqp : q = σ.p
    · subst hqp
      exact ⟨R, hR, le_sup_left⟩
    · obtain ⟨Y, hY, hDY⟩ := exists_isSylowOf_normalized_of_odd hq hD2 hDX hXodd
      exact ⟨Y, hY, (le_inf hY.le (hYN q hq hqp Y hY hDY)).trans le_sup_right⟩
  set Opx := pCoreIn σ.p X with hOpx
  have hXOpx : X ≤ Subgroup.normalizer (Opx : Set G) :=
    DataConstruction.le_normalizer_pCoreIn σ.p X
  have hRC : R ≤ Opx ⊔ (X ⊓ σ.C) := by
    intro ρ hρ
    have hρ' : ρ ∈ (R : Set G) := hρ
    rw [Conjugacy.coe_eq_mul_comp hσ hRodd hTR] at hρ'
    obtain ⟨_, ⟨_, ⟨c, hc, u0, hu0, rfl⟩, u1, hu1, rfl⟩, u2, hu2, rfl⟩ := hρ'
    have hcomp : ∀ i : Fin 3, comp σ R i ⊆ Opx := by
      intro i u hu
      apply hRT
      have hmem : u ∈ Subgroup.closure (comp σ R i) := Subgroup.subset_closure hu
      rw [← commutator_closure_comp_eq hσ hRodd hTR i] at hmem
      exact Subgroup.commutator_mono ((Subgroup.closure_le R).mpr (comp_subset R i)) le_rfl hmem
    have hcX : c ∈ X ⊓ σ.C := ⟨hR.le hc.1, hc.2⟩
    have ho : u0 * u1 * u2 ∈ Opx :=
      Opx.mul_mem (Opx.mul_mem (hcomp 0 hu0) (hcomp 1 hu1)) (hcomp 2 hu2)
    show c * u0 * u1 * u2 ∈ Opx ⊔ (X ⊓ σ.C)
    rw [show c * u0 * u1 * u2 = c * (u0 * u1 * u2) by group, sup_comm]
    exact Subgroup.mul_mem_sup hcX ho
  have hXN : X = Opx ⊔ (X ⊓ σ.N) := by
    refine le_antisymm ?_ (sup_le (pCoreIn_le σ.p X) inf_le_left)
    calc X = R ⊔ (X ⊓ σ.N) := hXRN.symm
      _ ≤ (Opx ⊔ (X ⊓ σ.C)) ⊔ (X ⊓ σ.N) := sup_le_sup_right hRC _
      _ ≤ Opx ⊔ (X ⊓ σ.N) := by
          refine sup_le (sup_le le_sup_left ?_) le_sup_right
          exact (inf_le_inf_left _ σ.C_le_N).trans le_sup_right
  set Op := pCoreIn σ.p σ.N with hOp
  have hWN : W ≤ σ.N := W_le_N hσ hJ hW
  have hXNnorm : X ⊓ σ.N ≤ Subgroup.normalizer ((W ⊔ Op : Subgroup G) : Set G) := by
    have hWXN : W ≤ Subgroup.normalizer ((X ⊓ σ.N : Subgroup G) : Set G) :=
      (le_inf hWX (hWN.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hY₁odd : Odd (Nat.card (W ⊔ (X ⊓ σ.N) : Subgroup G)) := by
      have := odd_card_sup_of_le_normalizer_of_odd hWXN (odd_card_of_le inf_le_left hXodd) hWodd
      rwa [sup_comm] at this
    have hDY₁ : σ.D ≤ Subgroup.normalizer ((W ⊔ (X ⊓ σ.N) : Subgroup G) : Set G) := by
      refine (le_inf hW.2.1 ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
      exact (le_inf hDX ((σ.D_le_N hσ).trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hY₁ := h49 W hW (W ⊔ (X ⊓ σ.N)) (sup_le hWN inf_le_right) hY₁odd hDY₁ le_sup_left
    exact (le_sup_right.trans hY₁).trans (sup_le (C_le_normalizer_W_sup hJ hW)
      (ON_le_normalizer_W_sup hσ hJ hW))
  set P₁ : Subgroup G := Op ⊓ X with hP₁
  have hWOp : W ≤ Subgroup.normalizer (Op : Set G) := hWN.trans N_le_normalizer_pCore
  have hWP₁ : W ≤ Subgroup.normalizer (P₁ : Set G) :=
    (le_inf hWOp hWX).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBw : P₁ ⊔ W = (W ⊔ Op) ⊓ (W ⊔ (X ⊓ σ.N)) := by
    apply le_antisymm
    · refine sup_le (le_inf ?_ ?_) (le_inf le_sup_left le_sup_left)
      · exact inf_le_left.trans le_sup_right
      · exact (le_inf inf_le_right (inf_le_left.trans (pCoreIn_le σ.p σ.N))).trans le_sup_right
    · intro u hu
      obtain ⟨w, hw, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer hWOp).mp hu.1
      have hvWX : v ∈ W ⊔ X := by
        have : v = w⁻¹ * (w * v) := by group
        rw [this]
        exact (W ⊔ X).mul_mem (Subgroup.mem_sup_left (W.inv_mem hw))
          ((sup_le_sup_left inf_le_left W) hu.2)
      obtain ⟨w', hw', x, hx, hwx⟩ := (mem_sup_iff_of_le_normalizer hWX).mp hvWX
      obtain ⟨a, ha⟩ := (DataConstruction.isPGroup_pCoreIn σ.p σ.N) ⟨v, hv⟩
      have hva : v ^ σ.p ^ a = 1 := by simpa using congrArg Subtype.val ha
      have hx' : w' * x * w'⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hWX hw') x).mp hx
      obtain ⟨m', hm', hpow⟩ := exists_pow_mul_eq (hWX hw') hx' (σ.p ^ a)
      rw [show w' * x * w'⁻¹ * w' = v by rw [← hwx]; group, hva] at hpow
      have hw'a : w' ^ σ.p ^ a ∈ X := by
        rw [eq_inv_of_mul_eq_one_right hpow.symm]
        exact X.inv_mem hm'
      have hcop : Nat.Coprime (Nat.card W) (σ.p ^ a) :=
        Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd hσ.p_prime).mpr hWp).symm
      have hw'X : w' ∈ X := mem_of_pow_mem_of_coprime hw' hcop hw'a
      have hvX : v ∈ X := by rw [← hwx]; exact X.mul_mem hw'X hx
      rw [sup_comm]
      exact Subgroup.mul_mem_sup hw ⟨hv, hvX⟩
  have hP₁p : IsPGroup σ.p P₁ := (DataConstruction.isPGroup_pCoreIn σ.p σ.N).to_le inf_le_left
  have hBwodd : Odd (Nat.card (P₁ ⊔ W : Subgroup G)) :=
    odd_card_of_le (sup_le (inf_le_right.trans le_sup_left) le_sup_right) hXWodd
  have hXNBw : X ⊓ σ.N ≤ Subgroup.normalizer ((P₁ ⊔ W : Subgroup G) : Set G) := by
    rw [hBw]
    refine (le_inf hXNnorm ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact le_sup_right.trans Subgroup.le_normalizer
  have hP₁O : P₁ ≤ Opx := by
    set Q : Subgroup G := Opx ⊔ P₁ with hQ
    have hP₁X : P₁ ≤ Subgroup.normalizer (Opx : Set G) := inf_le_right.trans hXOpx
    have hQp : IsPGroup σ.p Q :=
      IsPGroup.to_sup_of_normal_left' (DataConstruction.isPGroup_pCoreIn σ.p X) hP₁p hP₁X
    have hQX : Q ≤ X := sup_le (pCoreIn_le σ.p X) inf_le_right
    have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := by
      rw [hXN]
      refine sup_le ?_ ?_
      · intro a ha
        apply DataConstruction.mem_normalizer_of_conj_mem
        intro g hg
        obtain ⟨o, ho, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer' hP₁X).mp hg
        have hvX : v ∈ X := hv.2
        have h1 : a * o * a⁻¹ ∈ Opx := Opx.mul_mem (Opx.mul_mem ha ho) (Opx.inv_mem ha)
        have h2 : a * v * a⁻¹ * v⁻¹ ∈ Opx := by
          rw [show a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) by group]
          exact Opx.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hXOpx hvX) a⁻¹).mp
            (Opx.inv_mem ha))
        rw [show a * (o * v) * a⁻¹ = (a * o * a⁻¹) * (a * v * a⁻¹ * v⁻¹) * v by group]
        exact Q.mul_mem (Q.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_left h2))
          (Subgroup.mem_sup_right hv)
      · refine (le_inf (inf_le_left.trans hXOpx) ?_).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
        exact (le_inf (inf_le_right.trans N_le_normalizer_pCore)
          (inf_le_left.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
    exact le_sup_right.trans (DataConstruction.le_pCoreIn hQX hXQ hQp)
  have hXNW : X ⊓ σ.N ≤ Opx ⊔ (X ⊓ Subgroup.normalizer (W : Set G)) := by
    intro y hy
    obtain ⟨v, hv, hvy⟩ := exists_inv_mul_mem_normalizer_of_complement hP₁p hWP₁ hWp hBwodd
      (hXNBw hy)
    rw [show y = v * (v⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup (hP₁O hv) ⟨X.mul_mem (X.inv_mem hv.2) hy.1, hvy⟩
  refine ⟨⟨hXN, ?_⟩, R, hR, hRC⟩
  refine le_antisymm ?_ (sup_le (pCoreIn_le σ.p X) inf_le_left)
  calc X = Opx ⊔ (X ⊓ σ.N) := hXN
    _ ≤ Opx ⊔ (X ⊓ Subgroup.normalizer (W : Set G)) := sup_le le_sup_left hXNW

end CFSG.ABGTheoremB.V4
