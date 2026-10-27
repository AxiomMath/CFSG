module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Offender

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Quasithin.Explicit

private theorem g2out_main
    {K : Type} [Group K] [Finite K] (L B : Subgroup K)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥L ≃* ↥(CFSG.Open.quasithinG2 F)) (hBN : B ≤ Subgroup.normalizer (L : Set K))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) :
    (innerPart L B).relIndex B ≤ 2 := by
  classical
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      hn F hNatF
  have hinv : ∀ x y : F ≃+* F, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    have h1 : ∀ k, x (x k) = k := fun k => congrArg (fun σ : F ≃+* F => σ k) hx
    have h2 : ∀ k, y (y k) = k := fun k => congrArg (fun σ : F ≃+* F => σ k) hy
    have h1' : ∃ k, x k ≠ k := by
      by_contra hcon
      push Not at hcon
      exact hx1 (RingEquiv.ext hcon)
    have h2' : ∃ k, y k ≠ k := by
      by_contra hcon
      push Not at hcon
      exact hy1 (RingEquiv.ext hcon)
    exact CFSG.Quasithin.B42G2.ringEquiv_involution_unique hNatF hn h1 h2 h1' h2'
  obtain ⟨φ⟩ := exists_g2AdjointEquiv (L := L) hn hF e
  let cg : MulAut ↥L →* MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
    (MulAut.congr φ).toMonoidHom
  let Φ : ↥B →* (F ≃+* F) := (Θ.comp cg).comp (CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN)
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L).map
      (MulAut.congr φ).toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ
  have hpre : cg ⁻¹'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) =
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    ext x
    rw [Set.mem_preimage, ← hmap]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [← (MulAut.congr φ).injective hyx]
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  have hker : Φ.ker = (innerPart L B).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      mem_innerPart]
    constructor
    · intro hb
      have hb' : CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
        have h1 : cg (CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner
              ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) := by
          rw [show CFSG.ComponentClassification.OuterAutomorphisms.inner
              ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) = Θ.ker from hΘker.symm]
          exact MonoidHom.mem_ker.mpr hb
        rw [← hmap] at h1
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
        rw [← (MulAut.congr φ).injective hyx]
        exact hy
      obtain ⟨l, hl, hag⟩ :=
        CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.exists_conjAgree_of_mem_range L B hBN b hb'
      exact ⟨b.2, l, hl, hag⟩
    · rintro ⟨hbB, l, hl, hag⟩
      rw [← MonoidHom.mem_ker, hΘker]
      have hconj : CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b =
          MulAut.conj ⟨l, hl⟩ := by
        apply MulEquiv.ext
        intro k
        apply Subtype.ext
        exact hag (k : K) k.2
      rw [hconj]
      change MulAut.congr φ (MulAut.conj ⟨l, hl⟩) ∈ MulAut.conj.range
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
      exact ⟨φ ⟨l, hl⟩, rfl⟩
  have hrange_sq : ∀ x ∈ Φ.range, x * x = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul, show ((b : ↥B) * b : ↥B) = 1 by
      exact Subtype.ext (by simpa using hB2 (b : K) b.2), map_one]
  have hrange_comm : ∀ x ∈ Φ.range, ∀ y ∈ Φ.range, x * y = y * x := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, show ((b : ↥B) * c : ↥B) = (c : ↥B) * b by
      exact Subtype.ext (hBc (b : K) b.2 (c : K) c.2)]
  have hrange_card : Nat.card Φ.range ≤ 2 := by
    by_cases htriv : ∀ y ∈ Φ.range, y = 1
    · have : Φ.range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr htriv
      rw [this, Subgroup.card_bot]
      norm_num
    · push Not at htriv
      obtain ⟨y₀, hy₀, hy₀1⟩ := htriv
      have hsub : (Φ.range : Set (F ≃+* F)) ⊆ {1, y₀} := by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hinv y y₀ (hrange_sq y hy) (hrange_sq y₀ hy₀) hy1 hy₀1)
      calc Nat.card Φ.range = Nat.card (Φ.range : Set (F ≃+* F)) := rfl
        _ ≤ Nat.card ({1, y₀} : Set (F ≃+* F)) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
            rw [Nat.card_coe_set_eq, Set.ncard_pair hy₀1.symm]
  have hBcard : Nat.card ↥B = Nat.card ↥(innerPart L B) * Nat.card Φ.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Φ.ker
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    have h2 : Nat.card (↥B ⧸ (innerPart L B).subgroupOf B) = Nat.card Φ.range := by
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
    rw [h1, h2, mul_comm]
  have hrel : Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index ((innerPart L B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    exact h1
  have heq : (innerPart L B).relIndex B = Nat.card Φ.range := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(innerPart L B)))
    rw [hrel, hBcard]
  rw [heq]
  exact hrange_card

theorem relIndex_innerPart_le_two_g2
    {K : Type} [Group K] [Finite K] (L B : Subgroup K)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* ↥(cayleyGroup F)) (hBN : B ≤ Subgroup.normalizer (L : Set K))
    (hB2 : ∀ b ∈ B, b * b = 1) : (innerPart L B).relIndex B ≤ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hchar : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := by
    intro b hb c hc
    have hbc : b * c * (b * c) = 1 := hB2 (b * c) (B.mul_mem hb hc)
    have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hB2 b hb)
    have hc1 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hB2 c hc)
    have h2 : b * c = (b * c)⁻¹ := eq_inv_of_mul_eq_one_right hbc
    rw [h2, mul_inv_rev, hb1, hc1]
  exact g2out_main L B hn hFc
    (e.trans (MulEquiv.subgroupCongr
      CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup.symm)) hBN hB2 hBc

end CFSG.LocalAnalysis.RankThreeUC.S15

end
