module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113TCent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Y
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_MinT

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

structure GoodE (B M E : Subgroup Q) : Prop where
  le_K : E ≤ t113K B M
  elem : IsElemAbelian 3 E
  nonCyc : ∃ u ∈ E, ∃ v ∈ E, (∀ m ∈ M, u * m = m * u) ∧ (∀ m ∈ M, v * m = m * v) ∧ u ≠ 1 ∧
    v ∉ Subgroup.zpowers u
  inf_bot : t113B0 B M ⊓ E = ⊥
  card_le : Nat.card B ≤ Nat.card (t113B0 B M) * Nat.card E

namespace Triple3

variable {B M : Subgroup Q} {c : Q} (T : Triple3 B M c)

include T

theorem goodE_Y (hH : ∀ E : Subgroup (MulAut ↥M), IsElemAbelian 3 E → Nat.card E ≤ 9) {y : Q}
    (hy : y ∈ M) (ho : orderOf y = 3) (hnc : ∃ m ∈ M, y * m ≠ m * y) :
    GoodE B M (t113Y c y) := by
  obtain ⟨hel, hcard, hK, hB0⟩ := T.Y_spec hy ho hnc
  refine ⟨hK, hel, ?_, ?_, ?_⟩
  · obtain ⟨u, hu, v, hv, h1, h2, h3, h4⟩ := T.Y12_noncyclic hy ho hnc
    exact ⟨u, T.Y12_le_Y y hu, v, T.Y12_le_Y y hv, h1, h2, h3, h4⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact hB0 z hz.2 hz.1
  · rw [hcard]
    have hH' := hH (t113H B M) T.H_elem
    calc Nat.card B = 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) := T.card_B
      _ ≤ 3 * 9 * Nat.card (t113B0 B M) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH')
      _ = Nat.card (t113B0 B M) * 27 := by ring

theorem goodE_Y12 (hH : Nat.card (t113H B M) ≤ 3) {y : Q} (hy : y ∈ M) (ho : orderOf y = 3)
    (hnc : ∃ m ∈ M, y * m ≠ m * y) : GoodE B M (t113Y12 c y) := by
  obtain ⟨hel, hcard, hK, hB0⟩ := T.Y12_spec hy ho hnc
  refine ⟨hK, hel, T.Y12_noncyclic hy ho hnc, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact hB0 z hz.2 hz.1
  · rw [hcard]
    calc Nat.card B = 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) := T.card_B
      _ ≤ 3 * 3 * Nat.card (t113B0 B M) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH)
      _ = Nat.card (t113B0 B M) * 9 := by ring

end Triple3

theorem exists_goodE_norm2 {B M : Subgroup Q} {c : Q} (Tr : Triple3 B M c)
    (hall : ∀ M' : Subgroup Q, IsComponentOf M' ⊤ →
      (Subgroup.normalizer (M' : Set Q)).relIndex B ∣ 3)
    (hH9 : ∀ E : Subgroup (MulAut ↥M), IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hU : ∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set Q))
    (h2M : 2 ∣ Nat.card M)
    (hmode : (∃ y ∈ M, orderOf y = 3 ∧ (∃ m ∈ M, y * m ≠ m * y) ∧
        ∃ T : Subgroup Q, T ≤ M ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ y ∈ Subgroup.normalizer (T : Set Q)) ∨
      ((∃ y ∈ M, orderOf y = 3 ∧ ∃ m ∈ M, y * m ≠ m * y) ∧
        ∀ E T : Subgroup (MulAut ↥M), IsElemAbelian 3 E → T ≠ ⊥ → IsPGroup 2 T →
          E ≤ Subgroup.normalizer (T : Set (MulAut ↥M)) → Nat.card E ≤ 3)) :
    ∃ E : Subgroup Q, GoodE B M E ∧ ∃ T : Subgroup Q, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      t113B0 B M ≤ Subgroup.normalizer (T : Set Q) ∧ E ≤ Subgroup.normalizer (T : Set Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ (L S : Subgroup Q) (f : Q), S ≤ L → (∀ l ∈ L, f * l = l * f) →
      f ∈ Subgroup.normalizer (S : Set Q) :=
    fun _ _ _ hSL hf => t113_mem_normalizer_of_commute fun j hj => hf j (hSL hj)
  have hB0M : ∀ b ∈ t113B0 B M, ∀ l ∈ M, b * l = l * b := fun b hb l hl =>
    (Tr.B0_comm_K hb l (Tr.L_le_K hl)).symm
  rcases hmode with ⟨y, hy, ho, hnc, T₁, hT₁M, hT₁ne, hT₁2, hyT₁⟩ | ⟨⟨y, hy, ho, hnc⟩, hSU⟩
  ·
    refine ⟨t113Y c y, Tr.goodE_Y hH9 hy ho hnc, T₁, hT₁ne, hT₁2, ?_, ?_⟩
    · intro b hb
      exact hnorm _ _ _ hT₁M (hB0M b hb)
    · have h1 : c⁻¹ * y * c ∈ Subgroup.normalizer (T₁ : Set Q) :=
        hnorm _ _ _ hT₁M fun l hl => (Tr.comm01 l hl _ (Tr.conj1_mem hy)).symm
      have h2 : (c ^ 2)⁻¹ * y * c ^ 2 ∈ Subgroup.normalizer (T₁ : Set Q) :=
        hnorm _ _ _ hT₁M fun l hl => (Tr.comm02 l hl _ (Tr.conj2_mem hy)).symm
      unfold t113Y
      exact sup_le (sup_le (Subgroup.zpowers_le.2 hyT₁) (Subgroup.zpowers_le.2 h1))
        (Subgroup.zpowers_le.2 h2)
  · by_cases hR : ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 R ∧ B ≤ Subgroup.normalizer (R : Set Q) ∧
        R ≤ Subgroup.centralizer (t113K B M : Set Q)
    ·
      obtain ⟨R, hRne, hR2, hBR, hRC⟩ := hR
      refine ⟨t113Y c y, Tr.goodE_Y hH9 hy ho hnc, R, hRne, hR2, ?_, ?_⟩
      · exact (inf_le_left : t113B0 B M ≤ B).trans hBR
      · have hY := (Tr.Y_spec hy ho hnc).2.2.1
        exact hY.trans ((Subgroup.le_centralizer_iff.1 hRC).trans (Subgroup.centralizer_le_normalizer _))
    · push Not at hR
      obtain ⟨S, hSne, hS2, hBS⟩ := hU
      obtain ⟨T, hT, hT2, hBT, hTmin, hTel, hTcard⟩ := minT113_proved Q B S Tr.elem hSne hS2 hBS
      have R3 : Red3 B M c T := ⟨Tr, hall, hT, hT2, hBT, hTmin, hTel, hTcard⟩
      by_cases hTK : T ≤ Subgroup.normalizer (t113K B M : Set Q)
      ·
        have hTM : T ≤ Subgroup.normalizer (M : Set Q) := Tr.cjk_le_normalizer hTK hBT hTel
        have hnotriv : ¬ ∀ t ∈ T, ∀ l ∈ M, t * l = l * t := fun htriv =>
          hR T hT hT2 hBT (cjk_le_centralizer hBT htriv)
        have hH3 : Nat.card (t113H B M) ≤ 3 := by
          set N : Subgroup Q := Subgroup.normalizer (M : Set Q) with hN
          set ρ : ↥N →* MulAut ↥M := M.normalizerMonoidHom with hρ
          set T' : Subgroup (MulAut ↥M) := (T.subgroupOf N).map ρ with hT'
          have hT'2 : IsPGroup 2 T' :=
            (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map ρ
          have hT'ne : T' ≠ ⊥ := by
            intro h
            apply hnotriv
            intro t ht l hl
            have hmem : (⟨t, hTM ht⟩ : ↥N) ∈ T.subgroupOf N := ht
            have h1 : ρ ⟨t, hTM ht⟩ ∈ T' := Subgroup.mem_map_of_mem _ hmem
            rw [h, Subgroup.mem_bot] at h1
            have h2 := congrArg (fun f : MulAut ↥M => ((f ⟨l, hl⟩ : ↥M) : Q)) h1
            have h3 : t * l * t⁻¹ = l := by
              simp only [MulAut.one_apply] at h2
              exact h2
            exact mul_inv_eq_iff_eq_mul.1 h3
          have hHN : t113H B M ≤ Subgroup.normalizer (T' : Set (MulAut ↥M)) := by
            apply mt113_le_normalizer
            rintro _ ⟨a', rfl⟩ x hx
            obtain ⟨n, hn, rfl⟩ := hx
            have hn' : (n : Q) ∈ T := hn
            refine ⟨Subgroup.inclusion inf_le_left a' * n * (Subgroup.inclusion inf_le_left a')⁻¹,
              ?_, ?_⟩
            · show (a' : Q) * n * (a' : Q)⁻¹ ∈ T
              exact ((Subgroup.mem_normalizer_iff.1 (hBT a'.2.2)) n).1 hn'
            · rw [map_mul, map_mul, map_inv]
              rfl
          exact hSU (t113H B M) T' Tr.H_elem hT'ne hT'2 hHN
        obtain ⟨P⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
        set S₂ : Subgroup Q := (P : Subgroup ↥M).map M.subtype with hS₂def
        have hS₂M : S₂ ≤ M := Subgroup.map_subtype_le _
        have hS₂ne : S₂ ≠ ⊥ := fun h =>
          P.ne_bot_of_dvd_card h2M ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h)
        have hS₂2 : IsPGroup 2 S₂ := P.isPGroup'.map _
        refine ⟨t113Y12 c y, Tr.goodE_Y12 hH3 hy ho hnc, S₂, hS₂ne, hS₂2, ?_, ?_⟩
        · intro b hb
          exact hnorm _ _ _ hS₂M (hB0M b hb)
        · intro z hz
          exact hnorm _ _ _ hS₂M (Tr.Y12_comm_M hy z hz)
      ·
        obtain ⟨g, hg, t, ht, hM4⟩ : ∃ g ∈ B, ∃ t ∈ T, ∀ b ∈ B,
            GLBConj (g * t) M ≠ GLBConj b M := by
          by_contra hcon
          push Not at hcon
          exact hTK (t113_T_le_normalizer_K hcon)
        have hAT := R3.A_centralizes hTK
        have hcomm : ∀ i : ℕ, ∀ u ∈ GLBConj (c ^ i) M, ∀ w ∈ GLBConj (g * t) M, u * w = w * u :=
          fun i u hu w hw =>
            Tr.comm_of_ne (hM4 (c ^ i) (B.pow_mem Tr.mem i)).symm u hu w hw
        have hB0M4 : ∀ b ∈ t113B0 B M, ∀ w ∈ GLBConj (g * t) M, b * w = w * b := by
          intro b hb w hw
          have hbA := Tr.B0_mem_A hb
          have h1 : Commute b g := Tr.comm_B hb.1 hg
          have h2 : Commute b t := hAT b hbA t ht
          have h12 : Commute b (g * t) := h1.mul_right h2
          have hm : Commute b ((g * t) * w * (g * t)⁻¹) := hB0M b hb _ (mem_gLBConj.1 hw)
          have hw' : w = (g * t)⁻¹ * ((g * t) * w * (g * t)⁻¹) * (g * t) := by group
          have : Commute b w := by
            rw [hw']
            exact (h12.inv_right.mul_right hm).mul_right h12
          exact this.eq
        have hYM4 : ∀ z ∈ t113Y c y, ∀ w ∈ GLBConj (g * t) M, z * w = w * z := by
          intro z hz w hw
          have hle : t113Y c y ≤ Subgroup.centralizer ({w} : Set Q) := by
            unfold t113Y
            refine sup_le (sup_le ?_ ?_) ?_
            · refine Subgroup.zpowers_le.2 ?_
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact hcomm 0 y (by rw [pow_zero, gLBConj_one]; exact hy) w hw
            · refine Subgroup.zpowers_le.2 ?_
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact hcomm 1 _ (by rw [pow_one]; exact Tr.conj1_mem hy) w hw
            · refine Subgroup.zpowers_le.2 ?_
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact hcomm 2 _ (Tr.conj2_mem hy) w hw
          exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
        have h2M4 : 2 ∣ Nat.card ↥(GLBConj (g * t) M) := by
          rw [← Nat.card_congr (conjEquiv (g * t) M).toEquiv]
          exact h2M
        obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(GLBConj (g * t) M)) := inferInstance
        set S₄ : Subgroup Q := (P : Subgroup ↥(GLBConj (g * t) M)).map (GLBConj (g * t) M).subtype
          with hS₄def
        have hS₄M : S₄ ≤ GLBConj (g * t) M := Subgroup.map_subtype_le _
        have hS₄ne : S₄ ≠ ⊥ := fun h =>
          P.ne_bot_of_dvd_card h2M4
            ((Subgroup.map_eq_bot_iff_of_injective _ (GLBConj (g * t) M).subtype_injective).1 h)
        have hS₄2 : IsPGroup 2 S₄ := P.isPGroup'.map _
        refine ⟨t113Y c y, Tr.goodE_Y hH9 hy ho hnc, S₄, hS₄ne, hS₄2, ?_, ?_⟩
        · intro b hb
          exact hnorm _ _ _ hS₄M (hB0M4 b hb)
        · intro z hz
          exact hnorm _ _ _ hS₄M (hYM4 z hz)

end CFSG.LocalAnalysis.GLTheoremA.I113
