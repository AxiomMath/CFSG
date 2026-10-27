module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Ehat
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Inner
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_MinT
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113TCent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA.I113

variable {Q : Type} [Group Q] [Finite Q]

structure QSetting (B M : Subgroup Q) (c : Q) : Prop where
  tri : Triple3 B M c
  hall : ∀ M' : Subgroup Q, IsComponentOf M' ⊤ →
    (Subgroup.normalizer (M' : Set Q)).relIndex B ∣ 3
  hH9 : ∀ E : Subgroup (MulAut ↥M), IsElemAbelian 3 E → Nat.card E ≤ 9
  hSyl : ∀ R : Sylow 3 ↥M, Nat.card (R : Subgroup ↥M) = 27 ∧
    (∃ r ∈ (R : Subgroup ↥M), ∃ s ∈ (R : Subgroup ↥M), r * s ≠ s * r) ∧
    ∀ r ∈ (R : Subgroup ↥M), r ^ 3 = 1
  h2M : 2 ∣ Nat.card M

section Cases

variable {B M : Subgroup Q} {c : Q}

theorem centralizer_le_normalizer_of_le {T : Subgroup Q} (hTM : T ≤ M) :
    Subgroup.centralizer (M : Set Q) ≤ Subgroup.normalizer (T : Set Q) :=
  (Subgroup.centralizer_le (s := (T : Set Q)) (t := (M : Set Q)) hTM).trans
    (Subgroup.centralizer_le_normalizer _)

theorem exists_two_of_central (h2M : 2 ∣ Nat.card M) {S : Subgroup Q}
    (hS : S ≤ Subgroup.centralizer (M : Set Q)) :
    ∃ T : Subgroup Q, T ≠ ⊥ ∧ IsPGroup 2 T ∧ S ≤ Subgroup.normalizer (T : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  set S₂ : Subgroup Q := (P : Subgroup ↥M).map M.subtype with hS₂def
  have hS₂M : S₂ ≤ M := Subgroup.map_subtype_le _
  have hS₂ne : S₂ ≠ ⊥ := fun h =>
    P.ne_bot_of_dvd_card h2M
      ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h)
  have hS₂2 : IsPGroup 2 S₂ := P.isPGroup'.map _
  refine ⟨S₂, hS₂ne, hS₂2, fun s hs => ?_⟩
  exact centralizer_le_normalizer_of_le hS₂M (hS hs)

theorem B0_le_centralizer (Tr : Triple3 B M c) :
    t113B0 B M ≤ Subgroup.centralizer (M : Set Q) := fun b hb =>
  Subgroup.mem_centralizer_iff.2 fun l hl => Tr.B0_comm_K hb l (Tr.L_le_K hl)

theorem good_caseI (S : QSetting B M c) (hH3 : Nat.card (t113H B M) ≤ 3) :
    ∃ y w : Q, GoodData B M (t113B0 B M) (ehat c y w) ⊥ M ∧
      t113B0 B M ⊔ ehat c y w ⊔ ⊥ ≤ Subgroup.centralizer (M : Set Q) := by
  have Tr := S.tri
  obtain ⟨y, hy, ho, hnc⟩ := exists_noncentral S.hSyl
  obtain ⟨w, hw, hw3, hwy, hwn⟩ := exists_w S.hSyl hy ho
  have hspec := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
  refine ⟨y, w, Triple3.goodData_of_ehat Tr hy ho hnc hw hw3 hwy hwn inf_le_left le_rfl
    (fun b hb => (Tr.B0_mem_A hb).1) (fun z hz e he => (Tr.B0_comm_K hz e (hspec.1 he)).symm) ?_, ?_⟩
  · rw [Tr.card_B]
    calc 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) ≤ 3 * 3 * Nat.card (t113B0 B M) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH3)
      _ = 9 * Nat.card (t113B0 B M) := by norm_num
  · refine sup_le (sup_le (B0_le_centralizer Tr) fun e he => ?_) bot_le
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hspec.2.2.2 e he l hl).symm

theorem good_caseA (S : QSetting B M c) (hH : 3 < Nat.card (t113H B M)) :
    ∃ y w a : Q, y ∈ M ∧ orderOf y = 3 ∧ (∃ m ∈ M, y * m ≠ m * y) ∧ a ∈ t113A B M ∧
      (∀ l ∈ M, a * l * a⁻¹ = y * l * y⁻¹) ∧ w ∈ M ∧ w ^ 3 = 1 ∧ y * w = w * y ∧
      w ∉ Subgroup.zpowers y ∧
      GoodData B M (t113B0 B M ⊔ Subgroup.zpowers a) (ehat c y w) ⊥ M := by
  have Tr := S.tri
  obtain ⟨y, hy, ho, hnc, a, ha, hay⟩ := exists_inner Tr S.hH9 S.hSyl hH
  obtain ⟨w, hw, hw3, hwy, hwn⟩ := exists_w S.hSyl hy ho
  have hspec := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
  have ha1 : a ∉ t113B0 B M := by
    intro hB0
    obtain ⟨m, hm, hne⟩ := hnc
    apply hne
    have h1 := hay m hm
    have h2 : a * m = m * a := (Tr.B0_comm_K hB0 m (Tr.L_le_K hm)).symm
    have h3 : a * m * a⁻¹ = m := by rw [h2]; group
    rw [h3] at h1
    have : y * m * y⁻¹ = m := h1.symm
    calc y * m = (y * m * y⁻¹) * y := by group
      _ = m * y := by rw [this]
  obtain ⟨-, hcard3, hDB, hDN⟩ := Triple3.B0_sup_zpowers Tr ha ha1
  have hH9 := S.hH9 (t113H B M) Tr.H_elem
  refine ⟨y, w, a, hy, ho, hnc, ha, hay, hw, hw3, hwy, hwn,
    Triple3.goodData_of_ehat Tr hy ho hnc hw hw3 hwy hwn hDB le_sup_left hDN ?_ ?_⟩
  · intro z hz e he
    have hle : t113B0 B M ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({e} : Set Q) := by
      refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Tr.B0_comm_K hb e (hspec.1 he)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Triple3.a_comm_ehat Tr ha.2 hay hy hw hwy e he
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
  · rw [Tr.card_B, hcard3]
    calc 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) ≤ 3 * 9 * Nat.card (t113B0 B M) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH9)
      _ = 9 * (3 * Nat.card (t113B0 B M)) := by ring

theorem exists_good_noT (S : QSetting B M c) :
    ∃ D E1 E2 M4 : Subgroup Q, GoodData B M D E1 E2 M4 := by
  by_cases hH3 : Nat.card (t113H B M) ≤ 3
  · obtain ⟨y, w, hG, -⟩ := good_caseI S hH3
    exact ⟨_, _, _, _, hG⟩
  · obtain ⟨y, w, a, -, -, -, -, -, -, -, -, -, hG⟩ := good_caseA S (not_le.1 hH3)
    exact ⟨_, _, _, _, hG⟩

theorem exists_good_T (S : QSetting B M c)
    (hU : ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Q))
    (hmode : (∀ y ∈ M, orderOf y = 3 → ∃ T : Subgroup Q, T ≤ M ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
          y ∈ Subgroup.normalizer (T : Set Q)) ∨
      (∀ E T : Subgroup (MulAut ↥M), IsElemAbelian 3 E → T ≠ ⊥ → IsPGroup 2 T →
          E ≤ Subgroup.normalizer (T : Set (MulAut ↥M)) → Nat.card E ≤ 3)) :
    ∃ D E1 E2 M4 : Subgroup Q, GoodData B M D E1 E2 M4 ∧ ∃ T : Subgroup Q, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ D ⊔ E1 ⊔ E2 ≤ Subgroup.normalizer (T : Set Q) := by
  classical
  have Tr := S.tri
  by_cases hH3 : Nat.card (t113H B M) ≤ 3
  ·
    obtain ⟨y, w, hG, hcent⟩ := good_caseI S hH3
    exact ⟨_, _, _, _, hG, exists_two_of_central S.h2M hcent⟩
  · have hH := not_le.1 hH3
    obtain ⟨y, w, a, hy, ho, hnc, ha, hay, hw, hw3, hwy, hwn, hG⟩ := good_caseA S hH
    have hspec := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
    have hB0N : ∀ (T : Subgroup Q), T ≤ M → t113B0 B M ≤ Subgroup.normalizer (T : Set Q) :=
      fun T hTM b hb => centralizer_le_normalizer_of_le hTM (B0_le_centralizer Tr hb)
    have hEN : ∀ (T : Subgroup Q), T ≤ M → ehat c y w ≤ Subgroup.normalizer (T : Set Q) :=
      fun T hTM e he => centralizer_le_normalizer_of_le hTM
        (Subgroup.mem_centralizer_iff.2 fun l hl => (hspec.2.2.2 e he l hl).symm)
    rcases hmode with hKD | hSU
    ·
      obtain ⟨T, hTM, hTne, hT2, hyT⟩ := hKD y hy ho
      refine ⟨_, _, _, _, hG, T, hTne, hT2, ?_⟩
      refine sup_le (sup_le (sup_le (hB0N T hTM) ?_) (hEN T hTM)) bot_le
      refine Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_fintype fun t ht => ?_)
      have htM : t ∈ M := hTM ht
      rw [hay t htM]
      exact (Subgroup.mem_normalizer_iff.1 hyT t).1 ht
    · by_cases hR : ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 R ∧ B ≤ Subgroup.normalizer (R : Set Q) ∧
          R ≤ Subgroup.centralizer (t113K B M : Set Q)
      ·
        obtain ⟨R, hRne, hR2, hBR, hRC⟩ := hR
        refine ⟨_, _, _, _, hG, R, hRne, hR2, ?_⟩
        refine sup_le (sup_le ?_ ?_) bot_le
        · exact (Triple3.B0_sup_zpowers Tr ha (by
            intro hB0
            obtain ⟨m, hm, hne⟩ := hnc
            apply hne
            have h1 := hay m hm
            have h2 : a * m = m * a := (Tr.B0_comm_K hB0 m (Tr.L_le_K hm)).symm
            have h3 : a * m * a⁻¹ = m := by rw [h2]; group
            rw [h3] at h1
            have : y * m * y⁻¹ = m := h1.symm
            calc y * m = (y * m * y⁻¹) * y := by group
              _ = m * y := by rw [this])).2.2.1.trans hBR
        · intro e he
          exact t113_mem_normalizer_of_commute fun j hj =>
            Subgroup.mem_centralizer_iff.1 (hRC hj) e (hspec.1 he)
      ·
        push Not at hR
        obtain ⟨U, hUne, hU2, hBU⟩ := hU
        obtain ⟨T, hT, hT2, hBT, hTmin, hTel, hTcard⟩ := minT113_proved Q B U Tr.elem hUne hU2 hBU
        have R3 : Red3 B M c T := ⟨Tr, S.hall, hT, hT2, hBT, hTmin, hTel, hTcard⟩
        by_cases hTK : T ≤ Subgroup.normalizer (t113K B M : Set Q)
        ·
          exfalso
          have hTM : T ≤ Subgroup.normalizer (M : Set Q) := Tr.cjk_le_normalizer hTK hBT hTel
          have hnotriv : ¬ ∀ t ∈ T, ∀ l ∈ M, t * l = l * t := fun htriv =>
            hR T hT hT2 hBT (cjk_le_centralizer hBT htriv)
          have hH3' : Nat.card (t113H B M) ≤ 3 := by
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
              refine ⟨Subgroup.inclusion inf_le_left a' * n *
                (Subgroup.inclusion inf_le_left a')⁻¹, ?_, ?_⟩
              · show (a' : Q) * n * (a' : Q)⁻¹ ∈ T
                exact ((Subgroup.mem_normalizer_iff.1 (hBT a'.2.2)) n).1 hn'
              · rw [map_mul, map_mul, map_inv]
                rfl
            exact hSU (t113H B M) T' Tr.H_elem hT'ne hT'2 hHN
          omega
        ·
          obtain ⟨g, hg, t, ht, hM4⟩ : ∃ g ∈ B, ∃ t ∈ T, ∀ b ∈ B,
              GLBConj (g * t) M ≠ GLBConj b M := by
            by_contra hcon
            push Not at hcon
            exact hTK (t113_T_le_normalizer_K hcon)
          have hAT := R3.A_centralizes hTK
          have hcomm : ∀ b ∈ B, ∀ u ∈ GLBConj b M, ∀ v ∈ GLBConj (g * t) M, u * v = v * u :=
            fun b hb u hu v hv => Tr.comm_of_ne (hM4 b hb).symm u hu v hv
          have hB0M : ∀ b ∈ t113B0 B M, ∀ l ∈ M, b * l = l * b := fun b hb l hl =>
            (Tr.B0_comm_K hb l (Tr.L_le_K hl)).symm
          have hB0M4 : ∀ b ∈ t113B0 B M, ∀ v ∈ GLBConj (g * t) M, b * v = v * b := by
            intro b hb v hv
            have hbA := Tr.B0_mem_A hb
            have h1 : Commute b g := Tr.comm_B hb.1 hg
            have h2 : Commute b t := hAT b hbA t ht
            have h12 : Commute b (g * t) := h1.mul_right h2
            have hm : Commute b ((g * t) * v * (g * t)⁻¹) := hB0M b hb _ (mem_gLBConj.1 hv)
            have hv' : v = (g * t)⁻¹ * ((g * t) * v * (g * t)⁻¹) * (g * t) := by group
            have : Commute b v := by
              rw [hv']
              exact (h12.inv_right.mul_right hm).mul_right h12
            exact this.eq
          have hy4 : (g * t)⁻¹ * y * (g * t) ∈ GLBConj (g * t) M := by
            rw [mem_gLBConj]
            have : (g * t) * ((g * t)⁻¹ * y * (g * t)) * (g * t)⁻¹ = y := by group
            rw [this]
            exact hy
          have ho4 : orderOf ((g * t)⁻¹ * y * (g * t)) = 3 := by
            rw [t113_orderOf_conj, ho]
          have hH9 := S.hH9 (t113H B M) Tr.H_elem
          have hGood := Triple3.goodData_of_M4 Tr hy ho hnc hw hw3 hwy hwn (Tr.comp_conj (g * t)) hcomm
            hB0M4 hy4 ho4 (noncentral_conj (g * t) hnc) (by
              rw [Tr.card_B]
              calc 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M)
                  ≤ 3 * 9 * Nat.card (t113B0 B M) :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH9)
                _ = 27 * Nat.card (t113B0 B M) := by norm_num)
          refine ⟨_, _, _, _, hGood, exists_two_of_central S.h2M ?_⟩
          refine sup_le (sup_le (B0_le_centralizer Tr) fun e he => ?_) ?_
          · exact Subgroup.mem_centralizer_iff.2 fun l hl => (hspec.2.2.2 e he l hl).symm
          · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
            have := hcomm 1 B.one_mem l (by rw [gLBConj_one]; exact hl) _ hy4
            exact this

end Cases

end CFSG.LocalAnalysis.GLTheoremA.I1132
