module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Q1

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_normalizer_of_lt {H P : Subgroup X} (hP : IsPGroup 2 P) (hHP : H ≤ P)
    (hne : H ≠ P) : ∃ x ∈ P, x ∉ H ∧ x ∈ normalizer (H : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hHP fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < normalizer (IP : Set P) := Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (H : Set X)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hHP]
    exact hxN
  exact mem_subgroupOf.mp hxsub

theorem eq_sylow_of_normalizer {S : Subgroup X} {P : Sylow 2 X} (hSP : S ≤ P)
    (h : ∀ x ∈ (P : Subgroup X), x ∈ normalizer (S : Set X) → x ∈ S) : S = P := by
  by_contra hne
  obtain ⟨x, hxP, hxS, hxN⟩ := exists_mem_normalizer_of_lt P.isPGroup' hSP hne
  exact hxS (h x hxP hxN)

omit [Finite X] in
theorem isPGroup_sup_zpowers {S : Subgroup X} {P : Subgroup X} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    {x : X} (hxP : x ∈ P) : IsPGroup 2 (S ⊔ zpowers x : Subgroup X) :=
  hP.to_le (sup_le hSP (zpowers_le.mpr hxP))

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem wt₂_zk : C.D₂.w₂ * (S.z * C.F.kF) * C.D₂.w₂⁻¹ = S.z * C.F.kF :=
  C.hact₂.2.2.2.2.2.2.2.2.2

theorem eq_of_fixed_Et {e : X} (he : e ∈ S.E (C.F.xF * C.F.yF))
    (hv : C.D₂.v * e * C.D₂.v⁻¹ = e) (hw₁ : C.D₂.w₁ * e * C.D₂.w₁⁻¹ = e)
    (hw₂ : C.D₂.w₂ * e * C.D₂.w₂⁻¹ = e) : e = 1 ∨ e = S.z * C.F.kF := by
  rcases (isRefl_xyF C.F).mem_E0_or (isK_zkF C.F) he with h | h
  · have h' : e ∈ S.E0 (C.F.xF * C.F.yF) (S.z * C.F.kF) := h
    rw [E0_eq] at h'
    have hel := elemAbelianTwo_zk (isK_zkF C.F)
    rcases mem_or_of_mem_sup hel (xyF_sq C.F) (fun _ hb => (isRefl_xyF C.F).comm_B
        (zk_le_B (isK_zkF C.F) hb)) h' with h1 | h1
    ·
      have hZ : e ∈ C.Zz := by rw [C.Zz_eq', sup_comm]; exact h1
      have hzel : ElemAbelianTwo (zpowers S.z) :=
        ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha)
          (zpowers_le.mpr z_mem_B hb), fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
      rcases mem_or_of_mem_sup hzel C.F.kF_sq (fun a ha => commute_of_mem_B (kF_mem_B C.F)
          (zpowers_le.mpr z_mem_B ha)) hZ with h2 | h2
      · rcases eq_one_or_eq_of_mem_zpowers z_sq h2 with h3 | h3
        · exact Or.inl h3
        · exact absurd (h3 ▸ hw₂) C.wt₂_z_ne
      · have hek : e = (e * C.F.kF) * C.F.kF := by rw [mul_assoc, C.kk, mul_one]
        rcases eq_one_or_eq_of_mem_zpowers z_sq h2 with h3 | h3
        · exfalso
          rw [h3, one_mul] at hek
          rw [hek] at hw₂
          apply C.wt₂_z_ne
          calc C.D₂.w₂ * S.z * C.D₂.w₂⁻¹ = C.D₂.w₂ * (S.z * C.F.kF * C.F.kF) * C.D₂.w₂⁻¹ := by
                rw [mul_assoc S.z C.F.kF C.F.kF, C.kk, mul_one]
            _ = (C.D₂.w₂ * (S.z * C.F.kF) * C.D₂.w₂⁻¹) * (C.D₂.w₂ * C.F.kF * C.D₂.w₂⁻¹) := by
                group
            _ = S.z := by rw [C.wt₂_zk, hw₂, mul_assoc, C.kk, mul_one]
        · right; rw [hek, h3]
    · exfalso
      set g := e * (C.F.xF * C.F.yF) with hg
      have hgZ : g ∈ C.Zz := by rw [C.Zz_eq', sup_comm]; exact h1
      have heg : e = g * (C.F.xF * C.F.yF) := by
        rw [hg, mul_assoc, ← pow_two, xyF_sq, mul_one]
      rw [heg, conj_mul_eq, C.fix_Zz C.wt₁_z C.wt₁_k hgZ, C.wt₁_xy, ← mul_assoc] at hw₁
      exact (isK_zkF C.F).ne_one (mul_left_cancel (hw₁.trans (mul_one _).symm))
  · exfalso
    set f := e * S.t with hf
    have hfE : f ∈ C.Et₀ := h
    have hef : e = f * S.t := by rw [hf, mul_assoc, tt S, mul_one]
    rw [hef, conj_mul_eq, C.vt_Et0 hfE, C.vt_t, ← mul_assoc] at hv
    exact (isK_zkF C.F).ne_one (mul_left_cancel (hv.trans (mul_one _).symm))

theorem eq_of_mem_center (C : Setup S) (P : Sylow 2 X) {a b : X} (ha : a ∈ (P : Subgroup X))
    (hb : b ∈ (P : Subgroup X)) (hac : ∀ x ∈ (P : Subgroup X), a * x = x * a)
    (hbc : ∀ x ∈ (P : Subgroup X), b * x = x * b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow C.D₂.isPGroup_S₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₀ P
  have hP : (P : Subgroup X) = (P₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]; rfl
  have key : ∀ c ∈ (P : Subgroup X), (∀ x ∈ (P : Subgroup X), c * x = x * c) →
      g⁻¹ * c * g = 1 ∨ g⁻¹ * c * g = S.z * C.F.kF := by
    intro c hc hcc
    have hcP₀ : g⁻¹ * c * g ∈ (P₀ : Subgroup X) := by
      rw [hP] at hc
      obtain ⟨d, hd, hdc⟩ := hc
      have : c = g * d * g⁻¹ := by rw [← hdc]; rfl
      rw [this, show g⁻¹ * (g * d * g⁻¹) * g = d by group]
      exact hd
    have hS : ∀ s ∈ C.D₂.S₁, (g⁻¹ * c * g) * s = s * (g⁻¹ * c * g) := by
      intro s hs
      have hgs : g * s * g⁻¹ ∈ (P : Subgroup X) := by
        rw [hP]; exact ⟨s, hP₀ hs, rfl⟩
      have := hcc _ hgs
      calc g⁻¹ * c * g * s = g⁻¹ * (c * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * c) * g := by rw [this]
        _ = s * (g⁻¹ * c * g) := by group
    have hES : S.E (C.F.xF * C.F.yF) ≤ C.D₂.S₁ := by
      rw [C.D₂.S₁_eq]; exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    have hcE : g⁻¹ * c * g ∈ S.E (C.F.xF * C.F.yF) := by
      have hle : ((P₀ : Subgroup X) ⊓ centralizer (S.E (C.F.xF * C.F.yF) : Set X)) ≤
          S.E (C.F.xF * C.F.yF) :=
        le_E_of_le_centralizer (isRefl_xyF C.F) (P₀.isPGroup'.to_le inf_le_left) inf_le_right
      exact hle ⟨hcP₀, mem_centralizer_iff.mpr fun e he => (hS e (hES he)).symm⟩
    have hconj : ∀ s ∈ C.D₂.S₁, s * (g⁻¹ * c * g) * s⁻¹ = g⁻¹ * c * g := fun s hs =>
      by rw [← hS s hs, mul_inv_cancel_right]
    refine C.eq_of_fixed_Et hcE (hconj _ ?_) (hconj _ ?_) (hconj _ ?_)
    · rw [C.D₂.S₁_eq]
      exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _))))
    · rw [C.D₂.S₁_eq]; exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · rw [C.D₂.S₁_eq]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
  have hne : ∀ c : X, c ≠ 1 → g⁻¹ * c * g ≠ 1 := fun c hc h => hc (by
    calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  rcases key a ha hac with h1 | h1
  · exact absurd h1 (hne a ha1)
  rcases key b hb hbc with h2 | h2
  · exact absurd h2 (hne b hb1)
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h1, h2]
    _ = b := by group

theorem z_comm_S₁ {x : X} (hx : x ∈ C.D₁.S₁) : S.z * x = x * S.z := by
  have hle : C.D₁.S₁ ≤ centralizer ({S.z} : Set X) := by
    rw [C.D₁.S₁_eq]
    have hc : ∀ g : X, g * S.z * g⁻¹ = S.z → g ∈ centralizer ({S.z} : Set X) := fun g hg => by
      rw [mem_centralizer_singleton_iff]
      calc g * S.z = g * S.z * g⁻¹ * g := by group
        _ = S.z * g := by rw [hg]
    refine sup_le (sup_le (sup_le (sup_le (fun e he => hc e ?_) (zpowers_le.mpr (hc _ ?_)))
      (zpowers_le.mpr (hc _ ?_))) (zpowers_le.mpr (hc _ ?_))) (zpowers_le.mpr (hc _ ?_))
    · exact conj_eq_of_comm (C.isRefl_y.elemAbelianTwo_E.comm e he S.z (z_mem_E _))
    · exact C.v_E0 C.z_mem_E0
    · exact C.w₁_E0 C.z_mem_E0
    · exact C.w₂_E0 C.z_mem_E0
    · exact conj_eq_of_comm (C.u_comm_B z_mem_B)
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem k_comm_S₁ {x : X} (hx : x ∈ C.D₁.S₁) : C.F.kF * x = x * C.F.kF := by
  have := C.D₁.k_fixed x (C.D₁.S₁_le hx)
  calc C.F.kF * x = x * (x⁻¹ * C.F.kF * x) := by group
    _ = x * C.F.kF := by
      rw [show x⁻¹ * C.F.kF * x = C.F.kF from by
        calc x⁻¹ * C.F.kF * x = x⁻¹ * (x * C.F.kF * x⁻¹) * x := by rw [this]
          _ = C.F.kF := by group]

theorem mem_normalizer_Q₁_of_mem_normalizer_S₁ {n : X} (hn : n ∈ normalizer (C.D₁.S₁ : Set X)) :
    n ∈ normalizer (C.D₁.Q₁ : Set X) :=
  mem_normalizer_of_map_eq (C.D₁.Q₁_char (Or.inr C.hq) n hn)

theorem false_of_normalizer_le
    (h : ∀ n ∈ normalizer (C.D₁.Q₁ : Set X), n ∈ normalizer (C.E₁ : Set X)) : False := by
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow C.D₁.isPGroup_S₁
  have hSP : C.D₁.S₁ = P := eq_sylow_of_normalizer hP fun x hxP hxN => by
    have hxE := h x (C.mem_normalizer_Q₁_of_mem_normalizer_S₁ hxN)
    have hle : C.D₁.S₁ ⊔ zpowers x ≤ normalizer (C.E₁ : Set X) :=
      sup_le C.D₁.S₁_le (zpowers_le.mpr hxE)
    have heq := C.D₁.S₁_maximal _ (isPGroup_sup_zpowers P.isPGroup' hP hxP) le_sup_left hle
    rw [← heq]
    exact mem_sup_right (mem_zpowers x)
  have hzP : S.z ∈ (P : Subgroup X) := by
    rw [← hSP, C.D₁.S₁_eq]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (z_mem_E _))))
  have hkP : C.F.kF ∈ (P : Subgroup X) := by
    rw [← hSP, C.D₁.S₁_eq]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (kF_mem_E _ _))))
  have heq := C.eq_of_mem_center P hzP hkP (fun x hx => C.z_comm_S₁ (hSP ▸ hx))
    (fun x hx => C.k_comm_S₁ (hSP ▸ hx)) S.z_ne_one C.isK_k.ne_one
  exact C.k_not_mem_zpowers_z (heq ▸ mem_zpowers _)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
