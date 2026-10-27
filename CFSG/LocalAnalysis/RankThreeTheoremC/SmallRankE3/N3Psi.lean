module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Q8D8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

theorem dual_V4 (f : Sp4.V4 → ZMod 2) (hf : ∀ a b, f (a + b) = f a + f b) :
    ∃ c : Sp4.V4, ∀ v, f v = Sp4.symp c v := by
  refine ⟨![f (Pi.single 1 1), f (Pi.single 0 1), f (Pi.single 3 1), f (Pi.single 2 1)],
    fun v => ?_⟩
  have f0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero] at h
    revert h
    generalize f 0 = x
    revert x
    decide
  have key : ∀ (i : Fin 4) (a : ZMod 2), f (Pi.single i a) = a * f (Pi.single i 1) := by
    intro i a
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
    · rw [Pi.single_zero, f0, zero_mul]
    · rw [one_mul]
  have hv : v = (Pi.single 0 (v 0) : Fin 4 → ZMod 2) + (Pi.single 1 (v 1) : Fin 4 → ZMod 2) +
      (Pi.single 2 (v 2) : Fin 4 → ZMod 2) + (Pi.single 3 (v 3) : Fin 4 → ZMod 2) := by
    funext i
    fin_cases i <;> simp
  have expand : f v = v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1) +
      v 2 * f (Pi.single 2 1) + v 3 * f (Pi.single 3 1) := by
    conv_lhs => rw [hv]
    rw [hf, hf, hf, key 0 (v 0), key 1 (v 1), key 2 (v 2), key 3 (v 3)]
  rw [expand]
  simp [Sp4.symp]
  ring

open scoped Classical in
@[expose] noncomputable def n3PV {R : Type} [Group R] (g : R) : ZMod 2 :=
  if g = 1 then 0 else 1

@[expose] noncomputable def n3Val {R : Type} [Group R] (s t : R) : ZMod 2 :=
  n3PV (s * t * s⁻¹ * t⁻¹)

theorem n3PV_one {R : Type} [Group R] : n3PV (1 : R) = 0 := by
  simp [n3PV]

theorem n3PV_eq_zero_iff {R : Type} [Group R] (g : R) : n3PV g = 0 ↔ g = 1 := by
  unfold n3PV
  split_ifs with h <;> simp [h]

theorem n3PV_add {R : Type} [Group R] {c : R} (hc1 : c ≠ 1) (hcc : c * c = 1) {x y : R}
    (hx : x = 1 ∨ x = c) (hy : y = 1 ∨ y = c) :
    n3PV (x * y) = n3PV x + n3PV y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [n3PV, hc1, hcc] <;> decide

theorem n3Cm_mul_left {R : Type} [Group R] (s s' t : R)
    (hc : ∀ g : R, g * (s' * t * s'⁻¹ * t⁻¹) = (s' * t * s'⁻¹ * t⁻¹) * g) :
    (s * s') * t * (s * s')⁻¹ * t⁻¹ = (s' * t * s'⁻¹ * t⁻¹) * (s * t * s⁻¹ * t⁻¹) := by
  have h := hc s
  calc (s * s') * t * (s * s')⁻¹ * t⁻¹
      = (s * (s' * t * s'⁻¹ * t⁻¹) * s⁻¹) * (s * t * s⁻¹ * t⁻¹) := by group
    _ = (s' * t * s'⁻¹ * t⁻¹) * (s * t * s⁻¹ * t⁻¹) := by rw [h]; group

theorem n3Cm_mul_right {R : Type} [Group R] (s t t' : R)
    (hd : ∀ g : R, g * (s * t' * s⁻¹ * t'⁻¹) = (s * t' * s⁻¹ * t'⁻¹) * g) :
    s * (t * t') * s⁻¹ * (t * t')⁻¹ = (s * t * s⁻¹ * t⁻¹) * (s * t' * s⁻¹ * t'⁻¹) := by
  have h := hd t
  calc s * (t * t') * s⁻¹ * (t * t')⁻¹
      = (s * t * s⁻¹ * t⁻¹) * (t * (s * t' * s⁻¹ * t'⁻¹) * t⁻¹) := by group
    _ = (s * t * s⁻¹ * t⁻¹) * (s * t' * s⁻¹ * t'⁻¹) := by rw [h]; group

theorem n3Cm_central_left {R : Type} [Group R] {n : R} (hn : n ∈ Subgroup.center R) (t : R) :
    n * t * n⁻¹ * t⁻¹ = 1 := by
  have h : t * n = n * t := Subgroup.mem_center_iff.mp hn t
  rw [← h]
  group

theorem n3Cm_central_right {R : Type} [Group R] (s : R) {m : R}
    (hm : m ∈ Subgroup.center R) : s * m * s⁻¹ * m⁻¹ = 1 := by
  have h : s * m = m * s := Subgroup.mem_center_iff.mp hm s
  rw [h]
  group

theorem n3Val_self {R : Type} [Group R] (s : R) : n3Val s s = 0 := by
  have h : s * s * s⁻¹ * s⁻¹ = 1 := by group
  unfold n3Val
  rw [h, n3PV_one]

theorem n3Val_central_left {R : Type} [Group R] {n : R} (hn : n ∈ Subgroup.center R) (t : R) :
    n3Val n t = 0 := by
  unfold n3Val
  rw [n3Cm_central_left hn t, n3PV_one]

theorem n3Val_central_right {R : Type} [Group R] (s : R) {m : R}
    (hm : m ∈ Subgroup.center R) : n3Val s m = 0 := by
  unfold n3Val
  rw [n3Cm_central_right s hm, n3PV_one]

theorem n3Val_mul_left {R : Type} [Group R] {c : R} (hc1 : c ≠ 1) (hcc : c * c = 1)
    (hcz : ∀ g : R, g * c = c * g)
    (hcm : ∀ s t : R, s * t * s⁻¹ * t⁻¹ = 1 ∨ s * t * s⁻¹ * t⁻¹ = c) (s s' t : R) :
    n3Val (s * s') t = n3Val s t + n3Val s' t := by
  have hc2 : ∀ g : R, g * (s' * t * s'⁻¹ * t⁻¹) = (s' * t * s'⁻¹ * t⁻¹) * g := by
    intro g
    rcases hcm s' t with h | h <;> rw [h]
    · simp
    · exact hcz g
  unfold n3Val
  rw [n3Cm_mul_left s s' t hc2, n3PV_add hc1 hcc (hcm s' t) (hcm s t)]
  exact add_comm _ _

theorem n3Val_mul_right {R : Type} [Group R] {c : R} (hc1 : c ≠ 1) (hcc : c * c = 1)
    (hcz : ∀ g : R, g * c = c * g)
    (hcm : ∀ s t : R, s * t * s⁻¹ * t⁻¹ = 1 ∨ s * t * s⁻¹ * t⁻¹ = c) (s t t' : R) :
    n3Val s (t * t') = n3Val s t + n3Val s t' := by
  have hd : ∀ g : R, g * (s * t' * s⁻¹ * t'⁻¹) = (s * t' * s⁻¹ * t'⁻¹) * g := by
    intro g
    rcases hcm s t' with h | h <;> rw [h]
    · simp
    · exact hcz g
  unfold n3Val
  rw [n3Cm_mul_right s t t' hd, n3PV_add hc1 hcc (hcm s t) (hcm s t')]

open scoped Classical in
theorem n3_core {R : Type} [Group R] (c : R) (hc1 : c ≠ 1) (hcc : c * c = 1)
    (hcen : ∀ s : R, (∀ g : R, g * s = s * g) ↔ (s = 1 ∨ s = c))
    (hcm : ∀ s t : R, s * t * s⁻¹ * t⁻¹ = 1 ∨ s * t * s⁻¹ * t⁻¹ = c)
    (hsq : ∀ s : R, s * s = 1 ∨ s * s = c)
    (hcard : Nat.card R = 32) :
    ∃ Ψ : R →* Multiplicative Sp4.V4, Function.Surjective Ψ ∧
      (∀ s : R, Ψ s = 1 ↔ s = 1 ∨ s = c) ∧
      (∀ s t : R, Sp4.symp (Multiplicative.toAdd (Ψ s)) (Multiplicative.toAdd (Ψ t)) =
        if s * t * s⁻¹ * t⁻¹ = 1 then 0 else 1) := by
  have hcz : ∀ g : R, g * c = c * g := (hcen c).2 (Or.inr rfl)
  have hN : ∀ s : R, s ∈ Subgroup.center R ↔ (s = 1 ∨ s = c) := fun s => by
    rw [Subgroup.mem_center_iff]
    exact hcen s
  have hNcard : Nat.card (Subgroup.center R) = 2 := by
    have hcN : c ∈ Subgroup.center R := (hN c).2 (Or.inr rfl)
    have hne : (1 : Subgroup.center R) ≠ ⟨c, hcN⟩ := by
      intro h
      exact hc1 (congrArg Subtype.val h).symm
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨c, hcN⟩, hne, ?_⟩
    rw [Set.eq_univ_iff_forall]
    rintro ⟨w, hw⟩
    rcases (hN w).1 hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hWcard : Nat.card (R ⧸ Subgroup.center R) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
    rw [hNcard, hcard] at h
    omega
  have hWcomm : ∀ a b : R ⧸ Subgroup.center R, a * b = b * a := by
    intro a b
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine (hN _).2 ?_
    have e : (s * t)⁻¹ * (t * s) = t⁻¹ * s⁻¹ * t * s := by group
    rw [e]
    simpa only [inv_inv] using hcm t⁻¹ s⁻¹
  letI instW : CommGroup (R ⧸ Subgroup.center R) :=
    { (inferInstance : Group (R ⧸ Subgroup.center R)) with mul_comm := hWcomm }
  have hL : ∀ s s' t : R, n3Val (s * s') t = n3Val s t + n3Val s' t :=
    fun s s' t => n3Val_mul_left hc1 hcc hcz hcm s s' t
  have hR : ∀ s t t' : R, n3Val s (t * t') = n3Val s t + n3Val s t' :=
    fun s t t' => n3Val_mul_right hc1 hcc hcz hcm s t t'
  have hLn : ∀ (s t : R) {n : R}, n ∈ Subgroup.center R → n3Val (s * n) t = n3Val s t := by
    intro s t n hn
    rw [hL, n3Val_central_left hn, add_zero]
  have hRm : ∀ (s t : R) {m : R}, m ∈ Subgroup.center R → n3Val s (t * m) = n3Val s t := by
    intro s t m hm
    rw [hR, n3Val_central_right s hm, add_zero]
  have wd : ∀ a₁ b₁ a₂ b₂ : R, QuotientGroup.leftRel (Subgroup.center R) a₁ a₂ →
      QuotientGroup.leftRel (Subgroup.center R) b₁ b₂ → n3Val a₁ b₁ = n3Val a₂ b₂ := by
    intro a₁ b₁ a₂ b₂ ha hb
    have ha' : a₁⁻¹ * a₂ ∈ Subgroup.center R := QuotientGroup.leftRel_apply.mp ha
    have hb' : b₁⁻¹ * b₂ ∈ Subgroup.center R := QuotientGroup.leftRel_apply.mp hb
    obtain ⟨n, hn, rfl⟩ : ∃ n ∈ Subgroup.center R, a₂ = a₁ * n :=
      ⟨a₁⁻¹ * a₂, ha', by group⟩
    obtain ⟨m, hm, rfl⟩ : ∃ m ∈ Subgroup.center R, b₂ = b₁ * m :=
      ⟨b₁⁻¹ * b₂, hb', by group⟩
    rw [hLn _ _ hn, hRm _ _ hm]
  obtain ⟨B, hB⟩ : ∃ B : (R ⧸ Subgroup.center R) → (R ⧸ Subgroup.center R) → ZMod 2,
      ∀ s t : R, B (s : R ⧸ Subgroup.center R) (t : R ⧸ Subgroup.center R) = n3Val s t :=
    ⟨Quotient.lift₂ (s₁ := QuotientGroup.leftRel (Subgroup.center R))
      (s₂ := QuotientGroup.leftRel (Subgroup.center R)) n3Val wd, fun s t => rfl⟩
  have hBsymp : Polar.SympForm B := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hN]
      exact hsq s
    · intro a a' b
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, hB, hB, hB, hL]
    · intro a b b'
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective b'
      rw [← QuotientGroup.mk_mul, hB, hB, hB, hR]
    · intro a
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
      rw [hB]
      exact n3Val_self s
    · intro a ha
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      have h : n3Val s g = 0 := by
        have h' := ha (g : R ⧸ Subgroup.center R)
        rwa [hB] at h'
      unfold n3Val at h
      have h2 := (n3PV_eq_zero_iff _).mp h
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
  obtain ⟨θ, hθ⟩ := Sp4.exists_symplectic_iso hBsymp hWcard
  refine ⟨θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center R)), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨w, rfl⟩ := θ.toEquiv.surjective y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨s, rfl⟩
  · intro s
    show θ (s : R ⧸ Subgroup.center R) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, hN]
  · intro s t
    exact (hθ (s : R ⧸ Subgroup.center R) (t : R ⧸ Subgroup.center R)).trans (hB s t)

theorem psi_exists {S : Subgroup Γ} {z : Γ} (hS : Q8D8Facts S z) :
    ∃ Ψ : ↥S →* Multiplicative Sp4.V4, PsiSpec S z Ψ := by
  obtain ⟨c, hc⟩ : ∃ c : ↥S, (c : Γ) = z := ⟨⟨z, hS.z_mem⟩, rfl⟩
  have hc1 : c ≠ 1 := by
    intro h
    apply hS.z_ne_one
    have h' : (c : Γ) = 1 := congrArg Subtype.val h
    rw [← hc]
    exact h'
  have hcc : c * c = 1 := by
    apply Subtype.ext
    show (c : Γ) * (c : Γ) = 1
    rw [hc]
    exact hS.z_mul_self
  have hcz : ∀ g : ↥S, g * c = c * g := by
    intro g
    apply Subtype.ext
    show (g : Γ) * (c : Γ) = (c : Γ) * (g : Γ)
    rw [hc]
    exact ((hS.center_iff z hS.z_mem).2 (Or.inr rfl) (g : Γ) g.2).symm
  have hcen : ∀ s : ↥S, (∀ g : ↥S, g * s = s * g) ↔ (s = 1 ∨ s = c) := by
    intro s
    have hs := hS.center_iff (s : Γ) s.2
    constructor
    · intro H
      have H' : ∀ s' ∈ S, (s : Γ) * s' = s' * (s : Γ) := by
        intro s' hs'
        exact (congrArg Subtype.val (H ⟨s', hs'⟩)).symm
      rcases hs.1 H' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (h.trans hc.symm))
    · rintro (h | h) g
      · rw [h, one_mul, mul_one]
      · rw [h]
        exact hcz g
  have hcm : ∀ s t : ↥S, s * t * s⁻¹ * t⁻¹ = 1 ∨ s * t * s⁻¹ * t⁻¹ = c := by
    intro s t
    rcases hS.comm_mem (s : Γ) s.2 (t : Γ) t.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr (Subtype.ext ?_)
      rw [hc]
      exact h
  have hsq : ∀ s : ↥S, s * s = 1 ∨ s * s = c := by
    intro s
    rcases hS.sq_mem (s : Γ) s.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr (Subtype.ext ?_)
      rw [hc]
      exact h
  obtain ⟨Ψ, h1, h2, h3⟩ := n3_core c hc1 hcc hcen hcm hsq hS.card_eq
  refine ⟨Ψ, h1, ?_, ?_⟩
  · intro s
    rw [h2 s, ← hc]
    constructor
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  · intro s t
    rw [h3 s t]
    have key : ((s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹ = 1) ↔ (s * t * s⁻¹ * t⁻¹ = 1) := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    by_cases h : s * t * s⁻¹ * t⁻¹ = 1
    · rw [if_pos h, if_pos (key.mpr h)]
    · have h' : ¬ ((s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹ = 1) := fun h'' => h (key.mp h'')
      rw [if_neg h, if_neg h']

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
