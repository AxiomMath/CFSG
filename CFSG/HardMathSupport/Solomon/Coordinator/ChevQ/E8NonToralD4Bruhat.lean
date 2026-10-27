module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Basic
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
public import CFSG.LieType.AlgebraicGroups.CocharacterCurve

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

variable {τ : Tag}

theorem exists_pos_invariant_functional {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {w : WeylGroup τ} (hw3 : w ^ 3 = 1) (hw : KernelPosStable a w) :
    ∃ f : Fin τ.rank → ℤ,
      (∀ α ∈ familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}, 0 < ∑ i, f i * α i) ∧
        ∀ μ : Fin τ.rank → ℤ, ∑ i, f i * (w • μ) i = ∑ i, f i * μ i :=
  exists_pos_smul_invariant_functional (by norm_num) hw3 (fun _ hα => hα.2.2) fun α hα =>
    ⟨(hw α hα.1 hα.2.2).1, (hw α hα.1 hα.2.2).1.1, (hw α hα.1 hα.2.2).2⟩

private theorem torus_conj_mem_rootSpan {L : Type} [Field L] {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {t x : ModGL τ L} (ht : t ∈ torusGroup τ L)
    (hx : x ∈ rootSpan τ L S) : t * x * t⁻¹ ∈ rootSpan τ L S := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [← map_rootSpan_of_forall (f := (MulAut.conj (rootDiagUnit τ l)).toMonoidHom) fun α hα =>
    map_conj_rootDiagUnit_rootSubgroup l (hS α hα)]
  exact ⟨x, hx, rfl⟩

private theorem monomial_conj_mem_rootSpan {L : Type} [Field L] {S T : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) (hT : ∀ α ∈ T, IsRoot τ α) {σ : WeylGroup τ}
    (hST : ∀ α ∈ S, σ • α ∈ T) {t x : ModGL τ L} (ht : t ∈ torusGroup τ L)
    (hx : x ∈ rootSpan τ L S) :
    t * canonicalRep (coxeterSystem τ) L σ * x * (t * canonicalRep (coxeterSystem τ) L σ)⁻¹ ∈
      rootSpan τ L T := by
  have h : canonicalRep (coxeterSystem τ) L σ * x * (canonicalRep (coxeterSystem τ) L σ)⁻¹ ∈
      rootSpan τ L ((fun α => σ • α) '' S) := by
    rw [← (canonical_weyl_root_transport τ L).1 σ S hS]
    exact ⟨x, hx, rfl⟩
  have h' := torus_conj_mem_rootSpan hT ht
    (rootSpan_mono (by rintro _ ⟨α, hα, rfl⟩; exact hST α hα) h)
  have e : t * canonicalRep (coxeterSystem τ) L σ * x * (t * canonicalRep (coxeterSystem τ) L σ)⁻¹ =
      t * (canonicalRep (coxeterSystem τ) L σ * x * (canonicalRep (coxeterSystem τ) L σ)⁻¹) *
        t⁻¹ := by group
  rw [e]
  exact h'

private theorem monomial_conj_mem_torusGroup {L : Type} [Field L] {σ : WeylGroup τ}
    {t x : ModGL τ L} (ht : t ∈ torusGroup τ L) (hx : x ∈ torusGroup τ L) :
    t * canonicalRep (coxeterSystem τ) L σ * x * (t * canonicalRep (coxeterSystem τ) L σ)⁻¹ ∈
      torusGroup τ L := by
  have h := (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) σ) x).1 hx
  have e : t * canonicalRep (coxeterSystem τ) L σ * x * (t * canonicalRep (coxeterSystem τ) L σ)⁻¹ =
      t * (canonicalRep (coxeterSystem τ) L σ * x * (canonicalRep (coxeterSystem τ) L σ)⁻¹) *
        t⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem ht h) (inv_mem ht)

private theorem exists_torus_mul_canonicalRep_mul_mul_inv {L : Type} [Field L]
    {t₁ t₂ : ModGL τ L} (ht₁ : t₁ ∈ torusGroup τ L) (ht₂ : t₂ ∈ torusGroup τ L)
    (w₁ w w₂ : WeylGroup τ) :
    ∃ k ∈ torusGroup τ L, t₁ * canonicalRep (coxeterSystem τ) L w₁ *
      canonicalRep (coxeterSystem τ) L w * (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹ =
        k * canonicalRep (coxeterSystem τ) L (w₁ * w * w₂⁻¹) := by
  have hN : ∀ (u : WeylGroup τ) {x : ModGL τ L}, x ∈ torusGroup τ L → ∃ c ∈ torusGroup τ L,
      canonicalRep (coxeterSystem τ) L u * x = c * canonicalRep (coxeterSystem τ) L u :=
    fun u x hx => ⟨_, (Subgroup.mem_normalizer_iff.1
      (canonicalRep_mem_normalizer (R := L) u) x).1 hx, by group⟩
  obtain ⟨k₁, hk₁, e₁⟩ := canonicalRep_mul_mem (R := L) w₁ w
  obtain ⟨k₀, hk₀, e₀⟩ := canonicalRep_mul_mem (R := L) w₂⁻¹ w₂
  rw [inv_mul_cancel, canonicalRep_one, mul_one] at e₀
  obtain ⟨k₂, hk₂, e₂⟩ := canonicalRep_mul_mem (R := L) (w₁ * w) w₂⁻¹
  obtain ⟨c₁, hc₁, f₁⟩ := hN (w₁ * w) (inv_mem hk₀)
  obtain ⟨c₂, hc₂, f₂⟩ := hN (w₁ * w * w₂⁻¹) (inv_mem ht₂)
  have hinv : (canonicalRep (coxeterSystem τ) L w₂)⁻¹ =
      k₀⁻¹ * canonicalRep (coxeterSystem τ) L w₂⁻¹ := by
    rw [eq_inv_mul_iff_mul_eq, ← e₀, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨t₁ * k₁ * c₁ * k₂ * c₂, mul_mem (mul_mem (mul_mem (mul_mem ht₁ hk₁) hc₁) hk₂) hc₂, ?_⟩
  calc _ = t₁ * (canonicalRep (coxeterSystem τ) L w₁ * canonicalRep (coxeterSystem τ) L w) *
        (canonicalRep (coxeterSystem τ) L w₂)⁻¹ * t₂⁻¹ := by group
    _ = t₁ * k₁ * (canonicalRep (coxeterSystem τ) L (w₁ * w) * k₀⁻¹) *
        canonicalRep (coxeterSystem τ) L w₂⁻¹ * t₂⁻¹ := by rw [e₁, hinv]; group
    _ = t₁ * k₁ * c₁ * (canonicalRep (coxeterSystem τ) L (w₁ * w) *
        canonicalRep (coxeterSystem τ) L w₂⁻¹) * t₂⁻¹ := by rw [f₁]; group
    _ = t₁ * k₁ * c₁ * k₂ * (canonicalRep (coxeterSystem τ) L (w₁ * w * w₂⁻¹) * t₂⁻¹) := by
        rw [e₂]; group
    _ = _ := by rw [f₂]; group

private theorem smul_mem_inversionSet {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {w w₁ w₂ : WeylGroup τ} (hw : w ∈ familyStabilizer a)
    (hw₁ : KernelPosStable a w₁) (hw₂ : KernelPosStable a w₂) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ familyKernel a ∩ inversionSet w) : w₂ • γ ∈ inversionSet (w₁ * w * w₂⁻¹) := by
  obtain ⟨hγK, hγr, hγpos, -, hγneg⟩ := hγ
  have hwγ : -(w • γ) ∈ familyKernel a := by
    refine ⟨IsRoot.neg (IsRoot.smul hγr w), fun i => ?_⟩
    have h := rootChar_add (a i) (-(w • γ)) (w • γ)
    rw [neg_add_cancel, rootChar_zero, hw i γ, hγK.2 i, mul_one] at h
    exact h.symm
  have hpos : 0 < height (-(w • γ)) := by
    rw [height_neg]
    linarith
  have h₁ := (hw₁ _ hwγ hpos).2
  rw [smul_neg, height_neg] at h₁
  refine ⟨IsRoot.smul hγr w₂, (hw₂ γ hγK hγpos).2, ?_⟩
  show IsRoot τ ((w₁ * w * w₂⁻¹) • w₂ • γ) ∧ height ((w₁ * w * w₂⁻¹) • w₂ • γ) < 0
  rw [mul_smul, mul_smul, inv_smul_smul]
  exact ⟨IsRoot.smul (IsRoot.smul hγr w) w₁, by linarith⟩

theorem familyGroup_conj_monomial_factors {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {m t₁ t₂ : ModGL τ L} {w₁ w₂ : WeylGroup τ}
    (hm : m ∈ familyGroup (K := L) a) (ht₁ : t₁ ∈ torusGroup τ L) (ht₂ : t₂ ∈ torusGroup τ L)
    (hw₁ : KernelPosStable a w₁) (hw₂ : KernelPosStable a w₂)
    (hconj : m * (t₂ * canonicalRep (coxeterSystem τ) L w₂) * m⁻¹ =
      t₁ * canonicalRep (coxeterSystem τ) L w₁) :
    ∃ u ∈ rootSpan τ L (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ t ∈ torusGroup τ L, ∃ w ∈ familyStabilizer a,
        ∃ v ∈ rootSpan τ L (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
          m = u * (t * canonicalRep (coxeterSystem τ) L w) * v ∧
            Commute (t₁ * canonicalRep (coxeterSystem τ) L w₁) u ∧
            Commute (t₂ * canonicalRep (coxeterSystem τ) L w₂) v ∧
            (t * canonicalRep (coxeterSystem τ) L w) * (t₂ * canonicalRep (coxeterSystem τ) L w₂) *
              (t * canonicalRep (coxeterSystem τ) L w)⁻¹ =
                t₁ * canonicalRep (coxeterSystem τ) L w₁ := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    familyCentralizer_factors τ L a m (familyGroup_le_familyCentralizer a hm)
  have hProot : ∀ α ∈ familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}, IsRoot τ α :=
    fun α hα => hα.2.1
  have hPP : ∀ α ∈ familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α},
      w₁ • α ∈ familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α} := fun α hα =>
    ⟨(hw₁ α hα.1 hα.2.2).1, (hw₁ α hα.1 hα.2.2).1.1, (hw₁ α hα.1 hα.2.2).2⟩
  have hPU : familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α} ⊆
      {α | IsRoot τ α ∧ 0 < height α} := Set.inter_subset_right
  have hz₁h := monomial_conj_mem_torusGroup (σ := w₁) ht₁ hh
  have hz₁u := monomial_conj_mem_rootSpan hProot hProot hPP ht₁ hu
  have hz₂v := monomial_conj_mem_rootSpan (T := inversionSet (w₁ * w * w₂⁻¹))
    (fun α hα => hα.1.1) (fun α hα => hα.1) (fun γ hγ => smul_mem_inversionSet hw hw₁ hw₂ hγ)
    ht₂ hv
  obtain ⟨k, hk, hkn⟩ := exists_torus_mul_canonicalRep_mul_mul_inv ht₁ ht₂ w₁ w w₂
  have hku : k⁻¹ * (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
      (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) * k ∈ posUnipotent τ L := by
    have h' := torus_conj_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hα.1)
      (inv_mem hk) (rootSpan_mono hPU hz₁u)
    rwa [inv_inv] at h'
  have heq : h * u * canonicalRep (coxeterSystem τ) L w * v =
      (t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
        (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹ * k) *
      (k⁻¹ * (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
        (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) * k) *
      canonicalRep (coxeterSystem τ) L (w₁ * w * w₂⁻¹) *
      (t₂ * canonicalRep (coxeterSystem τ) L w₂ * v *
        (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹) := by
    calc h * u * canonicalRep (coxeterSystem τ) L w * v =
        t₁ * canonicalRep (coxeterSystem τ) L w₁ *
          (h * u * canonicalRep (coxeterSystem τ) L w * v) *
          (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹ := by
          rw [← hconj]
          group
      _ = (t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
            (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
            (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁ * canonicalRep (coxeterSystem τ) L w *
            (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹) *
          (t₂ * canonicalRep (coxeterSystem τ) L w₂ * v *
            (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹) := by group
      _ = (t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
            (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
            (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
          (k * canonicalRep (coxeterSystem τ) L (w₁ * w * w₂⁻¹)) *
          (t₂ * canonicalRep (coxeterSystem τ) L w₂ * v *
            (t₂ * canonicalRep (coxeterSystem τ) L w₂)⁻¹) := by rw [hkn]
      _ = _ := by group
  obtain ⟨-, hh', hu', hv'⟩ := bruhat_factor_unique τ L w (w₁ * w * w₂⁻¹) h _ u _ v _ hh
    (mul_mem hz₁h hk) (rootSpan_mono hPU hu) hku (rootSpan_mono Set.inter_subset_right hv) hz₂v
    heq
  have e₁ : t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
      (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹ = h * k⁻¹ := eq_mul_inv_of_mul_eq hh'.symm
  have e₂ : t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
      (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹ = k * u * k⁻¹ := by
    calc _ = k * (k⁻¹ * (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) * k) * k⁻¹ := by group
      _ = k * u * k⁻¹ := by rw [← hu']
  have hc₁ : Commute (t₁ * canonicalRep (coxeterSystem τ) L w₁) (h * u * h⁻¹) := by
    refine mul_inv_eq_iff_eq_mul.1 ?_
    calc t₁ * canonicalRep (coxeterSystem τ) L w₁ * (h * u * h⁻¹) *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹ =
        (t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
        (t₁ * canonicalRep (coxeterSystem τ) L w₁ * u *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹) *
        (t₁ * canonicalRep (coxeterSystem τ) L w₁ * h *
          (t₁ * canonicalRep (coxeterSystem τ) L w₁)⁻¹)⁻¹ := by group
      _ = h * u * h⁻¹ := by rw [e₁, e₂]; group
  have hc₂ : Commute (t₂ * canonicalRep (coxeterSystem τ) L w₂) v :=
    mul_inv_eq_iff_eq_mul.1 hv'.symm
  have hv2 : v * (t₂ * canonicalRep (coxeterSystem τ) L w₂) * v⁻¹ =
      t₂ * canonicalRep (coxeterSystem τ) L w₂ := mul_inv_eq_of_eq_mul hc₂.eq.symm
  have hn : h * canonicalRep (coxeterSystem τ) L w * (t₂ * canonicalRep (coxeterSystem τ) L w₂) *
      (h * canonicalRep (coxeterSystem τ) L w)⁻¹ = t₁ * canonicalRep (coxeterSystem τ) L w₁ := by
    calc _ = (h * u * h⁻¹)⁻¹ * (h * u * canonicalRep (coxeterSystem τ) L w *
          (v * (t₂ * canonicalRep (coxeterSystem τ) L w₂) * v⁻¹) *
          (h * u * canonicalRep (coxeterSystem τ) L w)⁻¹) * (h * u * h⁻¹) := by
          rw [hv2]
          group
      _ = (h * u * h⁻¹)⁻¹ * (h * u * canonicalRep (coxeterSystem τ) L w * v *
          (t₂ * canonicalRep (coxeterSystem τ) L w₂) *
          (h * u * canonicalRep (coxeterSystem τ) L w * v)⁻¹) * (h * u * h⁻¹) := by group
      _ = (h * u * h⁻¹)⁻¹ * (t₁ * canonicalRep (coxeterSystem τ) L w₁) * (h * u * h⁻¹) := by
          rw [hconj]
      _ = t₁ * canonicalRep (coxeterSystem τ) L w₁ := by
          rw [hc₁.symm.inv_left.eq, inv_mul_cancel_right]
  have hIP : familyKernel a ∩ inversionSet w ⊆
      familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α} := fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩
  exact ⟨h * u * h⁻¹, torus_conj_mem_rootSpan hProot hh hu, h, hh, w, hw, v,
    rootSpan_mono hIP hv, by group, hc₁, hc₂, hn⟩

theorem exists_closedIdentityComponent_mul_monomial {L : Type} [Field L] [IsAlgClosed L]
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) {m t₁ t₂ : ModGL τ L} {w₁ w₂ : WeylGroup τ}
    (hm : m ∈ familyGroup (K := L) a) (ht₁ : t₁ ∈ torusGroup τ L) (ht₂ : t₂ ∈ torusGroup τ L)
    (hw₁ : KernelPosStable a w₁) (hw₂ : KernelPosStable a w₂) (hw₁3 : w₁ ^ 3 = 1)
    (hw₂3 : w₂ ^ 3 = 1)
    (hconj : m * (t₂ * canonicalRep (coxeterSystem τ) L w₂) * m⁻¹ =
      t₁ * canonicalRep (coxeterSystem τ) L w₁) :
    ∃ y ∈ closedIdentityComponent (familyGroup (K := L) a ⊓
        Subgroup.centralizer {t₁ * canonicalRep (coxeterSystem τ) L w₁}),
      ∃ t ∈ torusGroup τ L, ∃ w ∈ familyStabilizer a,
        m = y * (t * canonicalRep (coxeterSystem τ) L w) ∧
          (t * canonicalRep (coxeterSystem τ) L w) * (t₂ * canonicalRep (coxeterSystem τ) L w₂) *
            (t * canonicalRep (coxeterSystem τ) L w)⁻¹ =
              t₁ * canonicalRep (coxeterSystem τ) L w₁ := by
  obtain ⟨u, hu, t, ht, w, hw, v, hv, rfl, hc₁, hc₂, hn⟩ :=
    familyGroup_conj_monomial_factors a hm ht₁ ht₂ hw₁ hw₂ hconj
  obtain ⟨f₁, hf₁, hf₁w⟩ := exists_pos_invariant_functional a hw₁3 hw₁
  obtain ⟨f₂, hf₂, hf₂w⟩ := exists_pos_invariant_functional a hw₂3 hw₂
  have hProot : ∀ α ∈ familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}, IsRoot τ α :=
    fun α hα => hα.2.1
  have hUM : ∀ x ∈ rootSpan τ L (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      x ∈ familyGroup (K := L) a := fun x hx =>
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hx)
  have hTM : ∀ x ∈ torusGroup τ L, x ∈ familyGroup (K := L) a := fun x hx =>
    Subgroup.mem_sup_left hx
  have hZ : ∀ x ∈ familyGroup (K := L) a, Commute (t₁ * canonicalRep (coxeterSystem τ) L w₁) x →
      x ∈ familyGroup (K := L) a ⊓
        Subgroup.centralizer {t₁ * canonicalRep (coxeterSystem τ) L w₁} := fun x hx hc =>
    Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hc.eq.symm⟩
  have hu' : u ∈ closedIdentityComponent (familyGroup (K := L) a ⊓
      Subgroup.centralizer {t₁ * canonicalRep (coxeterSystem τ) L w₁}) := by
    have h := conj_mem_closedIdentityComponent_of_contract (g := 1) hProot f₁ hf₁ hu
      (fun s => by
        rw [one_mul, inv_one, mul_one]
        exact hZ _ (hTM _ (rootDiagUnit_mem_torusGroup _))
          (commute_rootDiagUnit_monomial ht₁ f₁ hf₁w s).symm)
      (by
        rw [one_mul, inv_one, mul_one]
        exact hZ _ (hUM _ hu) hc₁)
    rwa [one_mul, inv_one, mul_one] at h
  have hnM : ∀ x ∈ familyGroup (K := L) a, t * canonicalRep (coxeterSystem τ) L w * x *
      (t * canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ familyGroup (K := L) a := by
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.1
      (canonicalRep_mem_normalizer_familyGroup (K := L) hw) x).1 hx
    have e : t * canonicalRep (coxeterSystem τ) L w * x *
        (t * canonicalRep (coxeterSystem τ) L w)⁻¹ =
          t * (canonicalRep (coxeterSystem τ) L w * x *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * t⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hTM _ ht) h1) (inv_mem (hTM _ ht))
  have hnC : ∀ x, Commute (t₂ * canonicalRep (coxeterSystem τ) L w₂) x →
      Commute (t₁ * canonicalRep (coxeterSystem τ) L w₁) (t * canonicalRep (coxeterSystem τ) L w *
        x * (t * canonicalRep (coxeterSystem τ) L w)⁻¹) := by
    intro x hx
    rw [← hn]
    have h := hx.map (MulAut.conj (t * canonicalRep (coxeterSystem τ) L w))
    simp only [MulAut.conj_apply] at h
    exact h
  have hv' := conj_mem_closedIdentityComponent_of_contract
    (Z := familyGroup (K := L) a ⊓
      Subgroup.centralizer {t₁ * canonicalRep (coxeterSystem τ) L w₁})
    hProot f₂ hf₂ hv
    (fun s => hZ _ (hnM _ (hTM _ (rootDiagUnit_mem_torusGroup _)))
      (hnC _ (commute_rootDiagUnit_monomial ht₂ f₂ hf₂w s).symm))
    (hZ _ (hnM _ (hUM _ hv)) (hnC _ hc₂))
  exact ⟨u * (t * canonicalRep (coxeterSystem τ) L w * v *
    (t * canonicalRep (coxeterSystem τ) L w)⁻¹), mul_mem hu' hv', t, ht, w, hw, by group, hn⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
