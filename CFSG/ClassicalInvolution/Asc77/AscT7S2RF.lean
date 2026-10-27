module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthAniso
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped MatrixGroups

section Six

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem elementaryGroup_le_of_six (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (h7 : 7 ≤ Module.finrank K V) {t₁ t₂ : V ≃ₗ[K] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {H : Subgroup (V ≃ₗ[K] V)}
    (hH₁ : ∀ ε : K, ε * ε = 1 → elemOn Q (eigenSub t₁ ε) ≤ H)
    (hH₂ : ∀ δ : K, δ * δ = 1 → elemOn Q (eigenSub t₂ δ) ≤ H)
    (hH₃ : ∀ c : K, c * c = 1 → elemOn Q (eigenSub (t₁ * t₂) c) ≤ H) :
    elementaryGroup Q ≤ H := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  by_cases hiso : ∃ e : V, e ≠ 0 ∧ Q e = 0 ∧ ∃ ε δ : K, t₁ e = ε • e ∧ t₂ e = δ • e
  · obtain ⟨e, he0, hQe, ε, δ, he1, he2⟩ := hiso
    have hε : ε * ε = 1 := eigenvalue_sq_eq_one ht₁ he0 he1
    have hδ : δ * δ = 1 := eigenvalue_sq_eq_one ht₂ he0 he2
    obtain ⟨P₀, hP₀e, hP₀f₁, hP₀f₂⟩ :=
      exists_hypPair_joint h2 hQ h₁ h₂ ht₁ ht₂ hc hε hδ hQe he0 he1 he2
    exact elementaryGroup_le_of_eigen h2 hQ (by omega) h₁ h₂ ht₁ ht₂ hc hε hδ P₀
      (by rw [hP₀e]; exact he1) hP₀f₁ (by rw [hP₀e]; exact he2) hP₀f₂
      (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) (hH₁ ε hε) (hH₂ δ hδ)
      (hH₃ (ε * δ) (by linear_combination (δ * δ) * hε + hδ))
  · push Not at hiso
    exact orthGenAniso K V Q hQ hodd h5 h7 t₁ t₂ h₁ h₂ ht₁ ht₂ hc
      (fun x ε δ h1 h2' hQx => by
        by_contra hx0
        exact hiso x hx0 hQx ε δ h1 h2') H hH₁ hH₂ hH₃

end Six

section Normalizer

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def normE (Q : QuadraticForm K V) (L : Subgroup (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.normalizer (L : Set (V ≃ₗ[K] V)) ⊓ elementaryGroup Q

theorem le_normE {L : Subgroup (V ≃ₗ[K] V)} (hL : L ≤ elementaryGroup Q) : L ≤ normE Q L :=
  le_inf Subgroup.le_normalizer hL

theorem mem_normE_of_commute {L : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hg : g ∈ elementaryGroup Q) (hc : ∀ h ∈ L, g * h = h * g) : g ∈ normE Q L :=
  ⟨Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun h hh => (hc h hh).symm), hg⟩

theorem La_neg_one_of_mem_span' (F : Frame Q) {x : V} (hx : x ∈ F.span) :
    F.La (-1) x = (-1 : K) • x := by
  rw [Frame.La_neg_one_apply, ← (Frame.mem_span_iff F).mp hx, two_smul]
  module

theorem eichler_mem_normE_perp (F : Frame Q) {u w : V} (hu : u ∈ F.perp) (hw : w ∈ F.perp) :
    eichler Q u w ∈ normE Q F.La.range := by
  refine mem_normE_of_commute (eichler_mem_elementaryGroup Q u w) ?_
  rintro _ ⟨A, rfl⟩
  have hgO := Frame.La_mem_orthogonalGroup F A
  have h := eichler_conj hgO u w
  rw [Frame.La_apply_of_coords_eq_zero F A ((Frame.mem_perp_iff F).mp hu),
    Frame.La_apply_of_coords_eq_zero F A ((Frame.mem_perp_iff F).mp hw)] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem eichler_mem_normE_span (h2 : (2 : K) ≠ 0) (F : Frame Q) {u w : V} (hu : u ∈ F.span)
    (hw : w ∈ F.span) : eichler Q u w ∈ normE Q F.La.range := by
  set g₀ := eichler Q u ((2 : K)⁻¹ • w) with hg₀
  have hsq : g₀ * g₀ = eichler Q u w := by
    by_cases h : Q u = 0 ∧ polar Q u w = 0
    · have h' : polar Q u ((2 : K)⁻¹ • w) = 0 := by rw [polar_smul_right_eq, h.2, mul_zero]
      rw [hg₀, eichler_mul h' h', ← two_smul K ((2 : K)⁻¹ • w), smul_smul, mul_inv_cancel₀ h2,
        one_smul]
    · have h' : ¬ (Q u = 0 ∧ polar Q u ((2 : K)⁻¹ • w) = 0) := by
        rintro ⟨h1, h3⟩
        apply h
        refine ⟨h1, ?_⟩
        rw [polar_smul_right_eq] at h3
        exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)
      rw [hg₀, eichler_of_not h, eichler_of_not h', mul_one]
  have hg₀O := eichler_mem_orthogonalGroup Q u ((2 : K)⁻¹ • w)
  have hcomm : F.La (-1) * g₀ = g₀ * F.La (-1) :=
    comm_of_scalar_elemOn (Frame.La_mem_orthogonalGroup F (-1)) (ε := (-1 : K))
      (by norm_num) (fun x hx => La_neg_one_of_mem_span' F hx)
      (eichler_mem_elemOn hu (F.span.smul_mem _ hw))
  have key : conjSubgroup (g₀ * g₀) F.La.range = F.La.range := by
    rw [conjSubgroup_mul]
    rcases Frame.conjSubgroup_La_range h2 hg₀O hcomm.symm with ⟨-, h1, -⟩ | ⟨-, h1, h3⟩
    · rw [h1, h1]
    · rw [h1, h3]
  rw [hsq] at key
  exact ⟨mem_normalizer_of_conjSubgroup_eq key, eichler_mem_elementaryGroup Q u w⟩

theorem mem_perp_of_eigenSub_one (h2 : (2 : K) ≠ 0) (F : Frame Q) {x : V}
    (hx : x ∈ eigenSub (F.La (-1)) 1) : x ∈ F.perp := by
  have h : x ∈ posSpace (F.La (-1)) := by
    rw [posSpace, Module.End.mem_eigenspace_iff]
    exact hx
  rwa [posSpace_La_neg_one h2] at h

theorem mem_span_of_eigenSub_neg_one (h2 : (2 : K) ≠ 0) (F : Frame Q) {x : V}
    (hx : x ∈ eigenSub (F.La (-1)) (-1)) : x ∈ F.span := by
  have h : x ∈ negSpace (F.La (-1)) := by
    rw [negSpace, Module.End.mem_eigenspace_iff]
    exact hx
  rwa [negSpace_La_neg_one h2] at h

theorem elemOn_eigenSub_le_normE (h2 : (2 : K) ≠ 0) (F : Frame Q) {ε : K} (hε : ε * ε = 1) :
    elemOn Q (eigenSub (F.La (-1)) ε) ≤ normE Q F.La.range := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
  rcases mul_self_eq_one_iff.mp hε with rfl | rfl
  · exact eichler_mem_normE_perp F (mem_perp_of_eigenSub_one h2 F hu)
      (mem_perp_of_eigenSub_one h2 F hw)
  · exact eichler_mem_normE_span h2 F (mem_span_of_eigenSub_neg_one h2 F hu)
      (mem_span_of_eigenSub_neg_one h2 F hw)

end Normalizer

section Swap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_jointSub_sup_of_eigenSub_mul (h2 : (2 : K) ≠ 0) {t₁ t₂ : V ≃ₗ[K] V}
    (ht₁ : t₁ * t₁ = 1) (hc : t₁ * t₂ = t₂ * t₁) {c : K} {x : V}
    (hx : x ∈ eigenSub (t₁ * t₂) c) :
    x ∈ jointSub t₁ t₂ 1 c ⊔ jointSub t₁ t₂ (-1) (-c) := by
  have e1 : ∀ y, t₁ (t₁ y) = y := fun y => by
    have := congrArg (fun g : V ≃ₗ[K] V => g y) ht₁
    simpa using this
  have ec : ∀ y, t₁ (t₂ y) = t₂ (t₁ y) := fun y => by
    have := congrArg (fun g : V ≃ₗ[K] V => g y) hc
    simpa using this
  have hx' : t₁ (t₂ x) = c • x := hx
  have h2x : t₂ x = c • t₁ x := by
    have := congrArg t₁ hx'
    rwa [e1, map_smul] at this
  have hx'' : t₂ (t₁ x) = c • x := by rw [← ec, hx']
  have h2a : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have h1 : (2 : K)⁻¹ • (x + t₁ x) ∈ jointSub t₁ t₂ 1 c := by
    rw [mem_jointSub]
    constructor
    · simp only [map_smul, map_add, e1]
      module
    · simp only [map_smul, map_add, hx'', h2x]
      module
  have h3 : (2 : K)⁻¹ • (x - t₁ x) ∈ jointSub t₁ t₂ (-1) (-c) := by
    rw [mem_jointSub]
    constructor
    · simp only [map_smul, map_sub, e1]
      module
    · simp only [map_smul, map_sub, hx'', h2x]
      module
  refine Submodule.mem_sup.mpr ⟨_, h1, _, h3, ?_⟩
  rw [← smul_add]
  have : x + t₁ x + (x - t₁ x) = (2 : K) • x := by module
  rw [this, smul_smul, h2a, one_smul]

theorem mem_negSpace_iff' {i : V ≃ₗ[K] V} {x : V} : x ∈ negSpace i ↔ i x = (-1 : K) • x := by
  rw [negSpace, Module.End.mem_eigenspace_iff]
  rfl

theorem mem_posSpace_iff' {i : V ≃ₗ[K] V} {x : V} : x ∈ posSpace i ↔ i x = (1 : K) • x := by
  rw [posSpace, Module.End.mem_eigenspace_iff]
  rfl

theorem jointSub_neg_neg (t₁ t₂ : V ≃ₗ[K] V) :
    jointSub t₁ t₂ (-1) (-1) = negSpace t₁ ⊓ negSpace t₂ := by
  ext x
  rw [Submodule.mem_inf, mem_negSpace_iff', mem_negSpace_iff', mem_jointSub]

theorem jointSub_one_neg (t₁ t₂ : V ≃ₗ[K] V) :
    jointSub t₁ t₂ 1 (-1) = posSpace t₁ ⊓ negSpace t₂ := by
  ext x
  rw [Submodule.mem_inf, mem_posSpace_iff', mem_negSpace_iff', mem_jointSub]

variable [FiniteDimensional K V]

theorem inv_mem_of_map_le {U U' : Submodule K V} (g : V ≃ₗ[K] V) (hg : ∀ x ∈ U, g x ∈ U')
    (hdim : Module.finrank K ↥U = Module.finrank K ↥U') : ∀ y ∈ U', g⁻¹ y ∈ U := by
  have hle : U.map (g : V →ₗ[K] V) ≤ U' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hd : Module.finrank K ↥(U.map (g : V →ₗ[K] V)) = Module.finrank K ↥U' := by
    rw [← hdim]
    exact LinearEquiv.finrank_map_eq g U
  have heq := Submodule.eq_of_le_of_finrank_eq hle hd
  intro y hy
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

variable [Finite K]

theorem elementaryGroup_le_of_swap (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (h7 : 7 ≤ Module.finrank K V) {t₁ t₂ g : V ≃ₗ[K] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1)
    (ht₂ : t₂ * t₂ = 1) (hc : t₁ * t₂ = t₂ * t₁) {H : Subgroup (V ≃ₗ[K] V)}
    (hH₁ : ∀ ε : K, ε * ε = 1 → elemOn Q (eigenSub t₁ ε) ≤ H)
    (hH₂ : ∀ δ : K, δ * δ = 1 → elemOn Q (eigenSub t₂ δ) ≤ H) (hgH : g ∈ H)
    (hfix : ∀ x, t₂ x = x → g x = x)
    (hswap : ∀ x, t₁ x = (-1 : K) • x → t₂ x = (-1 : K) • x →
      t₁ (g x) = (1 : K) • g x ∧ t₂ (g x) = (-1 : K) • g x)
    (hswap' : ∀ y, t₁ y = (1 : K) • y → t₂ y = (-1 : K) • y →
      t₁ (g⁻¹ y) = (-1 : K) • g⁻¹ y ∧ t₂ (g⁻¹ y) = (-1 : K) • g⁻¹ y) :
    elementaryGroup Q ≤ H := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have hginv : ∀ y ∈ jointSub t₁ t₂ 1 (-1), g⁻¹ y ∈ jointSub t₁ t₂ (-1) (-1) :=
    fun y hy => hswap' y hy.1 hy.2
  have hgO' : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hgO
  refine elementaryGroup_le_of_six hQ hodd h5 h7 h₁ h₂ ht₁ ht₂ hc hH₁ hH₂ ?_
  intro c hc2
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  ·
    have hsub : eigenSub (t₁ * t₂) 1 ≤ jointSub t₁ t₂ 1 1 ⊔ jointSub t₁ t₂ (-1) (-1) :=
      fun x hx => mem_jointSub_sup_of_eigenSub_mul h2 ht₁ hc hx
    refine (elemOn_mono hsub).trans ?_
    intro h hh
    have hS : ∀ x ∈ jointSub t₁ t₂ 1 1 ⊔ jointSub t₁ t₂ (-1) (-1),
        g x ∈ jointSub t₁ t₂ 1 1 ⊔ jointSub t₁ t₂ 1 (-1) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      refine Submodule.add_mem_sup ?_ (hswap b hb.1 hb.2)
      rw [hfix a (by simpa using (mem_jointSub.mp ha).2)]
      exact ha
    have hS' : elemOn Q (jointSub t₁ t₂ 1 1 ⊔ jointSub t₁ t₂ 1 (-1)) ≤ H := by
      refine (elemOn_mono ?_).trans (hH₁ 1 (by norm_num))
      exact sup_le (fun x hx => hx.1) fun x hx => hx.1
    have h3 := hS' (conj_mem_elemOn_of_le hgO hS hh)
    have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hgH) h3) hgH
  ·
    have hsub : eigenSub (t₁ * t₂) (-1) ≤ jointSub t₁ t₂ 1 (-1) ⊔ jointSub t₁ t₂ (-1) 1 := by
      intro x hx
      have := mem_jointSub_sup_of_eigenSub_mul h2 ht₁ hc hx
      rwa [neg_neg] at this
    refine (elemOn_mono hsub).trans ?_
    intro h hh
    have hS : ∀ x ∈ jointSub t₁ t₂ 1 (-1) ⊔ jointSub t₁ t₂ (-1) 1,
        g⁻¹ x ∈ jointSub t₁ t₂ (-1) (-1) ⊔ jointSub t₁ t₂ (-1) 1 := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      refine Submodule.add_mem_sup (hginv a ha) ?_
      have hgb : g b = b := hfix b (by simpa using (mem_jointSub.mp hb).2)
      have e : g⁻¹ b = b := by
        calc g⁻¹ b = g⁻¹ (g b) := by rw [hgb]
          _ = b := by simp
      rw [e]
      exact hb
    have hS' : elemOn Q (jointSub t₁ t₂ (-1) (-1) ⊔ jointSub t₁ t₂ (-1) 1) ≤ H := by
      refine (elemOn_mono ?_).trans (hH₁ (-1) (by norm_num))
      exact sup_le (fun x hx => hx.1) fun x hx => hx.1
    have h3 := hS' (conj_mem_elemOn_of_le hgO' hS hh)
    have e : h = g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hgH h3) (H.inv_mem hgH)

end Swap

section Frames

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem elementaryGroup_le_normE_sup (hQ : (polarBilin Q).Nondegenerate)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (h7 : 7 ≤ Module.finrank K V)
    (F₁ F₂ : Frame Q) (hc : F₁.La (-1) * F₂.La (-1) = F₂.La (-1) * F₁.La (-1))
    (A : SL(2, K))
    (hA : ∀ x ∈ negSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1)),
      F₂.La A x ∈ posSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1)))
    (hA' : ∀ x ∈ posSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1)),
      F₂.La A⁻¹ x ∈ negSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1))) :
    elementaryGroup Q ≤ normE Q F₁.La.range ⊔ normE Q F₂.La.range := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have hL₂ : F₂.La.range ≤ elementaryGroup Q :=
    (IsFundamental.of_frame F₂).le_elementaryGroup
  refine elementaryGroup_le_of_swap hQ hodd h5 h7 (Frame.La_mem_orthogonalGroup F₁ (-1))
    (Frame.La_mem_orthogonalGroup F₂ (-1)) (Frame.La_mem_orthogonalGroup F₂ A)
    (Frame.La_neg_one_mul_self F₁) (Frame.La_neg_one_mul_self F₂) hc
    (H := normE Q F₁.La.range ⊔ normE Q F₂.La.range)
    (fun ε hε => (elemOn_eigenSub_le_normE h2 F₁ hε).trans le_sup_left)
    (fun δ hδ => (elemOn_eigenSub_le_normE h2 F₂ hδ).trans le_sup_right)
    (Subgroup.mem_sup_right (le_normE hL₂ ⟨A, rfl⟩)) ?_ ?_ ?_
  · intro x hx
    have hx' : x ∈ F₂.perp :=
      mem_perp_of_eigenSub_one h2 F₂ (by rw [mem_eigenSub, one_smul]; exact hx)
    exact Frame.La_apply_of_coords_eq_zero F₂ A ((Frame.mem_perp_iff F₂).mp hx')
  · intro x hx1 hx2
    have h := hA x ⟨mem_negSpace_iff'.mpr hx1, mem_negSpace_iff'.mpr hx2⟩
    exact ⟨mem_posSpace_iff'.mp h.1, mem_negSpace_iff'.mp h.2⟩
  · intro y hy1 hy2
    have h := hA' y ⟨mem_posSpace_iff'.mpr hy1, mem_negSpace_iff'.mpr hy2⟩
    rw [map_inv] at h
    exact ⟨mem_negSpace_iff'.mp h.1, mem_negSpace_iff'.mp h.2⟩

theorem elementaryGroup_le_normE_sup_of_dim (hQ : (polarBilin Q).Nondegenerate)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (h7 : 7 ≤ Module.finrank K V)
    (F₁ F₂ : Frame Q) (hc : F₁.La (-1) * F₂.La (-1) = F₂.La (-1) * F₁.La (-1))
    (hdim : Module.finrank K ↥(negSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1))) =
      Module.finrank K ↥(posSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1))))
    (A : SL(2, K))
    (hA : ∀ x ∈ negSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1)),
      F₂.La A x ∈ posSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1))) :
    elementaryGroup Q ≤ normE Q F₁.La.range ⊔ normE Q F₂.La.range :=
  elementaryGroup_le_normE_sup hQ hodd h5 h7 F₁ F₂ hc A hA fun x hx => by
    have h := inv_mem_of_map_le (F₂.La A) hA hdim x hx
    rwa [← map_inv] at h

end Frames

end CFSG.ClassicalInvolution.Asc77.T7S2R
