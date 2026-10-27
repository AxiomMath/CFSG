module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Closure

variable {M : Type*} [Group M]

theorem closure_le_centralizer_of_forall_commute {S T : Set M}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    closure S ≤ centralizer (closure T : Set M) := by
  rw [closure_le]
  intro s hs
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro x hx
  have hle : closure T ≤ centralizer ({s} : Set M) := by
    rw [closure_le]
    intro t ht
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (h s hs t ht).symm
  exact (mem_centralizer_singleton_iff.mp (hle hx))

end Closure

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_smul_mem_rootGroup_right {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (t : K) : eichler Q u (t • w) ∈ rootGroup Q w := by
  have htw : Q (t • w) = 0 := by rw [QuadraticMap.map_smul, hw, smul_zero]
  have hutw : polar Q u (t • w) = 0 := by rw [polar_smul_right_eq, huw, mul_zero]
  rw [eichler_eq_eichler_neg hu htw hutw, eichler_smul_left]
  refine eichler_mem_rootGroup ?_
  rw [polar_smul_right_eq, polar_neg_right, polar_comm, huw, neg_zero, mul_zero]

theorem eichler_smul_mem_rootGroup_left {u w : V} (huw : polar Q u w = 0) (t : K) :
    eichler Q u (t • w) ∈ rootGroup Q u :=
  eichler_mem_rootGroup (by rw [polar_smul_right_eq, huw, mul_zero])

end Eichler

section LeviFix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

@[expose] def leviFix (H : Subgroup (V ≃ₗ[K] V)) (P₁ P₂ : HypPair Q) : Subgroup (V ≃ₗ[K] V) :=
  H ⊓ rootLevi Q P₁ P₂ ⊓ fixPtSub K {x | InW P₁ P₂ x}

theorem mem_leviFix {H : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V} :
    g ∈ leviFix H P₁ P₂ ↔ g ∈ H ∧ g ∈ rootLevi Q P₁ P₂ ∧ ∀ x, InW P₁ P₂ x → g x = x := by
  simp only [leviFix, mem_inf, mem_fixPtSub, Set.mem_ofPred_eq, and_assoc]

variable (P₁ P₂) in
@[expose] def planeCoeff (g : V ≃ₗ[K] V) : Matrix (Fin 2) (Fin 2) K :=
  !![polar Q (g P₁.e) P₁.f, polar Q (g P₂.e) P₁.f; polar Q (g P₁.e) P₂.f, polar Q (g P₂.e) P₂.f]

theorem planeCoeff_apply_e (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    g P₁.e = planeCoeff P₁ P₂ g 0 0 • P₁.e + planeCoeff P₁ P₂ g 1 0 • P₂.e ∧
      g P₂.e = planeCoeff P₁ P₂ g 0 1 • P₁.e + planeCoeff P₁ P₂ g 1 1 • P₂.e :=
  apply_e_eq_coeff h₁₂ hc

theorem polar_comb_coeff (h₁₂ : P₁.Orth P₂) (a c : K) :
    polar Q (a • P₁.e + c • P₂.e) P₁.f = a ∧ polar Q (a • P₁.e + c • P₂.e) P₂.f = c :=
  ⟨polar_comb_f₁ h₁₂ a c, polar_comb_f₂ h₁₂ a c⟩

theorem planeCoeff_mul (h₁₂ : P₁.Orth P₂) {g h : V ≃ₗ[K] V}
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g)
    (hhc : h * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * h) :
    planeCoeff P₁ P₂ (g * h) = planeCoeff P₁ P₂ g * planeCoeff P₁ P₂ h := by
  obtain ⟨g1, g2⟩ := planeCoeff_apply_e h₁₂ hgc
  obtain ⟨k1, k2⟩ := planeCoeff_apply_e h₁₂ hhc
  have e1 : (g * h) P₁.e = (planeCoeff P₁ P₂ g 0 0 * planeCoeff P₁ P₂ h 0 0 +
      planeCoeff P₁ P₂ g 0 1 * planeCoeff P₁ P₂ h 1 0) • P₁.e +
      (planeCoeff P₁ P₂ g 1 0 * planeCoeff P₁ P₂ h 0 0 +
        planeCoeff P₁ P₂ g 1 1 * planeCoeff P₁ P₂ h 1 0) • P₂.e := by
    rw [LinearEquiv.mul_apply, k1, map_add, map_smul, map_smul, g1, g2]
    module
  have e2 : (g * h) P₂.e = (planeCoeff P₁ P₂ g 0 0 * planeCoeff P₁ P₂ h 0 1 +
      planeCoeff P₁ P₂ g 0 1 * planeCoeff P₁ P₂ h 1 1) • P₁.e +
      (planeCoeff P₁ P₂ g 1 0 * planeCoeff P₁ P₂ h 0 1 +
        planeCoeff P₁ P₂ g 1 1 * planeCoeff P₁ P₂ h 1 1) • P₂.e := by
    rw [LinearEquiv.mul_apply, k2, map_add, map_smul, map_smul, g1, g2]
    module
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one] <;>
    first
    | (change polar Q ((g * h) P₁.e) P₁.f = _; rw [e1, (polar_comb_coeff h₁₂ _ _).1])
    | (change polar Q ((g * h) P₂.e) P₁.f = _; rw [e2, (polar_comb_coeff h₁₂ _ _).1])
    | (change polar Q ((g * h) P₁.e) P₂.f = _; rw [e1, (polar_comb_coeff h₁₂ _ _).2])
    | (change polar Q ((g * h) P₂.e) P₂.f = _; rw [e2, (polar_comb_coeff h₁₂ _ _).2])

theorem planeCoeff_one (h₁₂ : P₁.Orth P₂) : planeCoeff P₁ P₂ (1 : V ≃ₗ[K] V) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeCoeff, P₁.polar_ef, P₂.polar_ef, h₁₂.ef, polar_comm Q P₂.e P₁.f, h₁₂.fe]

theorem det_planeCoeff (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    (planeCoeff P₁ P₂ g).det = 1 := by
  rw [Matrix.det_fin_two]
  exact det_coeff_eq_one h₁₂ hg hc

theorem leviFix_commute_e {H : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V} (hg : g ∈ leviFix H P₁ P₂) :
    g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g :=
  mem_centralizer_singleton_iff.mp (mem_leviFix.mp hg).2.1.1.2

theorem leviFix_mem_orthogonalGroup {H : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hg : g ∈ leviFix H P₁ P₂) : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (mem_leviFix.mp hg).2.1.1.1

variable (P₁ P₂) in
@[expose] noncomputable def leviCoeff (h₁₂ : P₁.Orth P₂) (H : Subgroup (V ≃ₗ[K] V)) :
    leviFix H P₁ P₂ →* SL(2, K) where
  toFun g := ⟨planeCoeff P₁ P₂ g, det_planeCoeff h₁₂ (leviFix_mem_orthogonalGroup g.2)
    (leviFix_commute_e g.2)⟩
  map_one' := Subtype.ext (planeCoeff_one h₁₂)
  map_mul' g h := Subtype.ext (planeCoeff_mul h₁₂ (leviFix_commute_e g.2) (leviFix_commute_e h.2))

theorem leviCoeff_apply (h₁₂ : P₁.Orth P₂) (H : Subgroup (V ≃ₗ[K] V)) (g : leviFix H P₁ P₂) :
    ((leviCoeff P₁ P₂ h₁₂ H g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      planeCoeff P₁ P₂ (g : V ≃ₗ[K] V) := rfl

theorem leviCoeff_injective (h₁₂ : P₁.Orth P₂) (H : Subgroup (V ≃ₗ[K] V)) :
    Function.Injective (leviCoeff P₁ P₂ h₁₂ H) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hM : planeCoeff P₁ P₂ (g : V ≃ₗ[K] V) = 1 := by
    rw [← leviCoeff_apply h₁₂ H g, hg]; rfl
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp g.2
  obtain ⟨g1, g2⟩ := planeCoeff_apply_e h₁₂ (leviFix_commute_e g.2)
  rw [hM] at g1 g2
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_smul, zero_smul, add_zero,
    zero_add] at g1 g2
  rw [mem_bot]
  exact Subtype.ext (eq_one_of_fixW_of_fix_e h₁₂ hgL hgW g1 g2)

theorem eichler_mem_leviFix (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) (t : K) :
    eichler Q P₁.e (t • P₂.f) ∈ leviFix H P₁ P₂ ∧ eichler Q P₂.e (t • P₁.f) ∈ leviFix H P₁ P₂ := by
  refine ⟨mem_leviFix.mpr ⟨hE _ _, eichler_smul_f_mem_rootLevi h₁₂ t, fun x hx => ?_⟩,
    mem_leviFix.mpr ⟨hE _ _, eichler_smul_f_mem_rootLevi' h₁₂ t, fun x hx => ?_⟩⟩
  · exact eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hx.1)
      (by rw [polar_smul_right_eq, polar_comm, hx.2.2.2, mul_zero])
  · exact eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hx.2.2.1)
      (by rw [polar_smul_right_eq, polar_comm, hx.2.1, mul_zero])

theorem leviCoeff_surjective (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) : Function.Surjective (leviCoeff P₁ P₂ h₁₂ H) := by
  intro A
  have hdet : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact A.2
  obtain ⟨m, hm, hm1, hm2⟩ := exists_word h₁₂ (leviFix H P₁ P₂)
    (fun t => (eichler_mem_leviFix h₁₂ hE t).1) (fun t => (eichler_mem_leviFix h₁₂ hE t).2) hdet
  refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
  rw [leviCoeff_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · change polar Q (m P₁.e) P₁.f = _; rw [hm1, (polar_comb_coeff h₁₂ _ _).1]; rfl
  · change polar Q (m P₂.e) P₁.f = _; rw [hm2, (polar_comb_coeff h₁₂ _ _).1]; rfl
  · change polar Q (m P₁.e) P₂.f = _; rw [hm1, (polar_comb_coeff h₁₂ _ _).2]; rfl
  · change polar Q (m P₂.e) P₂.f = _; rw [hm2, (polar_comb_coeff h₁₂ _ _).2]; rfl

variable (P₁ P₂) in
@[expose] noncomputable def leviFixEquiv (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) : leviFix H P₁ P₂ ≃* SL(2, K) :=
  MulEquiv.ofBijective (leviCoeff P₁ P₂ h₁₂ H)
    ⟨leviCoeff_injective h₁₂ H, leviCoeff_surjective h₁₂ hE⟩

theorem leviFix_le_closure (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) :
    leviFix H P₁ P₂ ≤ closure (Set.range (fun t : K => eichler Q P₁.e (t • P₂.f)) ∪
      Set.range (fun t : K => eichler Q P₂.e (t • P₁.f))) := by
  set C := closure (Set.range (fun t : K => eichler Q P₁.e (t • P₂.f)) ∪
    Set.range (fun t : K => eichler Q P₂.e (t • P₁.f))) with hC
  have hCle : C ≤ leviFix H P₁ P₂ := by
    rw [hC, closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact (eichler_mem_leviFix h₁₂ hE t).1
    · exact (eichler_mem_leviFix h₁₂ hE t).2
  intro g hg
  obtain ⟨g1, g2⟩ := planeCoeff_apply_e h₁₂ (leviFix_commute_e hg)
  have hdet := det_planeCoeff h₁₂ (leviFix_mem_orthogonalGroup hg) (leviFix_commute_e hg)
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨m, hm, hm1, hm2⟩ := exists_word h₁₂ C
    (fun t => subset_closure (Or.inl ⟨t, rfl⟩)) (fun t => subset_closure (Or.inr ⟨t, rfl⟩)) hdet
  have hmL := hCle hm
  have heq : leviCoeff P₁ P₂ h₁₂ H ⟨m, hmL⟩ = leviCoeff P₁ P₂ h₁₂ H ⟨g, hg⟩ := by
    apply Subtype.ext
    rw [leviCoeff_apply, leviCoeff_apply]
    ext i j
    fin_cases i <;> fin_cases j
    · change polar Q (m P₁.e) P₁.f = polar Q (g P₁.e) P₁.f
      rw [hm1, (polar_comb_coeff h₁₂ _ _).1]; rfl
    · change polar Q (m P₂.e) P₁.f = polar Q (g P₂.e) P₁.f
      rw [hm2, (polar_comb_coeff h₁₂ _ _).1]; rfl
    · change polar Q (m P₁.e) P₂.f = polar Q (g P₁.e) P₂.f
      rw [hm1, (polar_comb_coeff h₁₂ _ _).2]; rfl
    · change polar Q (m P₂.e) P₂.f = polar Q (g P₂.e) P₂.f
      rw [hm2, (polar_comb_coeff h₁₂ _ _).2]; rfl
  have := congrArg Subtype.val (leviCoeff_injective h₁₂ H heq)
  change m = g at this
  rw [← this]
  exact hm

end LeviFix

section Commute

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ P₃ P₄ : HypPair Q}

theorem leviFix_le_centralizer_flip (h₁₂ : P₁.Orth P₂) {H H' : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) (hE' : ∀ u w : V, eichler Q u w ∈ H') :
    leviFix H P₁ P₂ ≤ centralizer (leviFix H' P₁ (flipPair P₂) : Set (V ≃ₗ[K] V)) := by
  have hf : P₁.Orth (flipPair P₂) := ⟨h₁₂.ef, h₁₂.ee, h₁₂.ff, h₁₂.fe⟩
  refine (leviFix_le_closure h₁₂ hE).trans ((closure_le_centralizer_of_forall_commute ?_).trans
    (centralizer_le (leviFix_le_closure hf hE')))
  have e1f2 : polar Q P₁.e P₂.f = 0 := h₁₂.ef
  have e1e2 : polar Q P₁.e P₂.e = 0 := h₁₂.ee
  have f2f1 : polar Q P₂.f P₁.f = 0 := by rw [polar_comm]; exact h₁₂.ff
  have e2f1 : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) _ (⟨s, rfl⟩ | ⟨s, rfl⟩) <;>
    simp only [flipPair_e, flipPair_f]
  · exact rootGroup_commute (eichler_smul_mem_rootGroup_left e1f2 t)
      (eichler_smul_mem_rootGroup_left e1e2 s)
  · exact rootGroup_commute (eichler_smul_mem_rootGroup_right P₁.Q_e P₂.Q_f e1f2 t)
      (eichler_smul_mem_rootGroup_left f2f1 s)
  · exact rootGroup_commute (eichler_smul_mem_rootGroup_left e2f1 t)
      (eichler_smul_mem_rootGroup_right P₁.Q_e P₂.Q_e e1e2 s)
  · exact rootGroup_commute (eichler_smul_mem_rootGroup_right P₂.Q_e P₁.Q_f e2f1 t)
      (eichler_smul_mem_rootGroup_right P₂.Q_f P₁.Q_f f2f1 s)

theorem inW_add_smul {x y : V} (hx : InW P₃ P₄ x) (hy : InW P₃ P₄ y) (a b : K) :
    InW P₃ P₄ (a • x + b • y) := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [polar_add_right, polar_smul_right_eq, x1, x2, x3, x4, y1, y2, y3, y4, mul_zero,
      add_zero]

theorem inW_of_orth (h₃ : P₁.Orth P₃) (h₄ : P₁.Orth P₄) : InW P₃ P₄ P₁.e ∧ InW P₃ P₄ P₁.f := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> rw [polar_comm]
  exacts [h₃.ee, h₃.ef, h₄.ee, h₄.ef, h₃.fe, h₃.ff, h₄.fe, h₄.ff]

theorem leviFix_le_centralizer_of_orth (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄)
    (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄) (H H' : Subgroup (V ≃ₗ[K] V)) :
    leviFix H P₁ P₂ ≤ centralizer (leviFix H' P₃ P₄ : Set (V ≃ₗ[K] V)) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp hg
  obtain ⟨-, hhL, hhW⟩ := mem_leviFix.mp hh
  obtain ⟨a1, a2⟩ := inW_of_orth h₁₃ h₁₄
  obtain ⟨b1, b2⟩ := inW_of_orth h₂₃ h₂₄
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hgL.1.2)
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff (orth_flipPair_flipPair h₁₂)
    (mem_centralizer_singleton_iff.mp hgL.2)
  simp only [flipPair_e, flipPair_f] at k1 k2
  refine (commute_of_fixW_of_fix h₁₂ hgW hhL.1.1 ⟨hhW _ a1, hhW _ a2, hhW _ b1, hhW _ b2⟩
    ⟨?_, ?_, ?_, ?_⟩).symm
  · rw [g1]; exact hhW _ (inW_add_smul a1 b1 _ _)
  · rw [k1]; exact hhW _ (inW_add_smul a2 b2 _ _)
  · rw [g2]; exact hhW _ (inW_add_smul a1 b1 _ _)
  · rw [k2]; exact hhW _ (inW_add_smul a2 b2 _ _)

end Commute

end CFSG.SeitzReduction.OmegaPilot
