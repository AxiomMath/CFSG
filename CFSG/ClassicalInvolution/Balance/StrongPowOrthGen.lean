module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal.Small

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def planeFrame [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (P : HypPair Q) : HypFrame Q 1 where
  vec _ s := cond s P.e P.f
  map_vec _ s := by cases s <;> simp [P.Q_e, P.Q_f]
  polar_vec_of_ne i j hij := absurd (Subsingleton.elim i j) hij
  polar_vec_not _ s := by cases s <;> simp [P.polar_ef, P.polar_fe]
  exists_aux _ _ := by
    obtain ⟨a, ha, haQ⟩ := hasAnisoPerp_of_three_le_finrank hQ h3 P
    rw [HypPair.mem_perp] at ha
    exact ⟨a, isUnit_iff_ne_zero.mpr haQ, fun s => by cases s <;> simp [ha.1, ha.2]⟩

@[simp] theorem planeFrame_vec_true [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (P : HypPair Q) (i : Fin 1) :
    (planeFrame hQ h3 P).vec i true = P.e := rfl

@[simp] theorem planeFrame_vec_false [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (P : HypPair Q) (i : Fin 1) :
    (planeFrame hQ h3 P).vec i false = P.f := rfl

theorem elementaryGroup_le_of_plane [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (P : HypPair Q) {H : Subgroup (V ≃ₗ[F] V)}
    (hH : ∀ v, polar Q P.e v = 0 → polar Q P.f v = 0 →
      eichler Q P.e v ∈ H ∧ eichler Q P.f v ∈ H) : elementaryGroup Q ≤ H := by
  set Fr : HypFrame Q 1 := planeFrame hQ h3 P with hFr
  set H' : Subgroup (V ≃ₗ[F] V) := H ⊓ elementaryGroup Q with hH'
  have hlong : ∀ {i j : Fin 1}, i ≠ j → ∀ (s t : Bool) (c : F),
      eichler Q (Fr.vec j t) (c • Fr.vec i s) ∈ H' := fun hij =>
    absurd (Subsingleton.elim _ _) hij
  have hperp : ∀ (i : Fin 1) (s : Bool) (v : V), (∀ k r, polar Q v (Fr.vec k r) = 0) →
      eichler Q (Fr.vec i s) v ∈ H' := by
    intro i s v hv
    have h1 : polar Q P.e v = 0 := by rw [polar_comm]; exact hv 0 true
    have h2 : polar Q P.f v = 0 := by rw [polar_comm]; exact hv 0 false
    obtain ⟨hE, hF⟩ := hH v h1 h2
    cases s
    · exact ⟨hF, eichler_mem_elementaryGroup Q _ _⟩
    · exact ⟨hE, eichler_mem_elementaryGroup Q _ _⟩
  have key : ∀ u w : V, Q u = 0 → polar Q u w = 0 → (∃ r, polar Q u (Fr.vec 0 r) ≠ 0) →
      eichler Q u w ∈ H' := by
    intro u w hu huw ⟨r, hr⟩
    obtain ⟨g, hg, hgu⟩ := Fr.exists_mem_apply_eq_smul_vec_not hlong hperp hu hr
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q (Subgroup.mem_inf.mp hg).2
    have hgw : polar Q (Fr.vec 0 (!r)) (polar Q u (Fr.vec 0 r) • g w) = 0 := by
      rw [polar_smul_right, ← polar_smul_left, ← hgu, polar_map_of_mem hgO, huw]
    have hkey : eichler Q u w = g⁻¹ * eichler Q (Fr.vec 0 (!r))
        (polar Q u (Fr.vec 0 r) • g w) * g := by
      rw [← eichler_smul_left, ← hgu, ← eichler_conj hgO]
      group
    rw [hkey]
    exact mul_mem (mul_mem (inv_mem hg) (Fr.eichler_vec_mem hlong hperp 0 (!r) hgw)) hg
  refine le_trans ?_ (inf_le_left : H' ≤ H)
  refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
  by_cases hpair : ∃ r, polar Q u (Fr.vec 0 r) ≠ 0
  · exact key u w hu huw hpair
  push Not at hpair
  have hue : polar Q P.e u = 0 := by rw [polar_comm]; exact hpair true
  have huf : polar Q P.f u = 0 := by rw [polar_comm]; exact hpair false
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact one_mem _
  have hperpu : u ∈ P.perp := HypPair.mem_perp.mpr ⟨hue, huf⟩
  obtain ⟨y, hy, hyu⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero hperpu hu0
  set w₀ : V := (polar Q u y)⁻¹ • y with hw₀
  have hw₀perp : w₀ ∈ P.perp := P.perp.smul_mem _ hy
  have huw₀ : polar Q u w₀ = 1 := by
    rw [hw₀, polar_smul_right_eq, inv_mul_cancel₀ hyu]
  obtain ⟨hew₀, -⟩ := HypPair.mem_perp.mp hw₀perp
  have hg₁ : eichler Q P.e w₀ ∈ H' := ⟨(hH w₀ hew₀ (HypPair.mem_perp.mp hw₀perp).2).1,
    eichler_mem_elementaryGroup Q _ _⟩
  have hg₁O := eichler_mem_orthogonalGroup Q P.e w₀
  have hg₁u : eichler Q P.e w₀ u = u - P.e := by
    rw [eichler_apply P.Q_e hew₀, polar_comm Q u P.e, hue, huw₀]
    simp [sub_eq_add_neg]
  have hu₁ : Q (eichler Q P.e w₀ u) = 0 := by rw [map_of_mem hg₁O, hu]
  have hu₁w : polar Q (eichler Q P.e w₀ u) (eichler Q P.e w₀ w) = 0 := by
    rw [polar_map_of_mem hg₁O, huw]
  have hu₁f : polar Q (eichler Q P.e w₀ u) (Fr.vec 0 false) ≠ 0 := by
    rw [hg₁u, planeFrame_vec_false, polar_sub_left, P.polar_ef, polar_comm Q u P.f, huf]
    simp
  have h1 := key _ _ hu₁ hu₁w ⟨false, hu₁f⟩
  have hkey : eichler Q u w = (eichler Q P.e w₀)⁻¹ *
      eichler Q (eichler Q P.e w₀ u) (eichler Q P.e w₀ w) * eichler Q P.e w₀ := by
    rw [← eichler_conj hg₁O]
    group
  rw [hkey]
  exact mul_mem (mul_mem (inv_mem hg₁) h1) hg₁

theorem polar_eq_zero_of_eigen {t : V ≃ₗ[F] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} {a b : F} (hx : t x = a • x)
    (hy : t y = b • y) (hab : a * b ≠ 1) : polar Q x y = 0 := by
  have h := polar_map_of_mem ht x y
  rw [hx, hy, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul] at h
  have h' : (a * b - 1) * polar Q x y = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab)

theorem eichler_mem_of_eigen (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1)
    {S₁ S₂ S₃ : Submodule F V} (hS₁ : ∀ x, t₁ x = ε • x → x ∈ S₁)
    (hS₂ : ∀ x, t₂ x = δ • x → x ∈ S₂) (hS₃ : ∀ x, t₁ (t₂ x) = (ε * δ) • x → x ∈ S₃)
    {H : Subgroup (V ≃ₗ[F] V)} (hH₁ : elemOn Q S₁ ≤ H) (hH₂ : elemOn Q S₂ ≤ H)
    (hH₃ : elemOn Q S₃ ≤ H) {u v : V} (huv : polar Q u v = 0) (hu₁ : t₁ u = ε • u)
    (hu₂ : t₂ u = δ • u) : eichler Q u v ∈ H := by
  have e1 : ∀ x, t₁ (t₁ x) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht₁
    simpa using this
  have e2 : ∀ x, t₂ (t₂ x) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht₂
    simpa using this
  have ec : ∀ x, t₁ (t₂ x) = t₂ (t₁ x) := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) hc
    simpa using this
  have hne : ∀ a : F, a * a = 1 → (a * -a ≠ 1) := fun a ha h => by
    apply h2
    linear_combination -h - ha
  set a : F := (2 : F)⁻¹ with ha
  have h2a : a * 2 = 1 := inv_mul_cancel₀ h2
  set v₁ : V := a • (v + ε • t₁ v) with hv₁
  set v' : V := a • (v - ε • t₁ v) with hv'
  have hsplit₁ : v = v₁ + v' := by
    rw [hv₁, hv', ← smul_add]
    have : v + ε • t₁ v + (v - ε • t₁ v) = (2 : F) • v := by module
    rw [this, smul_smul, h2a, one_smul]
  have ht₁v₁ : t₁ v₁ = ε • v₁ := by
    rw [hv₁]
    simp only [map_smul, map_add, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε
  have ht₁v' : t₁ v' = (-ε) • v' := by
    rw [hv']
    simp only [map_smul, map_sub, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε
  set v₂ : V := a • (v' + δ • t₂ v') with hv₂
  set v₃ : V := a • (v' - δ • t₂ v') with hv₃
  have hsplit₂ : v' = v₂ + v₃ := by
    rw [hv₂, hv₃, ← smul_add]
    have : v' + δ • t₂ v' + (v' - δ • t₂ v') = (2 : F) • v' := by module
    rw [this, smul_smul, h2a, one_smul]
  have ht₂v₂ : t₂ v₂ = δ • v₂ := by
    rw [hv₂]
    simp only [map_smul, map_add, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ
  have ht₂v₃ : t₂ v₃ = (-δ) • v₃ := by
    rw [hv₃]
    simp only [map_smul, map_sub, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ
  have ht₁v₂ : t₁ v₂ = (-ε) • v₂ := by
    rw [hv₂]
    simp only [map_smul, map_add, ec, ht₁v']
    module
  have ht₁v₃ : t₁ v₃ = (-ε) • v₃ := by
    rw [hv₃]
    simp only [map_smul, map_sub, ec, ht₁v']
    module
  have hu_v' : polar Q u v' = 0 :=
    polar_eq_zero_of_eigen h₁ hu₁ ht₁v'
      (by rw [mul_neg, hε]; intro h; apply h2; linear_combination -h)
  have hu_v₃ : polar Q u v₃ = 0 :=
    polar_eq_zero_of_eigen h₂ hu₂ ht₂v₃
      (by rw [mul_neg, hδ]; intro h; apply h2; linear_combination -h)
  have hu_v₁ : polar Q u v₁ = 0 := by
    have : polar Q u v = polar Q u v₁ + polar Q u v' := by
      rw [← polar_add_right, ← hsplit₁]
    rw [huv, hu_v', add_zero] at this
    exact this.symm
  have hu_v₂ : polar Q u v₂ = 0 := by
    have : polar Q u v' = polar Q u v₂ + polar Q u v₃ := by
      rw [← polar_add_right, ← hsplit₂]
    rw [hu_v', hu_v₃, add_zero] at this
    exact this.symm
  have hmul : eichler Q u v = eichler Q u v₁ * eichler Q u v₂ * eichler Q u v₃ := by
    rw [eichler_mul hu_v₁ hu_v₂, eichler_mul (by rw [polar_add_right, hu_v₁, hu_v₂, add_zero])
      hu_v₃, hsplit₁, hsplit₂, add_assoc]
  have hS₁u : u ∈ S₁ := hS₁ u hu₁
  have hS₂u : u ∈ S₂ := hS₂ u hu₂
  have hS₃u : u ∈ S₃ := hS₃ u (by rw [hu₂, map_smul, hu₁, smul_smul, mul_comm])
  rw [hmul]
  refine mul_mem (mul_mem (hH₁ (eichler_mem_elemOn hS₁u (hS₁ v₁ ht₁v₁)))
    (hH₂ (eichler_mem_elemOn hS₂u (hS₂ v₂ ht₂v₂)))) (hH₃ (eichler_mem_elemOn hS₃u
      (hS₃ v₃ ?_)))
  rw [ht₂v₃, map_smul, ht₁v₃, smul_smul]
  congr 1
  ring

theorem elementaryGroup_le_of_eigen [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ Module.finrank F V) {t₁ t₂ : V ≃ₗ[F] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1) (P : HypPair Q)
    (hPe₁ : t₁ P.e = ε • P.e) (hPf₁ : t₁ P.f = ε • P.f) (hPe₂ : t₂ P.e = δ • P.e)
    (hPf₂ : t₂ P.f = δ • P.f) {S₁ S₂ S₃ : Submodule F V} (hS₁ : ∀ x, t₁ x = ε • x → x ∈ S₁)
    (hS₂ : ∀ x, t₂ x = δ • x → x ∈ S₂) (hS₃ : ∀ x, t₁ (t₂ x) = (ε * δ) • x → x ∈ S₃)
    {H : Subgroup (V ≃ₗ[F] V)} (hH₁ : elemOn Q S₁ ≤ H) (hH₂ : elemOn Q S₂ ≤ H)
    (hH₃ : elemOn Q S₃ ≤ H) : elementaryGroup Q ≤ H :=
  elementaryGroup_le_of_plane hQ h3 P fun _ hv₁ hv₂ =>
    ⟨eichler_mem_of_eigen h2 h₁ h₂ ht₁ ht₂ hc hε hδ hS₁ hS₂ hS₃ hH₁ hH₂ hH₃ hv₁ hPe₁ hPe₂,
      eichler_mem_of_eigen h2 h₁ h₂ ht₁ ht₂ hc hε hδ hS₁ hS₂ hS₃ hH₁ hH₂ hH₃ hv₂ hPf₁ hPf₂⟩

theorem exists_joint_component (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1) (y : V) :
    ∃ y₂ : V, t₁ y₂ = ε • y₂ ∧ t₂ y₂ = δ • y₂ ∧
      ∀ x, t₁ x = ε • x → t₂ x = δ • x → polar Q x y₂ = polar Q x y := by
  have e1 : ∀ x, t₁ (t₁ x) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht₁
    simpa using this
  have e2 : ∀ x, t₂ (t₂ x) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht₂
    simpa using this
  have ec : ∀ x, t₁ (t₂ x) = t₂ (t₁ x) := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) hc
    simpa using this
  set a : F := (2 : F)⁻¹ with ha
  have h2a : a * 2 = 1 := inv_mul_cancel₀ h2
  set y₁ : V := a • (y + ε • t₁ y) with hy₁
  set r₁ : V := a • (y - ε • t₁ y) with hr₁
  have hsplit₁ : y = y₁ + r₁ := by
    rw [hy₁, hr₁, ← smul_add]
    have : y + ε • t₁ y + (y - ε • t₁ y) = (2 : F) • y := by module
    rw [this, smul_smul, h2a, one_smul]
  have ht₁y₁ : t₁ y₁ = ε • y₁ := by
    rw [hy₁]
    simp only [map_smul, map_add, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε
  have ht₁r₁ : t₁ r₁ = (-ε) • r₁ := by
    rw [hr₁]
    simp only [map_smul, map_sub, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε
  set y₂ : V := a • (y₁ + δ • t₂ y₁) with hy₂
  set r₂ : V := a • (y₁ - δ • t₂ y₁) with hr₂
  have hsplit₂ : y₁ = y₂ + r₂ := by
    rw [hy₂, hr₂, ← smul_add]
    have : y₁ + δ • t₂ y₁ + (y₁ - δ • t₂ y₁) = (2 : F) • y₁ := by module
    rw [this, smul_smul, h2a, one_smul]
  have ht₂y₂ : t₂ y₂ = δ • y₂ := by
    rw [hy₂]
    simp only [map_smul, map_add, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ
  have ht₂r₂ : t₂ r₂ = (-δ) • r₂ := by
    rw [hr₂]
    simp only [map_smul, map_sub, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ
  have ht₁y₂ : t₁ y₂ = ε • y₂ := by
    rw [hy₂]
    simp only [map_smul, map_add, ec, ht₁y₁]
    module
  refine ⟨y₂, ht₁y₂, ht₂y₂, fun x hx₁ hx₂ => ?_⟩
  have hne : ∀ b : F, b * b = 1 → b * -b ≠ 1 := fun b hb h => by
    apply h2
    linear_combination -h - hb
  have h0₁ : polar Q x r₁ = 0 := polar_eq_zero_of_eigen h₁ hx₁ ht₁r₁ (hne ε hε)
  have h0₂ : polar Q x r₂ = 0 := polar_eq_zero_of_eigen h₂ hx₂ ht₂r₂ (hne δ hδ)
  have e3 : polar Q x y = polar Q x y₁ + polar Q x r₁ := by rw [← polar_add_right, ← hsplit₁]
  have e4 : polar Q x y₁ = polar Q x y₂ + polar Q x r₂ := by rw [← polar_add_right, ← hsplit₂]
  rw [e3, e4, h0₁, h0₂, add_zero, add_zero]

theorem exists_hypPair_joint (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {t₁ t₂ : V ≃ₗ[F] V} (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1) {e : V} (he : Q e = 0)
    (he0 : e ≠ 0) (he₁ : t₁ e = ε • e) (he₂ : t₂ e = δ • e) :
    ∃ P : HypPair Q, P.e = e ∧ t₁ P.f = ε • P.f ∧ t₂ P.f = δ • P.f := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ he0
  obtain ⟨y₂, hy₁, hy₂, hpair⟩ := exists_joint_component (Q := Q) h2 h₁ h₂ ht₁ ht₂ hc hε hδ y
  have hpy : polar Q e y₂ ≠ 0 := by rw [hpair e he₁ he₂]; exact hy
  set h' : V := (polar Q e y₂)⁻¹ • y₂ with hh'
  have hh'1 : polar Q e h' = 1 := by rw [hh', polar_smul_right_eq, inv_mul_cancel₀ hpy]
  have hh'₁ : t₁ h' = ε • h' := by
    rw [hh', LinearEquiv.map_smul, hy₁, smul_comm]
  have hh'₂ : t₂ h' = δ • h' := by
    rw [hh', LinearEquiv.map_smul, hy₂, smul_comm]
  clear_value h'
  refine ⟨HypPair.ofPolarEqOne he hh'1, rfl, ?_, ?_⟩
  · rw [HypPair.ofPolarEqOne_f, map_sub, LinearEquiv.map_smul, hh'₁, he₁, smul_sub,
      smul_comm ε (Q h') e]
  · rw [HypPair.ofPolarEqOne_f, map_sub, LinearEquiv.map_smul, hh'₂, he₂, smul_sub,
      smul_comm δ (Q h') e]

@[expose] def eigenSub (t : V ≃ₗ[F] V) (ε : F) : Submodule F V where
  carrier := {x | t x = ε • x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy, smul_add]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [LinearEquiv.map_smul, hx, smul_comm]

theorem mem_eigenSub {t : V ≃ₗ[F] V} {ε : F} {x : V} : x ∈ eigenSub t ε ↔ t x = ε • x := Iff.rfl

theorem exists_eigen_split (h2 : (2 : F) ≠ 0) {t : V ≃ₗ[F] V} (ht : t * t = 1) {ε : F}
    (hε : ε * ε = 1) (z : V) :
    ∃ zp zm : V, z = zp + zm ∧ t zp = ε • zp ∧ t zm = (-ε) • zm := by
  have e1 : ∀ x, t (t x) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht
    simpa using this
  set a : F := (2 : F)⁻¹ with ha
  have h2a : a * 2 = 1 := inv_mul_cancel₀ h2
  refine ⟨a • (z + ε • t z), a • (z - ε • t z), ?_, ?_, ?_⟩
  · rw [← smul_add]
    have : z + ε • t z + (z - ε • t z) = (2 : F) • z := by module
    rw [this, smul_smul, h2a, one_smul]
  · simp only [map_smul, map_add, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε
  · simp only [map_smul, map_sub, e1]
    match_scalars <;> first | ring1 | linear_combination (-a) * hε

theorem polarNondegOn_eigenSub (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {t : V ≃ₗ[F] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hsq : t * t = 1) {ε : F}
    (hε : ε * ε = 1) : PolarNondegOn Q (eigenSub t ε) := by
  intro x hx hxW
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  obtain ⟨zp, zm, hz, hzp, hzm⟩ := exists_eigen_split h2 hsq hε z
  have hne : ε * -ε ≠ 1 := fun h => by
    apply h2
    linear_combination -h - hε
  rw [hz, polar_add_right, hxW zp hzp, polar_eq_zero_of_eigen ht (mem_eigenSub.mp hx) hzm hne,
    add_zero]

theorem mem_eigenSub_iff_of_comm {s g : V ≃ₗ[F] V} (hg : g * s = s * g) {ε : F} {x : V} :
    x ∈ eigenSub s ε ↔ g x ∈ eigenSub s ε := by
  have hgs : ∀ x, g (s x) = s (g x) := fun x => by
    have := congrArg (fun h : V ≃ₗ[F] V => h x) hg
    simpa using this
  rw [mem_eigenSub, mem_eigenSub]
  constructor
  · intro h
    rw [← hgs, h, LinearEquiv.map_smul]
  · intro h
    apply g.injective
    rw [hgs, h, LinearEquiv.map_smul]

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
