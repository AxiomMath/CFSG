module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Shape
import CFSG.RankThree.PartOne.S12.TerminalWeylPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Equiv

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem s3e_swap_iff_aux : ∀ s : Perm (Fin 5), (s * s = 1 ∧ s ≠ 1 ∧
    (Finset.univ.filter (fun g : Perm (Fin 5) => g * s = s * g)).card = 12) ↔
    ∃ x y : Fin 5, x ≠ y ∧ s = swap x y := by
  decide +kernel

theorem s3e_nonab_aux : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x := by
  decide +kernel

theorem s3e_isSwap_map (ψ : Perm (Fin 5) ≃* Perm (Fin 5)) {s : Perm (Fin 5)} (hs : s.IsSwap) :
    (ψ s).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  obtain ⟨h1, h2, h3⟩ := (s3e_swap_iff_aux (swap x y)).mpr ⟨x, y, hxy, rfl⟩
  have k1 : ψ (swap x y) * ψ (swap x y) = 1 := by rw [← map_mul, h1, map_one]
  have k2 : ψ (swap x y) ≠ 1 := fun h => h2 (ψ.map_eq_one_iff.mp h)
  have k3 : (Finset.univ.filter (fun g : Perm (Fin 5) =>
      g * ψ (swap x y) = ψ (swap x y) * g)).card = 12 := by
    rw [← h3]
    refine Finset.card_bij' (fun g _ => ψ.symm g) (fun g _ => ψ g) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [← map_mul, ← map_mul, hg]
    · intro g _
      simp
    · intro g _
      simp
  obtain ⟨x', y', hxy', h4⟩ := (s3e_swap_iff_aux (ψ (swap x y))).mp ⟨k1, k2, k3⟩
  exact ⟨x', y', hxy', h4⟩

section Diag

variable {A : Type*} [Group A]

theorem s3e_swapHom_diag (g : Multiplicative (ZMod 2)) (x : A) :
    swapHom A g (x, x) = (x, x) := by
  rcases zmod2_cases g with rfl | rfl
  · simp
  · rw [swapHom_one']; rfl

theorem s3e_left_base (a b : A) : (base a b).left = (a, b) := rfl

theorem s3e_left_base_mul_tau (a b : A) : (base a b * tau).left = (a, b) := by
  rw [SemidirectProduct.mul_left]
  have h1 : (base a b).right = 1 := rfl
  have h2 : (tau : Wr2 A).left = 1 := rfl
  rw [h1, h2]
  simp [s3e_left_base]

theorem s3e_cent_cases {w : Wr2 A} (hw : w ∈ centralizer ({tau} : Set (Wr2 A))) :
    w.left.1 = w.left.2 ∧
      (w = base w.left.1 w.left.1 ∨ w = base w.left.1 w.left.1 * tau) := by
  rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · have hab : a = b := (mem_centralizer_tau_iff a b).mp hw
    subst hab
    rw [s3e_left_base]
    exact ⟨rfl, Or.inl rfl⟩
  · have hw' : base a b ∈ centralizer ({tau} : Set (Wr2 A)) := by
      have h1 : (base a b * tau) * tau ∈ centralizer ({tau} : Set (Wr2 A)) :=
        Subgroup.mul_mem _ hw (mem_centralizer_singleton_iff.mpr rfl)
      rwa [mul_assoc, tau_mul_tau, mul_one] at h1
    have hab : a = b := (mem_centralizer_tau_iff a b).mp hw'
    subst hab
    rw [s3e_left_base_mul_tau]
    exact ⟨rfl, Or.inr rfl⟩

@[expose] def s3e_diag : centralizer ({tau} : Set (Wr2 A)) →* A where
  toFun w := (w : Wr2 A).left.1
  map_one' := rfl
  map_mul' w w' := by
    have h := (s3e_cent_cases w'.2).1
    have h' : (w' : Wr2 A).left = ((w' : Wr2 A).left.1, (w' : Wr2 A).left.1) :=
      Prod.ext rfl h.symm
    show ((w : Wr2 A) * (w' : Wr2 A)).left.1 = _
    rw [SemidirectProduct.mul_left, h', s3e_swapHom_diag]
    rfl

end Diag

section WreathHom

theorem s3e_exists_wreath_hom {D A : Type*} [Group D] [Group A] (Γ : Subgroup D) (t : D)
    (ht : t * t = 1) (htΓ : ∀ g ∈ Γ, t * g * t ∈ Γ) (hdich : ∀ d, d ∈ Γ ∨ d * t ∈ Γ)
    (hnot : t ∉ Γ) (π : Γ →* A) :
    ∃ ι : D →* Wr2 A,
      (∀ g : Γ, ι g = base (π g) (π ⟨t * g * t, htΓ g g.2⟩)) ∧ ι t = tau ∧
      ∀ d, d ∉ Γ → ∃ a b, ι d = base a b * tau := by
  classical
  have htt : ∀ x : D, t * (t * x) = x := fun x => by rw [← mul_assoc, ht, one_mul]
  have key : ∀ x y : D, x * t * (t * y) = x * y := fun x y => by
    rw [mul_assoc, htt]
  let cT : Γ →* Γ :=
    { toFun := fun g => ⟨t * g * t, htΓ g g.2⟩
      map_one' := Subtype.ext (by simpa using ht)
      map_mul' := fun g g' => Subtype.ext (by
        show t * (↑g * ↑g') * t = (t * ↑g * t) * (t * ↑g' * t)
        simp only [mul_assoc, htt]) }
  have hcc : ∀ g : Γ, cT (cT g) = g := fun g => Subtype.ext (by
    show t * (t * ↑g * t) * t = ↑g
    simp only [mul_assoc, ht, htt, mul_one])
  let ι₀ : Γ →* Wr2 A := (SemidirectProduct.inl : A × A →* Wr2 A).comp (π.prod (π.comp cT))
  have hι₀ : ∀ g : Γ, ι₀ g = base (π g) (π (cT g)) := fun g => rfl
  have hconj : ∀ g : Γ, ι₀ (cT g) = tau * ι₀ g * tau := fun g => by
    rw [hι₀, hι₀, hcc, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
  obtain ⟨f, hf1, hf2⟩ : ∃ f : D → Wr2 A, (∀ d (h : d ∈ Γ), f d = ι₀ ⟨d, h⟩) ∧
      ∀ d (h : d ∉ Γ) (h' : d * t ∈ Γ), f d = ι₀ ⟨d * t, h'⟩ * tau :=
    ⟨fun d => if h : d ∈ Γ then ι₀ ⟨d, h⟩ else
        ι₀ ⟨d * t, (hdich d).resolve_left h⟩ * tau,
      fun d h => by simp [h], fun d h h' => by simp [h]⟩
  have hmul : ∀ d d' : D, f (d * d') = f d * f d' := by
    intro d d'
    by_cases hd : d ∈ Γ <;> by_cases hd' : d' ∈ Γ
    · rw [hf1 _ (Γ.mul_mem hd hd'), hf1 d hd, hf1 d' hd']
      exact map_mul ι₀ ⟨d, hd⟩ ⟨d', hd'⟩
    · have hdd' : d * d' ∉ Γ := fun h => hd' (by
        simpa using Γ.mul_mem (Γ.inv_mem hd) h)
      have h't := (hdich d').resolve_left hd'
      have h3 : d * d' * t ∈ Γ := by rw [mul_assoc]; exact Γ.mul_mem hd h't
      rw [hf2 _ hdd' h3, hf1 d hd, hf2 d' hd' h't]
      have : (⟨d * d' * t, h3⟩ : Γ) = ⟨d, hd⟩ * ⟨d' * t, h't⟩ := Subtype.ext (mul_assoc _ _ _)
      rw [this, map_mul, mul_assoc]
    · have hdd' : d * d' ∉ Γ := fun h => hd (by
        simpa using Γ.mul_mem h (Γ.inv_mem hd'))
      have h1t := (hdich d).resolve_left hd
      have e : (d * t) * (t * d' * t) = d * d' * t := by
        rw [mul_assoc t d' t, key, mul_assoc]
      have h3 : d * d' * t ∈ Γ := by rw [← e]; exact Γ.mul_mem h1t (htΓ d' hd')
      rw [hf2 _ hdd' h3, hf2 d hd h1t, hf1 d' hd']
      have : (⟨d * d' * t, h3⟩ : Γ) = ⟨d * t, h1t⟩ * cT ⟨d', hd'⟩ := Subtype.ext e.symm
      rw [this, map_mul, hconj]
      simp only [mul_assoc, tau_mul_tau, mul_one]
    · have h1t := (hdich d).resolve_left hd
      have h2t := (hdich d').resolve_left hd'
      have e : (d * t) * (t * (d' * t) * t) = d * d' := by
        rw [mul_assoc t (d' * t) t, key, mul_assoc d' t t, ht, mul_one]
      have h3 : d * d' ∈ Γ := by rw [← e]; exact Γ.mul_mem h1t (htΓ _ h2t)
      rw [hf1 _ h3, hf2 d hd h1t, hf2 d' hd' h2t]
      have : (⟨d * d', h3⟩ : Γ) = ⟨d * t, h1t⟩ * cT ⟨d' * t, h2t⟩ := Subtype.ext e.symm
      rw [this, map_mul, hconj]
      simp only [mul_assoc]
  have hf_one : f 1 = 1 := by
    rw [hf1 1 (one_mem _)]
    exact map_one ι₀
  refine ⟨MonoidHom.mk' f hmul, ?_, ?_, ?_⟩
  · intro g
    show f g = _
    rw [hf1 g g.2]
    rfl
  · have h' : t * t ∈ Γ := by rw [ht]; exact one_mem _
    show f t = _
    rw [hf2 t hnot h']
    have : (⟨t * t, h'⟩ : Γ) = 1 := Subtype.ext ht
    rw [this, map_one, one_mul]
  · intro d hd
    have h' := (hdich d).resolve_left hd
    exact ⟨_, _, hf2 d hd h'⟩

end WreathHom

section Factors

variable {D : Type} [Group D] {t : D}

def s3e_Pres (c : CaseAData D t) (d : D) : Prop :=
  (∀ a ∈ c.Y₁, d * a * d⁻¹ ∈ c.Y₁) ∧ (∀ b ∈ c.Y₂, d * b * d⁻¹ ∈ c.Y₂)

def s3e_Swp (c : CaseAData D t) (d : D) : Prop :=
  (∀ a ∈ c.Y₁, d * a * d⁻¹ ∈ c.Y₂) ∧ (∀ b ∈ c.Y₂, d * b * d⁻¹ ∈ c.Y₁)

theorem s3e_nonab (c : CaseAData D t) : ∃ a ∈ c.Y₁, ∃ a' ∈ c.Y₁, a * a' ≠ a' * a := by
  obtain ⟨x, y, hxy⟩ := s3e_nonab_aux
  refine ⟨(c.e₁.symm x : D), (c.e₁.symm x).2, (c.e₁.symm y : D), (c.e₁.symm y).2, fun h => hxy ?_⟩
  have h' : c.e₁.symm x * c.e₁.symm y = c.e₁.symm y * c.e₁.symm x := Subtype.ext h
  have := congrArg c.e₁ h'
  simpa using this

theorem s3e_not_pres_swp (c : CaseAData D t) {d : D} (h1 : s3e_Pres c d) (h2 : s3e_Swp c d) :
    False := by
  obtain ⟨a, ha, a', ha', hne⟩ := s3e_nonab c
  apply hne
  have hc := c.comm _ (h1.1 a ha) _ (h2.1 a' ha')
  have : d * (a * a') * d⁻¹ = d * (a' * a) * d⁻¹ := by
    calc d * (a * a') * d⁻¹ = (d * a * d⁻¹) * (d * a' * d⁻¹) := by group
      _ = (d * a' * d⁻¹) * (d * a * d⁻¹) := hc
      _ = d * (a' * a) * d⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel this)

theorem s3e_pres_inv (c : CaseAData D t) {d : D} (h : s3e_Pres c d) : s3e_Pres c d⁻¹ := by
  rcases c.perm d⁻¹ with h' | ⟨h1, h2⟩
  · exact h'
  · exfalso
    obtain ⟨a, ha, a', ha', hne⟩ := s3e_nonab c
    have hY : ∀ a ∈ c.Y₁, a ∈ c.Y₂ := fun a ha => by
      have := h.2 _ (h1 a ha)
      simpa [mul_assoc] using this
    exact hne (c.comm a ha a' (hY a' ha'))

def s3e_Gam (c : CaseAData D t) : Subgroup D where
  carrier := {d | s3e_Pres c d}
  mul_mem' {d d'} hd hd' := by
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have := hd.1 _ (hd'.1 a ha)
      simpa [mul_assoc] using this
    · have := hd.2 _ (hd'.2 b hb)
      simpa [mul_assoc] using this
  one_mem' := ⟨fun a ha => by simpa using ha, fun b hb => by simpa using hb⟩
  inv_mem' {d} hd := s3e_pres_inv c hd

theorem s3e_Y₁_le (c : CaseAData D t) : c.Y₁ ≤ s3e_Gam c := fun y hy =>
  ⟨fun a ha => Subgroup.mul_mem _ (Subgroup.mul_mem _ hy ha) (Subgroup.inv_mem _ hy),
    fun b hb => by
      have := c.comm y hy b hb
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hb⟩

variable (c : CaseAData D t) (hsq : t * t = 1)
include hsq

theorem s3e_inv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq

theorem s3e_swap1 {a : D} (ha : a ∈ c.Y₁) : t * a * t ∈ c.Y₂ := by
  have := c.swap₁ a ha
  rwa [s3e_inv_t hsq] at this

theorem s3e_swap2 {b : D} (hb : b ∈ c.Y₂) : t * b * t ∈ c.Y₁ := by
  have := c.swap₂ b hb
  rwa [s3e_inv_t hsq] at this

omit hsq in
theorem s3e_t_swp : s3e_Swp c t :=
  ⟨fun a ha => c.swap₁ a ha, fun b hb => c.swap₂ b hb⟩

omit hsq in
theorem s3e_t_not_mem : t ∉ s3e_Gam c := fun h => s3e_not_pres_swp c h (s3e_t_swp c)

theorem s3e_conj_t_mem {g : D} (hg : g ∈ s3e_Gam c) : t * g * t ∈ s3e_Gam c := by
  have hinv : (t * g * t)⁻¹ = t * g⁻¹ * t := by
    simp [mul_inv_rev, s3e_inv_t hsq, mul_assoc]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [hinv]
    have h1 := s3e_swap1 c hsq ha
    have h2 := hg.2 _ h1
    have h3 := s3e_swap2 c hsq h2
    have e : t * g * t * a * (t * g⁻¹ * t) = t * (g * (t * a * t) * g⁻¹) * t := by group
    rw [e]; exact h3
  · rw [hinv]
    have h1 := s3e_swap2 c hsq hb
    have h2 := hg.1 _ h1
    have h3 := s3e_swap1 c hsq h2
    have e : t * g * t * b * (t * g⁻¹ * t) = t * (g * (t * b * t) * g⁻¹) * t := by group
    rw [e]; exact h3

theorem s3e_dich (d : D) : d ∈ s3e_Gam c ∨ d * t ∈ s3e_Gam c := by
  rcases c.perm d with h | h
  · exact Or.inl h
  · right
    have hinv : (d * t)⁻¹ = t * d⁻¹ := by
      rw [mul_inv_rev, s3e_inv_t hsq]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rw [hinv]
      have e : d * t * a * (t * d⁻¹) = d * (t * a * t) * d⁻¹ := by group
      rw [e]; exact h.2 _ (s3e_swap1 c hsq ha)
    · rw [hinv]
      have e : d * t * b * (t * d⁻¹) = d * (t * b * t) * d⁻¹ := by group
      rw [e]; exact h.1 _ (s3e_swap2 c hsq hb)

end Factors

theorem s3e_pi_eq_one {D : Type*} [Group D] {Γ Y : Subgroup D}
    (e : Y ≃* alternatingGroup (Fin 5)) (hYΓ : Y ≤ Γ) (π : Γ →* Perm (Fin 5))
    (hπY : ∀ (y : D) (hy : y ∈ Y),
      π ⟨y, hYΓ hy⟩ = ((e ⟨y, hy⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)))
    (g : Γ) (hg : ∀ y ∈ Y, (g : D) * y = y * g) : π g = 1 := by
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by norm_num)
  rw [map_one]
  ext a
  have hy := (e.symm a).2
  have h1 := hπY (e.symm a : D) hy
  have h2 : π g * π ⟨(e.symm a : D), hYΓ hy⟩ = π ⟨(e.symm a : D), hYΓ hy⟩ * π g := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hg _ hy)
  have h3 : ((e ⟨(e.symm a : D), hy⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = (a : Perm (Fin 5)) := by
    have : (⟨(e.symm a : D), hy⟩ : Y) = e.symm a := rfl
    rw [this, MulEquiv.apply_symm_apply]
  rw [h3] at h1
  rw [h1] at h2
  rw [MulAut.conjNormal_apply, MulAut.one_apply]
  rw [h2]
  group

theorem s3e_exists_iota {D : Type} [Group D] {t : D} (c : CaseAData D t) (hsq : t * t = 1) :
    ∃ ι : D →* Wr2 (Perm (Fin 5)), Function.Injective ι ∧ ι t = tau ∧
      ∀ a b : alternatingGroup (Fin 5),
        base (a : Perm (Fin 5)) (b : Perm (Fin 5)) ∈ ι.range := by
  obtain ⟨π, hπY, hπK⟩ := CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv
    (Γ := s3e_Gam c) c.e₁ (s3e_Y₁_le c) (fun g hg y hy => hg.1 y hy)
  obtain ⟨ι, hι1, hιt, hιo⟩ := s3e_exists_wreath_hom (s3e_Gam c) t hsq
    (fun g hg => s3e_conj_t_mem c hsq hg) (s3e_dich c hsq) (s3e_t_not_mem c) π
  have htt : ∀ x : D, t * (t * x) = x := fun x => by rw [← mul_assoc, hsq, one_mul]
  refine ⟨ι, ?_, hιt, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro d hd1
    by_cases hd : d ∈ s3e_Gam c
    · have h := hι1 ⟨d, hd⟩
      have h' : ι d = base (π ⟨d, hd⟩) (π ⟨t * d * t, s3e_conj_t_mem c hsq hd⟩) := h
      rw [hd1, ← base_one, base_injective] at h'
      have h1 := hπK _ h'.1.symm
      have h2 := hπK _ h'.2.symm
      refine c.faithful d (fun a ha => h1 a ha) (fun b hb => ?_)
      have h3 := h2 (t * b * t) (s3e_swap2 c hsq hb)
      have h4 : t * (d * b) * t = t * (b * d) * t := by
        simp only [mul_assoc, htt] at h3 ⊢
        exact h3
      exact mul_left_cancel (mul_right_cancel h4)
    · obtain ⟨a, b, hab⟩ := hιo d hd
      exfalso
      apply swapChar_base_mul_tau_ne_one a b
      rw [← hab, hd1, map_one]
  · have hmem : ∀ y : ↥c.Y₁, ι (y : D) = base (((c.e₁ y : alternatingGroup (Fin 5)) : Perm (Fin 5))) 1 := by
      intro y
      have h := hι1 ⟨(y : D), s3e_Y₁_le c y.2⟩
      have h' : ι (y : D) = base (π ⟨(y : D), s3e_Y₁_le c y.2⟩)
          (π ⟨t * (y : D) * t, s3e_conj_t_mem c hsq (s3e_Y₁_le c y.2)⟩) := h
      rw [h', hπY (y : D) y.2]
      congr 2
      refine s3e_pi_eq_one c.e₁ (s3e_Y₁_le c) π hπY _ (fun z hz => ?_)
      exact (c.comm z hz _ (s3e_swap1 c hsq y.2)).symm
    have hmem2 : ∀ y : ↥c.Y₁, ι (t * (y : D) * t) =
        base 1 (((c.e₁ y : alternatingGroup (Fin 5)) : Perm (Fin 5))) := by
      intro y
      rw [map_mul, map_mul, hιt, hmem y, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
    intro a b
    have e1 : base (a : Perm (Fin 5)) (b : Perm (Fin 5)) =
        base (a : Perm (Fin 5)) 1 * base 1 (b : Perm (Fin 5)) := by
      rw [base_mul_base, mul_one, one_mul]
    rw [e1]
    refine Subgroup.mul_mem _ ⟨(c.e₁.symm a : D), ?_⟩ ⟨t * (c.e₁.symm b : D) * t, ?_⟩
    · rw [hmem]; simp
    · rw [hmem2]; simp

theorem s3e_finish {D : Type} [Group D] {t : D} {K : Subgroup D} (ht_ne : t ≠ 1)
    (hKt : ∀ k ∈ K, k * t = t * k) (hdisj : Disjoint (zpowers t) K)
    (eK : ↥K ≃* Perm (Fin 5)) (ι : D →* Wr2 (Perm (Fin 5))) (hinj : Function.Injective ι)
    (hιt : ι t = tau)
    (hbase : ∀ a b : alternatingGroup (Fin 5),
      base (a : Perm (Fin 5)) (b : Perm (Fin 5)) ∈ ι.range) :
    (ι.range = ⊤ ∨ ι.range = DE4) ∧
      ∀ (k : D) (hk : k ∈ K), (eK ⟨k, hk⟩).IsSwap →
        ∃ σ : Perm (Fin 5), σ.IsSwap ∧ (ι k = base σ σ ∨ ι k = base σ σ * tau) := by
  have hcent : ∀ k : K, ι (k : D) ∈ centralizer ({tau} : Set (Wr2 (Perm (Fin 5)))) := by
    intro k
    rw [mem_centralizer_singleton_iff, ← hιt, ← map_mul, ← map_mul, hKt k k.2]
  let θ : K →* Perm (Fin 5) :=
    s3e_diag.comp ((ι.comp K.subtype).codRestrict
      (centralizer ({tau} : Set (Wr2 (Perm (Fin 5))))) hcent)
  have hθ : ∀ k : K, ι (k : D) = base (θ k) (θ k) ∨ ι (k : D) = base (θ k) (θ k) * tau :=
    fun k => (s3e_cent_cases (hcent k)).2
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rcases hθ k with h | h
    · rw [hk, base_one] at h
      exact Subtype.ext (hinj (h.trans (map_one ι).symm))
    · rw [hk, base_one, one_mul, ← hιt] at h
      have hkt : (k : D) = t := hinj h
      exfalso
      apply ht_ne
      refine (Subgroup.disjoint_def.mp hdisj) (mem_zpowers t) ?_
      rw [← hkt]; exact k.2
  let ψ : Perm (Fin 5) →* Perm (Fin 5) := θ.comp eK.symm.toMonoidHom
  have hψinj : Function.Injective ψ := hθinj.comp eK.symm.injective
  have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
  let ψe : Perm (Fin 5) ≃* Perm (Fin 5) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hψe : ∀ k : K, ψe (eK k) = θ k := fun k => by
    show ψ (eK k) = θ k
    simp [ψ]
  have hdiag : ∀ σ : Perm (Fin 5), base σ σ ∈ ι.range := by
    intro σ
    obtain ⟨s, hs⟩ := hψsurj σ
    have hσ : θ (eK.symm s) = σ := hs
    rcases hθ (eK.symm s) with h | h
    · exact ⟨(eK.symm s : D), by rw [h, hσ]⟩
    · refine ⟨(eK.symm s : D) * t, ?_⟩
      rw [map_mul, h, hσ, hιt, mul_assoc, tau_mul_tau, mul_one]
  have htau : tau ∈ ι.range := ⟨t, hιt⟩
  have hDE : DE4 ≤ ι.range := by
    intro w hw
    rw [mem_DE4] at hw
    have hbase_mem : ∀ a b : Perm (Fin 5), sgnProd (base a b) = 1 → base a b ∈ ι.range := by
      intro a b hab
      rw [sgnProd_base] at hab
      have hm : a⁻¹ * b ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv]
        rcases Int.units_eq_one_or (Perm.sign a) with ha | ha <;>
          rcases Int.units_eq_one_or (Perm.sign b) with hb | hb <;>
          simp_all
      have e1 : base a b = base a a * base 1 (a⁻¹ * b) := by
        rw [base_mul_base, mul_one, mul_inv_cancel_left]
      rw [e1]
      exact Subgroup.mul_mem _ (hdiag a) (hbase 1 ⟨a⁻¹ * b, hm⟩)
    rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact hbase_mem a b hw
    · refine Subgroup.mul_mem _ (hbase_mem a b ?_) htau
      rwa [map_mul, sgnProd_tau, mul_one] at hw
  refine ⟨?_, ?_⟩
  · by_cases hle : ∃ x ∈ ι.range, x ∉ DE4
    · left
      obtain ⟨x, hx, hxD⟩ := hle
      rw [eq_top_iff]
      intro w _
      have hx1 : sgnProd x = -1 := by
        rcases Int.units_eq_one_or (sgnProd x) with h | h
        · exact absurd (mem_DE4.mpr h) hxD
        · exact h
      rcases Int.units_eq_one_or (sgnProd w) with h | h
      · exact hDE (mem_DE4.mpr h)
      · have h1 : w * x ∈ DE4 := by
          rw [mem_DE4, map_mul, h, hx1]; rfl
        have := Subgroup.mul_mem _ (hDE h1) (Subgroup.inv_mem _ hx)
        simpa using this
    · right
      refine le_antisymm (fun x hx => ?_) hDE
      by_contra hxD
      exact hle ⟨x, hx, hxD⟩
  · intro k hk hsw
    refine ⟨θ ⟨k, hk⟩, ?_, hθ ⟨k, hk⟩⟩
    rw [← hψe]
    exact s3e_isSwap_map ψe hsw

theorem caseA_embed {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}
    (h : DShape D t K) (c : CaseAData D t) (eK : ↥K ≃* Equiv.Perm (Fin 5)) :
    ∃ ι : D →* Wr2 (Equiv.Perm (Fin 5)), Function.Injective ι ∧ ι t = tau ∧
      (∀ a b : alternatingGroup (Fin 5),
        base (a : Equiv.Perm (Fin 5)) (b : Equiv.Perm (Fin 5)) ∈ ι.range) ∧
      (ι.range = ⊤ ∨ ι.range = DE4) ∧
      ∀ (k : D) (hk : k ∈ K), (eK ⟨k, hk⟩).IsSwap →
        ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧ (ι k = base σ σ ∨ ι k = base σ σ * tau) := by
  obtain ⟨ι, hinj, hιt, hbase⟩ := s3e_exists_iota c h.t_sq
  have hKt : ∀ k ∈ K, k * t = t * k := fun k hk => by
    have hk' : k ∈ centralizer ({t} : Set D) := by
      rw [h.cent]; exact Subgroup.mem_sup_right hk
    exact mem_centralizer_singleton_iff.mp hk'
  obtain ⟨hr, hsw⟩ := s3e_finish h.t_ne hKt h.disj eK ι hinj hιt hbase
  exact ⟨ι, hinj, hιt, hbase, hr, hsw⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
