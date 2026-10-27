module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPerp
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap

section Aniso

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

structure IsAnisoCoord (Q : QuadraticForm K (ι → K)) (a a' : ι) (b c : K) : Prop where
  ne : a ≠ a'
  map_left : Q (Pi.single a 1) = 1
  map_right : Q (Pi.single a' 1) = c
  polar_left : ∀ v, polar Q (Pi.single a 1) v = b * v a'
  polar_right : ∀ v, polar Q (Pi.single a' 1) v = b * v a
  irr : ∀ s : K, s ^ 2 + b * s + c ≠ 0

variable {Q : QuadraticForm K (ι → K)} {a a' : ι} {b c : K}

theorem IsAnisoCoord.c_ne_zero (h : IsAnisoCoord Q a a' b c) : c ≠ 0 := by
  have := h.irr 0
  simpa using this

theorem IsAnisoCoord.b_ne_zero [Finite K] [CharP K 2] (h : IsAnisoCoord Q a a' b c) : b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' c
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  exact h.irr r (by linear_combination hr + r ^ 2 * h2)

theorem IsAnisoCoord.map_add_smul (h : IsAnisoCoord Q a a' b c) (x y : K) {p : ι → K}
    (hpa : p a = 0) (hpb : p a' = 0) :
    Q (x • Pi.single a 1 + y • Pi.single a' 1 + p) = x ^ 2 + b * x * y + c * y ^ 2 + Q p := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q) (x • _), QuadraticMap.map_smul,
    QuadraticMap.map_smul, h.map_left, h.map_right, polar_add_left, polar_smul_left,
    polar_smul_left, polar_smul_left, h.polar_left, h.polar_left, h.polar_right, hpa, hpb]
  simp
  ring

theorem IsAnisoCoord.apply_eq (h : IsAnisoCoord Q a a' b c) (v : ι → K) :
    Q v = v a ^ 2 + b * v a * v a' + c * v a' ^ 2 + Q (perpPart a a' v) := by
  conv_lhs => rw [eq_add_perpPart a a' v]
  exact h.map_add_smul _ _ (perpPart_apply_left h.ne v) (perpPart_apply_right h.ne v)

theorem IsAnisoCoord.polar_plane_left (h : IsAnisoCoord Q a a' b c) (x y : K) (w : ι → K) :
    polar Q (x • Pi.single a 1 + y • Pi.single a' 1) w = b * (x * w a' + y * w a) := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, h.polar_left, h.polar_right, smul_eq_mul,
    smul_eq_mul]
  ring

theorem IsAnisoCoord.polar_plane_perp (h : IsAnisoCoord Q a a' b c) (x y : K) {p : ι → K}
    (hp : p ∈ perpSub K a a') : polar Q (x • Pi.single a 1 + y • Pi.single a' 1) p = 0 := by
  rw [h.polar_plane_left, hp.1, hp.2]
  ring

end Aniso

section Rotation

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a a' : ι}

@[expose] def anisoRotFun (a a' : ι) (b c p s : K) (v : ι → K) : ι → K := fun i =>
  if i = a then p * v a + c * s * v a' else if i = a' then s * v a + (p + b * s) * v a' else v i

@[expose] def anisoRotLin (a a' : ι) (b c p s : K) : (ι → K) →ₗ[K] (ι → K) where
  toFun := anisoRotFun a a' b c p s
  map_add' v w := by
    funext i
    simp only [anisoRotFun, Pi.add_apply]
    split_ifs <;> ring
  map_smul' r v := by
    funext i
    simp only [anisoRotFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

variable {b c : K}

theorem anisoRotLin_apply (p s : K) (v : ι → K) (i : ι) :
    anisoRotLin a a' b c p s v i =
      if i = a then p * v a + c * s * v a' else if i = a' then s * v a + (p + b * s) * v a'
        else v i := rfl

theorem anisoRotLin_apply_left (p s : K) (v : ι → K) :
    anisoRotLin a a' b c p s v a = p * v a + c * s * v a' := by
  simp [anisoRotLin_apply]

theorem anisoRotLin_apply_right (hne : a ≠ a') (p s : K) (v : ι → K) :
    anisoRotLin a a' b c p s v a' = s * v a + (p + b * s) * v a' := by
  simp [anisoRotLin_apply, hne.symm]

theorem anisoRotLin_apply_of_ne {i : ι} (hia : i ≠ a) (hib : i ≠ a') (p s : K) (v : ι → K) :
    anisoRotLin a a' b c p s v i = v i := by
  simp [anisoRotLin_apply, hia, hib]

theorem anisoRotLin_comp_apply (hne : a ≠ a') (p s p' s' : K) (v : ι → K) :
    anisoRotLin a a' b c p s (anisoRotLin a a' b c p' s' v) =
      anisoRotLin a a' b c (p * p' + c * s * s') (p * s' + p' * s + b * s * s') v := by
  funext i
  by_cases hia : i = a
  · subst hia
    rw [anisoRotLin_apply_left, anisoRotLin_apply_left, anisoRotLin_apply_left, anisoRotLin_apply_right hne]
    ring
  · by_cases hib : i = a'
    · subst hib
      rw [anisoRotLin_apply_right hne, anisoRotLin_apply_right hne, anisoRotLin_apply_left,
        anisoRotLin_apply_right hne]
      ring
    · rw [anisoRotLin_apply_of_ne hia hib, anisoRotLin_apply_of_ne hia hib, anisoRotLin_apply_of_ne hia hib]

theorem anisoRotLin_comm_apply (hne : a ≠ a') (p s p' s' : K) (v : ι → K) :
    anisoRotLin a a' b c p s (anisoRotLin a a' b c p' s' v) =
      anisoRotLin a a' b c p' s' (anisoRotLin a a' b c p s v) := by
  rw [anisoRotLin_comp_apply hne, anisoRotLin_comp_apply hne,
    show p * p' + c * s * s' = p' * p + c * s' * s by ring,
    show p * s' + p' * s + b * s * s' = p' * s + p * s' + b * s' * s by ring]

theorem anisoRotLin_one_zero (v : ι → K) : anisoRotLin a a' b c 1 0 v = v := by
  funext i
  simp only [anisoRotLin_apply]
  split_ifs with h1 h2
  · subst h1; ring
  · subst h2; ring
  · rfl

theorem anisoRotLin_apply_of_mem_perpSub (p s : K) {v : ι → K} (hv : v ∈ perpSub K a a') :
    anisoRotLin a a' b c p s v = v := by
  funext i
  simp only [anisoRotLin_apply]
  split_ifs with h1 h2
  · subst h1
    rw [hv.1, hv.2]
    ring
  · subst h2
    rw [hv.1, hv.2]
    ring
  · rfl

theorem anisoRotLin_mem_planeSub (p s : K) {v : ι → K} (hv : v ∈ planeSub K a a') :
    anisoRotLin a a' b c p s v ∈ planeSub K a a' := by
  intro i hia hib
  rw [anisoRotLin_apply_of_ne hia hib]
  exact hv i hia hib

theorem perpPart_anisoRotLin (hne : a ≠ a') (p s : K) (v : ι → K) :
    perpPart a a' (anisoRotLin a a' b c p s v) = perpPart a a' v := by
  funext i
  by_cases hia : i = a
  · subst hia
    rw [perpPart_apply_left hne, perpPart_apply_left hne]
  · by_cases hib : i = a'
    · subst hib
      rw [perpPart_apply_right hne, perpPart_apply_right hne]
    · rw [perpPart_apply_of_ne hia hib, perpPart_apply_of_ne hia hib,
        anisoRotLin_apply_of_ne hia hib]

theorem anisoRotLin_inv_comp_apply [CharP K 2] (hne : a ≠ a') {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) (v : ι → K) :
    anisoRotLin a a' b c (p + b * s) s (anisoRotLin a a' b c p s v) = v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [anisoRotLin_comp_apply hne, show (p + b * s) * p + c * s * s = 1 by linear_combination hN,
    show (p + b * s) * s + p * s + b * s * s = 0 by linear_combination (p * s + b * s ^ 2) * h2,
    anisoRotLin_one_zero]

theorem anisoRotLin_comp_inv_apply [CharP K 2] (hne : a ≠ a') {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) (v : ι → K) :
    anisoRotLin a a' b c p s (anisoRotLin a a' b c (p + b * s) s v) = v := by
  rw [anisoRotLin_comm_apply hne, anisoRotLin_inv_comp_apply hne hN]

@[expose] noncomputable def anisoRotEquiv [CharP K 2] (hne : a ≠ a') (b c : K) {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofLinearMap (anisoRotLin a a' b c p s) (anisoRotLin a a' b c (p + b * s) s)
    (LinearMap.ext fun v => anisoRotLin_comp_inv_apply hne hN v)
    (LinearMap.ext fun v => anisoRotLin_inv_comp_apply hne hN v)

theorem anisoRotEquiv_apply [CharP K 2] (hne : a ≠ a') {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) (v : ι → K) :
    anisoRotEquiv hne b c hN v = anisoRotLin a a' b c p s v := rfl

theorem norm_rot_mul [CharP K 2] (p s p' s' : K) :
    (p * p' + c * s * s') ^ 2 + b * (p * p' + c * s * s') * (p * s' + p' * s + b * s * s') +
        c * (p * s' + p' * s + b * s * s') ^ 2 =
      (p ^ 2 + b * p * s + c * s ^ 2) * (p' ^ 2 + b * p' * s' + c * s' ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (2 * c * p * p' * s * s' + b ^ 2 * c * s ^ 2 * s' ^ 2 +
    b * c * p * s * s' ^ 2 + b * c * p' * s ^ 2 * s') * h2

@[expose] def anisoRotSub [CharP K 2] (hne : a ≠ a') (b c : K) :
    Subgroup ((ι → K) ≃ₗ[K] (ι → K)) where
  carrier := {g | ∃ p s : K, p ^ 2 + b * p * s + c * s ^ 2 = 1 ∧
    ∀ v, g v = anisoRotLin a a' b c p s v}
  one_mem' := ⟨1, 0, by ring, fun v => (anisoRotLin_one_zero v).symm⟩
  mul_mem' := by
    rintro g g' ⟨p, s, hN, hg⟩ ⟨p', s', hN', hg'⟩
    refine ⟨p * p' + c * s * s', p * s' + p' * s + b * s * s', ?_, fun v => ?_⟩
    · rw [norm_rot_mul, hN, hN', one_mul]
    · rw [LinearEquiv.mul_apply, hg', hg, anisoRotLin_comp_apply hne]
  inv_mem' := by
    rintro g ⟨p, s, hN, hg⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    refine ⟨p + b * s, s, by linear_combination hN + (b * p * s + b ^ 2 * s ^ 2) * h2,
      fun v => ?_⟩
    have hv : g (anisoRotLin a a' b c (p + b * s) s v) = v := by
      rw [hg, anisoRotLin_comp_inv_apply hne hN]
    calc g⁻¹ v = g⁻¹ (g (anisoRotLin a a' b c (p + b * s) s v)) := by rw [hv]
      _ = anisoRotLin a a' b c (p + b * s) s v := g.symm_apply_apply _

theorem mem_anisoRotSub [CharP K 2] (hne : a ≠ a') {g : (ι → K) ≃ₗ[K] (ι → K)} :
    g ∈ anisoRotSub hne b c ↔ ∃ p s : K, p ^ 2 + b * p * s + c * s ^ 2 = 1 ∧
      ∀ v, g v = anisoRotLin a a' b c p s v := Iff.rfl

theorem anisoRotEquiv_mem_anisoRotSub [CharP K 2] (hne : a ≠ a') {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) : anisoRotEquiv hne b c hN ∈ anisoRotSub hne b c :=
  ⟨p, s, hN, fun _ => rfl⟩

theorem anisoRotSub_comm [CharP K 2] (hne : a ≠ a') {g g' : (ι → K) ≃ₗ[K] (ι → K)}
    (hg : g ∈ anisoRotSub hne b c) (hg' : g' ∈ anisoRotSub hne b c) : g * g' = g' * g := by
  obtain ⟨p, s, -, hgp⟩ := hg
  obtain ⟨p', s', -, hgp'⟩ := hg'
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgp', hgp, hgp, hgp',
    anisoRotLin_comm_apply hne]

theorem eq_one_of_mem_anisoRotSub_of_mul_self [CharP K 2] (hne : a ≠ a') (hb : b ≠ 0)
    {g : (ι → K) ≃ₗ[K] (ι → K)} (hg : g ∈ anisoRotSub hne b c) (hgg : g * g = 1) : g = 1 := by
  obtain ⟨p, s, hN, hgp⟩ := hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := congrFun (LinearEquiv.congr_fun hgg (Pi.single a 1)) a'
  rw [LinearEquiv.mul_apply, hgp, hgp, anisoRotLin_comp_apply hne, anisoRotLin_apply_right hne,
    LinearEquiv.coe_one, id] at h1
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, mul_one, mul_zero, add_zero] at h1
  have hs : s = 0 := by
    have : b * s ^ 2 = 0 := by linear_combination h1 - (p * s) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hb)
  have hp : p = 1 := by
    apply eq_one_of_mul_self_eq_one
    rw [hs] at hN
    linear_combination hN
  ext v
  rw [hgp, hp, hs, anisoRotLin_one_zero, LinearEquiv.coe_one, id]

end Rotation

section Isometry

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
  {a a' : ι} {b c : K}

theorem IsAnisoCoord.anisoRotLin_isometry [CharP K 2] (h : IsAnisoCoord Q a a' b c) {p s : K}
    (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1) (v : ι → K) :
    Q (anisoRotLin a a' b c p s v) = Q v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [h.apply_eq, h.apply_eq v, perpPart_anisoRotLin h.ne, anisoRotLin_apply_left,
    anisoRotLin_apply_right h.ne]
  linear_combination (v a ^ 2 + b * v a * v a' + c * v a' ^ 2) * hN +
    ((2 * p * c * s + b * c * s ^ 2) * v a * v a' + (b * c * p * s + b ^ 2 * c * s ^ 2) * v a' ^ 2) *
      h2

theorem IsAnisoCoord.anisoRotSub_le_orthogonalGroup [CharP K 2] (h : IsAnisoCoord Q a a' b c) :
    anisoRotSub h.ne b c ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro g ⟨p, s, hN, hg⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [hg, h.anisoRotLin_isometry hN]

end Isometry

section Dickson

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a a' : ι} {b c : K}

open Module
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] noncomputable def planeSubEquiv (hne : a ≠ a') : planeSub K a a' ≃ₗ[K] K × K where
  toFun w := ((w : ι → K) a, (w : ι → K) a')
  invFun z := ⟨z.1 • Pi.single a 1 + z.2 • Pi.single a' 1, by
    intro i hia hib
    simp [hia, hib]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := Subtype.ext (eq_planePart_of_mem hne w.2).symm
  right_inv z := by
    simp [hne, hne.symm]

theorem finrank_planeSub (hne : a ≠ a') : finrank K (planeSub K a a') = 2 := by
  rw [(planeSubEquiv (K := K) hne).finrank_eq, finrank_prod, finrank_self]

theorem sub_mem_planeSub_of_rot {g : (ι → K) ≃ₗ[K] (ι → K)} {p s : K}
    (hg : ∀ v, g v = anisoRotLin a a' b c p s v) (v : ι → K) : g v - v ∈ planeSub K a a' := by
  intro i hia hib
  rw [Pi.sub_apply, hg, anisoRotLin_apply_of_ne hia hib, sub_self]

theorem rot_sub_apply_plane (hne : a ≠ a') {g : (ι → K) ≃ₗ[K] (ι → K)} {p s : K}
    (hg : ∀ v, g v = anisoRotLin a a' b c p s v) (α β : K) :
    g (α • Pi.single a 1 + β • Pi.single a' 1) - (α • Pi.single a 1 + β • Pi.single a' 1) =
      ((p - 1) * α + c * s * β) • Pi.single a 1 + (s * α + (p + b * s - 1) * β) •
        Pi.single a' 1 := by
  funext i
  rw [Pi.sub_apply, hg]
  by_cases hia : i = a
  · rw [hia, anisoRotLin_apply_left]
    simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    ring
  · by_cases hib : i = a'
    · rw [hib, anisoRotLin_apply_right hne]
      simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
      ring
    · rw [anisoRotLin_apply_of_ne hia hib]
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]

theorem commSpace_eq_planeSub_of_rot [CharP K 2] (hne : a ≠ a') (hb : b ≠ 0)
    {g : (ι → K) ≃ₗ[K] (ι → K)} {p s : K} (hN : p ^ 2 + b * p * s + c * s ^ 2 = 1)
    (hs : s ≠ 0) (hg : ∀ v, g v = anisoRotLin a a' b c p s v) : commSpace g = planeSub K a a' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbs : b * s ≠ 0 := mul_ne_zero hb hs
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact sub_mem_planeSub_of_rot hg v
  ·
    have hea : (Pi.single a 1 : ι → K) ∈ commSpace g := by
      refine mem_commSpace.mpr ⟨((p + 1 + b * s) / (b * s)) • Pi.single a 1 +
        (s / (b * s)) • Pi.single a' 1, ?_⟩
      rw [rot_sub_apply_plane hne hg]
      have e1 : (p - 1) * ((p + 1 + b * s) / (b * s)) + c * s * (s / (b * s)) = 1 := by
        field_simp
        linear_combination hN - (b * s) * h2
      have e2 : s * ((p + 1 + b * s) / (b * s)) + (p + b * s - 1) * (s / (b * s)) = 0 := by
        field_simp
        linear_combination (p + b * s) * h2
      rw [e1, e2, one_smul, zero_smul, add_zero]
    have heb : (Pi.single a' 1 : ι → K) ∈ commSpace g := by
      refine mem_commSpace.mpr ⟨((c * s) / (b * s)) • Pi.single a 1 +
        ((p + 1) / (b * s)) • Pi.single a' 1, ?_⟩
      rw [rot_sub_apply_plane hne hg]
      have e1 : (p - 1) * ((c * s) / (b * s)) + c * s * ((p + 1) / (b * s)) = 0 := by
        field_simp
        linear_combination (c * p) * h2
      have e2 : s * ((c * s) / (b * s)) + (p + b * s - 1) * ((p + 1) / (b * s)) = 1 := by
        field_simp
        linear_combination hN
      rw [e1, e2, one_smul, zero_smul, zero_add]
    intro w hw
    rw [eq_planePart_of_mem hne hw]
    exact add_mem (Submodule.smul_mem _ _ hea) (Submodule.smul_mem _ _ heb)

theorem IsAnisoCoord.anisoRotSub_le_orthDerived [Finite K] [CharP K 2] [Fintype ι]
    {Q : QuadraticForm K (ι → K)} (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    anisoRotSub h.ne b c ≤ orthDerived Q := by
  intro g hg
  have hgO := h.anisoRotSub_le_orthogonalGroup hg
  obtain ⟨p, s, hN, hgp⟩ := hg
  apply CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  refine mem_omegaGroup.mpr ⟨hgO, ?_⟩
  by_cases hs : s = 0
  · have hp : p = 1 := by
      apply eq_one_of_mul_self_eq_one
      rw [hs] at hN
      linear_combination hN
    have hg1 : g = 1 := by
      ext v
      rw [hgp, hp, hs, anisoRotLin_one_zero, LinearEquiv.coe_one, id]
    rw [hg1]
    have : commSpace (1 : (ι → K) ≃ₗ[K] (ι → K)) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨v, rfl⟩
      simp
    rw [this, finrank_bot]
    exact ⟨0, rfl⟩
  · rw [commSpace_eq_planeSub_of_rot h.ne h.b_ne_zero hN hs hgp, finrank_planeSub h.ne]
    exact ⟨1, rfl⟩

end Dickson

end CFSG.SeitzReduction.OmegaPilot
