module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5VLikeField

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

structure RootCoords (P : Subgroup G) (a : ℕ) (y : G) (u v : G → BinaryGaloisField (2 * a + 1))
    (κ : BinaryGaloisField (2 * a + 1)) : Prop where
  mul : ∀ x ∈ P, ∀ x' ∈ P, u (x * x') = u x + u x' ∧
    v (x * x') = v x + v x' + u x * u x' ^ 2 ^ (a + 1)
  inj : ∀ x ∈ P, ∀ x' ∈ P, u x = u x' → v x = v x' → x = x'
  surj : ∀ α β, ∃ x ∈ P, u x = α ∧ v x = β
  conj_mem : ∀ x ∈ P, y⁻¹ * x * y ∈ P
  conj_u : ∀ x ∈ P, u (y⁻¹ * x * y) = κ * u x
  conj_v : ∀ x ∈ P, u x = 0 → v (y⁻¹ * x * y) = κ ^ (2 ^ (a + 1) + 1) * v x

open SuzukiAut CFSG.BenderSuzuki.MatrixGroups in
theorem exists_rootCoords_of_sz {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {a : ℕ}
    (ha : 1 ≤ a) (e : rankTwoQuot L ≃* Sz a) (hP : IsSylowOf 2 P L) {y : G} (hyL : y ∈ L)
    (hyP : y ∈ normalizer (P : Set G)) :
    ∃ (u v : G → BinaryGaloisField (2 * a + 1)) (κ : BinaryGaloisField (2 * a + 1)),
      RootCoords P a y u v κ := by
  classical
  have hm : 0 < a := by omega
  set e' : rankTwoQuot L ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm with he'
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e' e'.surjective
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_rootSub a hm
  set S : Sylow 2 (SuzukiMatrixGroup a) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hS : (S : Subgroup (SuzukiMatrixGroup a)) = (R : Subgroup _).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup a) S₀ S
  have hmem : ∀ s, s ∈ (S : Subgroup (SuzukiMatrixGroup a)) ↔ g⁻¹ * s * g ∈ rootSub a := by
    intro s
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS₀]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  set Ψ : L →* SuzukiMatrixGroup a := (MulAut.conj g⁻¹).toMonoidHom.comp
    (e'.toMonoidHom.comp (QuotientGroup.mk' (center L))) with hΨ
  have hΨapp : ∀ l, Ψ l = g⁻¹ * e' (QuotientGroup.mk' (center L) l) * g := fun l => by
    simp [hΨ]
  have hΨP : ∀ x (hx : x ∈ P), Ψ ⟨x, hP.le hx⟩ ∈ rootSub a := fun x hx => by
    rw [hΨapp, ← hmem, hS]
    exact ⟨_, hR ▸ ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hΨsurj : ∀ s ∈ rootSub a, ∃ x, ∃ hx : x ∈ P, Ψ ⟨x, hP.le hx⟩ = s := by
    intro s hs
    have h1 : g * s * g⁻¹ ∈ (S : Subgroup (SuzukiMatrixGroup a)) := by
      rw [hmem]; simpa [mul_assoc] using hs
    rw [hS] at h1
    obtain ⟨r, hr, hrs⟩ := h1
    rw [← hR] at hr
    obtain ⟨⟨x, hx⟩, rfl⟩ := hr
    refine ⟨x, hx, ?_⟩
    rw [hΨapp]
    have : e' (sylowProj hP.le ⟨x, hx⟩) = g * s * g⁻¹ := hrs
    rw [sylowProj_apply] at this
    rw [this]
    group
  have hΨinj : ∀ x (hx : x ∈ P) x' (hx' : x' ∈ P), Ψ ⟨x, hP.le hx⟩ = Ψ ⟨x', hP.le hx'⟩ →
      x = x' := by
    intro x hx x' hx' h
    rw [hΨapp, hΨapp, mul_left_inj, mul_right_inj] at h
    have h2 : sylowProj hP.le ⟨x, hx⟩ = sylowProj hP.le ⟨x', hx'⟩ := e'.injective h
    exact congrArg Subtype.val (sylowProj_injective hZ hP.isPGroup hP.le h2)
  have hex : ∀ x : G, ∃ αβ : BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1),
      ∀ hx : x ∈ P, Ψ ⟨x, hP.le hx⟩ = root a αβ.1 αβ.2 := by
    intro x
    by_cases hx : x ∈ P
    · obtain ⟨α, β, h⟩ := (mem_rootSub a).mp (hΨP x hx)
      exact ⟨(α, β), fun _ => h⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose f hf using hex
  set yb := Ψ ⟨y, hyL⟩ with hyb
  have hyconj : ∀ x (hx : x ∈ P), Ψ ⟨y⁻¹ * x * y, hP.le (by
      simpa using (mem_normalizer_iff.mp (inv_mem hyP) x).mp hx)⟩ =
      yb⁻¹ * Ψ ⟨x, hP.le hx⟩ * yb := by
    intro x hx
    rw [hyb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hybN : yb ∈ normalizer ((rootSub a : Subgroup (SuzukiMatrixGroup a)) : Set _) := by
    refine mem_normalizer_of_conj_mem_of_finite fun s hs => ?_
    obtain ⟨x, hx, rfl⟩ := hΨsurj s hs
    have hx' : y * x * y⁻¹ ∈ P := (mem_normalizer_iff.mp hyP x).mp hx
    have := hΨP _ hx'
    rwa [show (⟨y * x * y⁻¹, hP.le hx'⟩ : L) = ⟨y, hyL⟩ * ⟨x, hP.le hx⟩ * ⟨y, hyL⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv] at this
  obtain ⟨r₀, hr₀, h₀, hh₀, hy₀⟩ := (normalizer_and_card_sylow a hm).1 yb hybN
  obtain ⟨u₀, v₀, rfl⟩ := (mem_rootSub a).mp hr₀
  obtain ⟨x₀, rfl⟩ := (mem_torusSub a hm).mp hh₀
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  have hc1 : ∀ α β : BinaryGaloisField (2 * a + 1), (root a u₀ v₀)⁻¹ * root a α β * root a u₀ v₀ =
      root a α (β + α * tits a u₀ + u₀ * tits a α) := by
    intro α β
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, root_mul a hm, root_mul a hm]
    have e1 : α + u₀ = u₀ + α := add_comm _ _
    have e2 : β + v₀ + α * tits a u₀ = v₀ + (β + α * tits a u₀ + u₀ * tits a α) + u₀ * tits a α :=
      by linear_combination (-(u₀ * tits a α)) * h2
    rw [e1, e2]
  obtain ⟨ξ, hξ⟩ : ∃ ξ : BinaryGaloisField (2 * a + 1), ξ = x₀ := ⟨_, rfl⟩
  have hx0 : ξ ≠ 0 := hξ ▸ x₀.ne_zero
  have hx₀ : ξ * tits a ξ ≠ 0 := mul_ne_zero hx0 ((map_ne_zero (tits a)).mpr hx0)
  have hc2 : ∀ α β : BinaryGaloisField (2 * a + 1), (torus a x₀)⁻¹ * root a α β * torus a x₀ =
      root a (ξ⁻¹ * α) ((ξ * tits a ξ)⁻¹ * β) := by
    intro α β
    have e : root a α β = torus a x₀ * root a (ξ⁻¹ * α) ((ξ * tits a ξ)⁻¹ * β) *
        (torus a x₀)⁻¹ := by
      rw [torus_conj_root, ← hξ, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul, ← mul_assoc,
        mul_inv_cancel₀ hx₀, one_mul]
    rw [e]
    group
  have hconj : ∀ z, (root a u₀ v₀ * torus a x₀)⁻¹ * z * (root a u₀ v₀ * torus a x₀) =
      (torus a x₀)⁻¹ * ((root a u₀ v₀)⁻¹ * z * root a u₀ v₀) * torus a x₀ := fun z => by group
  refine ⟨fun x => (f x).1, fun x => (f x).2, ξ⁻¹, ⟨fun x hx x' hx' => ?_,
    fun x hx x' hx' hu hv => ?_, fun α β => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx hu => ?_⟩⟩
  · have h1 := hf (x * x') (mul_mem hx hx')
    rw [show (⟨x * x', hP.le (mul_mem hx hx')⟩ : L) = ⟨x, hP.le hx⟩ * ⟨x', hP.le hx'⟩ from rfl,
      map_mul, hf x hx, hf x' hx', root_mul a hm] at h1
    obtain ⟨e1, e2⟩ := root_injective a h1
    exact ⟨e1.symm, by rw [← e2, tits_apply]⟩
  · refine hΨinj x hx x' hx' ?_
    rw [hf x hx, hf x' hx', hu, hv]
  · obtain ⟨x, hx, hxs⟩ := hΨsurj _ (root_mem a α β)
    rw [hf x hx] at hxs
    obtain ⟨e1, e2⟩ := root_injective a hxs
    exact ⟨x, hx, e1, e2⟩
  · simpa using (mem_normalizer_iff.mp (inv_mem hyP) x).mp hx
  · have hx' : y⁻¹ * x * y ∈ P := by simpa using (mem_normalizer_iff.mp (inv_mem hyP) x).mp hx
    have h1 := hf _ hx'
    rw [hyconj x hx, hf x hx, hy₀, hconj, hc1, hc2] at h1
    exact (root_injective a h1).1.symm
  · have hx' : y⁻¹ * x * y ∈ P := by simpa using (mem_normalizer_iff.mp (inv_mem hyP) x).mp hx
    have h1 := hf _ hx'
    rw [hyconj x hx, hf x hx, hy₀, hconj, hc1, hc2] at h1
    rw [(root_injective a h1).2.symm]
    rw [hu, zero_mul, add_zero, map_zero, mul_zero, add_zero, tits_apply, inv_pow, ← pow_succ']

namespace RootCoords

variable {P : Subgroup G} {a : ℕ} {y : G} {u v : G → BinaryGaloisField (2 * a + 1)}
  {κ : BinaryGaloisField (2 * a + 1)}

omit [Finite G] in
theorem u_one (h : RootCoords P a y u v κ) : u 1 = 0 := by
  have h1 := (h.mul 1 (one_mem _) 1 (one_mem _)).1
  rw [mul_one] at h1
  exact (add_eq_left.mp h1.symm)

omit [Finite G] in
theorem v_one (h : RootCoords P a y u v κ) : v 1 = 0 := by
  have h1 := (h.mul 1 (one_mem _) 1 (one_mem _)).2
  rw [mul_one, h.u_one, zero_mul, add_zero] at h1
  exact (add_eq_left.mp h1.symm)

omit [Finite G] in
theorem inv (h : RootCoords P a y u v κ) {x : G} (hx : x ∈ P) :
    u x⁻¹ = u x ∧ v x⁻¹ = v x + u x ^ (2 ^ (a + 1) + 1) := by
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, h3⟩ := h.mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.u_one] at h1
  rw [mul_inv_cancel, h.v_one] at h3
  have hu : u x⁻¹ = u x := by linear_combination -h1 - u x * h2
  refine ⟨hu, ?_⟩
  rw [hu] at h3
  linear_combination -h3 - (v x + u x ^ (2 ^ (a + 1) + 1)) * h2

omit [Finite G] in
theorem sq (h : RootCoords P a y u v κ) {x : G} (hx : x ∈ P) :
    u (x ^ 2) = 0 ∧ v (x ^ 2) = u x ^ (2 ^ (a + 1) + 1) := by
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, h3⟩ := h.mul x hx x hx
  rw [← _root_.sq] at h1 h3
  exact ⟨by linear_combination h1 + u x * h2, by linear_combination h3 + v x * h2⟩

omit [Finite G] in
theorem comm (h : RootCoords P a y u v κ) {x x' : G} (hx : x ∈ P) (hx' : x' ∈ P) :
    u (x * x' * x⁻¹ * x'⁻¹) = 0 ∧
      v (x * x' * x⁻¹ * x'⁻¹) = u x * u x' ^ 2 ^ (a + 1) + u x' * u x ^ 2 ^ (a + 1) := by
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  obtain ⟨i1, i2⟩ := h.inv hx
  obtain ⟨i3, i4⟩ := h.inv hx'
  obtain ⟨a1, b1⟩ := h.mul _ hx _ hx'
  obtain ⟨a2, b2⟩ := h.mul _ (mul_mem hx hx') _ (inv_mem hx)
  obtain ⟨a3, b3⟩ := h.mul _ (mul_mem (mul_mem hx hx') (inv_mem hx)) _ (inv_mem hx')
  rw [i1, a1] at a2
  rw [i3, a2] at a3
  rw [i1, i2, a1, b1] at b2
  rw [i3, i4, a2, b2] at b3
  refine ⟨by linear_combination a3 + (u x + u x') * h2, ?_⟩
  rw [b3]
  linear_combination (v x + v x' + u x ^ (2 ^ (a + 1) + 1) + u x' ^ (2 ^ (a + 1) + 1) +
    u x * u x' ^ 2 ^ (a + 1)) * h2

omit [Finite G] in
theorem commute_of_u_eq_zero (h : RootCoords P a y u v κ) {x : G} (hx : x ∈ P) (hu : u x = 0)
    {x' : G} (hx' : x' ∈ P) : x' * x = x * x' := by
  obtain ⟨a1, b1⟩ := h.mul _ hx' _ hx
  obtain ⟨a2, b2⟩ := h.mul _ hx _ hx'
  refine h.inj _ (mul_mem hx' hx) _ (mul_mem hx hx') (by rw [a1, a2]; exact add_comm _ _) ?_
  rw [b1, b2, hu, zero_mul, add_zero, zero_pow (pow_pos two_pos _).ne', mul_zero, add_zero]
  exact add_comm _ _

omit [Finite G] in
theorem mem_center_iff (h : RootCoords P a y u v κ) (ha : 1 ≤ a) {x : G} (hx : x ∈ P) :
    x ∈ P ⊓ centralizer (P : Set G) ↔ u x = 0 := by
  classical
  refine ⟨fun hxc => ?_, fun hu =>
    mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun x' hx' => h.commute_of_u_eq_zero hx hu hx'⟩⟩
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  have hfix : ∀ x' ∈ P, u x * u x' ^ 2 ^ (a + 1) = u x' * u x ^ 2 ^ (a + 1) := by
    intro x' hx'
    have hc := mem_centralizer_iff.mp (mem_inf.mp hxc).2 x' hx'
    have e1 := (h.mul _ hx' _ hx).2
    have e2 := (h.mul _ hx _ hx').2
    rw [hc, e2] at e1
    linear_combination e1
  obtain ⟨x₁, hx₁, hu₁, -⟩ := h.surj 1 0
  have h1 := hfix x₁ hx₁
  rw [hu₁, one_pow, mul_one, one_mul] at h1
  rcases VLike.eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (VLike.coprime_a_succ a) h1.symm
    with h0 | h1'
  · exact h0
  · exfalso
    have hall : ∀ w : BinaryGaloisField (2 * a + 1), w = 0 ∨ w = 1 := by
      intro w
      obtain ⟨x', hx', hu', -⟩ := h.surj w 0
      have h3 := hfix x' hx'
      rw [h1', one_mul, one_pow, mul_one, hu'] at h3
      exact VLike.eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (VLike.coprime_a_succ a) h3
    have hsub : (Finset.univ : Finset (BinaryGaloisField (2 * a + 1))) ⊆ {0, 1} := fun w _ => by
      rcases hall w with hw | hw <;> simp [hw]
    have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, hK] at h4
    have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h5.trans h4) (by norm_num)

omit [Finite G] in
theorem pow_conj (h : RootCoords P a y u v κ) (k : ℕ) {x : G} (hx : x ∈ P) :
    (y ^ k)⁻¹ * x * y ^ k ∈ P ∧ u ((y ^ k)⁻¹ * x * y ^ k) = κ ^ k * u x ∧
      (u x = 0 → v ((y ^ k)⁻¹ * x * y ^ k) = (κ ^ (2 ^ (a + 1) + 1)) ^ k * v x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    obtain ⟨hm, hu, hv⟩ := ih
    have e : (y ^ (k + 1))⁻¹ * x * y ^ (k + 1) = y⁻¹ * ((y ^ k)⁻¹ * x * y ^ k) * y := by
      rw [pow_succ]; group
    rw [e]
    refine ⟨h.conj_mem _ hm, by rw [h.conj_u _ hm, hu, pow_succ]; ring, fun hu0 => ?_⟩
    rw [h.conj_v _ hm (by rw [hu, hu0, mul_zero]), hv hu0, pow_succ]
    ring

end RootCoords

namespace Sec3.SzR

variable {L T R : Subgroup G} {a : ℕ} {y d : G}

theorem exists_rootCoords (hS : SzR G L T R a y d) :
    ∃ (u v : G → BinaryGaloisField (2 * a + 1)) (κ : BinaryGaloisField (2 * a + 1)),
      RootCoords (T ⊓ L) a d u v κ ∧ ∀ w, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w := by
  obtain ⟨hyL, hyN⟩ := mem_inf.mp hS.torus.mem
  obtain ⟨u, v, κ, h⟩ := exists_rootCoords_of_sz hS.oddCenter hS.one_le hS.iso.some
    hS.sec3.isSylowOf_T₁ hyL hyN
  have hdy : ∀ x ∈ T ⊓ L, d⁻¹ * x * d = y⁻¹ * x * y := fun x hx => by
    simpa using inv_pow_conj_eq hS.mem_normalizer_gmsW hS.torus.mem_normalizer_gmsW hS.conj_eq 1
      x (mem_sup_left hx)
  have hd : RootCoords (T ⊓ L) a d u v κ :=
    ⟨h.mul, h.inj, h.surj, fun x hx => hdy x hx ▸ h.conj_mem x hx,
      fun x hx => hdy x hx ▸ h.conj_u x hx, fun x hx hu => hdy x hx ▸ h.conj_v x hx hu⟩
  refine ⟨u, v, κ, hd, fun w hw => ?_⟩
  obtain ⟨b₁, hb₁, hu₁, hv₁⟩ := hd.surj 0 1
  obtain ⟨b, hb, hu, hv⟩ := hd.surj 0 w
  have hA₁ := (hd.mem_center_iff hS.one_le hb₁).mpr hu₁
  have hA := (hd.mem_center_iff hS.one_le hb).mpr hu
  have hb₁1 : b₁ ≠ 1 := by rintro rfl; rw [hd.v_one] at hv₁; exact zero_ne_one hv₁
  have hb1 : b ≠ 1 := by rintro rfl; rw [hd.v_one] at hv; exact hw hv.symm
  obtain ⟨k, hk⟩ := hS.exists_pow_conj_eq_gmsA hA₁ hA hb₁1 hb1
  have h1 := (hd.pow_conj k hb₁).2.2 hu₁
  rw [hk, hv, hv₁, mul_one] at h1
  exact ⟨k, h1.symm⟩

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
