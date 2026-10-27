module

public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Orth
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

structure InducedBy (θ : ↥(orthDerived Q) →* S) (g : V ≃ₗ[K] V) (x : MulAut S) : Prop where
  mem : ∀ h ∈ orthDerived Q, g * h * g⁻¹ ∈ orthDerived Q
  act : ∀ h : ↥(orthDerived Q), x (θ h) = θ ⟨g * h * g⁻¹, mem h h.2⟩

theorem neg_one_mem_commutator [Finite K] (hK : Nat.card K = 3) :
    (-1 : SL(2, K)) ∈ commutator SL(2, K) :=
  (mem_commutator_sl2_iff hK).mpr (by rw [show 4 = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow])

theorem sl2I_mem_commutator [Finite K] (hK : Nat.card K = 3) :
    (sl2I : SL(2, K)) ∈ commutator SL(2, K) :=
  (mem_commutator_sl2_iff hK).mpr sl2I_pow_four

theorem eq_of_theta_eq_of_apply (hQ : (polarBilin Q).Nondegenerate)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {m m' : V ≃ₗ[K] V} (hm : m ∈ orthDerived Q) (hm' : m' ∈ orthDerived Q)
    (h : θ ⟨m, hm⟩ = θ ⟨m', hm'⟩) {u : V} (hu : u ≠ 0) (hmu : m u = m' u) : m = m' := by
  haveI : Nontrivial V := ⟨⟨u, 0, hu⟩⟩
  obtain ⟨c, -, hc⟩ := exists_smul_of_map_eq hQ hker h
  have hmu0 : m u ≠ 0 := fun h0 => hu (m.injective (by rw [h0, map_zero]))
  have hc1 : c = 1 := by
    have h1 : (1 - c) • m u = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      exact hmu.trans (hc u)
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hmu0)).symm
  refine LinearEquiv.ext fun v => ?_
  have hv := hc v
  rw [hc1, one_smul] at hv
  exact hv.symm

private theorem lapply_inv_apply (g : V ≃ₗ[K] V) (v : V) : g (g⁻¹ v) = v := by simp

private theorem linv_apply_apply (g : V ≃ₗ[K] V) (v : V) : g⁻¹ (g v) = v := by simp

private theorem exists_ne_zero_mem_perp [FiniteDimensional K V] (F : Frame Q)
    (hn : 5 ≤ Module.finrank K V) : ∃ v ∈ F.perp, v ≠ 0 := by
  have h := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank K F.perp by omega)
  exact ⟨v, v.2, fun h0 => hv (Subtype.ext h0)⟩

private theorem La_apply_of_mem_perp (F : Frame Q) (a : SL(2, K)) {v : V} (hv : v ∈ F.perp) :
    F.La a v = v :=
  F.La_apply_of_coords_eq_zero a ((Frame.mem_perp_iff F).mp hv)

private theorem exists_smul_conj [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x) {m : V ≃ₗ[K] V}
    (hm : m ∈ orthDerived Q) (hfix : x (θ ⟨m, hm⟩) = θ ⟨m, hm⟩) :
    ∃ c : K, c * c = 1 ∧ ∀ v, m v = c • (g * m * g⁻¹) v :=
  exists_smul_of_map_eq hQ hker ((hx.act ⟨m, hm⟩).symm.trans hfix)

theorem commute_La_neg_one_of_fix [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hfix : ∀ a ∈ frameMember θ F, x a = a) : g * F.La (-1) = F.La (-1) * g := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_mem_perp F hn
  haveI : Nontrivial V := ⟨⟨v₀, 0, hv₀0⟩⟩
  obtain ⟨c, hc, hcv⟩ := exists_smul_conj hQ hker hx (La_neg_one_mem_orthDerived F)
    (hfix _ (La_mem_frameMember θ F (neg_one_mem_commutator hK)))
  have hcases : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with rfl | rfl
  · refine LinearEquiv.ext fun v => ?_
    have h1 := hcv (g v)
    rw [one_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, linv_apply_apply] at h1
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact h1.symm
  · exfalso
    have hgv₀ : F.La (-1) (g v₀) = -(g v₀) := by
      have h1 := hcv (g v₀)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, linv_apply_apply,
        La_apply_of_mem_perp F (-1) hv₀, neg_one_smul] at h1
      exact h1
    obtain ⟨c', hc', hc'v⟩ := exists_smul_conj hQ hker hx
      (frameQ8_le F (La_mem_frameQ8 F (sl2I_mem_commutator hK)))
      (hfix _ (La_mem_frameMember θ F (sl2I_mem_commutator hK)))
    have hLi : F.La sl2I (g v₀) = c' • g v₀ := by
      rw [hc'v (g v₀), LinearEquiv.mul_apply, LinearEquiv.mul_apply, linv_apply_apply,
        La_apply_of_mem_perp F _ hv₀]
    have hsq : F.La sl2I (F.La sl2I (g v₀)) = -(g v₀) := by
      have h1 : F.La (-1) = F.La sl2I * F.La sl2I := by
        rw [← map_mul, ← pow_two, sl2I_sq]
      rw [← hgv₀, h1, LinearEquiv.mul_apply]
    have hsq' : F.La sl2I (F.La sl2I (g v₀)) = g v₀ := by
      rw [hLi, map_smul, hLi, smul_smul, hc', one_smul]
    have h3 : g v₀ = -(g v₀) := hsq'.symm.trans hsq
    have h4 : (2 : K) • g v₀ = 0 := by
      rw [two_smul]
      nth_rw 1 [h3]
      exact neg_add_cancel _
    have h5 : g v₀ = 0 := (smul_eq_zero.mp h4).resolve_left h2
    exact hv₀0 (g.injective (by rw [h5, map_zero]))

theorem commute_La_of_fix [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hfix : ∀ a ∈ frameMember θ F, x a = a) :
    ∀ a ∈ commutator SL(2, K), g * F.La a = F.La a * g := by
  intro a ha
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hg₁ := commute_La_neg_one_of_fix hK hQ hn hker hx hfix
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_mem_perp F hn
  have hLa : F.La a ∈ orthDerived Q := frameQ8_le F (La_mem_frameQ8 F ha)
  have hconj : g * F.La a * g⁻¹ = F.La a := by
    refine eq_of_theta_eq_of_apply hQ hker (hx.mem _ hLa) hLa ?_ hv₀0 ?_
    · exact (hx.act ⟨F.La a, hLa⟩).symm.trans (hfix _ (La_mem_frameMember θ F ha))
    · have hperp : g⁻¹ v₀ ∈ F.perp := Frame.map_mem_perp h2 (Frame.inv_commute_La hg₁) hv₀
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_apply_of_mem_perp F a hperp,
        lapply_inv_apply, La_apply_of_mem_perp F a hv₀]
  calc g * F.La a = g * F.La a * g⁻¹ * g := by group
    _ = F.La a * g := by rw [hconj]

theorem exists_w₀_of_member [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F₁ : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hg₁ : g * F₁.La (-1) = F₁.La (-1) * g) {w : S} (hw : w ∈ frameMember θ F₁)
    (hw4 : orderOf w = 4) (hxw : ∀ b ∈ frameMember θ F₁, x b = w * b * w⁻¹) :
    ∃ w₀ ∈ commutator SL(2, K), w₀ * w₀ = -1 ∧
      ∀ b ∈ commutator SL(2, K), g * F₁.La b * g⁻¹ = F₁.La (w₀ * b * w₀⁻¹) := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_mem_perp F₁ hn
  obtain ⟨w₀, hw₀, rfl⟩ := (mem_frameMember_iff θ F₁).mp hw
  have hLw₀ : F₁.La w₀ ∈ orthDerived Q := frameQ8_le F₁ (La_mem_frameQ8 F₁ hw₀)
  have hw₀4 : w₀ ^ 4 = 1 := (mem_commutator_sl2_iff hK).mp hw₀
  have hw₀sq : w₀ * w₀ = -1 := by
    rcases eq_one_or_neg_one hK (show (w₀ ^ 2) ^ 2 = 1 by rw [← pow_mul]; exact hw₀4) with h | h
    · exfalso
      have hw2 : θ ⟨F₁.La w₀, hLw₀⟩ * θ ⟨F₁.La w₀, hLw₀⟩ = 1 := by
        rw [← map_mul]
        have : (⟨F₁.La w₀, hLw₀⟩ * ⟨F₁.La w₀, hLw₀⟩ : ↥(orthDerived Q)) = 1 :=
          Subtype.ext (by
            show F₁.La w₀ * F₁.La w₀ = 1
            rw [← map_mul, ← pow_two, h, map_one])
        rw [this, map_one]
      have hdvd := orderOf_dvd_of_pow_eq_one (show θ ⟨F₁.La w₀, hLw₀⟩ ^ 2 = 1 by
        rw [pow_two]; exact hw2)
      rw [hw4] at hdvd
      omega
    · rwa [pow_two] at h
  refine ⟨w₀, hw₀, hw₀sq, fun b hb => ?_⟩
  have hLb : F₁.La b ∈ orthDerived Q := frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)
  have hb' : w₀ * b * w₀⁻¹ ∈ commutator SL(2, K) := mul_mem (mul_mem hw₀ hb) (inv_mem hw₀)
  have hLb' : F₁.La (w₀ * b * w₀⁻¹) ∈ orthDerived Q :=
    frameQ8_le F₁ (La_mem_frameQ8 F₁ hb')
  refine eq_of_theta_eq_of_apply hQ hker (hx.mem _ hLb) hLb' ?_ hv₀0 ?_
  · calc θ ⟨g * F₁.La b * g⁻¹, hx.mem _ hLb⟩ = x (θ ⟨F₁.La b, hLb⟩) :=
          (hx.act ⟨F₁.La b, hLb⟩).symm
      _ = θ ⟨F₁.La w₀, hLw₀⟩ * θ ⟨F₁.La b, hLb⟩ * (θ ⟨F₁.La w₀, hLw₀⟩)⁻¹ :=
          hxw _ (La_mem_frameMember θ F₁ hb)
      _ = θ (⟨F₁.La w₀, hLw₀⟩ * ⟨F₁.La b, hLb⟩ * (⟨F₁.La w₀, hLw₀⟩ : ↥(orthDerived Q))⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = θ ⟨F₁.La (w₀ * b * w₀⁻¹), hLb'⟩ := by
          congr 1
          refine Subtype.ext ?_
          show F₁.La w₀ * F₁.La b * (F₁.La w₀)⁻¹ = F₁.La (w₀ * b * w₀⁻¹)
          rw [map_mul, map_mul, map_inv]
  · have hperp : g⁻¹ v₀ ∈ F₁.perp := Frame.map_mem_perp h2 (Frame.inv_commute_La hg₁) hv₀
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_apply_of_mem_perp F₁ b hperp,
      lapply_inv_apply, La_apply_of_mem_perp F₁ _ hv₀]

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
