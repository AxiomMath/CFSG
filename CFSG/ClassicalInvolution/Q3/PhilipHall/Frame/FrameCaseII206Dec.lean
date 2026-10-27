module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Mem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Dec

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem Std20Frame.kbar_equiv_q8' : Nonempty (Kbar K' ≃* Q8) := by
  obtain ⟨g, -, hgK⟩ := d.swap
  obtain ⟨e⟩ := kbar_equiv_q8 d
  rw [← hgK]
  exact nonempty_kbar_conj_equiv g e

theorem Std20Frame.card_RSet : ∀ P ∈ RSet (CoreAssembly.conjClass K), Nat.card P = 8 := by
  intro P hP
  obtain ⟨L, hL, hPL⟩ := exists_isSylow2In_of_mem_RSet hP
  rw [← Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K hL d.hR hPL]
  exact d.card8

theorem Std20Frame.nonempty_R_equiv : Nonempty (↥R ≃* Q8) :=
  nonempty_equiv_q8' (Sec6Gen.isQuatSub_of_mem_RSet d.late_hΩ
    (mem_RSet_of_isSylow2In d.late_mem_K d.hR)) d.card8

theorem Std20Frame.nonempty_R'_equiv : Nonempty (↥R' ≃* Q8) := by
  have hR'Ω := mem_RSet_of_isSylow2In d.late_mem_K' d.hR'
  exact nonempty_equiv_q8' (Sec6Gen.isQuatSub_of_mem_RSet d.late_hΩ hR'Ω) (d.card_RSet _ hR'Ω)

theorem Std20Frame.V_le_X : V ≤ sec20X (CoreAssembly.conjClass K) z K K' := by
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  exact tw.hVX

theorem Std20Frame.mul_self_eq_t {v : G} (hv : v ∈ V) (hv1 : v * v ≠ 1) : v * v = t := by
  have hcR := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ d.hV d.late_mem_K d.hR
  have hV4 : Nat.card V = 4 := by rw [d.card8] at hcR; omega
  have hw4 : v ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥V) (x := ⟨v, hv⟩)
    rw [hV4] at this
    simpa using congrArg Subtype.val this
  have hww : (v * v) * (v * v) = 1 := by
    calc (v * v) * (v * v) = v ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := hw4
  exact d.eq_t_of_invol_mem_V (V.mul_mem hv hv) hww hv1

theorem Std20Frame.exists_four_gens_eq_t :
    ∃ x ∈ K ⊓ W, ∃ x' ∈ K' ⊓ W, x * x = z ∧ x' * x' = z ∧ x * x' = t := by
  obtain ⟨⟨x, hx, hx2⟩, ⟨x₁, hx₁, hx₁2⟩⟩ := d.late_exists_four_gens
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hcomm : x * x₁ = x₁ * x := d.late_hWc x hx.2 x₁ hx₁.2
  have hnot : x₁ ∉ K := fun h =>
    TwinExact.not_mem_inf_of_sq d.late_hΩ d.late_mem_K d.late_mem_K' d.K_ne_K' d.viol.hzK hx₁2
      ⟨h, hx₁.1⟩
  have hp : (x * x₁) * (x * x₁) = 1 := by
    calc (x * x₁) * (x * x₁) = (x * x) * (x₁ * x₁) := by
          rw [mul_assoc, ← mul_assoc x₁, ← hcomm]
          group
      _ = 1 := by rw [hx2, hx₁2, hz2]
  have hne1 : x * x₁ ≠ 1 := fun h => hnot (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact K.inv_mem hx.1)
  have hnez : x * x₁ ≠ z := fun h => hnot (by
    have e1 : x₁ = x := by
      calc x₁ = x⁻¹ * (x * x₁) := by group
        _ = x⁻¹ * (x * x) := by rw [h, hx2]
        _ = x := by group
    rw [e1]
    exact hx.1)
  rcases d.late_inv_W _ (W.mul_mem hx.2 hx₁.2) hp with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hnez
  · exact ⟨x, hx, x₁, hx₁, hx2, hx₁2, h⟩
  · have hinv : x₁⁻¹ = x₁ * z :=
      (eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hx₁2, hz2])).symm
    refine ⟨x, hx, x₁⁻¹, ⟨K'.inv_mem hx₁.1, W.inv_mem hx₁.2⟩, hx2, ?_, ?_⟩
    · rw [← mul_inv_rev, hx₁2]
      exact inv_eq_of_mul_eq_one_right hz2
    · rw [hinv, ← mul_assoc, h, mul_assoc, ← d.late_zt_comm, ← mul_assoc, hz2, one_mul]

theorem Std20Frame.mem_X_of_conj (c8 : Concl20_8 S K' R) {c g : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = c) :
    c ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  have hc2 : c * c = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [d.viol.hzK.sq]; group
  obtain ⟨y, hy, hyS⟩ := d.exists_conj_le_S (isPGroup_zpowers_of_mul_self hc2)
    (Subgroup.zpowers_le.mpr hc)
  have h1 : y * c * y⁻¹ ∈ (S : Subgroup G) := hyS (conj_mem_conjSub (Subgroup.mem_zpowers c))
  have h2 : (y * g) * z * (y * g)⁻¹ = y * c * y⁻¹ := by rw [← hg]; group
  have h4 := conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins
    ((Subgroup.centralizer _).inv_mem hy) (conj_mem_conjSub (n := y⁻¹) (d.P1 c8 h1 h2))
  have e1 : y⁻¹ * (y * c * y⁻¹) * y⁻¹⁻¹ = c := by group
  rwa [e1] at h4

theorem Std20Frame.M_le_kerG :
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') ≤ kerG K :=
  sup_le (fun _ hy => oddCoreX_le_kerG d hy)
    (sup_le (fun _ hy => K_le_kerG d hy) (fun _ hy => K'_le_kerG d hy))

theorem Std20Frame.M_le_kerG' :
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') ≤ kerG K' := by
  have hXN : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K' : Set G) :=
    fun _ hx => ((sec20X_le_normalizers_frame d) hx).2
  refine sup_le (fun y hy => ?_) (sup_le (fun y hy => ?_) (fun y hy => ?_))
  · exact mem_kerG.mpr ⟨hXN (oddCoreOf_le_self _ hy),
      psiK_eq_one_of_mem_oddCore K' _ le_sec20X_right hXN hy⟩
  · exact mem_kerG.mpr ⟨(le_trivialOnQuot_K' d hy).1,
      psiK_eq_one_of_mem_trivialOnQuot K' (le_trivialOnQuot_K' d hy)⟩
  · exact mem_kerG.mpr ⟨Subgroup.le_normalizer hy, psiK_eq_one_of_mem K' hy⟩

theorem Std20Frame.exists_mul_of_mem_X (c3 : Concl20_3 K K' V z) {c : G}
    (hc : c ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∃ m ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K'), ∃ v ∈ V,
      c = m * v := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hXM : X = (oddCoreOf X ⊔ (K ⊔ K')) ⊔ V := by
    calc X = oddCoreOf X ⊔ (V ⊔ (K ⊔ K')) := c3
      _ = (oddCoreOf X ⊔ (K ⊔ K')) ⊔ V := by rw [sup_comm V (K ⊔ K'), ← sup_assoc]
  have hVN : V ≤ Subgroup.normalizer ((oddCoreOf X ⊔ (K ⊔ K') : Subgroup G) : Set G) := by
    intro v hv
    have hvX : v ∈ X := d.V_le_X hv
    have hvN := (sec20X_le_normalizers_frame d) hvX
    rw [mem_normalizer_iff_conjSub_eq, conjSub_sup', conjSub_sup',
      ← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem hvX,
      mem_normalizer_iff_conjSub_eq.mp hvN.1, mem_normalizer_iff_conjSub_eq.mp hvN.2]
  have hc' : c ∈ (((oddCoreOf X ⊔ (K ⊔ K')) ⊔ V : Subgroup G) : Set G) := by
    rw [← hXM]
    exact hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVN] at hc'
  obtain ⟨m, hm, v, hv, rfl⟩ := hc'
  exact ⟨m, hm, v, hv, rfl⟩

theorem Std20Frame.not_innerOn_of_not_mem (c3 : Concl20_3 K K' V z) {c : G}
    (hc : c ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (hcM : c ∉ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    ¬ InnerOn K c ∧ ¬ InnerOn K' c := by
  obtain ⟨m, hm, v, hv, rfl⟩ := d.exists_mul_of_mem_X c3 hc
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨e'⟩ := d.kbar_equiv_q8'
  have hv1 : v * v ≠ 1 := by
    intro h
    apply hcM
    refine Subgroup.mul_mem _ hm ?_
    by_cases h1 : v = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [d.eq_t_of_invol_mem_V hv h h1]
      exact Subgroup.mem_sup_right d.htKK
  obtain ⟨ho, ho'⟩ := frame203Outer G K K' J S R R' W V z t d v hv hv1
  have hvN := (sec20X_le_normalizers_frame d) (d.V_le_X hv)
  obtain ⟨hmN, -⟩ := mem_kerG.mp (d.M_le_kerG hm)
  obtain ⟨hmN', -⟩ := mem_kerG.mp (d.M_le_kerG' hm)
  exact ⟨not_innerOn_mul e hmN hvN.1 (innerOn_of_mem_kerG e (d.M_le_kerG hm)) ho,
    not_innerOn_mul e' hmN' hvN.2 (innerOn_of_mem_kerG e' (d.M_le_kerG' hm)) ho'⟩

theorem Std20Frame.psiK_eq_of_not_innerOn (c3 : Concl20_3 K K' V z) {L : Subgroup G}
    (eL : Kbar L ≃* Q8)
    (hXN : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (L : Set G))
    (hML : oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') ≤ kerG L)
    {v₀ c : G} (hv₀ : v₀ ∈ V) (hv₀2 : v₀ * v₀ = t)
    (hc : c ∈ sec20X (CoreAssembly.conjClass K) z K K') (hcout : ¬ InnerOn L c) :
    psiK L ⟨c, hXN hc⟩ = psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ := by
  obtain ⟨m, hm, v, hv, rfl⟩ := d.exists_mul_of_mem_X c3 hc
  obtain ⟨hmN, hm1⟩ := mem_kerG.mp (hML hm)
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hXN (d.V_le_X hv)
  have htK : t ∈ kerG L := hML (Subgroup.mem_sup_right d.htKK)
  have e1 : (⟨m * v, hXN hc⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨m, hmN⟩ * ⟨v, hvN⟩ := rfl
  rw [e1, map_mul, hm1, one_mul]
  have hv1 : v * v ≠ 1 := by
    intro hv1
    apply hcout
    refine innerOn_of_mem_kerG eL ((kerG L).mul_mem (hML hm) ?_)
    by_cases h1 : v = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [d.eq_t_of_invol_mem_V hv hv1 h1]
      exact htK
  have hvt := d.mul_self_eq_t hv hv1
  have hcomm : v₀ * v = v * v₀ := d.late_hWc v₀ (d.hVW hv₀) v (d.hVW hv)
  have hp : (v * v₀) * (v * v₀) = 1 := by
    calc (v * v₀) * (v * v₀) = (v * v) * (v₀ * v₀) := by
          rw [mul_assoc, ← mul_assoc v₀, hcomm]
          group
      _ = 1 := by rw [hvt, hv₀2]; exact d.viol.hzJ.sq
  have hvv₀ : v * v₀ ∈ kerG L := by
    by_cases h1 : v * v₀ = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [d.eq_t_of_invol_mem_V (V.mul_mem hv hv₀) hp h1]
      exact htK
  obtain ⟨hvv₀N, h2⟩ := mem_kerG.mp hvv₀
  obtain ⟨htN, h3⟩ := mem_kerG.mp htK
  have h4 : psiK L ⟨v, hvN⟩ * psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ = 1 := by
    rw [← map_mul]
    exact h2
  have h5 : psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ * psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ = 1 := by
    rw [← map_mul]
    have e2 : (⟨v₀, hXN (d.V_le_X hv₀)⟩ * ⟨v₀, hXN (d.V_le_X hv₀)⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = ⟨t, htN⟩ := Subtype.ext hv₀2
    rw [e2]
    exact h3
  calc psiK L ⟨v, hvN⟩ = psiK L ⟨v, hvN⟩ *
        (psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ * psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩) := by
        rw [h5, mul_one]
    _ = psiK L ⟨v₀, hXN (d.V_le_X hv₀)⟩ := by rw [← mul_assoc, h4, one_mul]

end Dec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
