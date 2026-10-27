module

public import CFSG.ClassicalInvolution.Phan.PhanS10Stab
public import CFSG.ClassicalInvolution.Phan.PhanS1Fib

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.Phan CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups Pointwise

section Step0

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}

theorem exists_mul_of_mem_parab_zero {x : spinGroup (quadOdd 3 (GaloisField p f))}
    (hx : x ∈ parab E {0}) : ∃ t ∈ torusSub E, ∃ ρ ∈ (E.ι 0).range, x = t * ρ := by
  rw [parab, Lsup_singleton] at hx
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (torusSub E) (E.ι 0).range
    (torusSub_le_normalizer_range (S := E) 0)
  have hx' : x ∈ (↑(torusSub E) : Set (spinGroup (quadOdd 3 (GaloisField p f)))) *
      (↑(E.ι 0).range : Set (spinGroup (quadOdd 3 (GaloisField p f)))) := by
    rw [← h]
    exact hx
  obtain ⟨t, ht, ρ, hρ, rfl⟩ := hx'
  exact ⟨t, ht, ρ, hρ, rfl⟩

variable [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

theorem eq_tor_zero_of_lineFix (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    {ρ : spinGroup (quadOdd 3 (GaloisField p f))} (hρ : ρ ∈ (E.ι 0).range)
    (hst : LineFix ρ (vXi D)) : ρ ∈ torusSub E := by
  obtain ⟨c, hc, hρc⟩ := hst
  have hρR : ρ ∈ M.R₀ := by
    have h := hρ
    rw [hr 0] at h
    exact h
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) ρ ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨_, hρR, rfl⟩
  have hρ' : actK ρ (vXi D) = extK (La0 h2 A).toLinearMap (vXi D) :=
    actK_eq_of_spinAction_eq hA.symm _
  obtain ⟨a, b, hab, rfl⟩ := N0.rot_of_fix A hc (by rw [← hρ', hρc])
  have hcab : c = algebraMap _ _ a + algebraMap _ _ b * D.θ := by
    apply smul_vXi_cancel D
    rw [← hρc, hρ', N0.rot_vXi]
  have hnorm : c * D.τ c = 1 := by
    rw [hcab]
    exact norm_rot D a b hab
  obtain ⟨x, hx1, -, -⟩ := exists_tor_zero_eigen D hg h2K h4 hr N0 hτ c hnorm
  obtain ⟨a', b', hab', h'⟩ := tor_zero_rot D hg h2K h4 hr N0 x
  have hc' : c = algebraMap _ _ a' + algebraMap _ _ b' * D.θ := by
    apply smul_vXi_cancel D
    rw [← hx1, actK_eq_of_spinAction_eq h', N0.rot_vXi]
  obtain ⟨rfl, rfl⟩ := eq_of_add_mul_theta D h2 (hcab.symm.trans hc')
  have : ρ = tor E 0 x :=
    eq_of_spinAction_eq_of_mem_R0 (M := M) hρR (tor_zero_mem (M := M) (hr 0) x)
      (by rw [← hA, h']; rfl)
  rw [this]
  exact tor_mem_torusSub E 0 x

theorem parab_zero_inf_parab_le_torus (hg : GoodFamily E)
    (h2K : (2 : GaloisField p (2 * f)) ≠ 0) (h4 : 4 ≤ Nat.card (GaloisField p f))
    (hr : ∀ i, (E.ι i).range = M.U i) (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c) :
    parab E {0} ⊓ parab E {1, 2} ≤ torusSub E := by
  rintro x ⟨hx0, hx12⟩
  obtain ⟨t, ht, ρ, hρ, rfl⟩ := exists_mul_of_mem_parab_zero hx0
  have hxs := parab_pair_le_stab D hg h2K h4 hr N0 N1 hx12
  have hts := parab_pair_le_stab D hg h2K h4 hr N0 N1 (torusSub_le_parab {1, 2} ht)
  have hρs : ρ ∈ stabLine (F := GaloisField p f) (vXi D) := by
    have := mul_mem (inv_mem hts) hxs
    rwa [inv_mul_cancel_left] at this
  exact mul_mem ht (eq_tor_zero_of_lineFix D hg h2K h4 hr N0 hτ hρ hρs)

theorem ptStep0_of_model (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c) : PtStep0 E := by
  intro e g hadj hpt
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  rw [phanSystem_adj_mk] at hadj
  rw [ptMap_eq_iff, mem_residue_mk_iff] at hpt
  exact QuotientGroup.eq.2 (parab_zero_inf_parab_le_torus D hg h2K h4 hr N0 N1 hτ ⟨hadj, hpt⟩)

end Step0

section Edge

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

theorem actK_R0_mem_l0 (hr : ∀ i, (E.ι i).range = M.U i) (N0 : Node0Facts D h2)
    {ρ : spinGroup (quadOdd 3 (GaloisField p f))} (hρ : ρ ∈ (E.ι 0).range) :
    ∃ a b : GaloisField p (2 * f), actK ρ (vXi D) = a • vXi D + b • vE2 D := by
  have hρR : ρ ∈ M.R₀ := by
    have h := hρ
    rw [hr 0] at h
    exact h
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) ρ ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨_, hρR, rfl⟩
  obtain ⟨a, b, c, d, h1, -⟩ := N0.mem_l0 A
  exact ⟨a, b, by rw [actK_eq_of_spinAction_eq hA.symm]; exact h1⟩

theorem tau_ne_zero' {c : GaloisField p (2 * f)} (hc : c ≠ 0) : D.τ c ≠ 0 := fun h =>
  hc (by rw [← D.tau_tau c, h, map_zero])

theorem edge_core (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ord : OrderFacts h2 M.D)
    {h k ρ ρ' : spinGroup (quadOdd 3 (GaloisField p f))} (hh : h ∈ parab E {1, 2})
    (hk : k ∈ parab E {1, 2}) (hρ : ρ ∈ (E.ι 0).range) (hρ' : ρ' ∈ (E.ι 0).range)
    (hρ'T : ρ' ∉ torusSub E) (hrel : h * ρ' = ρ * k) : h ∈ parab E {2} := by
  have h4K : (4 : GaloisField p (2 * f)) ≠ 0 := by
    have : (4 : GaloisField p (2 * f)) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2K h2K
  obtain ⟨lam, hlam, hhξ⟩ := parab_pair_le_stab D hg h2K h4 hr N0 N1 hh
  obtain ⟨lam', hlam', hkξ⟩ := parab_pair_le_stab D hg h2K h4 hr N0 N1 hk
  obtain ⟨a, b, hρξ⟩ := actK_R0_mem_l0 D hr N0 hρ
  obtain ⟨a', b', hρ'ξ⟩ := actK_R0_mem_l0 D hr N0 hρ'
  have hb' : b' ≠ 0 := by
    intro hb0
    apply hρ'T
    have ha0 : a' ≠ 0 := by
      intro ha0
      apply actK_ne_zero (g := ρ') (vXi_ne_zero D)
      rw [hρ'ξ, hb0, ha0]
      simp
    exact eq_tor_zero_of_lineFix D hg h2K h4 hr N0 hτ hρ'
      ⟨a', ha0, by rw [hρ'ξ, hb0, zero_smul, add_zero]⟩
  have h1 : actK (h * ρ') (vXi D) = actK (ρ * k) (vXi D) := by rw [hrel]
  simp only [actK_mul, hρ'ξ, hkξ, map_add, map_smul, hhξ, hρξ, smul_add, smul_smul] at h1
  have hX : b' • actK h (vE2 D) = (lam' * a - a' * lam) • vXi D + (lam' * b) • vE2 D := by
    calc b' • actK h (vE2 D) =
          ((lam' * a) • vXi D + (lam' * b) • vE2 D) - (a' * lam) • vXi D := by
          rw [← h1]
          abel
      _ = (lam' * a - a' * lam) • vXi D + (lam' * b) • vE2 D := by
          rw [sub_smul]
          abel
  have hX' : actK h (vE2 D) = (b'⁻¹ * (lam' * a - a' * lam)) • vXi D +
      (b'⁻¹ * (lam' * b)) • vE2 D := by
    calc actK h (vE2 D) = b'⁻¹ • (b' • actK h (vE2 D)) := by
          rw [smul_smul, inv_mul_cancel₀ hb', one_smul]
      _ = _ := by rw [hX, smul_add, smul_smul, smul_smul]
  have horth : hrm D (actK h (vE2 D)) (actK h (vXi D)) = 0 := by
    rw [hrm_actK, hrm_vE2_vXi]
  have hx0 : b'⁻¹ * (lam' * a - a' * lam) = 0 := by
    rw [hX', hhξ, hrm_smul_right, hrm_add_left, hrm_smul_left, hrm_smul_left, hrm_vXi_vXi,
      hrm_vE2_vXi] at horth
    have h5 : (b'⁻¹ * (lam' * a - a' * lam)) * 4 = 0 := by
      have := (mul_eq_zero.mp horth).resolve_left (tau_ne_zero' D hlam)
      linear_combination this
    exact (mul_eq_zero.mp h5).resolve_right h4K
  rw [hx0, zero_smul, zero_add] at hX'
  have hy0 : b'⁻¹ * (lam' * b) ≠ 0 := by
    intro hy
    apply actK_ne_zero (g := h) (vE2_ne_zero D)
    rw [hX', hy, zero_smul]
  have hlamN : lam * D.τ lam = 1 := by
    have h5 := hrm_actK D h (vXi D) (vXi D)
    rw [hhξ, hrm_smul_left, hrm_smul_right, hrm_vXi_vXi, ← mul_assoc] at h5
    have : (lam * D.τ lam - 1) * 4 = 0 := by linear_combination h5
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h4K)
  set y := b'⁻¹ * (lam' * b) with hy
  have hyN : y * D.τ y = 1 := by
    have h5 := hrm_actK D h (vE2 D) (vE2 D)
    rw [hX', hrm_smul_left, hrm_smul_right, hrm_vE2_vE2, ← mul_assoc] at h5
    have : (y * D.τ y - 1) * (-4) = 0 := by linear_combination h5
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (neg_ne_zero.mpr h4K))
  have hyl : (y * lam) * D.τ (y * lam) = 1 := by
    rw [map_mul]
    linear_combination (y * D.τ y) * hlamN + hyN
  obtain ⟨t, ht, ht1, ht2, -⟩ :=
    exists_torus01_eigen D hg h2K h4 hr N0 N1 hτ lam (y * lam) hlamN hyl
  have hτy : D.τ lam * (y * lam) = y := by linear_combination y * hlamN
  rw [hτy] at ht2
  have hfix1 : actK (t⁻¹ * h) (vXi D) = vXi D := by
    rw [actK_mul, hhξ, map_smul, actK_inv_of_eigen hlam ht1, smul_smul, mul_inv_cancel₀ hlam,
      one_smul]
  have hfix2 : actK (t⁻¹ * h) (vE2 D) = vE2 D := by
    rw [actK_mul, hX', map_smul, actK_inv_of_eigen hy0 ht2, smul_smul, mul_inv_cancel₀ hy0,
      one_smul]
  have hspan := fix_span_fr0_of_fix D (h2F := h2) h2K hfix1 hfix2
  have hU2 := ord.fixW0 _ hspan
  have hg2 : t⁻¹ * h ∈ (E.ι 2).range := by
    rw [hr 2]
    exact hU2
  have hg2' : t⁻¹ * h ∈ parab E {2} := Lsup_le_parab {2} (by rw [Lsup_singleton]; exact hg2)
  have : h = t * (t⁻¹ * h) := by group
  rw [this]
  exact mul_mem (torusSub_le_parab {2} ht) hg2'

theorem edge_group (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ord : OrderFacts h2 M.D)
    {h k r r' : spinGroup (quadOdd 3 (GaloisField p f))} (hh : h ∈ parab E {1, 2})
    (hk : k ∈ parab E {1, 2}) (hr0 : r ∈ parab E {0}) (hr' : r' ∈ parab E {0})
    (hnr : r ∉ parab E {1, 2}) (hrel : h * r' = r * k) :
    h ∈ parab E {2} ∧ k ∈ parab E {2} := by
  obtain ⟨t₁, ht₁, ρ₁, hρ₁, rfl⟩ := exists_mul_of_mem_parab_zero hr0
  obtain ⟨t₂, ht₂, ρ₂, hρ₂, rfl⟩ := exists_mul_of_mem_parab_zero hr'
  have hT12 : torusSub E ≤ parab E {1, 2} := torusSub_le_parab {1, 2}
  have hT2 : torusSub E ≤ parab E {2} := torusSub_le_parab {2}
  have hρ₁T : ρ₁ ∉ torusSub E := fun hT => hnr (mul_mem (hT12 ht₁) (hT12 hT))
  have hρ₂T : ρ₂ ∉ torusSub E := by
    intro hT
    refine hnr ?_
    have : t₁ * ρ₁ = h * (t₂ * ρ₂) * k⁻¹ := by rw [hrel]; group
    rw [this]
    exact mul_mem (mul_mem hh (hT12 (mul_mem ht₂ hT))) (inv_mem hk)
  have hrel1 : (t₁⁻¹ * h * t₂) * ρ₂ = ρ₁ * k := by
    calc (t₁⁻¹ * h * t₂) * ρ₂ = t₁⁻¹ * (h * (t₂ * ρ₂)) := by group
      _ = t₁⁻¹ * ((t₁ * ρ₁) * k) := by rw [hrel]
      _ = ρ₁ * k := by group
  have hh1 : t₁⁻¹ * h * t₂ ∈ parab E {1, 2} :=
    mul_mem (mul_mem (inv_mem (hT12 ht₁)) hh) (hT12 ht₂)
  have hP1 := edge_core D hg h2K h4 hr N0 N1 hτ ord hh1 hk hρ₁ hρ₂ hρ₂T hrel1
  refine ⟨?_, ?_⟩
  · have : h = t₁ * (t₁⁻¹ * h * t₂) * t₂⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (hT2 ht₁) hP1) (inv_mem (hT2 ht₂))
  · have hrel2 : k⁻¹ * ρ₁⁻¹ = ρ₂⁻¹ * (t₁⁻¹ * h * t₂)⁻¹ := by
      have := congrArg (fun x => x⁻¹) hrel1
      simpa only [mul_inv_rev] using this.symm
    have hρ₁T' : ρ₁⁻¹ ∉ torusSub E := fun hT => hρ₁T (by simpa using inv_mem hT)
    have := edge_core D hg h2K h4 hr N0 N1 hτ ord (inv_mem hk) (inv_mem hh1) (inv_mem hρ₂)
      (inv_mem hρ₁) hρ₁T' hrel2
    simpa using inv_mem this

theorem ptEdge_of_model (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ord : OrderFacts h2 M.D) : PtEdge E := by
  intro a b c d hac hbd hab hcd hne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective d
  rw [phanSystem_adj_mk] at hac hbd
  rw [ptMap_eq_iff, mem_residue_mk_iff] at hab hcd
  have hne' : a⁻¹ * c ∉ parab E {1, 2} := fun h =>
    hne (by
      rw [ptMap_mk, ptMap_mk]
      exact QuotientGroup.eq.2 h)
  have hrel : (a⁻¹ * b) * (b⁻¹ * d) = (a⁻¹ * c) * (c⁻¹ * d) := by group
  obtain ⟨h1, h2'⟩ := edge_group D hg h2K h4 hr N0 N1 hτ ord hab hcd hac hbd hne' hrel
  exact ⟨(mem_residue_mk_iff _ _ _).2 h2', (mem_residue_mk_iff _ _ _).2 h1⟩

end Edge

end CFSG.ClassicalInvolution.PhanB3.S
