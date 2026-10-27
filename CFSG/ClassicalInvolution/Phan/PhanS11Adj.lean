module

public import CFSG.ClassicalInvolution.Phan.PhanS10Edge
public import CFSG.ClassicalInvolution.Phan.PhanS11Col
public import CFSG.ClassicalInvolution.Phan.PhanS9O4Plane
import CFSG.ClassicalInvolution.Phan.PhanP17Ell

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.Phan CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups Pointwise

section Gen

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem quad_eq_zero_of_polar_self (h2 : (2 : K) ≠ 0) {x : W7 K}
    (h : polar (quadOdd 3 K) x x = 0) : quadOdd 3 K x = 0 := by
  rw [QuadraticMap.polar_self] at h
  have h' : (2 : K) * quadOdd 3 K x = 0 := by simpa [nsmul_eq_mul] using h
  exact (mul_eq_zero.mp h').resolve_left h2

theorem four_ne_zero_of (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem sixteen_ne_zero_of (h2 : (2 : K) ≠ 0) : (16 : K) ≠ 0 := by
  have : (16 : K) = 4 * 4 := by norm_num
  rw [this]
  exact mul_ne_zero (four_ne_zero_of h2) (four_ne_zero_of h2)

theorem isFF7_vXi (h2 : (2 : K) ≠ 0) : IsFF7 D (vXi D) :=
  ⟨quad_eq_zero_of_polar_self h2 (polar_vXi_vXi D), by
    rw [hrm_vXi_vXi]
    exact four_ne_zero_of h2⟩

theorem isFF7_vE2 (h2 : (2 : K) ≠ 0) : IsFF7 D (vE2 D) :=
  ⟨quad_eq_zero_of_polar_self h2 (polar_vE2_vE2 D), by
    rw [hrm_vE2_vE2]
    exact neg_ne_zero.mpr (four_ne_zero_of h2)⟩

theorem isFF7_vE3 (h2 : (2 : K) ≠ 0) : IsFF7 D (vE3 D) :=
  ⟨quad_eq_zero_of_polar_self h2 (polar_vE3_vE3 D), by
    rw [hrm_vE3_vE3]
    exact four_ne_zero_of h2⟩

theorem emb_P_decomp (s z : F) :
    emb (K := K) (mk7 s 0 0 s 0 0 z : W7 F) =
      algebraMap F K s • emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F) +
        algebraMap F K z • emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F) := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7, Algebra.algebraMap_eq_smul_one]
  · fin_cases i <;> simp [emb, mk7, Algebra.algebraMap_eq_smul_one]
  · simp [emb, mk7, Algebra.algebraMap_eq_smul_one]

theorem polar_perp_plSpan (h2 : (2 : K) ≠ 0) {y : W7 K}
    (h1 : polar (quadOdd 3 K) y (vXi D) = 0) (h3 : hrm D y (vXi D) = 0) :
    ∀ r ∈ plSpan F, polar (quadOdd 3 K) y (emb r) = 0 := by
  have h2θ : (2 * D.θ : K) ≠ 0 := mul_ne_zero h2 (theta_ne_zero D)
  have h6 : polar (quadOdd 3 K) y (conjV D (vXi D)) = 0 := h3
  have ha : polar (quadOdd 3 K) y (emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F)) = 0 := by
    have h5 := congrArg (polar (quadOdd 3 K) y) (two_smul_emb_a (F := F) D)
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_add_right, h1, h6] at h5
    have : (2 : K) * polar (quadOdd 3 K) y (emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F)) = 0 := by
      simpa [smul_eq_mul] using h5
    exact (mul_eq_zero.mp this).resolve_left h2
  have hb : polar (quadOdd 3 K) y (emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F)) = 0 := by
    have h5 := congrArg (polar (quadOdd 3 K) y) (two_theta_smul_emb_b (F := F) D)
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_sub_right, h1, h6] at h5
    have : (2 * D.θ : K) * polar (quadOdd 3 K) y (emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F)) = 0 := by
      simpa [smul_eq_mul] using h5
    exact (mul_eq_zero.mp this).resolve_left h2θ
  rintro _ ⟨⟨s, z⟩, rfl⟩
  rw [plMap_apply, emb_P_decomp, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right, ha, hb]
  simp

theorem finrank_plSpan' : Module.finrank F (plSpan F) = 2 := by
  rw [LinearMap.finrank_range_of_inj plMap_injective]
  simp

theorem col7_vXi_l0 (h2 : (2 : K) ≠ 0) {a b : K} (hb : b ≠ 0) :
    Col7 D (vXi D) (a • vXi D + b • vE2 D) := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, polar_vXi_vXi, polar_vXi_vE2]
    simp
  · have key : gram7 D (vXi D) (a • vXi D + b • vE2 D) = -16 * (b * D.τ b) := by
      simp only [gram7, hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right,
        hrm_vXi_vXi, hrm_vE2_vE2, hrm_vXi_vE2, hrm_vE2_vXi]
      ring
    have hτb : D.τ b ≠ 0 := fun h => hb (by rw [← D.tau_tau b, h, map_zero])
    rw [key]
    exact mul_ne_zero (neg_ne_zero.mpr (sixteen_ne_zero_of h2)) (mul_ne_zero hb hτb)

theorem not_col7_smul (c : K) : ¬ Col7 D (vXi D) (c • vXi D) := by
  intro h
  apply h.2
  have := gram7_smul D 1 c (vXi D) (vXi D)
  rw [one_smul] at this
  rw [this]
  simp [gram7]

end Gen

section Adj

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

structure Setup (M : ModelB3 p f h2)
    (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))))
    (D : KDat (GaloisField p f) (GaloisField p (2 * f))) : Prop where
  good : GoodFamily E
  h2K : (2 : GaloisField p (2 * f)) ≠ 0
  h4 : 4 ≤ Nat.card (GaloisField p f)
  range : ∀ i, (E.ι i).range = M.U i
  n0 : Node0Facts D h2
  n1 : Node1Facts D h2
  tau : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c
  witt : WittFact D
  ord : OrderFacts h2 M.D
  hodd : Odd (Nat.card (GaloisField p f))
  hn1 : ¬ IsSquare (-1 : GaloisField p f)

variable (S : Setup M E D)

include S

theorem Setup.parab_eq : parab E {1, 2} = stabLine (F := GaloisField p f) (vXi D) :=
  parab_pair_eq_stab D S.good S.h2K S.h4 S.range S.n0 S.n1 S.tau S.ord

theorem Setup.mem_parab_iff {g : spinGroup (quadOdd 3 (GaloisField p f))} :
    g ∈ parab E {1, 2} ↔ LineFix g (vXi D) := by
  rw [S.parab_eq]
  exact mem_stabLine

theorem Setup.R0_mem {u : spinGroup (quadOdd 3 (GaloisField p f))} (hu : u ∈ M.R₀) :
    u ∈ (E.ι 0).range := by
  rw [S.range 0]
  exact hu

theorem Setup.mem_R0 {u : spinGroup (quadOdd 3 (GaloisField p f))} (hu : u ∈ (E.ι 0).range) :
    u ∈ M.R₀ := by
  rw [S.range 0] at hu
  exact hu

theorem Setup.exists_move_xi {y : W7 (GaloisField p (2 * f))} (hy : IsFF7 D y) :
    ∃ g : spinGroup (quadOdd 3 (GaloisField p f)), ∃ c : GaloisField p (2 * f), c ≠ 0 ∧
      actK g (vXi D) = c • y := by
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  obtain ⟨g, -, c, hc, hg⟩ := S.witt.move S.hodd S.h2K S.hn1 (R := ⊥)
    (CFSG.ClassicalInvolution.PhanP.nondegenerate_restrict_of_forall _ (fun x hx _ => by
      simpa using hx))
    (by simp) (isFF7_vXi D S.h2K) hy
    (fun r hr => by
      rw [(Submodule.mem_bot (GaloisField p f)).mp hr]
      have : emb (K := GaloisField p (2 * f)) (0 : W7 (GaloisField p f)) = 0 := by
        funext t
        simp [emb]
      rw [this]
      exact QuadraticMap.polar_zero_right _ _)
    (fun r hr => by
      rw [(Submodule.mem_bot (GaloisField p f)).mp hr]
      have : emb (K := GaloisField p (2 * f)) (0 : W7 (GaloisField p f)) = 0 := by
        funext t
        simp [emb]
      rw [this]
      exact QuadraticMap.polar_zero_right _ _)
  exact ⟨g, c, hc, hg⟩

theorem Setup.exists_move_perpP {y : W7 (GaloisField p (2 * f))} (hy : IsFF7 D y)
    (hyP : ∀ r ∈ plSpan (GaloisField p f),
      polar (quadOdd 3 (GaloisField p (2 * f))) y (emb r) = 0) :
    ∃ g : spinGroup (quadOdd 3 (GaloisField p f)),
      (∀ r ∈ plSpan (GaloisField p f), spinAction (quadOdd 3 (GaloisField p f)) g r = r) ∧
        ∃ c : GaloisField p (2 * f), c ≠ 0 ∧ actK g y = c • vE2 D := by
  have hPe : ∀ r ∈ plSpan (GaloisField p f),
      polar (quadOdd 3 (GaloisField p (2 * f))) (vE2 D) (emb r) = 0 :=
    polar_perp_plSpan D S.h2K (by rw [QuadraticMap.polar_comm]; exact polar_vXi_vE2 D)
      (hrm_vE2_vXi D)
  exact S.witt.move S.hodd S.h2K S.hn1 (plSpan_regular h2)
    (by rw [finrank_plSpan']; norm_num) hy (isFF7_vE2 D S.h2K) hyP hPe

theorem Setup.fixP_mem_parab {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : ∀ r ∈ plSpan (GaloisField p f), spinAction (quadOdd 3 (GaloisField p f)) g r = r) :
    g ∈ parab E {1, 2} :=
  theta_range_le_parab (E := E) (M := M) S.range
    (S.ord.fixP g (fun s z => hg (mk7 s 0 0 s 0 0 z) ⟨(s, z), rfl⟩))

theorem Setup.col7_of_mul {p₁ u p₂ : spinGroup (quadOdd 3 (GaloisField p f))}
    (hp₁ : p₁ ∈ parab E {1, 2}) (hu : u ∈ (E.ι 0).range) (hp₂ : p₂ ∈ parab E {1, 2})
    (hk : p₁ * u * p₂ ∉ parab E {1, 2}) : Col7 D (vXi D) (actK (p₁ * u * p₂) (vXi D)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := S.mem_parab_iff.1 hp₁
  obtain ⟨c₂, hc₂, h₂⟩ := S.mem_parab_iff.1 hp₂
  obtain ⟨a, b, hab⟩ := actK_R0_mem_l0 D S.range S.n0 hu
  have hb : b ≠ 0 := by
    intro hb0
    apply hk
    have ha : a ≠ 0 := by
      intro ha0
      apply actK_ne_zero (g := u) (vXi_ne_zero D)
      rw [hab, ha0, hb0]
      simp
    have huT := eq_tor_zero_of_lineFix D S.good S.h2K S.h4 S.range S.n0 S.tau hu
      ⟨a, ha, by rw [hab, hb0, zero_smul, add_zero]⟩
    exact mul_mem (mul_mem hp₁ (torusSub_le_parab {1, 2} huT)) hp₂
  have h3 : actK (p₁ * u * p₂) (vXi D) = c₂ • actK p₁ (a • vXi D + b • vE2 D) := by
    rw [actK_mul, actK_mul, h₂, map_smul, hab, map_smul]
  have hw : Col7 D (vXi D) (a • vXi D + b • vE2 D) := col7_vXi_l0 D S.h2K hb
  have hcol : Col7 D (vXi D) (actK p₁ (a • vXi D + b • vE2 D)) := by
    rw [← col7_actK D p₁⁻¹, actK_inv_of_eigen hc₁ h₁, ← actK_mul, inv_mul_cancel, actK_one]
    have := (col7_smul D (c := c₁⁻¹) (d := 1) (inv_ne_zero hc₁) one_ne_zero
      (a := vXi D) (b := a • vXi D + b • vE2 D)).2 hw
    rwa [one_smul] at this
  rw [h3]
  have := (col7_smul D (c := 1) (d := c₂) one_ne_zero hc₂ (a := vXi D)
    (b := actK p₁ (a • vXi D + b • vE2 D))).2 hcol
  rwa [one_smul] at this

theorem Setup.exists_mul_of_col7 {k : spinGroup (quadOdd 3 (GaloisField p f))}
    (hk : Col7 D (vXi D) (actK k (vXi D))) :
    ∃ p₁ ∈ parab E {1, 2}, ∃ u ∈ (E.ι 0).range, ∃ p₂ ∈ parab E {1, 2}, k = p₁ * u * p₂ := by
  set y := actK k (vXi D) with hy
  have hffy : IsFF7 D y := isFF7_actK D S.h2K k (isFF7_vXi D S.h2K)
  have h4K := four_ne_zero_of S.h2K
  set lam : GaloisField p (2 * f) := hrm D y (vXi D) / 4 with hlam
  set y' := y + (-lam) • vXi D with hy'
  have hpyξ : polar (quadOdd 3 (GaloisField p (2 * f))) y (vXi D) = 0 := by
    rw [QuadraticMap.polar_comm]
    exact hk.1
  have hhyξ : hrm D y' (vXi D) = 0 := by
    rw [hy', hrm_add_left, hrm_smul_left, hrm_vXi_vXi, neg_mul, hlam, div_mul_cancel₀ _ h4K,
      add_neg_cancel]
  have hpy'ξ : polar (quadOdd 3 (GaloisField p (2 * f))) y' (vXi D) = 0 := by
    rw [hy', QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hpyξ, polar_vXi_vXi]
    simp
  have hpyy : polar (quadOdd 3 (GaloisField p (2 * f))) y y = 0 := by
    rw [QuadraticMap.polar_self, hffy.1]
    simp
  have hpy'y' : polar (quadOdd 3 (GaloisField p (2 * f))) y' y' = 0 := by
    rw [hy', QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hpyy, hpyξ,
      QuadraticMap.polar_comm _ (vXi D) y, hpyξ, polar_vXi_vXi]
    simp
  have hQy' : quadOdd 3 (GaloisField p (2 * f)) y' = 0 :=
    quad_eq_zero_of_polar_self S.h2K hpy'y'
  have hτ4 : D.τ (4 : GaloisField p (2 * f)) = 4 := map_ofNat D.τ 4
  have hhy'y' : hrm D y' y' ≠ 0 := by
    have key : hrm D y' y' = gram7 D (vXi D) y / 4 := by
      have hs : hrm D (vXi D) y = D.τ (hrm D y (vXi D)) := hrm_conj_symm D _ _
      rw [hy', hrm_add_left, hrm_add_right, hrm_add_right, hrm_smul_left, hrm_smul_left,
        hrm_smul_right, hrm_smul_right, hrm_vXi_vXi, gram7, hrm_vXi_vXi, hs, hlam, map_neg,
        map_div₀, hτ4]
      field_simp
      ring
    rw [key]
    exact div_ne_zero hk.2 h4K
  obtain ⟨g₁, hg₁P, c, hc, hg₁⟩ := S.exists_move_perpP ⟨hQy', hhy'y'⟩
    (polar_perp_plSpan D S.h2K hpy'ξ hhyξ)
  have hg₁ξ : actK g₁ (vXi D) = vXi D :=
    actK_vXi_of_fixP D (fun s z => hg₁P (mk7 s 0 0 s 0 0 z) ⟨(s, z), rfl⟩)
  have hg₁p : g₁ ∈ parab E {1, 2} := S.fixP_mem_parab hg₁P
  have hyy' : y = y' + lam • vXi D := by
    rw [hy', add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have hz : actK g₁ y = lam • vXi D + c • vE2 D := by
    rw [hyy', map_add, hg₁, map_smul, hg₁ξ, add_comm]
  have hzff : IsFF7 D (lam • vXi D + c • vE2 D) := by
    rw [← hz]
    exact isFF7_actK D S.h2K g₁ hffy
  obtain ⟨A, c', hc', hA⟩ := S.n0.move lam c hzff
  obtain ⟨u, hu, hAu⟩ : ∃ u ∈ M.R₀, spinAction (quadOdd 3 (GaloisField p f)) u = La0 h2 A := by
    have : La0 h2 A ∈ (fr0 h2).La.range := ⟨A, rfl⟩
    rw [← M.map_eq] at this
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, hu'⟩
  have hu' : actK u (vXi D) = c' • (lam • vXi D + c • vE2 D) := by
    rw [actK_eq_of_spinAction_eq hAu]
    exact hA
  have hm : actK (g₁⁻¹ * u) (vXi D) = c' • y := by
    rw [actK_mul, hu', ← hz, map_smul, ← actK_mul, inv_mul_cancel, actK_one]
  have hq : k⁻¹ * (g₁⁻¹ * u) ∈ parab E {1, 2} :=
    S.mem_parab_iff.2 ⟨c', hc', by
      rw [actK_mul, hm, map_smul, hy, ← actK_mul, inv_mul_cancel, actK_one]⟩
  exact ⟨g₁⁻¹, inv_mem hg₁p, u, S.R0_mem hu, (k⁻¹ * (g₁⁻¹ * u))⁻¹, inv_mem hq, by group⟩

theorem Setup.adj_iff_col7 (g h : spinGroup (quadOdd 3 (GaloisField p f))) :
    (ptGraph E).Adj (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2})
        (h : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) ↔
      Col7 D (actK g (vXi D)) (actK h (vXi D)) := by
  constructor
  · rintro ⟨hne, c, d, hc, hd, hadj⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective d
    rw [ptMap_mk] at hc hd
    have hq₁ : α⁻¹ * g ∈ parab E {1, 2} := QuotientGroup.eq.1 hc
    have hq₂ : β⁻¹ * h ∈ parab E {1, 2} := QuotientGroup.eq.1 hd
    rw [phanSystem_adj_mk] at hadj
    obtain ⟨t, ht, ρ, hρ, hαβ⟩ := exists_mul_of_mem_parab_zero hadj
    have hk : g⁻¹ * h = ((α⁻¹ * g)⁻¹ * t) * ρ * (β⁻¹ * h) := by
      calc g⁻¹ * h = (α⁻¹ * g)⁻¹ * (α⁻¹ * β) * (β⁻¹ * h) := by group
        _ = _ := by rw [hαβ]; group
    have hknot : g⁻¹ * h ∉ parab E {1, 2} := fun hmem => hne (QuotientGroup.eq.2 hmem)
    have hp₁ : (α⁻¹ * g)⁻¹ * t ∈ parab E {1, 2} :=
      mul_mem (inv_mem hq₁) (torusSub_le_parab {1, 2} ht)
    have hcol := S.col7_of_mul hp₁ hρ hq₂ (by rw [← hk]; exact hknot)
    rw [← hk] at hcol
    have := (col7_actK D g _ _).2 hcol
    rwa [← actK_mul, mul_inv_cancel_left] at this
  · intro hcol
    have hcol' : Col7 D (vXi D) (actK (g⁻¹ * h) (vXi D)) := by
      have := (col7_actK D g⁻¹ _ _).2 hcol
      rwa [← actK_mul, ← actK_mul, inv_mul_cancel, actK_one] at this
    obtain ⟨p₁, hp₁, u, hu, p₂, hp₂, hk⟩ := S.exists_mul_of_col7 hcol'
    have hne : (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) ≠ h := by
      intro heq
      have hmem : g⁻¹ * h ∈ parab E {1, 2} := QuotientGroup.eq.1 heq
      obtain ⟨c, -, hc⟩ := S.mem_parab_iff.1 hmem
      rw [hc] at hcol'
      exact not_col7_smul D c hcol'
    refine ⟨hne, QuotientGroup.mk (g * p₁), QuotientGroup.mk (g * p₁ * u), ?_, ?_, ?_⟩
    · rw [ptMap_mk]
      exact QuotientGroup.eq.2 (by simpa using inv_mem hp₁)
    · rw [ptMap_mk]
      refine QuotientGroup.eq.2 ?_
      have : (g * p₁ * u)⁻¹ * h = p₂ := by
        have hh : h = g * (p₁ * u * p₂) := by rw [← hk]; group
        rw [hh]
        group
      rw [this]
      exact hp₂
    · rw [phanSystem_adj_mk]
      have : (g * p₁)⁻¹ * (g * p₁ * u) = u := by group
      rw [this]
      exact Lsup_le_parab {0} (by rw [Lsup_singleton]; exact hu)

end Adj

end CFSG.ClassicalInvolution.PhanB3.S
