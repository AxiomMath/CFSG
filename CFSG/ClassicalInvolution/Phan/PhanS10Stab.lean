module

public import CFSG.ClassicalInvolution.Phan.PhanS10Vec
import CFSG.ClassicalInvolution.Asc77.AscB3CG
public import CFSG.ClassicalInvolution.Phan.PhanB5Block
public import CFSG.ClassicalInvolution.Phan.PhanS10Tor

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.PhanD4 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section StabLine

variable {F K : Type} [Field F] [Field K] [Algebra F K]

@[expose] noncomputable def stabLine (x : W7 K) : Subgroup (spinGroup (quadOdd 3 F)) where
  carrier := {g | LineFix g x}
  one_mem' := ⟨1, one_ne_zero, by simp [actK_one]⟩
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨c', hc', hb⟩
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    rw [actK_mul, hb, map_smul, ha, smul_smul, mul_comm]
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    have h : actK a⁻¹ (actK a x) = x := by rw [← actK_mul, inv_mul_cancel, actK_one]
    rw [ha, map_smul] at h
    calc actK a⁻¹ x = c⁻¹ • (c • actK a⁻¹ x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • x := by rw [h]

theorem mem_stabLine {x : W7 K} {g : spinGroup (quadOdd 3 F)} :
    g ∈ stabLine (F := F) x ↔ LineFix g x := Iff.rfl

end StabLine

section Model

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem mk7_mem_span_fr0 (s a b z : GaloisField p f) :
    mk7 s a b s (-a) (-b) z ∈ (fr0 h2).span := by
  rw [Frame.mem_span_iff_inv _ h2, La0_neg_one, neg_mk7]
  simp

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem U2_fix_span {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map M.D.θ)
    {x : W7 (GaloisField p f)} (hx : x ∈ (fr0 h2).span) :
    spinAction (quadOdd 3 (GaloisField p f)) g x = x := by
  obtain ⟨y, ⟨B, rfl⟩, rfl⟩ := hg
  exact theta_twShort_fix_span M.D.isLevi M.D.nat M.D.fix h2 B hx

theorem actK_vXi_of_fixP {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : ∀ s z : GaloisField p f, spinAction (quadOdd 3 (GaloisField p f)) g
      (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z) : actK g (vXi D) = vXi D :=
  actK_vXi_of_fix D g (by simpa using hg 1 0) (by simpa using hg 0 1)

theorem U2_actK_vXi {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map M.D.θ) :
    actK g (vXi D) = vXi D :=
  actK_vXi_of_fix D g (U2_fix_span (M := M) hg (by simpa using mk7_mem_span_fr0 (h2 := h2) 1 0 0 0))
    (U2_fix_span (M := M) hg (by simpa using mk7_mem_span_fr0 (h2 := h2) 0 0 0 1))

theorem U2_actK_vE2 {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map M.D.θ) :
    actK g (vE2 D) = vE2 D :=
  actK_vE2_of_fix D g (U2_fix_span (M := M) hg (by simpa using mk7_mem_span_fr0 (h2 := h2) 0 1 0 0))
    (U2_fix_span (M := M) hg (by simpa using mk7_mem_span_fr0 (h2 := h2) 0 0 1 0))

end Model

section Pair

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem tor_two_mem_U2 (hr : ∀ i, (E.ι i).range = M.U i)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    tor E 2 x ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map M.D.θ := by
  have : tor E 2 x ∈ (E.ι 2).range := ⟨torusTwo _ x, rfl⟩
  rw [hr 2] at this
  exact this

theorem torus_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    {t : spinGroup (quadOdd 3 (GaloisField p f))} (ht : t ∈ torusSub E) :
    ∃ κ ν : GaloisField p (2 * f), κ * D.τ κ = 1 ∧ ν * D.τ ν = 1 ∧
      actK t (vXi D) = κ • vXi D ∧ actK t (vE2 D) = (D.τ κ * ν) • vE2 D := by
  obtain ⟨τ', rfl⟩ := ht
  rw [mTor_apply]
  obtain ⟨κ, hκ, h0ξ, h0e2, -⟩ := tor_zero_eigen D hg h2K h4 hr N0 (τ' 0)
  obtain ⟨ν, hν, h1ξ, h1e2, -⟩ := tor_one_eigen D hg h2K h4 hr N1 (τ' 1)
  have h2mem := tor_two_mem_U2 (M := M) hr (τ' 2)
  refine ⟨κ, ν, hκ, hν, ?_, ?_⟩
  · rw [actK_mul, actK_mul, U2_actK_vXi D (M := M) h2mem, h1ξ, h0ξ]
  · rw [actK_mul, actK_mul, U2_actK_vE2 D (M := M) h2mem, h1e2, map_smul, h0e2, smul_smul,
      mul_comm ν (D.τ κ)]

theorem exists_torus01_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (κ ν : GaloisField p (2 * f)) (hκ : κ * D.τ κ = 1) (hν : ν * D.τ ν = 1) :
    ∃ t ∈ torusSub E, actK t (vXi D) = κ • vXi D ∧ actK t (vE2 D) = (D.τ κ * ν) • vE2 D ∧
      actK t (vE3 D) = D.τ ν • vE3 D := by
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_tor_zero_eigen D hg h2K h4 hr N0 hτ κ hκ
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_tor_one_eigen D hg h2K h4 hr N1 hτ ν hν
  refine ⟨tor E 0 x * tor E 1 y, mul_mem (tor_mem_torusSub E 0 x) (tor_mem_torusSub E 1 y),
    ?_, ?_, ?_⟩
  · rw [actK_mul, hy1, hx1]
  · rw [actK_mul, hy2, map_smul, hx2, smul_smul, mul_comm ν (D.τ κ)]
  · rw [actK_mul, hy3, map_smul, hx3]

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem theta_range_le_parab (hr : ∀ i, (E.ι i).range = M.U i) :
    M.D.θ.range ≤ parab E {1, 2} := by
  have hrange : M.D.θ.range =
      (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map M.D.θ ⊔
        (longBlock (GaloisField p f) 2 1).range.map M.D.θ := by
    rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.Asc77.B3C.twShort_sup_longBlock h2,
      ← MonoidHom.range_eq_map]
  rw [hrange]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · have hx2 : x ∈ (E.ι 2).range := by rw [hr 2]; exact hx
    refine Lsup_le_parab {1, 2} ?_
    rw [Lsup_pair]
    exact Subgroup.mem_sup_right hx2
  · have hx1 : x ∈ (E.ι 1).range := by rw [hr 1]; exact hx
    refine Lsup_le_parab {1, 2} ?_
    rw [Lsup_pair]
    exact Subgroup.mem_sup_left hx1

theorem parab_pair_le_stab (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2) :
    parab E {1, 2} ≤ stabLine (F := GaloisField p f) (vXi D) := by
  refine sup_le (fun t ht => ?_) ?_
  · obtain ⟨κ, ν, hκ, hν, h1, -⟩ := torus_eigen D hg h2K h4 hr N0 N1 ht
    refine mem_stabLine.2 ⟨κ, ?_, h1⟩
    intro h0
    rw [h0, zero_mul] at hκ
    exact zero_ne_one hκ
  · rw [Lsup_pair]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [hr 1] at hx
      obtain ⟨y, -, rfl⟩ := hx
      refine mem_stabLine.2 ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact actK_vXi_of_fixP D (fun s z => theta_fix_P M.D.fix y s z)
    · rw [hr 2] at hx
      exact mem_stabLine.2 ⟨1, one_ne_zero, by rw [one_smul]; exact U2_actK_vXi D (M := M) hx⟩

theorem stab_le_parab_pair (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ord : OrderFacts h2 M.D) :
    stabLine (F := GaloisField p f) (vXi D) ≤ parab E {1, 2} := by
  intro g hgs
  obtain ⟨c, hc, hgc⟩ := hgs
  have h4K : (4 : GaloisField p (2 * f)) ≠ 0 := by
    have : (4 : GaloisField p (2 * f)) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2K h2K
  have hnorm : c * D.τ c = 1 := by
    have h1 := hrm_actK D g (vXi D) (vXi D)
    rw [hgc, hrm_smul_left, hrm_smul_right, hrm_vXi_vXi, ← mul_assoc] at h1
    have : (c * D.τ c - 1) * 4 = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h4K)
  obtain ⟨x, hx1, -, -⟩ := exists_tor_zero_eigen D hg h2K h4 hr N0 hτ c hnorm
  have ht₀ : tor E 0 x ∈ torusSub E := tor_mem_torusSub E 0 x
  have hfix : actK ((tor E 0 x)⁻¹ * g) (vXi D) = vXi D := by
    rw [actK_mul, hgc, map_smul, actK_inv_of_eigen hc hx1, smul_smul, mul_inv_cancel₀ hc,
      one_smul]
  have hP := fix_P_all_of_fix_vXi D h2K hfix
  have hθ := theta_range_le_parab (E := E) (M := M) hr (ord.fixP _ hP)
  have : g = tor E 0 x * ((tor E 0 x)⁻¹ * g) := by group
  rw [this]
  exact mul_mem (torusSub_le_parab {1, 2} ht₀) hθ

theorem parab_pair_eq_stab (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2) (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ord : OrderFacts h2 M.D) :
    parab E {1, 2} = stabLine (F := GaloisField p f) (vXi D) :=
  le_antisymm (parab_pair_le_stab D hg h2K h4 hr N0 N1)
    (stab_le_parab_pair D hg h2K h4 hr N0 hτ ord)

end Pair

end CFSG.ClassicalInvolution.PhanB3.S
