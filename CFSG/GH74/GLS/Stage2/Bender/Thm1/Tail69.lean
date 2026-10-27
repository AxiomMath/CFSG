module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Dichotomy
public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.Lemma23d
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der615
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.TailAux

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G]

structure TailCtx (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q : Subgroup G) : Prop where
  ctx : Ctx6 G z k S M p
  qp : QP z p (Op p M) Q
  eCyc : IsCyclic ↥(Ep p M)
  extra : IsExtraspecialPGroup p ↥Q
  card : Nat.card ↥Q = p ^ 3
  sup : Op p M = Q ⊔ zOf (Op p M)
  zCyc : IsCyclic ↥(zOf (Op p M))

variable {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} {Q : Subgroup G}

theorem TailCtx.mQ (h : TailCtx z k S M p Q) : M ≤ normalizer (Q : Set G) :=
  le_normalizer_QP (le_normalizer_Op p M) h.qp

theorem TailCtx.comm_Z (h : TailCtx z k S M p Q) :
    ⁅M, M⁆ ≤ centralizer ((zOf (Op p M) : Subgroup G) : Set G) := by
  refine commutator_le_centralizer_of_cyclic h.zCyc fun m hm => ?_
  have hP := le_normalizer_Op p M hm
  exact mem_normalizer_inf hP (mem_normalizer_centralizer hP)

theorem TailCtx.comm_E (h : TailCtx z k S M p Q) :
    ⁅M, M⁆ ≤ centralizer ((Ep p M : Subgroup G) : Set G) :=
  commutator_le_centralizer_of_cyclic h.eCyc (le_normalizer_Ep p M)

omit [Finite G] in
theorem commute_inv_mul {u b t : G} (hu : u * t = t * u) (hb : b * t = t * b) :
    (u⁻¹ * b) * t = t * (u⁻¹ * b) := by
  have hu' : u⁻¹ * t = t * u⁻¹ := by
    calc u⁻¹ * t = u⁻¹ * (t * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * t) * u⁻¹ := by rw [hu]
      _ = t * u⁻¹ := by group
  calc u⁻¹ * b * t = u⁻¹ * (b * t) := by group
    _ = u⁻¹ * (t * b) := by rw [hb]
    _ = (u⁻¹ * t) * b := by group
    _ = (t * u⁻¹) * b := by rw [hu']
    _ = t * (u⁻¹ * b) := by group

theorem TailCtx.eq_one_of_actsTriv (h : TailCtx z k S M p Q) {b : G} (hbK : b ∈ ⁅M, M⁆)
    (hb : b * b = 1) (hT : ActsTriv Q b) : b = 1 := by
  have hC := h.ctx
  have hp := hC.prime
  have hbM : b ∈ M := commutator_le_left_of_normalizes Subgroup.le_normalizer hbK
  have hQP : Q ≤ Op p M := h.qp.1
  have hexp : ∀ x ∈ Q, x ^ p = 1 := h.qp.2.2.1
  obtain ⟨u, huQ, hc⟩ := exists_inner_of_extraspecial_gen hp h.extra hexp (h.mQ hbM) hT
  have huP : u ∈ Op p M := hQP huQ
  have hcM : u⁻¹ * b ∈ M := M.mul_mem (M.inv_mem (Op_le p M huP)) hbM
  have hcZ : ∀ a ∈ zOf (Op p M), (u⁻¹ * b) * a = a * (u⁻¹ * b) := fun a ha =>
    commute_inv_mul (Subgroup.mem_centralizer_iff.mp ha.2 u huP)
      (Subgroup.mem_centralizer_iff.mp (h.comm_Z hbK) a ha).symm
  have hOE : Op p M ≤ centralizer ((Ep p M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep p hp M)
  have hcE : ∀ e ∈ Ep p M, (u⁻¹ * b) * e = e * (u⁻¹ * b) := fun e he =>
    commute_inv_mul (Subgroup.mem_centralizer_iff.mp (hOE huP) e he).symm
      (Subgroup.mem_centralizer_iff.mp (h.comm_E hbK) e he).symm
  have hcP : ∀ w ∈ Op p M, (u⁻¹ * b) * w = w * (u⁻¹ * b) := by
    intro w hw
    have hw' : w ∈ Q ⊔ zOf (Op p M) := by rw [← h.sup]; exact hw
    have hle : Q ⊔ zOf (Op p M) ≤ centralizer ({u⁻¹ * b} : Set G) := by
      refine sup_le (fun q hq => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc q hq)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcZ a ha).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw')).symm
  have hcF : u⁻¹ * b ∈ Fm M := mem_Fm_of_centralizes_Op_Ep (hC.Fs_eq hC.mem) hp hcM hcP hcE
  have hbF : b ∈ Fm M := by
    have e : b = u * (u⁻¹ * b) := by group
    rw [e]
    exact (Fm M).mul_mem (Op_le_Fm p hp M huP) hcF
  exact eq_one_of_mul_self_eq_one_of_odd (odd_card_Fm hC.hyp hC.mem) hbF hb

theorem TailCtx.actsInv (h : TailCtx z k S M p Q) {b : G} (hbK : b ∈ ⁅M, M⁆) (hb : b * b = 1)
    (hb1 : b ≠ 1) : ActsInv Q b := by
  have hC := h.ctx
  have hbM : b ∈ M := commutator_le_left_of_normalizes Subgroup.le_normalizer hbK
  have hZ : zOf Q ≤ Cen b := by
    intro c hc
    have hcP : c ∈ zOf (Op p M) := zOf_le_zOf_of_eq_sup h.qp.1 h.sup hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h.comm_Z hbK) c hcP)
  rcases dichotomy hC.prime hC.p_ne_two (extraG_of_isExtraspecial h.extra) h.card h.qp.2.2.1 hb
      (h.mQ hbM) hZ with hT | hI
  · exact absurd (h.eq_one_of_actsTriv hbK hb hT) hb1
  · exact hI

theorem TailCtx.key (h : TailCtx z k S M p Q) {b₁ b₂ : G} (h₁ : b₁ ∈ ⁅M, M⁆) (h₂ : b₂ ∈ ⁅M, M⁆)
    (hb₁ : b₁ * b₁ = 1) (hb₂ : b₂ * b₂ = 1) (hcomm : b₁ * b₂ = b₂ * b₁) :
    b₁ = 1 ∨ b₂ = 1 ∨ b₁ = b₂ := by
  by_cases e₁ : b₁ = 1
  · exact Or.inl e₁
  by_cases e₂ : b₂ = 1
  · exact Or.inr (Or.inl e₂)
  refine Or.inr (Or.inr ?_)
  have hI₁ := h.actsInv h₁ hb₁ e₁
  have hI₂ := h.actsInv h₂ hb₂ e₂
  have hbM₂ : b₂ ∈ M := commutator_le_left_of_normalizes Subgroup.le_normalizer h₂
  have hT : ActsTriv Q (b₁ * b₂) := actsTriv_mul (h.mQ hbM₂) hI₁ hI₂
  have hK : b₁ * b₂ ∈ ⁅M, M⁆ := (⁅M, M⁆).mul_mem h₁ h₂
  have hsq : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
      _ = b₁ * (b₁ * b₂) * b₂ := by rw [hcomm]
      _ = (b₁ * b₁) * (b₂ * b₂) := by group
      _ = 1 := by rw [hb₁, hb₂, one_mul]
  have h1 := h.eq_one_of_actsTriv hK hsq hT
  calc b₁ = b₁ * (b₂ * b₂) := by rw [hb₂, mul_one]
    _ = (b₁ * b₂) * b₂ := by group
    _ = b₂ := by rw [h1, one_mul]

end Ctx

section Final

theorem tail6_9_of (h33 : IVK_3_3_lift) : Tail6_9 := by
  intro G _ _ z k S M p hC Q hQ hEcyc _ hQe hcard hPQ hZcyc _
  have h : TailCtx z k S M p Q := ⟨hC, hQ, hEcyc, hQe, hcard, hPQ, hZcyc⟩
  exfalso
  have h23 : 2 ≤ pRank 2 ↥(⁅Cen z, Cen z⁆ : Subgroup G) := lemma23_d (h33 G z k S hC.ctx)
  have hCM : ⁅Cen z, Cen z⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hC.cen_le hC.cen_le
  have hle : pRank 2 ↥(⁅Cen z, Cen z⁆ : Subgroup G) ≤ 1 := by
    refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun A hA => ?_
    by_contra hgt
    have : IsElementaryAbelian 2 ↥A := hA
    have : Fintype ↥A := Fintype.ofFinite _
    have h3 : 2 < Fintype.card ↥A := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hgt
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
    obtain ⟨x, y, hx1, hy1, hxy⟩ : ∃ x y : ↥A, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
      by_cases ha1 : a = 1
      · exact ⟨b, c, fun hh => hab (ha1.trans hh.symm), fun hh => hac (ha1.trans hh.symm), hbc⟩
      by_cases hb1 : b = 1
      · exact ⟨a, c, ha1, fun hh => hbc (hb1.trans hh.symm), hac⟩
      exact ⟨a, b, ha1, hb1, hab⟩
    have hsq : ∀ t : ↥A, (t.1.1 : G) * t.1.1 = 1 := by
      intro t
      have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) t.1 t.2
      have h2 := congrArg (fun w : ↥(⁅Cen z, Cen z⁆ : Subgroup G) => (w : G)) h1
      simpa [pow_two] using h2
    have hcm : ∀ s t : ↥A, (s.1.1 : G) * t.1.1 = t.1.1 * s.1.1 := by
      intro s t
      have h1 := congrArg (fun w : ↥A => ((w.1 : ↥(⁅Cen z, Cen z⁆ : Subgroup G)) : G)) (mul_comm' s t)
      simpa using h1
    have hne : ∀ t : ↥A, t ≠ 1 → (t.1.1 : G) ≠ 1 := by
      intro t ht h1
      exact ht (Subtype.ext (Subtype.ext h1))
    rcases h.key (hCM x.1.2) (hCM y.1.2) (hsq x) (hsq y) (hcm x y) with h1 | h1 | h1
    · exact hne x hx1 h1
    · exact hne y hy1 h1
    · exact hxy (Subtype.ext (Subtype.ext h1))
  omega

end Final

end CFSG.GH74.GLS.Stage2.Bender.Thm1
