module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBT2

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace T2Data

variable (D : B.T2Data)

@[expose] def qp (b : Bool) : X := if b then D.q else 1

theorem qp_mem_P (b : Bool) : D.qp b ∈ D.P := by
  cases b
  · exact one_mem _
  · exact D.q_mem

theorem exists_E0_of_actsAs {g h : X} (hg : g ∈ D.P) (hh : h ∈ D.P) (hgh : ActsAs B.Q1 g h) :
    ∃ e : MB, MB.inE0 e = true ∧ g = h * B.ι e := by
  obtain ⟨e, he, hee⟩ := B.mem_E0_of_mem_centralizer_Q1 D.isPGroup
    (mul_mem (inv_mem hh) hg) (mem_centralizer_Q1_of_actsAs hgh)
  exact ⟨e, he, by rw [hee, mul_inv_cancel_left]⟩

theorem exists_E0_of_acts {g h : X} {f : List MB} (hg : g ∈ D.P) (hh : h ∈ D.P)
    (hgf : B.ActsQ1 g f) (hhf : B.ActsQ1 h f) : ∃ e : MB, MB.inE0 e = true ∧ g = h * B.ι e :=
  D.exists_E0_of_actsAs hg hh (hgf.actsAs_of_eq hhf)

theorem mem_R2_of_actsAs {g r : X} (hg : g ∈ D.P) (hr : r ∈ D.R.R2) (hgr : ActsAs B.Q1 g r) :
    g ∈ D.R.R2 := by
  obtain ⟨e, -, rfl⟩ := D.exists_E0_of_actsAs hg (D.R2_le hr) hgr
  exact mul_mem hr (D.R.ι_mem_R2 e)

theorem q_conj_mem {r : X} (hr : r ∈ D.R.R2) : D.q * r * D.q⁻¹ ∈ D.R.R2 := by
  obtain ⟨h', hh', hact⟩ := conj_R2_actsAs D.R D.hp D.hj D.acts_q r hr
  exact D.mem_R2_of_actsAs (mul_mem (mul_mem D.q_mem (D.R2_le hr)) (inv_mem D.q_mem)) hh' hact

theorem q_sq_mem : D.q * D.q ∈ D.R.R2 :=
  D.mem_R2_of_actsAs (mul_mem D.q_mem D.q_mem) (D.R.ι_mem_R2 MB.w₂)
    (sq_actsAs_R2 D.R D.hp D.hj D.acts_q)

theorem qp_conj_mem (b : Bool) {r : X} (hr : r ∈ D.R.R2) : D.qp b * r * (D.qp b)⁻¹ ∈ D.R.R2 := by
  cases b
  · simpa [qp] using hr
  · exact D.q_conj_mem hr

theorem qp_mul_qp (b b' : Bool) :
    D.qp b * D.qp b' = (if b && b' then D.q * D.q else 1) * D.qp (xor b b') := by
  cases b <;> cases b' <;> simp [qp]

theorem qp_inv (b : Bool) : (D.qp b)⁻¹ = (if b then (D.q * D.q)⁻¹ else 1) * D.qp b := by
  cases b
  · simp [qp]
  · show D.q⁻¹ = (D.q * D.q)⁻¹ * D.q
    group

theorem sqp_mem (b : Bool) : (if b then D.q * D.q else 1) ∈ D.R.R2 := by
  cases b
  · exact one_mem _
  · exact D.q_sq_mem

@[expose] def T2 : Subgroup X where
  carrier := {x | ∃ r ∈ D.R.R2, ∃ b : Bool, x = r * D.qp b}
  mul_mem' := by
    rintro _ _ ⟨r, hr, b, rfl⟩ ⟨r', hr', b', rfl⟩
    refine ⟨r * (D.qp b * r' * (D.qp b)⁻¹) * (if b && b' then D.q * D.q else 1),
      mul_mem (mul_mem hr (D.qp_conj_mem b hr')) (D.sqp_mem (b && b')), xor b b', ?_⟩
    calc r * D.qp b * (r' * D.qp b') = r * (D.qp b * r' * (D.qp b)⁻¹) * (D.qp b * D.qp b') := by
          group
      _ = _ := by rw [D.qp_mul_qp]; group
  one_mem' := ⟨1, one_mem _, false, by simp [qp]⟩
  inv_mem' := by
    rintro _ ⟨r, hr, b, rfl⟩
    have h1 : (if b then (D.q * D.q)⁻¹ else 1) ∈ D.R.R2 := by
      cases b
      · exact one_mem _
      · exact inv_mem D.q_sq_mem
    refine ⟨(if b then (D.q * D.q)⁻¹ else 1) * (D.qp b * r⁻¹ * (D.qp b)⁻¹),
      mul_mem h1 (D.qp_conj_mem b (inv_mem hr)), b, ?_⟩
    calc (r * D.qp b)⁻¹ = (D.qp b)⁻¹ * r⁻¹ := mul_inv_rev _ _
      _ = (if b then (D.q * D.q)⁻¹ else 1) * D.qp b * r⁻¹ := by rw [D.qp_inv]
      _ = _ := by group

theorem T2_le_P : D.T2 ≤ D.P := by
  rintro _ ⟨r, hr, b, rfl⟩
  exact mul_mem (D.R2_le hr) (D.qp_mem_P b)

theorem isPGroup_T2 : IsPGroup 2 D.T2 := D.isPGroup.to_le D.T2_le_P

theorem R2_le_T2 : D.R.R2 ≤ D.T2 := fun r hr => ⟨r, hr, false, by simp [qp]⟩

theorem ι_mem_T2 (s : MB) : B.ι s ∈ D.T2 := D.R2_le_T2 (D.R.ι_mem_R2 s)

theorem S₁_le_T2 : B.G.D₁.S₁ ≤ D.T2 := by
  intro g hg
  obtain ⟨x, rfl⟩ := B.exists_ι hg
  exact D.ι_mem_T2 x

theorem qp_mem_T2 (b : Bool) : D.qp b ∈ D.T2 := ⟨1, one_mem _, b, by simp⟩

theorem nf_mem_T2 (s : MB) (a b : Bool) : B.ι s * D.R.cp a * D.qp b ∈ D.T2 :=
  ⟨_, ⟨s, a, rfl⟩, b, rfl⟩

theorem exists_nf {x : X} (hx : x ∈ D.T2) :
    ∃ s : MB, ∃ a b : Bool, x = B.ι s * D.R.cp a * D.qp b := by
  obtain ⟨_, ⟨s, a, rfl⟩, b, rfl⟩ := hx
  exact ⟨s, a, b, rfl⟩

theorem actsQ1_qp (b : Bool) : B.ActsQ1 (D.qp b) (if b then MB.g0Q D.p else MB.gensQ1) := by
  cases b
  · simpa [qp] using actsQ1_one
  · exact D.acts_q

theorem qp_list_mem (b : Bool) :
    ∀ x ∈ (if b then MB.g0Q D.p else MB.gensQ1), MB.inQ1 x = true := by
  cases b
  · exact fun x hx => MB.gensQ1_mem x hx
  · exact MB.g0Q_mem D.p D.hp

theorem actsQ1_nf (s : MB) (a b : Bool) :
    B.ActsQ1 (B.ι s * D.R.cp a * D.qp b) (MB.H4elt D.p s a b) :=
  (D.R.actsQ1_R2 D.hj s a).mul (D.actsQ1_qp b) (D.qp_list_mem b)

theorem H4elt_rep (s : MB) (a b : Bool) : MB.H4elt D.p (MB.rep s) a b = MB.H4elt D.p s a b := by
  rw [MB.H4elt, MB.H4elt, MB.H2elt, MB.H2elt, MB.conjQ1_rep]

@[expose] def lift (τ : MB × Bool × Bool) : X := B.ι τ.1 * D.R.cp τ.2.1 * D.qp τ.2.2

theorem lift_mem_T2 (τ : MB × Bool × Bool) : D.lift τ ∈ D.T2 := D.nf_mem_T2 _ _ _

theorem actsQ1_lift (τ : MB × Bool × Bool) :
    B.ActsQ1 (D.lift τ) (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) := D.actsQ1_nf _ _ _

theorem exists_H4T {x : X} (hx : x ∈ D.T2) :
    ∃ τ ∈ MB.H4T, B.ActsQ1 x (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) := by
  obtain ⟨s, a, b, rfl⟩ := D.exists_nf hx
  refine ⟨(MB.rep s, a, b), MB.mem_H4T (MB.rep_mem s) a b, ?_⟩
  rw [D.H4elt_rep]
  exact D.actsQ1_nf s a b

theorem exists_lift {x : X} (hx : x ∈ D.T2) :
    ∃ τ ∈ MB.H4T, ∃ e : MB, MB.inE0 e = true ∧ x = D.lift τ * B.ι e := by
  obtain ⟨τ, hτ, hact⟩ := D.exists_H4T hx
  obtain ⟨e, he, rfl⟩ := D.exists_E0_of_acts (D.T2_le_P hx) (D.T2_le_P (D.lift_mem_T2 τ)) hact
    (D.actsQ1_lift τ)
  exact ⟨τ, hτ, e, he, rfl⟩

theorem H4elt_mem (s : MB) (a b : Bool) : ∀ x ∈ MB.H4elt D.p s a b, MB.inQ1 x = true :=
  MB.compQ1_mem (R2Data.H2elt_mem _ s a)

end T2Data

end BData

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
