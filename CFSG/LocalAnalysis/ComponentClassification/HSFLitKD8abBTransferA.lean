module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBSylowC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBTrData

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB

theorem Q1reps_inQ1 : ∀ f ∈ Q1reps, inQ1 f = true := by decide +kernel

theorem applyQ1_mem {f : List MB} (hf : ∀ x ∈ f, inQ1 x = true) (y : MB) :
    inQ1 (applyQ1 f y) = true := KD8abB.nfProd_mem (H := Q1h) f _ hf

theorem sqOK_spec {φ : List MB} (h : sqOK φ = true) :
    ∃ f : MB, inQ1 f = true ∧ f * f = 1 ∧ compQ1 φ φ = conjQ1 f := by
  simp only [sqOK, List.any_eq_true, List.mem_filter, beq_iff_eq] at h
  obtain ⟨f, ⟨hf, hff⟩, heq⟩ := h
  exact ⟨f, Q1reps_inQ1 f hf, hff, heq⟩

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

theorem ι_mem_A {a : MB} (ha : MB.inQC a = true) :
    B.ι a ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ ⊔ B.G.D₁.C₁ := by
  obtain ⟨bs, -, rfl⟩ := List.mem_map.mp (MB.AL_spec a ha)
  rw [map_nfProd]
  refine nfProd_mem _ _ fun g hg => ?_
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hE0 : ∀ e : MB, MB.inE0 e = true →
      B.ι e ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ ⊔ B.G.D₁.C₁ := fun e he =>
    mem_sup_left (B.G.V₁.E0_le_Q0 (B.ι_mem_E0 he))
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [B.ι_w₂]; exact mem_sup_left B.G.V₁.w₂_mem_Q0
  · rw [B.ι_w₁]; exact mem_sup_left B.G.V₁.w₁N_mem_Q0
  · rw [map_mul, B.ι_t, B.ι_v]
    refine B.G.V₁.tvN_mem_Q0C1 ?_
    have := congrArg B.ι MB.w₂_conj_v
    rwa [map_mul, map_mul, map_inv, map_mul, B.ι_w₂, B.ι_v, B.ι_y] at this
  · exact hE0 MB.z (by decide +kernel)
  · exact hE0 MB.y (by decide +kernel)
  · exact hE0 MB.k (by decide +kernel)

theorem not_conjTo_A {a : MB} (ha : MB.inQC a = true) : ¬ ConjTo t (B.ι a) :=
  B.G.D₁.no_conj_of (Or.inr B.h₁) _ (ι_mem_A ha)

omit [Finite X] in
include A in
theorem sq_of_conjTo {m : X} (h : ConjTo t m) : m * m = 1 := by
  obtain ⟨g, rfl⟩ := h
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [KD7.tt (A := A)]; group

namespace T2Data

variable (D : B.T2Data)

@[expose] def Nm (m : X) : Subgroup X where
  carrier := {y | y ∈ D.T2 ∧ ∃ e : MB, MB.inE0 e = true ∧ y * m * y⁻¹ = B.ι e * m}
  mul_mem' := by
    rintro y₁ y₂ ⟨h₁, e₁, he₁, hy₁⟩ ⟨h₂, e₂, he₂, hy₂⟩
    obtain ⟨e₃, he₃, hy₃⟩ := D.conj_E0_T2 h₁ he₂
    refine ⟨mul_mem h₁ h₂, e₃ * e₁,
      mul_mem (show e₃ ∈ MB.E0h from he₃) (show e₁ ∈ MB.E0h from he₁), ?_⟩
    calc y₁ * y₂ * m * (y₁ * y₂)⁻¹ = y₁ * (y₂ * m * y₂⁻¹) * y₁⁻¹ := by group
      _ = (y₁ * B.ι e₂ * y₁⁻¹) * (y₁ * m * y₁⁻¹) := by rw [hy₂]; group
      _ = B.ι (e₃ * e₁) * m := by rw [hy₃, hy₁, map_mul]; group
  one_mem' := ⟨one_mem _, 1, by decide +kernel, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, e, he, hye⟩
    obtain ⟨e', he', hy'⟩ := D.conj_E0_T2 (inv_mem hy) he
    refine ⟨inv_mem hy, e'⁻¹, inv_mem (show e' ∈ MB.E0h from he'), ?_⟩
    have h1 : m = y⁻¹ * B.ι e * y * (y⁻¹ * m * y) := by
      calc m = y⁻¹ * (y * m * y⁻¹) * y := by group
        _ = y⁻¹ * (B.ι e * m) * y := by rw [hye]
        _ = y⁻¹ * B.ι e * y * (y⁻¹ * m * y) := by group
    have h2 : y⁻¹ * B.ι e * y = B.ι e' := by simpa using hy'
    rw [h2] at h1
    calc y⁻¹ * m * y⁻¹⁻¹ = (B.ι e')⁻¹ * (B.ι e' * (y⁻¹ * m * y)) := by group
      _ = B.ι e'⁻¹ * m := by rw [← h1, map_inv]

theorem card_Nm_centralizer {m : X} (hm : m ∈ D.T2) (hm2 : m * m = 1) {τ : MB × Bool × Bool}
    (hτ : τ ∈ MB.H4T) (hact : B.ActsQ1 m (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)) :
    8 * (MB.commL D.p (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)).length ≤
      MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) *
        Nat.card (D.Nm m ⊓ centralizer ({m} : Set X) : Subgroup X) := by
  classical
  set φ := MB.H4elt D.p τ.1 τ.2.1 τ.2.2 with hφ
  have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)
  rw [← hφ] at hspec
  have hφm := D.H4elt_mem τ.1 τ.2.1 τ.2.2
  rw [← hφ] at hφm
  have hge := D.card_ge_of_lifts (D.Nm m) (MB.commL D.p φ)
    (fun e he => (List.mem_filter.mp he).1)
    ((MB.H4Zof_nodup D.p D.hp).sublist ((List.filter_sublist).map _)) ?_ ?_
  ·
    set I : Finset X := ((MB.E0L.filter fun e => MB.applyQ1 φ e == e).map
      fun e => B.ι e * m).toFinset with hI
    have hIcard : I.card ≤ MB.nfix φ := by
      rw [hI, MB.nfix]
      exact (List.toFinset_card_le _).trans (by rw [List.length_map])
    have horb : ∀ y ∈ D.Nm m, y * m * y⁻¹ ∈ I := by
      rintro y ⟨-, e, he, hye⟩
      rw [hye, hI, List.mem_toFinset, List.mem_map]
      refine ⟨e, List.mem_filter.mpr ⟨(MB.mem_E0L e).mp he, beq_iff_eq.mpr ?_⟩, rfl⟩
      have hsq : (B.ι e * m) * (B.ι e * m) = 1 := by
        rw [← hye]
        calc y * m * y⁻¹ * (y * m * y⁻¹) = y * (m * m) * y⁻¹ := by group
          _ = 1 := by rw [hm2]; group
      have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
      have h1 : m * B.ι e * m⁻¹ = (B.ι e)⁻¹ := by
        rw [hmi]
        calc m * B.ι e * m = (B.ι e)⁻¹ * ((B.ι e * m) * (B.ι e * m)) := by group
          _ = (B.ι e)⁻¹ := by rw [hsq, mul_one]
      apply B.ι_injective
      rw [← hact e (MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he)), h1, ← map_inv,
        show e⁻¹ = e from inv_eq_of_mul_eq_one_right (MB.E0L_sq e ((MB.mem_E0L e).mp he))]
    have h2 := KD8abC.card_le_of_orbit I horb
    calc 8 * (MB.commL D.p φ).length ≤ Nat.card (D.Nm m) := hge
      _ ≤ I.card * Nat.card (D.Nm m ⊓ centralizer ({m} : Set X) : Subgroup X) := h2
      _ ≤ _ := Nat.mul_le_mul_right _ hIcard
  ·
    intro e he
    obtain ⟨heZ, hcomm⟩ := List.mem_filter.mp he
    obtain ⟨hτ', hφ'⟩ := MB.mem_H4Zof_spec D.hp heZ
    have hact' := D.actsQ1_lift e.1
    rw [← hφ'] at hact'
    have hlT := D.lift_mem_T2 e.1
    refine ⟨hlT, ?_⟩
    have hφ'm : ∀ x ∈ e.2, MB.inQ1 x = true := by
      rw [hφ']; exact D.H4elt_mem _ _ _
    have h1 := hact'.mul hact hφm
    have h2 := hact.mul hact' hφ'm
    rw [beq_iff_eq.mp hcomm] at h2
    obtain ⟨e', he', hee⟩ := D.exists_E0_of_acts (mul_mem (D.T2_le_P hlT) (D.T2_le_P hm))
      (mul_mem (D.T2_le_P hm) (D.T2_le_P hlT)) h1 h2
    obtain ⟨e'', he'', hee''⟩ := D.conj_E0_T2 (mul_mem hm hlT) he'
    refine ⟨e'', he'', ?_⟩
    calc D.lift e.1 * m * (D.lift e.1)⁻¹ = (m * D.lift e.1 * B.ι e') * (D.lift e.1)⁻¹ := by
          rw [← hee]
      _ = (m * D.lift e.1) * B.ι e' * (m * D.lift e.1)⁻¹ * m := by group
      _ = B.ι e'' * m := by rw [hee'']
  ·
    intro e he
    have heE := (MB.mem_E0L e).mpr he
    refine ⟨D.ι_mem_T2 e, e * (MB.applyQ1 φ e⁻¹), mul_mem (show e ∈ MB.E0h from heE)
      (show _ ∈ MB.E0h from hspec.2.2.2.2 e⁻¹ ((MB.mem_E0L _).mp
        (inv_mem (show e ∈ MB.E0h from heE)))), ?_⟩
    have h1 := hact e⁻¹ (MB.inQ1_of_inQC _ (MB.inQC_of_inE0 _ (inv_mem (show e ∈ MB.E0h from heE))))
    rw [map_mul, ← h1, map_inv]
    group

theorem pow_four {m : X} {φ : List MB} (hact : B.ActsQ1 m φ) (hφl : φ.length = 7)
    (hφm : ∀ x ∈ φ, MB.inQ1 x = true)
    (hsq : (MB.commL D.p φ).all (fun e' => MB.sqOK e'.2) = true) {y : X} (hy : y ∈ D.Nm m) :
    y ^ 4 = 1 := by
  obtain ⟨hyT, e, he, hye⟩ := hy
  obtain ⟨τ, hτ, hacty, -⟩ := D.exists_entry hyT
  have hφym := D.H4elt_mem τ.1 τ.2.1 τ.2.2
  have hl := MB.H4elt_length D.hp τ.1 τ.2.1 τ.2.2
  have h1 := hacty.mul hact hφm
  have h2 := hact.mul hacty hφym
  have hym : y * m = B.ι e * (m * y) := by
    calc y * m = (y * m * y⁻¹) * y := by group
      _ = B.ι e * (m * y) := by rw [hye]; group
  have h3 : B.ActsQ1 (y * m) (MB.compQ1 φ (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)) := fun x hx => by
    have hz := MB.applyQ1_mem (MB.compQ1_mem (g := MB.H4elt D.p τ.1 τ.2.1 τ.2.2) hφm) x
    rw [hym, show B.ι e * (m * y) * B.ι x * (B.ι e * (m * y))⁻¹ =
      B.ι e * (m * y * B.ι x * (m * y)⁻¹) * (B.ι e)⁻¹ by group, h2 x hx, ← map_inv,
      ← map_mul, ← map_mul, ← MB.E0_comm_Q1 _ hz e ((MB.mem_E0L e).mp he),
      mul_inv_cancel_right]
  have hcomm : MB.compQ1 (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) φ =
      MB.compQ1 φ (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) :=
    h1.eq_list h3 (by simp [MB.compQ1, hφl]) (by simp [MB.compQ1, hl])
  have hmem : (τ, MB.H4elt D.p τ.1 τ.2.1 τ.2.2) ∈ MB.commL D.p φ :=
    List.mem_filter.mpr ⟨MB.mem_H4Zof D.hp hτ, beq_iff_eq.mpr hcomm.symm⟩
  obtain ⟨f, hfQ, hff, hfe⟩ := MB.sqOK_spec (List.all_eq_true.mp hsq _ hmem)
  have h4 := hacty.mul hacty hφym
  rw [hfe] at h4
  obtain ⟨e', he', hyy⟩ := D.exists_E0_of_actsAs (mul_mem (D.T2_le_P hyT) (D.T2_le_P hyT))
    (D.T2_le_P (D.ι_mem_T2 f)) h4.actsAs
  have hfe' : f * e' = e' * f := MB.E0_comm_Q1 f hfQ e' ((MB.mem_E0L e').mp he')
  have hee : e' * e' = 1 := MB.E0L_sq e' ((MB.mem_E0L e').mp he')
  calc y ^ 4 = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = B.ι (f * e' * (f * e')) := by rw [hyy, ← map_mul, ← map_mul]
    _ = 1 := by
      rw [show f * e' * (f * e') = (f * f) * (e' * e') by
        rw [mul_assoc, ← mul_assoc e', ← hfe', mul_assoc, mul_assoc], hff, hee, one_mul,
        map_one]

end T2Data

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
