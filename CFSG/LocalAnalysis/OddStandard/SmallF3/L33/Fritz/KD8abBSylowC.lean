module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBSylowB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abCTools

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB
open CFSG.ComponentClassification.HSFLit.Sec8
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem g0tau_mem : ∀ i : Fin 4, g0tau i ∈ H4T := by decide +kernel

theorem ar0_inQ1 : ∀ i : Fin 4, inQ1 (ar0 i) = true := by decide +kernel

theorem ar1_inQ1 : ∀ i : Fin 4, inQ1 (ar1 i) = true := by decide +kernel

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace T2Data

variable (D : B.T2Data)

theorem conj_E0_T2 {x : X} (hx : x ∈ D.T2) {e : MB} (he : MB.inE0 e = true) :
    ∃ e' : MB, MB.inE0 e' = true ∧ x * B.ι e * x⁻¹ = B.ι e' := by
  obtain ⟨τ, hτ, hact, -⟩ := D.exists_entry hx
  refine ⟨_, (MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)).2.2.2.2 e ((MB.mem_E0L e).mp he),
    hact e (MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he))⟩

theorem t_comm_E0 {e : MB} (he : MB.inE0 e = true) : B.ι e * t = t * B.ι e := by
  have h := congrArg B.ι (MB.E0_comm_Q1 MB.t (by decide +kernel) e ((MB.mem_E0L e).mp he))
  rw [map_mul, map_mul, B.ι_t] at h
  exact h.symm

theorem conj_rt {x : X} {φ : List MB} (hx : B.ActsQ1 x φ)
    (hE : ∀ e ∈ MB.E0L, MB.inE0 (MB.applyQ1 φ e) = true) {r e₀ e₁ w : MB}
    (hrQ : MB.inQ1 r = true) (he₀ : MB.inE0 e₀ = true) (hwQ : MB.inQ1 w = true)
    (he₁ : MB.inE0 e₁ = true) (hst : MB.applyQ1 φ (r * MB.t) = e₁ * w) :
    ∃ e : MB, MB.inE0 e = true ∧ x * (B.ι (r * e₀) * t) * x⁻¹ = B.ι e * B.ι w := by
  have hrtQ : MB.inQ1 (r * MB.t) = true := mul_mem (show r ∈ MB.Q1h from hrQ)
    (show MB.t ∈ MB.Q1h from (by decide +kernel : MB.inQ1 MB.t = true))
  have he₀Q : MB.inQ1 e₀ = true := MB.inQ1_of_inQC e₀ (MB.inQC_of_inE0 e₀ he₀)
  have he₂ := hE e₀ ((MB.mem_E0L e₀).mp he₀)
  refine ⟨e₁ * MB.applyQ1 φ e₀, mul_mem (show e₁ ∈ MB.E0h from he₁)
    (show MB.applyQ1 φ e₀ ∈ MB.E0h from he₂), ?_⟩
  have hbt : B.ι (r * e₀) * t = B.ι (r * MB.t) * B.ι e₀ := by
    rw [map_mul, map_mul, B.ι_t, mul_assoc, t_comm_E0 he₀, ← mul_assoc]
  calc x * (B.ι (r * e₀) * t) * x⁻¹ =
      (x * B.ι (r * MB.t) * x⁻¹) * (x * B.ι e₀ * x⁻¹) := by rw [hbt]; group
    _ = B.ι (e₁ * w * MB.applyQ1 φ e₀) := by
      rw [hx _ hrtQ, hx _ he₀Q, hst]
      simp only [map_mul]
    _ = _ := by
      rw [mul_assoc, MB.E0_comm_Q1 w hwQ _ ((MB.mem_E0L _).mp he₂), ← mul_assoc, map_mul]

theorem false_of_normalizer {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : D.T2 ≤ Q) {h : X}
    (hhQ : h ∈ Q) (hN : h ∈ normalizer (D.T2 : Set X)) (hh : h ∉ D.T2) : False := by
  obtain ⟨i, hfix⟩ := D.exists_E0_match hN
  set r := D.lift (MB.E0tau i) with hr
  have hrT : r ∈ D.T2 := D.lift_mem_T2 _
  set h' := r⁻¹ * h with hh'
  have hh'N : h' ∈ normalizer (D.T2 : Set X) := mul_mem (inv_mem (le_normalizer hrT)) hN
  have hh'Q : h' ∈ Q := mul_mem (inv_mem (hTQ hrT)) hhQ
  have hh'T : h' ∉ D.T2 := fun h1 => hh (by
    have := mul_mem hrT h1
    rwa [hh', mul_inv_cancel_left] at this)
  have hfixi : ∀ e : MB, MB.inE0 e = true → h'⁻¹ * B.ι e * h' = B.ι e := fun e he => by
    have := hfix e he
    calc h'⁻¹ * B.ι e * h' = h'⁻¹ * (h' * B.ι e * h'⁻¹) * h' := by rw [this]
      _ = B.ι e := by group
  obtain ⟨x', hx'Q, hx'⟩ := D.conj_Q1 hh'N (x := MB.t) (by decide +kernel)
  rw [B.ι_t] at hx'
  have hx'A : MB.inQC x' = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨a', ha', ha'e⟩ := D.conj_A (inv_mem hh'N) hc
    have ht' : MB.t = a' := B.ι_injective (by
      rw [← ha'e, ← hx', B.ι_t]
      group)
    rw [← ht', MB.t_not_inQC] at ha'
    exact Bool.false_ne_true ha'
  set b := x' * MB.t⁻¹ with hb
  have hbA : MB.inQC b = true := MB.inQC_mul_t x' hx'Q hx'A
  set e₀ := (MB.arep b)⁻¹ * b with he₀def
  have he₀ : MB.inE0 e₀ = true := MB.arep_spec b hbA
  have hbt : h' * t * h'⁻¹ = B.ι (MB.arep b * e₀) * t := by
    rw [hx', he₀def, mul_inv_cancel_left, hb, map_mul, map_inv, B.ι_t, inv_mul_cancel_right]
  have hE0' : ∀ x ∈ D.T2, ∀ e : MB, MB.inE0 e = true →
      ∃ e' : MB, MB.inE0 e' = true ∧ (x * h') * B.ι e * (x * h')⁻¹ = B.ι e' := by
    intro x hx e he
    obtain ⟨e', he', hee⟩ := D.conj_E0_T2 hx he
    refine ⟨e', he', ?_⟩
    have h1 := hfix e he
    calc x * h' * B.ι e * (x * h')⁻¹ = x * (h' * B.ι e * h'⁻¹) * x⁻¹ := by group
      _ = B.ι e' := by rw [h1, hee]
  rcases MB.arep_cases b with ⟨j₀, hj₀⟩ | ⟨j₁, hj₁⟩
  ·
    have hτ₀m : MB.g0tau j₀ ∈ MB.H4T := MB.g0tau_mem j₀
    have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ₀m)
    set r' := D.lift (MB.g0tau j₀) with hr'
    have hr'T : r' ∈ D.T2 := D.lift_mem_T2 _
    obtain ⟨e, he, hconj⟩ := conj_rt (D.actsQ1_lift (MB.g0tau j₀)) hspec.2.2.2.2
      (r := MB.ar0 j₀) (e₀ := e₀) (w := MB.t) (MB.ar0_inQ1 j₀) he₀ (by decide +kernel)
      (MB.g0tau_facts D.p D.hp j₀) (by group)
    have hgN : r' * h' ∈ normalizer (S.E S.y : Set X) := by
      refine mem_normalizer_E₁ (hE0' r' hr'T) ⟨e, he, ?_⟩
      calc r' * h' * t * (r' * h')⁻¹ = r' * (h' * t * h'⁻¹) * r'⁻¹ := by group
        _ = r' * (B.ι (MB.ar0 j₀ * e₀) * t) * r'⁻¹ := by rw [hbt, hj₀]
        _ = B.ι e * B.ι MB.t := hconj
        _ = B.ι e * t := by rw [B.ι_t]
    have hgQ : r' * h' ∈ Q := mul_mem (hTQ hr'T) hh'Q
    have hmax := B.G.D₁.S₁_maximal (B.G.D₁.S₁ ⊔ zpowers (r' * h'))
      (hQ.to_le (sup_le (D.S₁_le_T2.trans hTQ) (zpowers_le.mpr hgQ))) le_sup_left
      (sup_le B.G.D₁.S₁_le (zpowers_le.mpr hgN))
    have hgS : r' * h' ∈ B.G.D₁.S₁ := hmax ▸ mem_sup_right (mem_zpowers _)
    apply hh'T
    have := mul_mem (inv_mem hr'T) (D.S₁_le_T2 hgS)
    rwa [inv_mul_cancel_left] at this
  ·
    set K : Subgroup X := D.T2 ⊓ (normalizer (S.E S.y : Set X)).map
      (MulAut.conj h').toMonoidHom with hK
    have hmemK : ∀ x : X, x ∈ K ↔ x ∈ D.T2 ∧ h'⁻¹ * x * h' ∈ normalizer (S.E S.y : Set X) := by
      intro x
      rw [hK, mem_inf, mem_map_equiv, MulAut.conj_symm_apply]
    have hKp : IsPGroup 2 K := D.isPGroup_T2.to_le inf_le_left
    have hKN : K ≤ normalizer (((S.E S.y).map (MulAut.conj h').toMonoidHom : Subgroup X) :
        Set X) := by
      intro x hx
      have hn := ((hmemK x).mp hx).2
      rw [mem_normalizer_iff]
      intro y
      rw [mem_map_equiv, mem_map_equiv,
        MulAut.conj_symm_apply, MulAut.conj_symm_apply,
        show h'⁻¹ * (x * y * x⁻¹) * h' =
          (h'⁻¹ * x * h') * (h'⁻¹ * y * h') * (h'⁻¹ * x * h')⁻¹ by group]
      exact mem_normalizer_iff.mp hn _
    have hle := KD8abC.card_le_256 B hKp hKN
    have hge := D.card_ge_of_lifts K (MB.stabL D.p (MB.ar1 j₁))
      (fun e he => (List.mem_filter.mp he).1)
      (((MB.H4Zof_nodup D.p D.hp).sublist ((List.filter_sublist).map _))) ?_ ?_
    · have := MB.stab_facts D.p D.hp j₁
      omega
    · intro e he
      obtain ⟨heZ, hst⟩ := List.mem_filter.mp he
      obtain ⟨hτ, hφ⟩ := MB.mem_H4Zof_spec D.hp heZ
      have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)
      have hact := D.actsQ1_lift e.1
      rw [← hφ] at hact hspec
      refine (hmemK _).mpr ⟨D.lift_mem_T2 _, ?_⟩
      have hc : MB.ar1 j₁ * e₀ = e₀ * MB.ar1 j₁ :=
        MB.E0_comm_Q1 _ (MB.ar1_inQ1 j₁) e₀ ((MB.mem_E0L e₀).mp he₀)
      have hb1 : b = MB.ar1 j₁ * e₀ := by rw [← hj₁, he₀def, mul_inv_cancel_left]
      have hbQ : MB.inQ1 b = true := MB.inQ1_of_inQC b hbA
      have hbtQ : MB.inQ1 (b * MB.t) = true :=
        mul_mem (show b ∈ MB.Q1h from hbQ)
          (show MB.t ∈ MB.Q1h from (by decide +kernel : MB.inQ1 MB.t = true))
      have he₁E : MB.inE0 (MB.applyQ1 e.2 (MB.ar1 j₁ * MB.t) * (MB.ar1 j₁ * MB.t)⁻¹ * e₀⁻¹) =
          true := mul_mem (show _ ∈ MB.E0h from hst) (inv_mem (show e₀ ∈ MB.E0h from he₀))
      obtain ⟨e₅, he₅, hconj⟩ := conj_rt hact hspec.2.2.2.2 (r := MB.ar1 j₁) (e₀ := e₀)
        (MB.ar1_inQ1 j₁) he₀ hbtQ he₁E (by rw [hb1, hc]; group)
      have hbt' : h' * t * h'⁻¹ = B.ι (MB.ar1 j₁ * e₀) * t := by rw [hbt, hj₁]
      have hbt'' : h'⁻¹ * B.ι (b * MB.t) * h' = t := by
        rw [map_mul, B.ι_t, hb1, ← hbt']
        group
      refine mem_normalizer_E₁ (B := B) (fun e' he' => ?_) ⟨e₅, he₅, ?_⟩
      · refine ⟨_, hspec.2.2.2.2 e' ((MB.mem_E0L e').mp he'), ?_⟩
        calc h'⁻¹ * D.lift e.1 * h' * B.ι e' * (h'⁻¹ * D.lift e.1 * h')⁻¹ =
            h'⁻¹ * (D.lift e.1 * (h' * B.ι e' * h'⁻¹) * (D.lift e.1)⁻¹) * h' := by group
          _ = h'⁻¹ * B.ι (MB.applyQ1 e.2 e') * h' := by
            rw [hfix e' he', hact e' (MB.inQ1_of_inQC e' (MB.inQC_of_inE0 e' he'))]
          _ = _ := hfixi _ (hspec.2.2.2.2 e' ((MB.mem_E0L e').mp he'))
      · calc h'⁻¹ * D.lift e.1 * h' * t * (h'⁻¹ * D.lift e.1 * h')⁻¹ =
            h'⁻¹ * (D.lift e.1 * (h' * t * h'⁻¹) * (D.lift e.1)⁻¹) * h' := by group
          _ = h'⁻¹ * (B.ι e₅ * B.ι (b * MB.t)) * h' := by rw [hbt', hconj]
          _ = (h'⁻¹ * B.ι e₅ * h') * (h'⁻¹ * B.ι (b * MB.t) * h') := by group
          _ = B.ι e₅ * t := by rw [hfixi e₅ he₅, hbt'']
    · intro e he
      refine (hmemK _).mpr ⟨D.ι_mem_T2 e, ?_⟩
      rw [hfixi e ((MB.mem_E0L e).mpr he)]
      exact le_normalizer (B.ι_mem_E₁ (MB.inE1_of_inE0 e ((MB.mem_E0L e).mpr he)))

theorem T2_maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → D.T2 ≤ Q → Q = D.T2 := by
  intro Q hQ hTQ
  by_contra hne
  obtain ⟨h, hhQ, hhT, hhN⟩ :=
    KD8abC.exists_mem_normalizer hQ (lt_of_le_of_ne hTQ (Ne.symm hne))
  exact D.false_of_normalizer hQ hTQ hhQ hhN hhT

@[expose] def sylow : Sylow 2 X where
  toSubgroup := D.T2
  isPGroup' := D.isPGroup_T2
  is_maximal' hQ hle := D.T2_maximal _ hQ hle

end T2Data

end BData

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
