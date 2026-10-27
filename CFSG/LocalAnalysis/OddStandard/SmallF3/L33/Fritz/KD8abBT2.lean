module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBT2Data

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB
open CFSG.ComponentClassification.HSFLit.Sec8
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem k_central : ∀ s : MB, s * k * s⁻¹ = k := by decide +kernel

theorem zk_central : ∀ s : MB, s * (z * k) * s⁻¹ = z * k := by decide +kernel

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace R2Data

variable (R : B.R2Data)

@[expose] def σ : List MB := (MB.r2Classes.getD R.j ([], 1)).1

@[expose] def s₂ : MB := (MB.r2Classes.getD R.j ([], 1)).2

@[expose] def cp (a : Bool) : X := if a then R.c else 1

@[expose] def σp (a : Bool) (x : MB) : MB := if a then MB.applyMB R.σ x else x

theorem cp_conj (a : Bool) (x : MB) : R.cp a * B.ι x * (R.cp a)⁻¹ = B.ι (R.σp a x) := by
  cases a
  · simp [cp, σp]
  · exact R.acts x

theorem cp_mul_cp (a a' : Bool) :
    R.cp a * R.cp a' = B.ι (if a && a' then R.s₂ else 1) * R.cp (xor a a') := by
  cases a <;> cases a' <;> simp [cp, s₂, R.sq]

theorem cp_inv (a : Bool) : (R.cp a)⁻¹ = B.ι (if a then R.s₂⁻¹ else 1) * R.cp a := by
  cases a
  · simp [cp]
  · show R.c⁻¹ = B.ι (R.s₂⁻¹) * R.c
    calc R.c⁻¹ = (R.c * R.c)⁻¹ * R.c := by group
      _ = _ := by rw [R.sq, ← map_inv]; rfl

@[expose] def R2 : Subgroup X where
  carrier := {x | ∃ s : MB, ∃ a : Bool, x = B.ι s * R.cp a}
  mul_mem' := by
    rintro _ _ ⟨s, a, rfl⟩ ⟨s', a', rfl⟩
    refine ⟨s * R.σp a s' * (if a && a' then R.s₂ else 1), xor a a', ?_⟩
    calc B.ι s * R.cp a * (B.ι s' * R.cp a') =
        B.ι s * (R.cp a * B.ι s' * (R.cp a)⁻¹) * (R.cp a * R.cp a') := by group
      _ = _ := by rw [R.cp_conj, R.cp_mul_cp, map_mul, map_mul]; group
  one_mem' := ⟨1, false, by simp [cp]⟩
  inv_mem' := by
    rintro _ ⟨s, a, rfl⟩
    refine ⟨(if a then R.s₂⁻¹ else 1) * R.σp a s⁻¹, a, ?_⟩
    rw [mul_inv_rev, R.cp_inv, map_mul, ← map_inv]
    calc B.ι (if a then R.s₂⁻¹ else 1) * R.cp a * B.ι s⁻¹ =
        B.ι (if a then R.s₂⁻¹ else 1) * (R.cp a * B.ι s⁻¹ * (R.cp a)⁻¹) * R.cp a := by group
      _ = _ := by rw [R.cp_conj]

theorem ι_mem_R2 (s : MB) : B.ι s ∈ R.R2 := ⟨s, false, by simp [cp]⟩

theorem cp_mem_R2 (a : Bool) : R.cp a ∈ R.R2 := ⟨1, a, by simp⟩

theorem R2_le_P : R.R2 ≤ R.P := by
  rintro _ ⟨s, a, rfl⟩
  refine mul_mem (R.S₁_le (B.ι_mem_S₁ s)) ?_
  cases a
  · exact one_mem _
  · exact R.c_mem

theorem isPGroup_R2 : IsPGroup 2 R.R2 := R.isPGroup.to_le R.R2_le_P

theorem cQ_acts : B.ActsQ1 R.c (MB.cQ R.j) := R.acts.actsQ1

theorem actsQ1_cp (a : Bool) : B.ActsQ1 (R.cp a) (if a then MB.cQ R.j else MB.gensQ1) := by
  cases a
  · simpa [cp] using actsQ1_one
  · exact R.cQ_acts

theorem cp_list_mem (j : ℕ) (hj : j < 8) (a : Bool) :
    ∀ x ∈ (if a then MB.cQ j else MB.gensQ1), MB.inQ1 x = true := by
  cases a
  · exact fun x hx => MB.gensQ1_mem x hx
  · exact MB.cQ_mem j hj

theorem actsQ1_R2 {p : ℕ × ℕ} (hj : R.j = p.1) (s : MB) (a : Bool) :
    B.ActsQ1 (B.ι s * R.cp a) (MB.H2elt p s a) := by
  rw [MB.H2elt, ← hj]
  exact (actsQ1_ι s).mul (R.actsQ1_cp a) (cp_list_mem R.j R.hj a)

theorem H2elt_mem (p : ℕ × ℕ) (s : MB) (a : Bool) :
    ∀ x ∈ MB.H2elt p s a, MB.inQ1 x = true :=
  MB.compQ1_mem (conjQ1_mem s)

theorem R2_le_normalizer_Q1 : R.R2 ≤ normalizer (B.Q1 : Set X) := by
  rintro _ ⟨s, a, rfl⟩
  exact (R.actsQ1_R2 (p := (R.j, 0)) rfl s a).mem_normalizer (H2elt_mem _ s a)

theorem R2_conj_k (s : MB) (a : Bool) :
    B.ι s * R.cp a * S.k * (B.ι s * R.cp a)⁻¹ = S.k ∨
      B.ι s * R.cp a * S.k * (B.ι s * R.cp a)⁻¹ = S.z * S.k := by
  have e1 : B.ι s * R.cp a * S.k * (B.ι s * R.cp a)⁻¹ =
      B.ι s * (R.cp a * B.ι MB.k * (R.cp a)⁻¹) * (B.ι s)⁻¹ := by rw [B.ι_k]; group
  rw [e1, R.cp_conj, ← map_inv, ← map_mul, ← map_mul]
  obtain ⟨h7, hlen⟩ := MB.r2Classes_k R.j R.hj
  cases a
  · left
    rw [show R.σp false MB.k = MB.k from rfl, MB.k_central, B.ι_k]
  · right
    rw [show R.σp true MB.k = MB.applyMB R.σ MB.k from rfl, σ, MB.applyMB_k _ hlen, h7,
      MB.zk_central, map_mul, B.ι_z, B.ι_k]

end R2Data

theorem mem_centralizer_Q1_of_actsAs {g h : X} (hgh : ActsAs B.Q1 g h) :
    h⁻¹ * g ∈ centralizer (B.Q1 : Set X) := by
  rw [mem_centralizer_iff]
  intro r hr
  have := hgh r hr
  calc r * (h⁻¹ * g) = h⁻¹ * (h * r * h⁻¹) * g := by group
    _ = h⁻¹ * (g * r * g⁻¹) * g := by rw [this]
    _ = h⁻¹ * g * r := by group

theorem conj_R2_actsAs (R : B.R2Data) {p : ℕ × ℕ} (hp : p ∈ MB.goodIdx) (hj : R.j = p.1)
    {g : X} (hg : B.ActsQ1 g (MB.g0Q p)) :
    ∀ h ∈ R.R2, ∃ h' ∈ R.R2, ActsAs B.Q1 (g * h * g⁻¹) h' := by
  have hgm := MB.g0Q_mem p hp
  have hgN : g ∈ normalizer (B.Q1 : Set X) := hg.mem_normalizer hgm
  have hgen : ∀ i : Fin 8, ActsAs B.Q1 (g * B.ι (MB.gens.getD i 1) * g⁻¹)
      (B.ι (MB.liftSp.getD i (1, false)).1 * R.cp (MB.liftSp.getD i (1, false)).2) := by
    intro i
    refine actsAs_conj_of hgN ?_
    have h1 := hg.mul (actsQ1_ι (MB.gens.getD i 1)) (conjQ1_mem _)
    have h2 := (R.actsQ1_R2 hj (MB.liftSp.getD i (1, false)).1
      (MB.liftSp.getD i (1, false)).2).mul hg hgm
    rw [MB.lift_sp p hp i] at h1
    exact h1.actsAs_of_eq h2
  have hS : ∀ s : MB, ∃ h' ∈ R.R2, ActsAs B.Q1 (g * B.ι s * g⁻¹) h' := by
    intro s
    set L₂ := MB.liftSp.map (fun x => B.ι x.1 * R.cp x.2) with hL₂
    refine ⟨Sec8.nfProd L₂ (MB.nfBits s), nfProd_mem _ _ fun x hx => ?_, ?_⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨y.1, y.2, rfl⟩
    have e1 : g * B.ι s * g⁻¹ = Sec8.nfProd (MB.gens.map fun a => g * B.ι a * g⁻¹)
        (MB.nfBits s) := by
      conv_lhs => rw [MB.nf_spec s]
      exact map_nfProd ((MulAut.conj g).toMonoidHom.comp B.ι) _ _
    rw [e1]
    refine ActsAs.nfProd _ _ _ ?_ fun h hh => ?_
    · have hf : ∀ i : Fin 8, ActsAs B.Q1 ((MB.gens.map fun a => g * B.ι a * g⁻¹).getD i 1)
          (L₂.getD i 1) := by
        intro i
        have := hgen i
        rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
          hL₂, List.getElem?_map, show MB.gens[(i : ℕ)]? = some (MB.gens.getD i 1) by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [MB.gens])]; rfl,
          show MB.liftSp[(i : ℕ)]? = some (MB.liftSp.getD i (1, false)) by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by simp [MB.liftSp_length])]; rfl]
      simp only [hL₂, MB.liftSp, MB.gens, List.map_cons, List.map_nil, List.forall₂_cons,
        List.Forall₂.nil, and_true]
      exact ⟨hf 0, hf 1, hf 2, hf 3, hf 4, hf 5, hf 6, hf 7⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hh
      exact R.R2_le_normalizer_Q1 ⟨y.1, y.2, rfl⟩
  have hc : ActsAs B.Q1 (g * R.c * g⁻¹) (B.ι (MB.w₂ * MB.w₁) * R.cp true) := by
    refine actsAs_conj_of hgN ?_
    have h1 := hg.mul R.cQ_acts (MB.cQ_mem R.j R.hj)
    have h2 := (R.actsQ1_R2 hj (MB.w₂ * MB.w₁) true).mul hg hgm
    rw [hj, MB.lift_c p hp] at h1
    exact h1.actsAs_of_eq h2
  rintro _ ⟨s, a, rfl⟩
  obtain ⟨h₁, hh₁, hact₁⟩ := hS s
  cases a
  · exact ⟨h₁, hh₁, by simpa [R2Data.cp] using hact₁⟩
  · refine ⟨h₁ * (B.ι (MB.w₂ * MB.w₁) * R.cp true), mul_mem hh₁ ⟨_, _, rfl⟩, ?_⟩
    have e2 : g * (B.ι s * R.cp true) * g⁻¹ = (g * B.ι s * g⁻¹) * (g * R.c * g⁻¹) := by
      show g * (B.ι s * R.c) * g⁻¹ = _
      group
    rw [e2]
    exact hact₁.mul (R.R2_le_normalizer_Q1 ⟨_, _, rfl⟩) hc

theorem sq_actsAs_R2 (R : B.R2Data) {p : ℕ × ℕ} (hp : p ∈ MB.goodIdx) (hj : R.j = p.1)
    {g : X} (hg : B.ActsQ1 g (MB.g0Q p)) : ActsAs B.Q1 (g * g) (B.ι MB.w₂) := by
  have h1 := hg.mul hg (MB.g0Q_mem p hp)
  rw [MB.lift_sq p hp] at h1
  simpa [R2Data.cp] using h1.actsAs_of_eq (R.actsQ1_R2 hj MB.w₂ false)

theorem not_actsAs_R2 (R : B.R2Data) {p : ℕ × ℕ} (hp : p ∈ MB.goodIdx)
    {g : X} (hg : B.ActsQ1 g (MB.g0Q p)) : ∀ h ∈ R.R2, ¬ ActsAs B.Q1 g h := by
  rintro _ ⟨s, a, rfl⟩ hact
  have hk : g * S.k * g⁻¹ = S.y * S.k := by
    have := hg MB.k (by decide +kernel)
    rwa [MB.g0Q_k p hp, map_mul, B.ι_y, B.ι_k] at this
  have := hact S.k (B.ι_k ▸ B.ι_mem_Q1 (by decide +kernel))
  rw [hk] at this
  rcases R.R2_conj_k s a with h | h <;> rw [h] at this
  · exact (isRefl_y S).ne_one (by simpa using this)
  · exact (isRefl_y S).ne_z (mul_right_cancel this)

structure T2Data (B : BData S T₁) where
  R : B.R2Data
  p : ℕ × ℕ
  hp : p ∈ MB.goodIdx
  hj : R.j = p.1
  q : X
  P : Subgroup X
  isPGroup : IsPGroup 2 P
  R2_le : R.R2 ≤ P
  q_mem : q ∈ P
  acts_q : B.ActsQ1 q (MB.g0Q p)

variable (B) in
theorem nonempty_t2Data : Nonempty (T2Data B) := by
  obtain ⟨R⟩ := B.nonempty_r2Data
  obtain ⟨δ, -, f, hf, hδ⟩ := B.exists_delta
  obtain ⟨i, hi, hfi⟩ := good_of R hf hδ
  have hfL : f ∈ MB.d3L := hfi ▸ MB.fdOf_mem_d3L hi
  have hfm := MB.d3L_mem _ hfL
  have h3 := MB.d3L_order _ hfL
  have hδi := actsQ1_inv hδ hfm h3
  have hq₀ : B.ActsQ1 (δ * (R.c * δ⁻¹)) (MB.g0Q (R.j, i)) := by
    have := hδ.mul (R.cQ_acts.mul hδi (MB.compQ1_mem hfm)) (MB.compQ1_mem (MB.cQ_mem R.j R.hj))
    rw [MB.g0Q, show MB.fdOf (R.j, i) = f from hfi]
    exact this
  have hN := hq₀.mem_normalizer (MB.g0Q_mem _ hi)
  obtain ⟨P, hP, hRP, -, q, hqP, hq⟩ := exists_actsAs R.isPGroup_R2 R.R2_le_normalizer_Q1 hN
    (conj_R2_actsAs R hi rfl hq₀) ⟨_, R.ι_mem_R2 MB.w₂, sq_actsAs_R2 R hi rfl hq₀⟩
    (not_actsAs_R2 R hi hq₀)
  have hqa : B.ActsQ1 q (MB.g0Q (R.j, i)) := fun x hx => by
    rw [← hq₀ x hx]
    exact hq _ ⟨x, hx, rfl⟩
  exact ⟨⟨R, (R.j, i), hi, rfl, q, P, hP, hRP, hqP, hqa⟩⟩

end BData

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
