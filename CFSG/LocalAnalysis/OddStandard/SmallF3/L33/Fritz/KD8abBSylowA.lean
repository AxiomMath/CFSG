module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBT2Sub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBSylData

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB
open CFSG.ComponentClassification.HSFLit.Sec8
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem sylCheck_spec {φ : List MB} {τ : MB × Bool × Bool} (h : sylCheck φ τ = true) :
    ((∀ g ∈ gensQ1, inZ (applyQ1 φ g * g⁻¹) = true) → innerT τ = true) ∧
    (∀ x ∈ Z2L, inZ (applyQ1 φ x * x⁻¹) = true) ∧
    ((∀ x ∈ Z2L, applyQ1 φ x = x) → ∃ a ∈ AL, compQ1 φ φ = conjQ1 a) ∧
    ((∀ e ∈ E0L, applyQ1 φ e = e) → innerT τ = true) ∧
    (∀ e ∈ E0L, inE0 (applyQ1 φ e) = true) := by
  simp only [sylCheck, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_false] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun hg => ?_, h2, fun hx => ?_, fun he => ?_, h5⟩
  · rcases h1 with ⟨g, hg', hne⟩ | h1
    · exact absurd (hg g hg') (by simpa using hne)
    · exact h1
  · rcases h3 with ⟨x, hx', hne⟩ | h3
    · exact absurd (hx x hx') (by simpa using hne)
    · exact h3
  · rcases h4 with ⟨e, he', hne⟩ | h4
    · exact absurd (he e he') (by simpa using hne)
    · exact h4

theorem mem_H4Zof_spec {p : ℕ × ℕ} (hp : p ∈ goodIdx) {e : (MB × Bool × Bool) × List MB}
    (he : e ∈ H4Zof p) : e.1 ∈ H4T ∧ e.2 = H4elt p e.1.1 e.1.2.1 e.1.2.2 := by
  rw [← H4Z_eq_of p hp, H4Z] at he
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp he
  exact ⟨hτ, rfl⟩

theorem sylCheck_of {p : ℕ × ℕ} (hp : p ∈ goodIdx) {τ : MB × Bool × Bool} (hτ : τ ∈ H4T) :
    sylCheck (H4elt p τ.1 τ.2.1 τ.2.2) τ = true := by
  have h := List.all_eq_true.mp (syl_facts p hp) _ (mem_H4Zof hp hτ)
  exact h

theorem QC_comm {a b : MB} (ha : inQC a = true) (hb : inQC b = true) : a * b = b * a := by
  obtain ⟨α, rfl⟩ := exists_coord ha
  obtain ⟨β, rfl⟩ := exists_coord hb
  rw [← coord_add, ← coord_add, add_comm]

theorem inZ_iff {x : MB} : inZ x = true ↔ x = 1 ∨ x = z := by
  simp [inZ]

theorem inQ1_of_inQC : ∀ x : MB, inQC x = true → inQ1 x = true := by decide +kernel

theorem inQC_of_inE0 : ∀ x : MB, inE0 x = true → inQC x = true := by decide +kernel

theorem E0L_gen : ∀ e ∈ E0L, e = 1 ∨ e = z ∨ e = y ∨ e = z * y ∨ e = k ∨ e = z * k ∨
    e = y * k ∨ e = z * y * k := by decide +kernel

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace T2Data

variable (D : B.T2Data)

theorem inQC_mul {a e : MB} (ha : MB.inQC a = true) (he : MB.inE0 e = true) :
    MB.inQC (a * e) = true :=
  mul_mem (show a ∈ MB.QC from ha) (show e ∈ MB.QC from MB.inQC_of_inE0 e he)

theorem exists_entry {x : X} (hx : x ∈ D.T2) :
    ∃ τ ∈ MB.H4T, B.ActsQ1 x (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) ∧
      ∃ e : MB, MB.inE0 e = true ∧ x = D.lift τ * B.ι e := by
  obtain ⟨τ, hτ, e, he, rfl⟩ := D.exists_lift hx
  refine ⟨τ, hτ, fun y hy => ?_, e, he, rfl⟩
  rw [show D.lift τ * B.ι e * B.ι y * (D.lift τ * B.ι e)⁻¹ =
    D.lift τ * (B.ι e * B.ι y * (B.ι e)⁻¹) * (D.lift τ)⁻¹ by group, ← map_inv, ← map_mul,
    ← map_mul, ← MB.E0_comm_Q1 y hy e ((MB.mem_E0L e).mp he), mul_inv_cancel_right]
  exact D.actsQ1_lift τ y hy

theorem exists_gen {φ : List MB} (hφ : φ ∈ MB.gensT2 D.p) : ∃ g ∈ D.T2, B.ActsQ1 g φ := by
  simp only [MB.gensT2, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hφ
  rcases hφ with ⟨a, -, rfl⟩ | rfl | rfl
  · exact ⟨B.ι a, D.ι_mem_T2 a, actsQ1_ι a⟩
  · refine ⟨D.R.cp true, D.R2_le_T2 (D.R.cp_mem_R2 true), ?_⟩
    have := D.R.actsQ1_cp true
    rwa [D.hj] at this
  · exact ⟨D.qp true, D.qp_mem_T2 true, D.actsQ1_qp true⟩

theorem conj_z_T2 {x : X} (hx : x ∈ D.T2) : x * S.z * x⁻¹ = S.z := by
  have hgz := MB.gensT2_z D.p D.hp
  have hzQ : MB.inQ1 MB.z = true := by decide +kernel
  obtain ⟨s, a, b, rfl⟩ := D.exists_nf hx
  have hc : D.R.cp a * S.z * (D.R.cp a)⁻¹ = S.z := by
    cases a
    · simp [R2Data.cp]
    · have h1 := D.R.actsQ1_cp true MB.z hzQ
      have h2 := hgz (MB.cQ D.p.1) (by simp [MB.gensT2])
      simp only [ite_true] at h1
      rw [D.hj, h2, B.ι_z] at h1
      exact h1
  have hq : D.qp b * S.z * (D.qp b)⁻¹ = S.z := by
    cases b
    · simp [qp]
    · have h1 := D.actsQ1_qp true MB.z hzQ
      have h2 := hgz (MB.g0Q D.p) (by simp [MB.gensT2])
      simp only [ite_true] at h1
      rw [h2, B.ι_z] at h1
      exact h1
  have hs : B.ι s * S.z * (B.ι s)⁻¹ = S.z := by
    rw [← B.ι_z, ← map_inv, ← map_mul, ← map_mul, ← (MB.center_mem s).1, mul_inv_cancel_right]
  calc B.ι s * D.R.cp a * D.qp b * S.z * (B.ι s * D.R.cp a * D.qp b)⁻¹ =
      B.ι s * (D.R.cp a * (D.qp b * S.z * (D.qp b)⁻¹) * (D.R.cp a)⁻¹) * (B.ι s)⁻¹ := by group
    _ = S.z := by rw [hq, hc, hs]

theorem conj_z {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) : g * S.z * g⁻¹ = S.z := by
  have hzT : S.z ∈ D.T2 := B.ι_z ▸ D.ι_mem_T2 MB.z
  have hz'T : g * S.z * g⁻¹ ∈ D.T2 := (mem_normalizer_iff.mp hg S.z).mp hzT
  have hcen : ∀ x ∈ D.T2, x * (g * S.z * g⁻¹) * x⁻¹ = g * S.z * g⁻¹ := by
    intro x hx
    have := D.conj_z_T2 (conj_inv_mem_of_mem_normalizer hg hx)
    calc x * (g * S.z * g⁻¹) * x⁻¹ = g * (g⁻¹ * x * g * S.z * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [this]
  have hcQ : g * S.z * g⁻¹ ∈ centralizer (B.Q1 : Set X) := by
    rw [mem_centralizer_iff]
    intro r hr
    have := hcen r (D.S₁_le_T2 (B.Q1_le_S₁ hr))
    calc r * (g * S.z * g⁻¹) = r * (g * S.z * g⁻¹) * r⁻¹ * r := by group
      _ = g * S.z * g⁻¹ * r := by rw [this]
  obtain ⟨e, he, hee⟩ := B.mem_E0_of_mem_centralizer_Q1 D.isPGroup (D.T2_le_P hz'T) hcQ
  have he' := (MB.mem_E0L e).mp he
  have h1 : e ≠ 1 := by
    rintro rfl
    rw [map_one] at hee
    exact z_ne_one S (by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [← hee]; group)
  by_contra hne
  have h2 : e ≠ MB.z := by
    rintro rfl
    exact hne (by rw [← hee, B.ι_z])
  obtain ⟨φ, hφ, hmove⟩ := MB.gensT2_move D.p D.hp e he' h1 h2
  obtain ⟨x, hx, hxφ⟩ := D.exists_gen hφ
  apply hmove
  apply B.ι_injective
  rw [← hxφ e (MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he)), hee]
  exact hcen x hx

@[expose] def IsZ (x : X) : Prop := x = 1 ∨ x = S.z

theorem isZ_inv {u v : X} (h : IsZ (S := S) (u * v * u⁻¹ * v⁻¹)) :
    IsZ (S := S) (v * u * v⁻¹ * u⁻¹) := by
  have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rcases h with h | h <;> rw [e, h]
  · left; exact inv_one
  · right; exact inv_eq_of_mul_eq_one_right (zz S)

theorem comm_Z2 {x : MB} (hx : x ∈ MB.Z2L) {y : X} (hy : y ∈ D.T2) :
    IsZ (S := S) (y * B.ι x * y⁻¹ * (B.ι x)⁻¹) := by
  obtain ⟨τ, hτ, hact, -⟩ := D.exists_entry hy
  have h := (MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)).2.1 x hx
  rw [MB.inZ_iff] at h
  rw [hact x (MB.inQ1_of_inQC x (MB.Z2L_inQC x hx)), ← map_inv, ← map_mul]
  rcases h with h | h
  · left; rw [h, map_one]
  · right; rw [h, B.ι_z]

theorem conj_Z2 {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) {x : MB} (hx : x ∈ MB.Z2L) :
    ∃ x' ∈ MB.Z2L, g * B.ι x * g⁻¹ = B.ι x' := by
  have hx''T : g * B.ι x * g⁻¹ ∈ D.T2 := (mem_normalizer_iff.mp hg _).mp (D.ι_mem_T2 x)
  have hz := D.conj_z hg
  have hcomm : ∀ y ∈ D.T2, IsZ (S := S) ((g * B.ι x * g⁻¹) * y * (g * B.ι x * g⁻¹)⁻¹ * y⁻¹) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ D.T2 := conj_inv_mem_of_mem_normalizer hg hy
    have e1 : (g * B.ι x * g⁻¹) * y * (g * B.ι x * g⁻¹)⁻¹ * y⁻¹ =
        g * (B.ι x * (g⁻¹ * y * g) * (B.ι x)⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rcases isZ_inv (D.comm_Z2 hx hy') with h | h <;> rw [e1, h]
    · left; group
    · right; exact hz
  obtain ⟨τ, hτ, hact, e, he, hxe⟩ := D.exists_entry hx''T
  have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)
  have hinner : MB.innerT τ = true := by
    refine hspec.1 fun a ha => ?_
    have haQ := MB.gensQ1_mem a ha
    rw [MB.inZ_iff]
    have hc := hcomm (B.ι a) (D.ι_mem_T2 a)
    rw [hact a haQ, ← map_inv, ← map_mul] at hc
    rcases hc with h | h
    · exact Or.inl (B.ι_injective (by rw [h, map_one]))
    · exact Or.inr (B.ι_injective (by rw [h, B.ι_z]))
  obtain ⟨s, a, b⟩ := τ
  simp only [MB.innerT, Bool.and_eq_true, Bool.not_eq_true'] at hinner
  obtain ⟨⟨rfl, rfl⟩, hsQ⟩ := hinner
  have hx' : g * B.ι x * g⁻¹ = B.ι (s * e) := by
    rw [hxe, lift, map_mul]
    simp [R2Data.cp, qp]
  refine ⟨s * e, ?_, hx'⟩
  have hseQ : MB.inQ1 (s * e) = true :=
    mul_mem (show s ∈ MB.Q1h from hsQ)
      (show e ∈ MB.Q1h from MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he))
  refine MB.Z2_of_gens D.p D.hp _ hseQ fun φ hφ => ?_
  obtain ⟨y, hy, hyφ⟩ := D.exists_gen hφ
  have hc := isZ_inv (hcomm y hy)
  rw [hx', hyφ _ hseQ, ← map_inv, ← map_mul] at hc
  rw [MB.inZ_iff]
  rcases hc with h | h
  · exact Or.inl (B.ι_injective (by rw [h, map_one]))
  · exact Or.inr (B.ι_injective (by rw [h, B.ι_z]))

theorem sq_of_W {w : X} (hw : w ∈ D.T2) (hc : ∀ x ∈ MB.Z2L, w * B.ι x * w⁻¹ = B.ι x) :
    ∃ a : MB, MB.inQC a = true ∧ w * w = B.ι a := by
  obtain ⟨τ, hτ, hact, -⟩ := D.exists_entry hw
  have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)
  have hfix : ∀ x ∈ MB.Z2L, MB.applyQ1 (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) x = x := by
    intro x hx
    apply B.ι_injective
    rw [← hact x (MB.inQ1_of_inQC x (MB.Z2L_inQC x hx))]
    exact hc x hx
  obtain ⟨a, haL, ha⟩ := hspec.2.2.1 hfix
  have h2 := hact.mul hact (D.H4elt_mem _ _ _)
  rw [ha] at h2
  obtain ⟨e, he, hwe⟩ := D.exists_E0_of_actsAs (mul_mem (D.T2_le_P hw) (D.T2_le_P hw))
    (D.T2_le_P (D.ι_mem_T2 a)) h2.actsAs
  exact ⟨a * e, inQC_mul (MB.AL_inQC a haL) he, by rw [hwe, map_mul]⟩

theorem conj_E0 {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) {e : MB}
    (he : MB.inE0 e = true) : ∃ e' : MB, MB.inE0 e' = true ∧ g * B.ι e * g⁻¹ = B.ι e' := by
  have hgi : g⁻¹ ∈ normalizer (D.T2 : Set X) := inv_mem hg
  obtain ⟨a, haL, rfl⟩ := MB.sq_AL e ((MB.mem_E0L e).mp he)
  have haQ := MB.AL_inQC a haL
  have hwT : g * B.ι a * g⁻¹ ∈ D.T2 := (mem_normalizer_iff.mp hg _).mp (D.ι_mem_T2 a)
  have hwc : ∀ x ∈ MB.Z2L, g * B.ι a * g⁻¹ * B.ι x * (g * B.ι a * g⁻¹)⁻¹ = B.ι x := by
    intro x hx
    obtain ⟨x', hx', hxe⟩ := D.conj_Z2 hgi hx
    have hxe' : g⁻¹ * B.ι x * g = B.ι x' := by simpa only [inv_inv] using hxe
    have hcomm : B.ι a * B.ι x' = B.ι x' * B.ι a := by
      rw [← map_mul, ← map_mul, MB.QC_comm haQ (MB.Z2L_inQC x' hx')]
    calc g * B.ι a * g⁻¹ * B.ι x * (g * B.ι a * g⁻¹)⁻¹ =
        g * (B.ι a * (g⁻¹ * B.ι x * g) * (B.ι a)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * B.ι x * g) * g⁻¹ := by rw [hxe', hcomm, mul_inv_cancel_right]
      _ = B.ι x := by group
  obtain ⟨a', ha'Q, ha'⟩ := D.sq_of_W hwT hwc
  have hww : g * B.ι a * g⁻¹ * (g * B.ι a * g⁻¹) = g * B.ι (a * a) * g⁻¹ := by
    rw [map_mul]; group
  refine ⟨a', MB.inE0_of_sq a' ha'Q ?_, by rw [← hww, ha']⟩
  apply B.ι_injective
  rw [map_mul, ← ha', hww, map_one,
    show g * B.ι (a * a) * g⁻¹ * (g * B.ι (a * a) * g⁻¹) = g * B.ι (a * a * (a * a)) * g⁻¹ by
      rw [map_mul (B.ι) (a * a) (a * a)]; group,
    MB.E0L_sq _ ((MB.mem_E0L _).mp he), map_one]
  group

theorem conj_Q1 {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) {x : MB}
    (hx : MB.inQ1 x = true) : ∃ x' : MB, MB.inQ1 x' = true ∧ g * B.ι x * g⁻¹ = B.ι x' := by
  have hgi : g⁻¹ ∈ normalizer (D.T2 : Set X) := inv_mem hg
  have hx''T : g * B.ι x * g⁻¹ ∈ D.T2 := (mem_normalizer_iff.mp hg _).mp (D.ι_mem_T2 x)
  obtain ⟨τ, hτ, hact, e, he, hxe⟩ := D.exists_entry hx''T
  have hspec := MB.sylCheck_spec (MB.sylCheck_of D.hp hτ)
  have hfix : ∀ e' ∈ MB.E0L, MB.applyQ1 (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) e' = e' := by
    intro e' he'
    have he'E := (MB.mem_E0L e').mpr he'
    obtain ⟨e'', he'', hee⟩ := D.conj_E0 hgi he'E
    have hee' : g⁻¹ * B.ι e' * g = B.ι e'' := by simpa only [inv_inv] using hee
    apply B.ι_injective
    rw [← hact e' (MB.inQ1_of_inQC e' (MB.inQC_of_inE0 e' he'E))]
    have hc : B.ι x * B.ι e'' = B.ι e'' * B.ι x := by
      rw [← map_mul, ← map_mul, MB.E0_comm_Q1 x hx e'' ((MB.mem_E0L e'').mp he'')]
    calc g * B.ι x * g⁻¹ * B.ι e' * (g * B.ι x * g⁻¹)⁻¹ =
        g * (B.ι x * (g⁻¹ * B.ι e' * g) * (B.ι x)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * B.ι e' * g) * g⁻¹ := by rw [hee', hc, mul_inv_cancel_right]
      _ = B.ι e' := by group
  have hinner := hspec.2.2.2.1 hfix
  obtain ⟨s, a, b⟩ := τ
  simp only [MB.innerT, Bool.and_eq_true, Bool.not_eq_true'] at hinner
  obtain ⟨⟨rfl, rfl⟩, hsQ⟩ := hinner
  refine ⟨s * e, mul_mem (show s ∈ MB.Q1h from hsQ)
    (show e ∈ MB.Q1h from MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he)), ?_⟩
  rw [hxe, lift, map_mul]
  simp [R2Data.cp, qp]

theorem conj_A {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) {a : MB} (ha : MB.inQC a = true) :
    ∃ a' : MB, MB.inQC a' = true ∧ g * B.ι a * g⁻¹ = B.ι a' := by
  have hgi : g⁻¹ ∈ normalizer (D.T2 : Set X) := inv_mem hg
  obtain ⟨x', hx'Q, hx'⟩ := D.conj_Q1 hg (MB.inQ1_of_inQC a ha)
  refine ⟨x', MB.inQC_of_comm_Z2 x' hx'Q fun w hw => ?_, hx'⟩
  obtain ⟨w', hw', hwe⟩ := D.conj_Z2 hgi hw
  have hwe' : g⁻¹ * B.ι w * g = B.ι w' := by simpa only [inv_inv] using hwe
  apply B.ι_injective
  rw [map_mul, map_mul, ← hx']
  have hc : B.ι a * B.ι w' = B.ι w' * B.ι a := by
    rw [← map_mul, ← map_mul, MB.QC_comm ha (MB.Z2L_inQC w' hw')]
  calc g * B.ι a * g⁻¹ * B.ι w = g * (B.ι a * (g⁻¹ * B.ι w * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * B.ι w * g) * B.ι a) * g⁻¹ := by rw [hwe', hc]
    _ = B.ι w * (g * B.ι a * g⁻¹) := by group

end T2Data

end BData

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
