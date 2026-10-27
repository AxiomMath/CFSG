module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3L34Odd

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

@[expose] def s3l_tp {Γ : Type*} [Group Γ] (t : Γ) (i : ZMod 2) : Γ := if i = 0 then 1 else t

section Cent

variable {Γ : Type*} [Group Γ] {w t : Γ} {A : Subgroup Γ}

theorem s3l_zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide

theorem s3l_tp_add (ht2 : t * t = 1) (i j : ZMod 2) : s3l_tp t (i + j) = s3l_tp t i * s3l_tp t j := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases s3l_zmod2_cases i with rfl | rfl <;> rcases s3l_zmod2_cases j with rfl | rfl <;>
    simp [s3l_tp, ht2, h11, h10]

theorem s3l_tp_comm (i : ZMod 2) (g : Γ) (h : g * t = t * g) : g * s3l_tp t i = s3l_tp t i * g := by
  unfold s3l_tp
  split_ifs <;> simp [h]

theorem s3l_tp_zero : s3l_tp t 0 = 1 := by simp [s3l_tp]

theorem s3l_tp_one : s3l_tp t 1 = t := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [s3l_tp, h10]

theorem s3l_cent_equiv (hw2 : w * w = 1) [(zpowers w).Normal]
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, a * t = t * a)
    (htn : t ∉ A) (hwn : w ∉ A) (htwn : t * w ∉ A)
    (hcent : ∀ g : Γ, g * t = t * g → ∃ v : Γ, (v = 1 ∨ v = t ∨ v = w ∨ v = t * w) ∧
      ∃ a ∈ A, g = v * a)
    (hnc : ∀ g : Γ, g * t * g⁻¹ ≠ t * w) :
    Nonempty (↥(centralizer ({((t : Γ) : Γ ⧸ zpowers w)} : Set (Γ ⧸ zpowers w))) ≃*
      Multiplicative (ZMod 2) × ↥A) := by
  have hmkw : ((w : Γ) : Γ ⧸ zpowers w) = 1 := (QuotientGroup.eq_one_iff w).2 (mem_zpowers w)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let f : Multiplicative (ZMod 2) × ↥A →* Γ ⧸ zpowers w :=
    MonoidHom.mk' (fun p => (((s3l_tp t p.1.toAdd * (p.2 : Γ) : Γ)) : Γ ⧸ zpowers w)) (by
      intro p q
      rw [← QuotientGroup.mk_mul]
      congr 1
      have h1 : s3l_tp t (p.1 * q.1).toAdd = s3l_tp t p.1.toAdd * s3l_tp t q.1.toAdd := by
        rw [toAdd_mul]; exact s3l_tp_add ht2 _ _
      have h2 := s3l_tp_comm (t := t) q.1.toAdd (p.2 : Γ) (htA _ p.2.2)
      simp only [Prod.fst_mul, Prod.snd_mul, h1, Subgroup.coe_mul]
      calc s3l_tp t p.1.toAdd * s3l_tp t q.1.toAdd * ((p.2 : Γ) * (q.2 : Γ))
          = s3l_tp t p.1.toAdd * (s3l_tp t q.1.toAdd * (p.2 : Γ)) * (q.2 : Γ) := by
            simp only [mul_assoc]
        _ = s3l_tp t p.1.toAdd * ((p.2 : Γ) * s3l_tp t q.1.toAdd) * (q.2 : Γ) := by rw [h2]
        _ = _ := by simp only [mul_assoc])
  have hf_apply : ∀ p, f p = (((s3l_tp t p.1.toAdd * (p.2 : Γ) : Γ)) : Γ ⧸ zpowers w) :=
    fun p => rfl
  have hf_cent : ∀ p, f p ∈ centralizer ({((t : Γ) : Γ ⧸ zpowers w)} : Set (Γ ⧸ zpowers w)) := by
    intro p
    rw [mem_centralizer_singleton_iff, hf_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have h1 : (p.2 : Γ) * t = t * (p.2 : Γ) := htA _ p.2.2
    have h2 := s3l_tp_comm (t := t) p.1.toAdd t rfl
    calc s3l_tp t p.1.toAdd * (p.2 : Γ) * t = s3l_tp t p.1.toAdd * (t * (p.2 : Γ)) := by
          rw [mul_assoc, h1]
      _ = (s3l_tp t p.1.toAdd * t) * (p.2 : Γ) := by rw [mul_assoc]
      _ = (t * s3l_tp t p.1.toAdd) * (p.2 : Γ) := by rw [← h2]
      _ = _ := by rw [mul_assoc]
  let f' : Multiplicative (ZMod 2) × ↥A →*
      ↥(centralizer ({((t : Γ) : Γ ⧸ zpowers w)} : Set (Γ ⧸ zpowers w))) :=
    f.codRestrict _ hf_cent
  refine ⟨(MulEquiv.ofBijective f' ⟨?_, ?_⟩).symm⟩
  ·
    rw [injective_iff_map_eq_one]
    rintro ⟨i, b⟩ h
    have h1 : f (i, b) = 1 := congrArg Subtype.val h
    rw [hf_apply, QuotientGroup.eq_one_iff] at h1
    simp only at h1
    have hi : i.toAdd = 0 ∨ i.toAdd = 1 := s3l_zmod2_cases _
    rcases s3l_mem_zpowers_two hw2 h1 with h2 | h2 <;> rcases hi with hi | hi
    · rw [hi, s3l_tp_zero, one_mul] at h2
      have : i = 1 := by
        apply Multiplicative.toAdd.injective; simpa using hi
      have hb : b = 1 := Subtype.ext h2
      rw [this, hb]
      rfl
    · rw [hi, s3l_tp_one] at h2
      exfalso
      apply htn
      have : (b : Γ) = t⁻¹ := eq_inv_of_mul_eq_one_right h2
      rw [hti] at this
      rw [← this]
      exact b.2
    · rw [hi, s3l_tp_zero, one_mul] at h2
      exact absurd (h2 ▸ b.2) hwn
    · rw [hi, s3l_tp_one] at h2
      exfalso
      apply htwn
      have : (b : Γ) = t * w := by
        calc (b : Γ) = t⁻¹ * (t * b) := by group
          _ = t * w := by rw [h2, hti]
      rw [← this]
      exact b.2
  ·
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hx0 := hx
    rw [mem_centralizer_singleton_iff] at hx
    have hx' : ((g * t : Γ) : Γ ⧸ zpowers w) = ((t * g : Γ) : Γ ⧸ zpowers w) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hx
    rw [QuotientGroup.eq] at hx'
    have hgt : g * t = t * g := by
      rcases s3l_mem_zpowers_two hw2 hx' with h1 | h1
      · exact inv_mul_eq_one.1 h1
      · exfalso
        have h3 : t * g = g * t * w := by
          calc t * g = (g * t) * ((g * t)⁻¹ * (t * g)) := by group
            _ = g * t * w := by rw [h1]
        apply hnc g⁻¹
        rw [inv_inv]
        calc g⁻¹ * t * g = g⁻¹ * (t * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * t * w) := by rw [h3]
          _ = t * w := by group
    obtain ⟨v, hv, a, ha, hg⟩ := hcent g hgt
    have hmk : ∀ i : ZMod 2, f (Multiplicative.ofAdd i, ⟨a, ha⟩) =
        ((s3l_tp t i * a : Γ) : Γ ⧸ zpowers w) := by
      intro i
      rw [hf_apply]
      simp
    have key : ∀ i : ZMod 2, ((s3l_tp t i * a : Γ) : Γ ⧸ zpowers w) = ((g : Γ) : Γ ⧸ zpowers w) →
        ∃ p, f' p = ⟨((g : Γ) : Γ ⧸ zpowers w), hx0⟩ := by
      intro i hi
      exact ⟨(Multiplicative.ofAdd i, ⟨a, ha⟩), Subtype.ext (by
        show f (Multiplicative.ofAdd i, ⟨a, ha⟩) = _
        rw [hmk, hi])⟩
    rcases hv with h | h | h | h <;> rw [h] at hg
    · refine key 0 ?_
      rw [s3l_tp_zero, hg]
    · refine key 1 ?_
      rw [s3l_tp_one, hg]
    · refine key 0 ?_
      rw [s3l_tp_zero, hg, QuotientGroup.mk_mul _ w a, hmkw]
      simp
    · refine key 1 ?_
      rw [s3l_tp_one, hg, QuotientGroup.mk_mul _ (t * w) a, QuotientGroup.mk_mul _ t w, hmkw, mul_one,
        QuotientGroup.mk_mul]

end Cent

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
