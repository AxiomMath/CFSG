module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelInv
public import Certificates.Certificate442306

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaInv Certificates.OmegaT11

local notation "P45" => Equiv.Perm (Fin 45)

theorem t11_mem_P_of_pow3 {a : P45}
    (ha : a ∈ QA45.originalSubgroup) (h3 : a ^ 3 = 1) : a ∈ QP45.originalSubgroup := by
  have hidx : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).index = 2 :=
    relIndex_QP45_QA45
  have h2 := Subgroup.sq_mem_of_index_two hidx (⟨a, ha⟩ : ↥QA45.originalSubgroup)
  have h2' : a ^ 2 ∈ QP45.originalSubgroup := by
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have e : (a ^ 2) ^ 2 = a := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  rw [← e]
  exact Subgroup.pow_mem _ h2' 2

section Cert

theorem t11_check_parts :
    k1Chk (elemsT QA45) (elemsT QP45) (centL (elemsT QA45) (r3 ()))
        (cubeL (centL (elemsT QA45) (r3 ()))) (r3 ()) (zeta0 ()) = true ∧
      k2Chk (elemsT QP45) (cubeL (centL (elemsT QA45) (r3 ()))) (r3 ()) (zeta0 ()) (lam0 ())
        (g1 ()) (g2 ()) = true ∧
      k3Chk (elemsT QA45) (elemsT QP45) (centL (elemsT QA45) (r3 ()))
        (cubeL (centL (elemsT QA45) (r3 ()))) (zeta0 ()) = true ∧
      k4Chk (elemsT QA45) (cubeL (centL (elemsT QA45) (r3 ()))) (zeta0 ()) = true := by
  have h := Certificates.certificate442306
  simp only [Certificates.OmegaT11.check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem t11_mem_centL {a x : P45} :
    x ∈ centL (elemsT QA45) a ↔ x ∈ QA45.originalSubgroup ∧ x * a = a * x := by
  simp only [centL, List.mem_filter, decide_eq_true_eq, mem_elemsT QA45 QA45_ok]

theorem t11_mem_cubeL {C : List P45} {x : P45} : x ∈ cubeL C ↔ x ∈ C ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  simp only [cubeL, List.mem_filter, decide_eq_true_eq]

theorem t11_k1 : zeta0 () ∈ QP45.originalSubgroup ∧ (zeta0 () * zeta0 () = 1 ∧ zeta0 () ≠ 1) ∧
    centCount (zeta0 ()) = 1152 ∧ zeta0 () * r3 () = r3 () * zeta0 () ∧
    (∀ g : P45, g ∈ QA45.originalSubgroup → g * r3 () = r3 () * g → g ^ 3 = 1 → g ≠ 1 →
      g * zeta0 () = zeta0 () * g) ∧
    (∀ g : P45, g ∈ QA45.originalSubgroup → g * r3 () = r3 () * g → g ^ 96 = 1) := by
  have h := t11_check_parts.1
  simp only [k1Chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨(mem_elemsT QP45 QP45_ok _).1 h1, h2, h3, h4, ?_, ?_⟩
  · intro g hg hgr hg3 hg1
    exact h5 g (t11_mem_cubeL.2 ⟨t11_mem_centL.2 ⟨hg, hgr⟩, hg3, hg1⟩)
  · intro g hg hgr
    exact h6 g (t11_mem_centL.2 ⟨hg, hgr⟩)

theorem t11_zeta0_mem_P : zeta0 () ∈ QP45.originalSubgroup :=
  t11_k1.1

theorem t11_invCent_zeta0 : InvCent 1152 (zeta0 ()) :=
  ⟨QP45_le_QA45 t11_k1.1, t11_k1.2.1.1, t11_k1.2.1.2, t11_k1.2.2.1⟩

theorem t11_zeta0_comm_r3 : zeta0 () * r3 () = r3 () * zeta0 () :=
  t11_k1.2.2.2.1

theorem t11_comm_zeta0 {g : P45} (hg : g ∈ QA45.originalSubgroup) (hgr : g * r3 () = r3 () * g)
    (hg3 : g ^ 3 = 1) : g * zeta0 () = zeta0 () * g := by
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  · exact t11_k1.2.2.2.2.1 g hg hgr hg3 hg1

theorem t11_pow96 {g : P45} (hg : g ∈ QA45.originalSubgroup) (hgr : g * r3 () = r3 () * g) :
    g ^ 96 = 1 :=
  t11_k1.2.2.2.2.2 g hg hgr

theorem t11_pow3_of_odd {g : P45} (hg : g ∈ QA45.originalSubgroup)
    (hgr : g * r3 () = r3 () * g) (hodd : Odd (orderOf g)) : g ^ 3 = 1 := by
  have hd : orderOf g ∣ 96 := orderOf_dvd_of_pow_eq_one (t11_pow96 hg hgr)
  have key : ∀ d ∈ Nat.divisors 96, Odd d → d ∣ 3 := by decide
  exact orderOf_dvd_iff_pow_eq_one.1 (key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hodd)

theorem t11_eq_zeta0 {x : P45} (hxP : x ∈ QP45.originalSubgroup) (hx : InvCent 1152 x)
    (hxr : x * r3 () = r3 () * x)
    (hcube : ∀ g ∈ QA45.originalSubgroup, g * r3 () = r3 () * g → g ^ 3 = 1 → g * x = x * g) :
    x = zeta0 () := by
  have h := t11_check_parts.2.2.1
  simp only [k3Chk, List.all_eq_true] at h
  have h1 := h x (t11_mem_centL.2 ⟨hx.1, hxr⟩)
  have hall : (cubeL (centL (elemsT QA45) (r3 ()))).all (fun g => decide (g * x = x * g)) =
      true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨hgC, hg3, -⟩ := t11_mem_cubeL.1 hg
    obtain ⟨hgA, hgr⟩ := t11_mem_centL.1 hgC
    exact decide_eq_true (hcube g hgA hgr hg3)
  have hxx : decide (x * x = 1 ∧ x ≠ 1) = true := decide_eq_true ⟨hx.2.1, hx.2.2.1⟩
  have hxP' : decide (x ∈ elemsT QP45) = true :=
    decide_eq_true ((mem_elemsT QP45 QP45_ok x).2 hxP)
  have hcnt : decide (cntL (elemsT QA45) x = 1152) = true := decide_eq_true hx.2.2.2
  simp only [hall, hxx, hxP', hcnt, Bool.and_self, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at h1
  exact h1

theorem t11_exists_comm : ∃ l ∈ QP45.originalSubgroup, ∃ b₁ ∈ QP45.originalSubgroup,
    ∃ b₂ ∈ QP45.originalSubgroup, b₁ * r3 () = r3 () * b₁ ∧ b₂ * r3 () = r3 () * b₂ ∧
      b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₁ * b₂ * (b₁ * b₂) = 1 ∧ b₁ * b₂ ≠ 1 ∧
      (r3 ())⁻¹ * l⁻¹ * r3 () * l = b₁ * b₂ * zeta0 () := by
  have h := t11_check_parts.2.1
  simp only [k2Chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hb1⟩, hb2⟩, hc1⟩, hc2⟩, hinv⟩, hcomm⟩ := h
  obtain ⟨hc1C, h13, -⟩ := t11_mem_cubeL.1 hc1
  obtain ⟨hc2C, h23, -⟩ := t11_mem_cubeL.1 hc2
  exact ⟨lam0 (), (mem_elemsT QP45 QP45_ok _).1 hl, g1 (), (mem_elemsT QP45 QP45_ok _).1 hb1,
    g2 (), (mem_elemsT QP45 QP45_ok _).1 hb2, (t11_mem_centL.1 hc1C).2,
    (t11_mem_centL.1 hc2C).2, h13, h23, hinv.1, hinv.2, hcomm⟩

theorem t11_invCent192 {a₁ a₂ : P45} (h₁ : a₁ ∈ QA45.originalSubgroup)
    (h₂ : a₂ ∈ QA45.originalSubgroup) (hc₁ : a₁ * r3 () = r3 () * a₁)
    (hc₂ : a₂ * r3 () = r3 () * a₂) (h₁3 : a₁ ^ 3 = 1) (h₂3 : a₂ ^ 3 = 1)
    (hsq : a₁ * a₂ * (a₁ * a₂) = 1) (hne : a₁ * a₂ ≠ 1) : InvCent 192 (a₁ * a₂ * zeta0 ()) := by
  have hone : ∀ b : P45, b ^ 3 = 1 → b * b = 1 → b = 1 := by
    intro b hb3 hb2
    have e : b ^ 3 = b := by rw [pow_succ, pow_two, hb2, one_mul]
    rw [← e, hb3]
  have ha₁ : a₁ ≠ 1 := by
    intro e
    rw [e, one_mul] at hsq hne
    exact hne (hone a₂ h₂3 hsq)
  have ha₂ : a₂ ≠ 1 := by
    intro e
    rw [e, mul_one] at hsq hne
    exact hne (hone a₁ h₁3 hsq)
  have h := t11_check_parts.2.2.2
  simp only [k4Chk, List.all_eq_true] at h
  have h1 := h a₁ (t11_mem_cubeL.2 ⟨t11_mem_centL.2 ⟨h₁, hc₁⟩, h₁3, ha₁⟩) a₂
    (t11_mem_cubeL.2 ⟨t11_mem_centL.2 ⟨h₂, hc₂⟩, h₂3, ha₂⟩)
  have hxx : decide (a₁ * a₂ * (a₁ * a₂) = 1 ∧ a₁ * a₂ ≠ 1) = true := decide_eq_true ⟨hsq, hne⟩
  simp only [hxx, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  exact ⟨QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem h₁ h₂)
    (QP45_le_QA45 t11_zeta0_mem_P), h2, h3, h4⟩

end Cert

end CFSG.OddStandard.SmallF3.Omega
