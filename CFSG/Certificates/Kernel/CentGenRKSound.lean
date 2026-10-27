module

public import Certificates.Data.Kernel.CentGenRK
public import CFSG.Certificates.Kernel.CentGenKSound

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch

variable {n w : Nat}

theorem cgRK_spec {A B : Nat} {a b : Equiv.Perm (Fin n)} (hA : PRep n w A a) (hB : PRep n w B b)
    {D : CGRK} (h : cgRK n w A B D = true) :
    ∃ e f s₁ s₂ : Equiv.Perm (Fin n),
      Subgroup.closure {s₁, s₂} = Subgroup.closure {a, b} ∧
      e ∈ Subgroup.closure {a, b} ∧ f ∈ Subgroup.closure {a, b} ∧
      e ^ D.p = 1 ∧ f ^ D.p = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < D.p, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  unfold cgRK at h
  simp only [sB, bA, Bool.and_eq_true] at h
  obtain ⟨hsz, hA0, hB0, h⟩ := h
  have psA : PS n w A a := ⟨hA, Nat.eq_of_beq_eq_true hA0⟩
  have psB : PS n w B b := ⟨hB, Nat.eq_of_beq_eq_true hB0⟩
  have hlen : ∀ (x y c : Nat), (initR x y c (pidn n w)).length = Nat.add c 2 := by
    intro x y c
    simp [initR, repR_eq]
  obtain ⟨R1, -, hR1, hfin⟩ := runK_sim hsz _ D.hints _ D.prog1 _ (initA a b) (hlen A B D.nx1)
    (ps_init hsz psA psB) h
  unfold finRK at hfin
  simp only [sB, bA, bN, Bool.and_eq_true] at hfin
  obtain ⟨he, hf, hef, he1, hne, hc1, hc2, h2⟩ := hfin
  set S1 := runA (initA a b) D.prog1 D.is1 with hS1
  set S2 := runA (initA a b) D.prog1 D.is2 with hS2
  set E := runA (initA a b) D.prog1 D.ie with hE
  set F := runA (initA a b) D.prog1 D.jf with hF
  have p1 := hR1 D.is1
  have p2 := hR1 D.is2
  have pe := hR1 D.ie
  have pf := hR1 D.jf
  rw [ps_beq hsz (ps_pow hsz pe D.p) (ps_one hsz), decide_eq_true_iff] at he
  rw [ps_beq hsz (ps_pow hsz pf D.p) (ps_one hsz), decide_eq_true_iff] at hf
  rw [ps_beq hsz (ps_mul hsz pe pf) (ps_mul hsz pf pe), decide_eq_true_iff] at hef
  rw [ps_beq hsz pe (ps_one hsz), Bool.not_eq_true', decide_eq_false_iff_not] at he1
  rw [ps_beq hsz (ps_mul hsz p1 pe) (ps_mul hsz pe p1), decide_eq_true_iff] at hc1
  rw [ps_beq hsz (ps_mul hsz p2 pf) (ps_mul hsz pf p2), decide_eq_true_iff] at hc2
  have hgen : ∀ r, initA a b r ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) :=
    initA_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hmem := runA_mem _ D.prog1 hgen
  obtain ⟨R2, -, hR2, hfin2⟩ := runK_sim hsz _ D.hints _ D.prog2 _ (initA S1 S2)
    (hlen _ _ D.nx2) (ps_init hsz p1 p2) h2
  simp only [bA, Bool.and_eq_true] at hfin2
  obtain ⟨hra, hrb⟩ := hfin2
  have hgen2 : ∀ r, initA S1 S2 r ∈ Subgroup.closure ({S1, S2} : Set (Equiv.Perm (Fin n))) :=
    initA_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have ea : runA (initA S1 S2) D.prog2 D.ra = a :=
    MOC.prep_unique (Nat.eq_of_beq_eq_true hra ▸ (hR2 D.ra).1) hA
  have eb : runA (initA S1 S2) D.prog2 D.rb = b :=
    MOC.prep_unique (Nat.eq_of_beq_eq_true hrb ▸ (hR2 D.rb).1) hB
  refine ⟨E, F, S1, S2, le_antisymm ?_ ?_, hmem D.ie, hmem D.jf, he, hf, hef, he1,
    fun k hk => ?_, hc1, hc2⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hmem D.is1, hmem D.is2]
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ea ▸ runA_mem _ D.prog2 hgen2 D.ra
    · exact eb ▸ runA_mem _ D.prog2 hgen2 D.rb
  · simpa using neAll_sound hsz pf pe D.p _ 1 (ps_one hsz) hne k hk

end CFSG.KC.CentGenK

end
