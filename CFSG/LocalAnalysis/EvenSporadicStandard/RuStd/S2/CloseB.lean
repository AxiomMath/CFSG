module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section CaseBDiag

variable {X : Type} [Group X] [Finite X]

theorem false_of_diag (d : ThreeLocalData X) {A B : Subgroup (X ⧸ CFSG.oddCore X)}
    (hAB1 : A ⊓ B = ⊥) {QA QB : Subgroup X}
    (hQAc : QA ≤ centralizer (CFSG.oddCore X : Set X))
    (hQBc : QB ≤ centralizer (CFSG.oddCore X : Set X))
    (hcomm : ∀ x ∈ QA, ∀ y ∈ QB, Commute x y)
    (hQAm : QA.map (proj X) = A) (hQBm : QB.map (proj X) = B)
    (hQA9 : 9 ∣ Nat.card QA) (hQB9 : 9 ∣ Nat.card QB)
    {a b : X ⧸ CFSG.oddCore X} (ha : a ∈ A) (hb : b ∈ B) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1)
    (hab : (QuotientGroup.mk d.f : X ⧸ CFSG.oddCore X) = a * b) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hao : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  obtain ⟨qa, hqa, hqa'⟩ : ∃ q ∈ QA, proj X q = a := by
    have : a ∈ QA.map (proj X) := by rw [hQAm]; exact ha
    exact Subgroup.mem_map.1 this
  obtain ⟨qb, hqb, hqb'⟩ : ∃ q ∈ QB, proj X q = b := by
    have : b ∈ QB.map (proj X) := by rw [hQBm]; exact hb
    exact Subgroup.mem_map.1 this
  obtain ⟨k, hk5, hk⟩ := exists_pPow_lift (proj X) 5 qa a hqa' ha5
  obtain ⟨l, hl5, hl⟩ := exists_pPow_lift (proj X) 5 qb b hqb' hb5
  set xa : X := qa ^ k with hxa
  set xb : X := qb ^ l with hxb
  have hxaQ : xa ∈ QA := pow_mem hqa k
  have hxbQ : xb ∈ QB := pow_mem hqb l
  have hxab : Commute xa xb := hcomm xa hxaQ xb hxbQ
  set o : X := (xa * xb)⁻¹ * d.f with ho
  have hoO : o ∈ CFSG.oddCore X := by
    have : proj X o = 1 := by
      rw [ho, map_mul, map_inv, map_mul, hk, hl]
      change (a * b)⁻¹ * (QuotientGroup.mk d.f : X ⧸ CFSG.oddCore X) = 1
      rw [hab]; group
    exact (QuotientGroup.eq_one_iff _).1 this
  have hfo : d.f = xa * xb * o := by rw [ho]; group
  have hxao : Commute xa o := ((mem_centralizer_iff.1 (hQAc hxaQ)) o hoO).symm
  have hxbo : Commute xb o := ((mem_centralizer_iff.1 (hQBc hxbQ)) o hoO).symm
  have hxaf : xa ∈ centralizer ({d.f} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hfo]
    exact (((Commute.refl xa).mul_right hxab).mul_right hxao).eq
  have hxbf : xb ∈ centralizer ({d.f} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hfo]
    exact (((hxab.symm).mul_right (Commute.refl xb)).mul_right hxbo).eq
  have hnorm : zpowers xa ≤ normalizer (zpowers xb : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hxab.symm.zpow_left m).eq)
  have hP5 : IsPGroup 5 ↥(zpowers xa ⊔ zpowers xb) :=
    IsPGroup.to_sup_of_normal_right' hk5 hl5 hnorm
  have hPC : zpowers xa ⊔ zpowers xb ≤ centralizer ({d.f} : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hxaf) (Subgroup.zpowers_le.2 hxbf)
  obtain ⟨F, hPF, hFC, hF25⟩ := exists_sylow_five_ge d hP5 hPC
  have hxaF : xa ∈ F := hPF (Subgroup.mem_sup_left (Subgroup.mem_zpowers xa))
  have hxbF : xb ∈ F := hPF (Subgroup.mem_sup_right (Subgroup.mem_zpowers xb))
  have hcount := d.count F hFC hF25
  let g : Fin 5 → X := fun i => if (i : ℕ) < 4 then xa ^ ((i : ℕ) + 1) else xb
  have hpa : ∀ m : ℕ, proj X (xa ^ m) = a ^ m := fun m => by rw [map_pow, hk]
  have hbne : ∀ m : ℕ, b ≠ a ^ m := by
    intro m hm
    have hbA : b ∈ A := by rw [hm]; exact A.pow_mem ha m
    have : b ∈ A ⊓ B := ⟨hbA, hb⟩
    rw [hAB1, Subgroup.mem_bot] at this
    exact hb1 this
  have hgmem : ∀ i, g i ∈ F ∧ g i ≠ 1 ∧ 9 ∣ Nat.card ↥(centralizer ({g i} : Set X)) := by
    intro i
    by_cases hi : (i : ℕ) < 4
    · have hgi : g i = xa ^ ((i : ℕ) + 1) := by simp [g, hi]
      rw [hgi]
      refine ⟨pow_mem hxaF _, ?_, ?_⟩
      · intro h1
        have := hpa ((i : ℕ) + 1)
        rw [h1, map_one] at this
        have h2 : orderOf a ∣ (i : ℕ) + 1 := orderOf_dvd_of_pow_eq_one this.symm
        rw [hao] at h2
        have := Nat.le_of_dvd (by omega) h2
        omega
      · have hle : QB ≤ centralizer ({xa ^ ((i : ℕ) + 1)} : Set X) := fun y hy => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact ((hcomm xa hxaQ y hy).pow_left _).symm.eq
        exact hQB9.trans (Subgroup.card_dvd_of_le hle)
    · have hgi : g i = xb := by simp [g, hi]
      rw [hgi]
      refine ⟨hxbF, ?_, ?_⟩
      · intro h1
        have : proj X xb = b := hl
        rw [h1, map_one] at this
        exact hb1 this.symm
      · have hle : QA ≤ centralizer ({xb} : Set X) := fun y hy => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hcomm y hy xb hxbQ).eq
        exact hQA9.trans (Subgroup.card_dvd_of_le hle)
  have hginj : Function.Injective (fun i : Fin 5 => proj X (g i)) := by
    intro i j hij
    simp only at hij
    have hi5 := i.2
    have hj5 := j.2
    by_cases hi : (i : ℕ) < 4 <;> by_cases hj : (j : ℕ) < 4
    · have hgi : g i = xa ^ ((i : ℕ) + 1) := by simp [g, hi]
      have hgj : g j = xa ^ ((j : ℕ) + 1) := by simp [g, hj]
      rw [hgi, hgj, hpa, hpa] at hij
      have h1 := pow_eq_pow_iff_modEq.1 hij
      rw [hao] at h1
      unfold Nat.ModEq at h1
      apply Fin.ext
      omega
    · have hgi : g i = xa ^ ((i : ℕ) + 1) := by simp [g, hi]
      have hgj : g j = xb := by simp [g, hj]
      rw [hgi, hgj, hpa, hl] at hij
      exact absurd hij.symm (hbne _)
    · have hgi : g i = xb := by simp [g, hi]
      have hgj : g j = xa ^ ((j : ℕ) + 1) := by simp [g, hj]
      rw [hgi, hgj, hpa, hl] at hij
      exact absurd hij (hbne _)
    · apply Fin.ext
      omega
  let G5 : Fin 5 → {x : X // x ∈ F ∧ x ≠ 1 ∧ 9 ∣ Nat.card ↥(centralizer ({x} : Set X))} :=
    fun i => ⟨g i, hgmem i⟩
  have hG5 : Function.Injective G5 := fun i j hij =>
    hginj (by simpa [G5] using congrArg (fun z => proj X z.1) hij)
  have := Nat.card_le_card_of_injective G5 hG5
  rw [Nat.card_fin] at this
  omega

end CaseBDiag

section CaseB

variable {X : Type} [Group X] [Finite X]

theorem false_of_case_b (d : ThreeLocalData X) (kd : KernelData d)
    {N A B : Subgroup (X ⧸ CFSG.oddCore X)} (hP : ProdSplit N A B)
    (hNK : N ≤ kd.Kt) (hf : (QuotientGroup.mk d.f : X ⧸ CFSG.oddCore X) ∈ N) : False := by
  have hπs := proj_surjective X
  set N1 : Subgroup X := N.comap (proj X) with hN1
  have hN1K : N1 ≤ kd.K := kd.comap_le hNK
  have hAS := hP.isA.nonabSimple
  have hBS := hP.isB.nonabSimple
  have core : ∀ C : Subgroup (X ⧸ CFSG.oddCore X), C ≤ N →
      (∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) → ⁅C, C⁆ = C →
      ∃ Q : Subgroup X, (∀ q ∈ Q, proj X q ∈ C) ∧ (∀ w ∈ N1, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧
        Q.map (proj X) = C ∧ ⁅Q, Q⁆ = Q ∧ Q ≤ centralizer (CFSG.oddCore X : Set X) := by
    intro C hCN hCn hCp
    have hπC : (C.comap (proj X)).map (proj X) = C :=
      Subgroup.map_comap_eq_self_of_surjective hπs C
    obtain ⟨Q, hQL, hQW, hQC, hQp⟩ := exists_perfect_core (W := N1) (L := C.comap (proj X))
      (proj X) (fun w hw l hl => by
        rw [Subgroup.mem_comap] at hl hw ⊢
        rw [map_mul, map_mul, map_inv]
        exact hCn _ hw _ hl) (by rw [hπC]; exact hCp)
    have hQK : Q ≤ kd.K := fun q hq => hN1K (hCN (hQL hq))
    refine ⟨Q, fun q hq => hQL hq, hQW, by rw [hQC, hπC], hQp, ?_⟩
    have h1 : ⁅Q, Q⁆ ≤ ⁅kd.K, kd.K⁆ := Subgroup.commutator_mono hQK hQK
    rw [hQp] at h1
    exact h1.trans kd.comm_le
  obtain ⟨QA, hQAA, hQAW, hQAm, hQAp, hQAc⟩ := core A hP.le_A hP.conj_A hAS.perfect
  obtain ⟨QB, hQBB, hQBW, hQBm, hQBp, hQBc⟩ := core B hP.le_B hP.conj_B hBS.perfect
  have hQAN : ∀ q ∈ QA, q ∈ N1 := fun q hq => hP.le_A (hQAA q hq)
  have hQBN : ∀ q ∈ QB, q ∈ N1 := fun q hq => hP.le_B (hQBB q hq)
  have h9 : ∀ (C Q : Subgroup _), Nat.card C = 360 → Q.map (proj X) = C → 9 ∣ Nat.card Q := by
    intro C Q hC hQ
    have h1 : Nat.card C ∣ Nat.card Q := by
      have := Subgroup.card_map_dvd (H := Q) (proj X)
      rwa [hQ] at this
    rw [hC] at h1
    exact (by norm_num : 9 ∣ 360).trans h1
  have hQA9 := h9 A QA hP.isA.card hQAm
  have hQB9 := h9 B QB hP.isB.card hQBm
  have cen : ∀ (Q : Subgroup X) (C D : Subgroup (X ⧸ CFSG.oddCore X)) (x : X),
      ⁅Q, Q⁆ = Q → Q ≤ centralizer (CFSG.oddCore X : Set X) →
      (∀ w ∈ N1, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) → (∀ q ∈ Q, proj X q ∈ D) → x ∈ N1 →
      proj X x ∈ C → (∀ c ∈ C, ∀ y ∈ D, c * y = y * c) → ∀ q ∈ Q, Commute x q := by
    intro Q C D x hQp hQc hQW hQD hx hxC hCD
    apply commute_of_perfect_of_central hQp (O := CFSG.oddCore X)
    · intro z _ hzO q hq
      exact (Subgroup.mem_centralizer_iff.1 (hQc hq) z hzO)
    · intro q hq
      exact hQW x hx q hq
    · intro q hq
      have e : proj X ⁅x, q⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hCD _ hxC _ (hQD q hq)
      exact (QuotientGroup.eq_one_iff _).1 e
  have hcomm : ∀ x ∈ QA, ∀ y ∈ QB, Commute x y := fun x hx =>
    cen QB A B x hQBp hQBc hQBW hQBB (hQAN x hx) (hQAA x hx) hP.comm
  have hfN1 : d.f ∈ N1 := hf
  obtain ⟨a, ha, b, hb, hab⟩ := hP.prod _ hf
  have hf5 : d.f ^ 5 = 1 := by
    have := pow_orderOf_eq_one d.f
    rwa [d.f_ord] at this
  by_cases hb1 : b = 1
  · have hfA : proj X d.f ∈ A := by
      have : proj X d.f = a * b := hab
      rw [this, hb1, mul_one]; exact ha
    have hc := cen QB A B d.f hQBp hQBc hQBW hQBB hfN1 hfA hP.comm
    have hQf : QB ≤ centralizer ({d.f} : Set X) := fun q hq => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc q hq).eq.symm
    exact d.f_nine (hQB9.trans (Subgroup.card_dvd_of_le hQf))
  by_cases ha1 : a = 1
  · have hfB : proj X d.f ∈ B := by
      have : proj X d.f = a * b := hab
      rw [this, ha1, one_mul]; exact hb
    have hc := cen QA B A d.f hQAp hQAc hQAW hQAA hfN1 hfB
      (fun c hc y hy => (hP.comm y hy c hc).symm)
    have hQf : QA ≤ centralizer ({d.f} : Set X) := fun q hq => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc q hq).eq.symm
    exact d.f_nine (hQA9.trans (Subgroup.card_dvd_of_le hQf))
  have h5 : (a * b) ^ 5 = 1 := by
    rw [← hab]
    show proj X d.f ^ 5 = 1
    rw [← map_pow, hf5, map_one]
  obtain ⟨ha5, hb5⟩ := hP.inf_pow_eq_one ha hb h5
  exact false_of_diag d hP.inf_eq_bot hQAc hQBc hcomm hQAm hQBm hQA9 hQB9 ha hb ha1 hb1 ha5 hb5 hab

end CaseB

end CFSG.EvenSporadicStandard.RuStd.S2.Close
