module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12ListA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACosetCount

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem baseGrp_le_m12Grp : baseGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
  rw [baseGrp, m12Grp, Subgroup.closure_le]
  rintro x (hx : x ∈ ({x₁, x₂} : Set G))
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem lam_conj_mem_baseGrp {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : lam * a * lam⁻¹ ∈ baseGrp x₁ x₂ := by
  have hll : lam * lam = 1 := by rw [← pow_two, ← h.ord_lam]; exact pow_orderOf_eq_one lam
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hll
  have hconj₂ : lam * x₂ * lam⁻¹ = x₁ := by
    rw [← h.conj_x₁, hlinv]
    calc lam * (lam * x₁ * lam) * lam = (lam * lam) * x₁ * (lam * lam) := by group
      _ = x₁ := by rw [hll, one_mul, mul_one]
  rw [baseGrp] at ha
  change lam * a * lam⁻¹ ∈ closure ({x₁, x₂} : Set G)
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [h.conj_x₁]; exact Subgroup.subset_closure (by simp)
      · rw [hconj₂]; exact Subgroup.subset_closure (by simp)
  | one => simpa using Subgroup.one_mem (closure ({x₁, x₂} : Set G))
  | mul x y _ _ ihx ihy =>
      have hmul : lam * (x * y) * lam⁻¹ = (lam * x * lam⁻¹) * (lam * y * lam⁻¹) := by group
      rw [hmul]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
      have hinv : lam * x⁻¹ * lam⁻¹ = (lam * x * lam⁻¹)⁻¹ := by group
      rw [hinv]
      exact Subgroup.inv_mem _ ihx

private theorem tau_conj_mem_baseGrp (h : Ctx t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : tau * a * tau⁻¹ ∈ baseGrp x₁ x₂ := by
  rw [baseGrp] at ha
  change tau * a * tau⁻¹ ∈ closure ({x₁, x₂} : Set G)
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [h.tau_x₁]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [h.tau_x₂]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  | one => simpa using Subgroup.one_mem (closure ({x₁, x₂} : Set G))
  | mul x y _ _ ihx ihy =>
      have hmul : tau * (x * y) * tau⁻¹ = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
      rw [hmul]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
      have hinv : tau * x⁻¹ * tau⁻¹ = (tau * x * tau⁻¹)⁻¹ := by group
      rw [hinv]
      exact Subgroup.inv_mem _ ihx

theorem lemma4_7d_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_7dConcl t S x₁ x₂ lam tau := by
  intro Y hY hy
  have hMrel : M12Rel x₁ x₂ lam tau := m12Rel_of_ctx h h44
  let M : Subgroup G := m12Grp x₁ x₂ lam tau
  let A : Subgroup G := baseGrp x₁ x₂
  let E8 : Subgroup G := Y ⊓ M
  have hY_eq : Y = zpowers t ⊔ E8 := (E16_facts h h43 h44 hY).1
  have hE8ab : CFSG.Open.IsElemAbelian 2 E8 := (E16_facts h h43 h44 hY).2.1
  have hE8card : Nat.card E8 = 8 := (E16_facts h h43 h44 hY).2.2
  have htY : t ∈ Y := t_mem_of_isE16 h h43 h44 hY
  have hzY : (x₁ * x₂) ^ 2 ∈ Y := z_mem_of_isE16 h h43 h44 hY
  have hMcard : Nat.card M = 64 := hMrel.card_m12Grp
  have hAcard : Nat.card A = 16 := (h.wreath.baseGrp_eq).2.2
  have hAlM : A ≤ M := baseGrp_le_m12Grp
  have hzA : (x₁ * x₂) ^ 2 ∈ A :=
    Subgroup.pow_mem A (Subgroup.mul_mem A
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2
  have hzM : (x₁ * x₂) ^ 2 ∈ M := hAlM hzA
  have hzE8 : (x₁ * x₂) ^ 2 ∈ E8 := ⟨hzY, hzM⟩
  have hE8A_eq : E8 ⊓ A = zpowers ((x₁ * x₂) ^ 2) := by
    apply le_antisymm
    · intro k hk
      obtain ⟨hkE8, hkA⟩ := hk
      have hkF : k ∈ fourGrp x₁ x₂ := by
        rw [(h.wreath.fourGrp_eq_omega).1]
        exact Subgroup.subset_closure ⟨hkA, hE8ab.2 k hkE8⟩
      have hk_cases : k = 1 ∨ k = x₁ ^ 2 ∨ k = (x₁ * x₂) ^ 2 ∨
          k = x₁ ^ 2 * (x₁ * x₂) ^ 2 :=
        mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
          (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
          (z_mul_self_ne_one h.toCtx0).1 hkF
      rcases hk_cases with hk1 | hky | hkz | hkyz
      · rw [hk1]; exact Subgroup.one_mem _
      · exact absurd (by rw [← hky]; exact hkE8.1) hy
      · rw [hkz]; exact Subgroup.mem_zpowers _
      · exfalso
        apply hy
        have hxy : x₁ ^ 2 = k * ((x₁ * x₂) ^ 2)⁻¹ := by rw [hkyz]; group
        rw [hxy]
        exact (E8.mul_mem hkE8 (E8.inv_mem hzE8)).1
    · rw [Subgroup.zpowers_le]
      exact ⟨hzE8, hzA⟩
  have hcardE8A : Nat.card (E8 ⊓ A : Subgroup G) = 2 := by
    rw [hE8A_eq, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact (z_mul_self_ne_one h.toCtx0).1)
      (z_mul_self_ne_one h.toCtx0).2
  have hrelIndex : A.relIndex M = 4 := by
    have hcard := Subgroup.relIndex_mul_card (H := A) (K := M)
    rw [inf_eq_left.mpr hAlM, hAcard, hMcard] at hcard
    omega
  have hcoset_card : Nat.card E8 = Nat.card (E8 ⊓ A : Subgroup G) * A.relIndex M := by
    rw [hE8card, hcardE8A, hrelIndex]
  have hcoset := exists_mem_coset_of_card_eq (H := M) (L := A) (Y := E8)
    hAlM inf_le_right hcoset_card
  have hlamM : lam ∈ M := Subgroup.subset_closure (by simp)
  have htauM : tau ∈ M := Subgroup.subset_closure (by simp)
  obtain ⟨e₁, he₁E8, he₁A⟩ := hcoset lam hlamM
  obtain ⟨e₂, he₂E8, he₂A⟩ := hcoset tau htauM
  let a : G := lam * (lam⁻¹ * e₁) * lam⁻¹
  have haA : a ∈ A := lam_conj_mem_baseGrp h.wreath he₁A
  have halam : a * lam = e₁ := by
    show (lam * (lam⁻¹ * e₁) * lam⁻¹) * lam = e₁
    group
  have halamE8 : a * lam ∈ E8 := by rw [halam]; exact he₁E8
  let b : G := tau * (tau⁻¹ * e₂) * tau⁻¹
  have hbA : b ∈ A := tau_conj_mem_baseGrp h he₂A
  have hbtau : b * tau = e₂ := by
    show (tau * (tau⁻¹ * e₂) * tau⁻¹) * tau = e₂
    group
  have hbtauE8 : b * tau ∈ E8 := by rw [hbtau]; exact he₂E8
  let D : Subgroup G := closure {t, (x₁ * x₂) ^ 2, a * lam, b * tau}
  have htD : t ∈ D := Subgroup.subset_closure (by simp)
  have hzD : (x₁ * x₂) ^ 2 ∈ D := Subgroup.subset_closure (by simp)
  have halD : a * lam ∈ D := Subgroup.subset_closure (by simp)
  have hbtD : b * tau ∈ D := Subgroup.subset_closure (by simp)
  have hzpD : zpowers ((x₁ * x₂) ^ 2) ≤ D := Subgroup.zpowers_le.mpr hzD
  have hDY : D ≤ Y := by
    change closure {t, (x₁ * x₂) ^ 2, a * lam, b * tau} ≤ Y
    rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({t, (x₁ * x₂) ^ 2, a * lam, b * tau} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact htY
    · exact hzY
    · exact halamE8.1
    · exact hbtauE8.1
  have hYD : Y ≤ D := by
    rw [hY_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact htD
    · intro e he
      obtain ⟨w, hwA, hcases⟩ := hMrel.coset_cases e he.2
      rcases hcases with hcase | rfl | rfl | rfl
      ·
        rw [hcase] at he ⊢
        have hwzp : w ∈ zpowers ((x₁ * x₂) ^ 2) := by
          rw [← hE8A_eq]; exact ⟨he, hwA⟩
        exact hzpD hwzp
      ·
        have hkey : w * b⁻¹ ∈ E8 ⊓ A := by
          refine ⟨?_, A.mul_mem hwA (A.inv_mem hbA)⟩
          have hwb : w * b⁻¹ = (w * tau) * (b * tau)⁻¹ := by group
          rw [hwb]
          exact E8.mul_mem he (E8.inv_mem hbtauE8)
        have hkey' : w * b⁻¹ ∈ zpowers ((x₁ * x₂) ^ 2) := by
          rw [← hE8A_eq]; exact hkey
        have hweq : w * tau = (w * b⁻¹) * (b * tau) := by group
        rw [hweq]
        exact D.mul_mem (hzpD hkey') hbtD
      ·
        have hkey : w * a⁻¹ ∈ E8 ⊓ A := by
          refine ⟨?_, A.mul_mem hwA (A.inv_mem haA)⟩
          have hwa : w * a⁻¹ = (w * lam) * (a * lam)⁻¹ := by group
          rw [hwa]
          exact E8.mul_mem he (E8.inv_mem halamE8)
        have hkey' : w * a⁻¹ ∈ zpowers ((x₁ * x₂) ^ 2) := by
          rw [← hE8A_eq]; exact hkey
        have hweq : w * lam = (w * a⁻¹) * (a * lam) := by group
        rw [hweq]
        exact D.mul_mem (hzpD hkey') halD
      ·
        let α : G := a * (lam * b * lam⁻¹)
        have hαA : α ∈ A := A.mul_mem haA (lam_conj_mem_baseGrp h.wreath hbA)
        have hc0E8 : (a * lam) * (b * tau) ∈ E8 := E8.mul_mem halamE8 hbtauE8
        have hc0D : (a * lam) * (b * tau) ∈ D := D.mul_mem halD hbtD
        have hc0eq : (a * lam) * (b * tau) = α * (lam * tau) := by
          show (a * lam) * (b * tau) = (a * (lam * b * lam⁻¹)) * (lam * tau)
          group
        have hdiffA : (w * (lam * tau)) * ((a * lam) * (b * tau))⁻¹ ∈ A := by
          have hd : (w * (lam * tau)) * ((a * lam) * (b * tau))⁻¹ = w * α⁻¹ := by
            rw [hc0eq]; group
          rw [hd]
          exact A.mul_mem hwA (A.inv_mem hαA)
        have hdiffE8 : (w * (lam * tau)) * ((a * lam) * (b * tau))⁻¹ ∈ E8 :=
          E8.mul_mem he (E8.inv_mem hc0E8)
        have hdiff' : (w * (lam * tau)) * ((a * lam) * (b * tau))⁻¹ ∈
            zpowers ((x₁ * x₂) ^ 2) := by
          rw [← hE8A_eq]; exact ⟨hdiffE8, hdiffA⟩
        have he_eq : w * (lam * tau) =
            ((w * (lam * tau)) * ((a * lam) * (b * tau))⁻¹) *
              ((a * lam) * (b * tau)) := by group
        rw [he_eq]
        exact D.mul_mem (hzpD hdiff') hc0D
  have hYeqD : Y = D := le_antisymm hYD hDY
  exact ⟨a, haA, b, hbA, halamE8.1, hbtauE8.1, hYeqD⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
