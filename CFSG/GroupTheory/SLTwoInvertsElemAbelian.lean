module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.InvertingElements
public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMBasic
public import CFSG.GH74.GLS.IVK.L2.ExistCyclic
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

open CFSG.Open

open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G]

private def sl2inv_C (h₀ : G) (E : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ E ∧ h₀ * x * h₀⁻¹ = x}
  one_mem' := ⟨E.one_mem, by group⟩
  mul_mem' := by
    rintro x y ⟨hxE, hx⟩ ⟨hyE, hy⟩
    exact ⟨E.mul_mem hxE hyE, by
      calc h₀ * (x * y) * h₀⁻¹ = (h₀ * x * h₀⁻¹) * (h₀ * y * h₀⁻¹) := by group
        _ = x * y := by rw [hx, hy]⟩
  inv_mem' := by
    rintro x ⟨hxE, hx⟩
    exact ⟨E.inv_mem hxE, by
      calc h₀ * x⁻¹ * h₀⁻¹ = (h₀ * x * h₀⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hx]⟩

private def sl2inv_I {q : ℕ} {E : Subgroup G} (hE : IsElemAbelian q E) (h₀ : G) :
    Subgroup G where
  carrier := {x | x ∈ E ∧ h₀ * x * h₀⁻¹ = x⁻¹}
  one_mem' := ⟨E.one_mem, by group⟩
  mul_mem' := by
    rintro x y ⟨hxE, hx⟩ ⟨hyE, hy⟩
    exact ⟨E.mul_mem hxE hyE, by
      have hxy : x * y = y * x := hE.comm hxE hyE
      calc h₀ * (x * y) * h₀⁻¹ = (h₀ * x * h₀⁻¹) * (h₀ * y * h₀⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [hx, hy]
        _ = (x * y)⁻¹ := by rw [hxy, mul_inv_rev]⟩
  inv_mem' := by
    rintro x ⟨hxE, hx⟩
    refine ⟨E.inv_mem hxE, ?_⟩
    have h := congrArg Inv.inv hx
    calc h₀ * x⁻¹ * h₀⁻¹ = (h₀ * x * h₀⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := h

private lemma sl2inv_C_le {h₀ : G} {E : Subgroup G} : sl2inv_C h₀ E ≤ E := fun _ hx => hx.1

private lemma sl2inv_I_le {q : ℕ} {E : Subgroup G} (hE : IsElemAbelian q E) {h₀ : G} :
    sl2inv_I hE h₀ ≤ E := fun _ hx => hx.1

private lemma sl2inv_conj_sq_eq_self {h₀ : G} {E : Subgroup G}
    (h₀2 : h₀ * h₀ ∈ Subgroup.centralizer (E : Set G)) {x : G} (hx : x ∈ E) :
    h₀ * (h₀ * x * h₀⁻¹) * h₀⁻¹ = x := by
  have hcomm : x * (h₀ * h₀) = (h₀ * h₀) * x :=
    (Subgroup.mem_centralizer_iff.mp h₀2) x hx
  calc h₀ * (h₀ * x * h₀⁻¹) * h₀⁻¹ = (h₀ * h₀) * x * (h₀ * h₀)⁻¹ := by group
    _ = x := by rw [hcomm.symm]; group

private lemma sl2inv_conj_mem {h₀ : G} {E : Subgroup G}
    (h₀N : h₀ ∈ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ E) :
    h₀ * x * h₀⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.mp h₀N x).mp hx

private lemma sl2inv_C_inf_I_eq_bot {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {E : Subgroup G}
    (hE : IsElemAbelian q E) {h₀ : G} :
    sl2inv_C h₀ E ⊓ sl2inv_I hE h₀ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxC, hxI⟩ := Subgroup.mem_inf.mp hx
  have hxE : x ∈ E := hxC.1
  have hx_eq : x = x⁻¹ := hxC.2.symm.trans hxI.2
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    calc x * x = x * x⁻¹ := congrArg (fun y => x * y) hx_eq
      _ = 1 := mul_inv_cancel x
  have h2dvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hqdvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one (hE.2 x hxE)
  have hqodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqodd
  have h1 : orderOf x = 1 := by
    have hgcd : Nat.gcd 2 q = 1 := hcop
    exact Nat.dvd_one.mp (by simpa [hgcd] using Nat.dvd_gcd h2dvd hqdvd)
  exact orderOf_eq_one_iff.mp h1

private lemma sl2inv_sup_C_I_eq {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {E : Subgroup G}
    (hE : IsElemAbelian q E) {h₀ : G}
    (h₀N : h₀ ∈ Subgroup.normalizer (E : Set G))
    (h₀2 : h₀ * h₀ ∈ Subgroup.centralizer (E : Set G)) :
    sl2inv_C h₀ E ⊔ sl2inv_I hE h₀ = E := by
  refine le_antisymm (sup_le sl2inv_C_le (sl2inv_I_le hE)) ?_
  intro x hx
  have hqodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
  let y : G := h₀ * x * h₀⁻¹
  have hyE : y ∈ E := sl2inv_conj_mem h₀N hx
  have hxy : x * y = y * x := hE.comm hx hyE
  have hyfix : h₀ * y * h₀⁻¹ = x := sl2inv_conj_sq_eq_self h₀2 hx
  have hcC : x * y ∈ sl2inv_C h₀ E := by
    refine ⟨E.mul_mem hx hyE, ?_⟩
    calc h₀ * (x * y) * h₀⁻¹ = (h₀ * x * h₀⁻¹) * (h₀ * y * h₀⁻¹) := by group
      _ = y * x := by rw [hyfix]
      _ = x * y := hxy.symm
  have hdI : x * y⁻¹ ∈ sl2inv_I hE h₀ := by
    refine ⟨E.mul_mem hx (E.inv_mem hyE), ?_⟩
    calc h₀ * (x * y⁻¹) * h₀⁻¹ = (h₀ * x * h₀⁻¹) * (h₀ * y⁻¹ * h₀⁻¹) := by group
      _ = y * (h₀ * y * h₀⁻¹)⁻¹ := by
            rw [show h₀ * x * h₀⁻¹ = y from rfl]
            group
      _ = y * x⁻¹ := by rw [hyfix]
      _ = (x * y⁻¹)⁻¹ := by rw [mul_inv_rev]; group
  have hyx : y * x = x * y := hxy.symm
  have hRHS : (x * y) * (x * y⁻¹) = x * x * (y * y⁻¹) := by
    calc (x * y) * (x * y⁻¹) = x * (y * x) * y⁻¹ := by group
      _ = x * (x * y) * y⁻¹ := by rw [hyx]
      _ = x * x * (y * y⁻¹) := by group
  have hx2 : x ^ 2 = (x * y) * (x * y⁻¹) := by
    rw [pow_two, hRHS]
    group
  have hx2_mem : x ^ 2 ∈ sl2inv_C h₀ E ⊔ sl2inv_I hE h₀ := by
    rw [hx2]
    exact Subgroup.mul_mem_sup hcC hdI
  have hxpow : x = (x ^ 2) ^ ((q + 1) / 2) := by
    obtain ⟨k, rfl⟩ := hqodd
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hE.2 x hx, one_mul]
  rw [hxpow]
  exact Subgroup.pow_mem _ hx2_mem _

private lemma sl2inv_conj_h_conj_h₀ {h₀ h c : G} {E : Subgroup G}
    (h₀N : h₀ ∈ Subgroup.normalizer (E : Set G))
    (hN : h ∈ Subgroup.normalizer (E : Set G))
    (hcE : c ∈ E)
    (ha : h₀ * h * h₀⁻¹ * h⁻¹ ∈ Subgroup.centralizer (E : Set G)) :
    h₀ * (h * c * h⁻¹) * h₀⁻¹ = h * (h₀ * c * h₀⁻¹) * h⁻¹ := by
  let a : G := h₀ * h * h₀⁻¹ * h⁻¹
  have hcomm_eq : h₀ * h = a * h * h₀ := by
    simp only [a]
    group
  have hzhE : h * (h₀ * c * h₀⁻¹) * h⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hN (h₀ * c * h₀⁻¹)).mp (sl2inv_conj_mem h₀N hcE)
  have hca : a * (h * (h₀ * c * h₀⁻¹) * h⁻¹) =
      (h * (h₀ * c * h₀⁻¹) * h⁻¹) * a :=
    ((Subgroup.mem_centralizer_iff.mp ha) _ hzhE).symm
  calc h₀ * (h * c * h⁻¹) * h₀⁻¹
      = (h₀ * h) * c * (h₀ * h)⁻¹ := by group
    _ = (a * h * h₀) * c * (a * h * h₀)⁻¹ := by rw [hcomm_eq]
    _ = a * (h * (h₀ * c * h₀⁻¹) * h⁻¹) * a⁻¹ := by group
    _ = h * (h₀ * c * h₀⁻¹) * h⁻¹ := by
          rw [hca]
          group

private lemma sl2inv_H_le_normalizer_C {h₀ : G} {E H : Subgroup G}
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (h₀N : h₀ ∈ Subgroup.normalizer (E : Set G))
    (hcommH : ∀ h ∈ H, h₀ * h * h₀⁻¹ * h⁻¹ ∈ Subgroup.centralizer (E : Set G)) :
    H ≤ Subgroup.normalizer (sl2inv_C h₀ E : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · rintro ⟨hcE, hc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHE hh) c).mp hcE, ?_⟩
    have hform := sl2inv_conj_h_conj_h₀ h₀N (hHE hh) hcE (hcommH h hh)
    rw [hform, hc]
  · intro hc
    have hcE : h * c * h⁻¹ ∈ E := hc.1
    have hh' : h⁻¹ ∈ H := H.inv_mem hh
    have hform := sl2inv_conj_h_conj_h₀ h₀N (hHE hh') hcE (hcommH h⁻¹ hh')
    refine ⟨?_, ?_⟩
    · have hmem := (Subgroup.mem_normalizer_iff.mp (hHE hh') (h * c * h⁻¹)).mp hcE
      convert hmem using 1
      group
    · have hinner : h⁻¹ * (h * c * h⁻¹) * h = c := by group
      simp only [inv_inv] at hform
      rw [hc.2] at hform
      simpa [hinner] using hform

private lemma sl2inv_H_le_normalizer_I {q : ℕ} {E H : Subgroup G} {h₀ : G}
    (hE : IsElemAbelian q E)
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (h₀N : h₀ ∈ Subgroup.normalizer (E : Set G))
    (hcommH : ∀ h ∈ H, h₀ * h * h₀⁻¹ * h⁻¹ ∈ Subgroup.centralizer (E : Set G)) :
    H ≤ Subgroup.normalizer (sl2inv_I hE h₀ : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · rintro ⟨hcE, hc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHE hh) c).mp hcE, ?_⟩
    have hform := sl2inv_conj_h_conj_h₀ h₀N (hHE hh) hcE (hcommH h hh)
    rw [hform, hc]
    group
  · intro hc
    have hcE : h * c * h⁻¹ ∈ E := hc.1
    have hh' : h⁻¹ ∈ H := H.inv_mem hh
    have hform := sl2inv_conj_h_conj_h₀ h₀N (hHE hh') hcE (hcommH h⁻¹ hh')
    refine ⟨?_, ?_⟩
    · have hmem := (Subgroup.mem_normalizer_iff.mp (hHE hh') (h * c * h⁻¹)).mp hcE
      convert hmem using 1
      group
    · have hinner : h⁻¹ * (h * c * h⁻¹) * h = c := by group
      simp only [inv_inv] at hform
      rw [hc.2] at hform
      simpa [hinner] using hform

lemma card_eq_prime_of_le_of_card_eq_sq {q : ℕ} [Fact q.Prime]
    {E A : Subgroup G} (hAE : A ≤ E) (hEc : Nat.card E = q ^ 2)
    (hA_ne_bot : A ≠ ⊥) (hA_ne_top : A ≠ E) :
    Nat.card A = q := by
  have hdvd : Nat.card A ∣ q ^ 2 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le hAE
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp hdvd
  have hk_pos : k ≠ 0 := by
    intro hk0
    apply hA_ne_bot
    apply Subgroup.card_eq_one.mp
    rw [hk_eq, hk0, pow_zero]
  have hk_ne_two : k ≠ 2 := by
    intro hk2
    apply hA_ne_top
    refine Subgroup.eq_of_le_of_card_ge hAE ?_
    rw [hEc, hk_eq, hk2]
  have hk1 : k = 1 := by omega
  rw [hk_eq, hk1, pow_one]

private lemma sl2inv_false_of_both
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {E H : Subgroup G}
    (hE : IsElemAbelian q E) (hEc : Nat.card E = q ^ 2)
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    {h₀ : G} (h₀H : h₀ ∈ H)
    (h₀_not_cent : h₀ ∉ Subgroup.centralizer (E : Set G))
    (h₀_sq_cent : h₀ * h₀ ∈ Subgroup.centralizer (E : Set G))
    (hcommH : ∀ h ∈ H, h₀ * h * h₀⁻¹ * h⁻¹ ∈ Subgroup.centralizer (E : Set G))
    {h₁ h₂ : G} (h₁H : h₁ ∈ H) (h₂H : h₂ ∈ H)
    (hd_not_cent : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∉ Subgroup.centralizer (E : Set G))
    (hC_ne_bot : sl2inv_C h₀ E ≠ ⊥) (hI_ne_bot : sl2inv_I hE h₀ ≠ ⊥) : False := by
  have h₀N : h₀ ∈ Subgroup.normalizer (E : Set G) := hHE h₀H
  have hCI_bot : sl2inv_C h₀ E ⊓ sl2inv_I hE h₀ = ⊥ :=
    sl2inv_C_inf_I_eq_bot hq2 hE
  have hE_sup : sl2inv_C h₀ E ⊔ sl2inv_I hE h₀ = E :=
    sl2inv_sup_C_I_eq hq2 hE h₀N h₀_sq_cent
  have hC_ne_E : sl2inv_C h₀ E ≠ E := by
    intro hCE
    apply h₀_not_cent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ sl2inv_C h₀ E := by rw [hCE]; exact hx
    have hfix : h₀ * x * h₀⁻¹ = x := hxC.2
    calc x * h₀ = (h₀ * x * h₀⁻¹) * h₀ := by rw [hfix]
      _ = h₀ * x := by group
  have hI_ne_E : sl2inv_I hE h₀ ≠ E := by
    intro hIE
    apply hC_ne_bot
    have hsup : sl2inv_C h₀ E = sl2inv_C h₀ E ⊓ sl2inv_I hE h₀ := by
      rw [hIE, inf_eq_left.mpr sl2inv_C_le]
    exact hsup.trans hCI_bot
  have hCcyc : IsCyclic (sl2inv_C h₀ E) := by
    have hcard : Nat.card (sl2inv_C h₀ E) = q :=
      card_eq_prime_of_le_of_card_eq_sq sl2inv_C_le hEc hC_ne_bot hC_ne_E
    have hprime : Nat.Prime (Nat.card (sl2inv_C h₀ E)) := by
      rw [hcard]
      exact Fact.out
    have : Fact (Nat.Prime (Nat.card (sl2inv_C h₀ E))) := ⟨hprime⟩
    exact isCyclic_of_prime_card rfl
  have hIcyc : IsCyclic (sl2inv_I hE h₀) := by
    have hcard : Nat.card (sl2inv_I hE h₀) = q :=
      card_eq_prime_of_le_of_card_eq_sq (sl2inv_I_le hE) hEc hI_ne_bot hI_ne_E
    have hprime : Nat.Prime (Nat.card (sl2inv_I hE h₀)) := by
      rw [hcard]
      exact Fact.out
    have : Fact (Nat.Prime (Nat.card (sl2inv_I hE h₀))) := ⟨hprime⟩
    exact isCyclic_of_prime_card rfl
  have hCH : H ≤ Subgroup.normalizer (sl2inv_C h₀ E : Set G) :=
    sl2inv_H_le_normalizer_C hHE h₀N hcommH
  have hIH : H ≤ Subgroup.normalizer (sl2inv_I hE h₀ : Set G) :=
    sl2inv_H_le_normalizer_I hE hHE h₀N hcommH
  have hdC_mem : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈
      Subgroup.centralizer (sl2inv_C h₀ E : Set G) :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.commutator_mem_centralizer_of_isCyclic
      hCcyc (hCH h₁H) (hCH h₂H)
  have hdI_mem : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈
      Subgroup.centralizer (sl2inv_I hE h₀ : Set G) :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.commutator_mem_centralizer_of_isCyclic
      hIcyc (hIH h₁H) (hIH h₂H)
  have hdC : ∀ x ∈ sl2inv_C h₀ E,
      (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x := by
    intro x hx
    have hcomm : x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) =
        (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x :=
      (Subgroup.mem_centralizer_iff.mp hdC_mem) x hx
    calc (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹
        = (x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ := by rw [← hcomm]
      _ = x := by group
  have hdI : ∀ x ∈ sl2inv_I hE h₀,
      (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x := by
    intro x hx
    have hcomm : x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) =
        (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x :=
      (Subgroup.mem_centralizer_iff.mp hdI_mem) x hx
    calc (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹
        = (x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ := by rw [← hcomm]
      _ = x := by group
  apply hd_not_cent
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxsup : x ∈ sl2inv_C h₀ E ⊔ sl2inv_I hE h₀ := by
    rw [hE_sup]
    exact hx
  obtain ⟨c, hc, i, hi, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute
      (A := sl2inv_C h₀ E) (B := sl2inv_I hE h₀)
      (fun a ha b hb => hE.comm (sl2inv_C_le ha) (sl2inv_I_le hE hb)) hxsup
  have hdx : (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c * i) = (c * i) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) := by
    calc (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c * i)
        = ((h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * c * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹) *
            ((h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * i * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹) *
            (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) := by group
      _ = c * i * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) := by rw [hdC c hc, hdI i hi]
  exact hdx.symm

private abbrev sl2inv_SL2 (q : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (ZMod q)

private def sl2inv_A (q : ℕ) [Fact q.Prime] : sl2inv_SL2 q :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

private def sl2inv_B (q : ℕ) [Fact q.Prime] : sl2inv_SL2 q :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private lemma sl2inv_A_mul_B_ne_B_mul_A (q : ℕ) [Fact q.Prime] :
    sl2inv_A q * sl2inv_B q ≠ sl2inv_B q * sl2inv_A q := by
  intro h
  have h00 := congrArg (fun s : sl2inv_SL2 q =>
    (s : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h00
  change ((!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) =
    ((!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) at h00
  have h21 : (2 : ZMod q) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  have h1 : (1 : ZMod q) ≠ 0 := by
    intro hz
    have hdvd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp (by simpa using hz)
    exact (Fact.out : q.Prime).not_dvd_one hdvd
  apply h1
  calc (1 : ZMod q) = 2 - 1 := by ring
    _ = 1 - 1 := by rw [h21]
    _ = 0 := by ring

theorem exists_inverting_of_sl2_quotient {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2)
    {E H : Subgroup G} (hE : CFSG.Open.IsElemAbelian q E) (hEc : Nat.card E = q ^ 2)
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (φ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf H) :
    ∃ h ∈ H, ∀ x ∈ E, h * x * h⁻¹ = x⁻¹ := by
  classical
  have h2z : (2 : ZMod q) ≠ 0 := by
    intro h2
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hq1 | hq2'
    · exact (Fact.out : q.Prime).ne_one hq1
    · exact hq2 hq2'
  have hneg_ne : (-1 : sl2inv_SL2 q) ≠ 1 := by
    have h := CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one (ZMod q) h2z
    simpa [CFSG.Semidihedral.OddFieldSL2.minusIdentity] using h
  have hneg_sq : (-1 : sl2inv_SL2 q) ^ 2 = 1 := by
    simpa [CFSG.Semidihedral.OddFieldSL2.minusIdentity] using
      CFSG.Semidihedral.OddFieldSL2.minusIdentity_square (ZMod q)
  have hneg_comm : ∀ s : sl2inv_SL2 q, (-1 : sl2inv_SL2 q) * s = s * (-1) := by
    intro s
    have hcenter := CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center (ZMod q)
    have h := (Subgroup.mem_center_iff.mp hcenter) s
    simpa [CFSG.Semidihedral.OddFieldSL2.minusIdentity] using h.symm
  obtain ⟨h₀, hh₀φ⟩ := hφ (-1 : sl2inv_SL2 q)
  have h₀_not_cent : (h₀ : G) ∉ Subgroup.centralizer (E : Set G) := by
    intro hc
    have hmem : h₀ ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr hc
    have hphi1 : φ h₀ = 1 := MonoidHom.mem_ker.mp hmem
    exact hneg_ne (hh₀φ.symm.trans hphi1)
  have h₀_sq_cent : (h₀ : G) * (h₀ : G) ∈ Subgroup.centralizer (E : Set G) := by
    have hmem : h₀ ^ 2 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hh₀φ, hneg_sq]
    rw [hker] at hmem
    have hcent : ((h₀ ^ 2 : ↥H) : G) ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.mem_subgroupOf.mp hmem
    simpa [pow_two] using hcent
  have hcommH : ∀ h ∈ H,
      (h₀ : G) * h * (h₀ : G)⁻¹ * h⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    intro h hh
    let y : ↥H := ⟨(h₀ : G) * h * (h₀ : G)⁻¹ * h⁻¹, by
      exact H.mul_mem (H.mul_mem (H.mul_mem h₀.2 hh) (H.inv_mem h₀.2)) (H.inv_mem hh)⟩
    have hy_eq : y = h₀ * ⟨h, hh⟩ * h₀⁻¹ * ⟨h, hh⟩⁻¹ := Subtype.ext rfl
    have hphi1 : φ y = 1 := by
      rw [hy_eq]
      simp only [map_mul, map_inv, hh₀φ]
      rw [hneg_comm (φ ⟨h, hh⟩)]
      group
    have hmem : y ∈ φ.ker := MonoidHom.mem_ker.mpr hphi1
    rw [hker] at hmem
    have hcent := Subgroup.mem_subgroupOf.mp hmem
    simpa [y] using hcent
  obtain ⟨h₁, hh₁φ⟩ := hφ (sl2inv_A q)
  obtain ⟨h₂, hh₂φ⟩ := hφ (sl2inv_B q)
  have hd_not_cent : (h₁ : G) * (h₂ : G) * (h₁ : G)⁻¹ * (h₂ : G)⁻¹ ∉
      Subgroup.centralizer (E : Set G) := by
    intro hc
    let y : ↥H := ⟨(h₁ : G) * (h₂ : G) * (h₁ : G)⁻¹ * (h₂ : G)⁻¹, by
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁.2 h₂.2) (H.inv_mem h₁.2)) (H.inv_mem h₂.2)⟩
    have hy_eq : y = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := Subtype.ext rfl
    have hphi_eq : φ y = sl2inv_A q * sl2inv_B q * (sl2inv_A q)⁻¹ * (sl2inv_B q)⁻¹ := by
      rw [hy_eq]
      simp only [map_mul, map_inv, hh₁φ, hh₂φ]
    have hmem : y ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr hc
    have hphi1 : φ y = 1 := MonoidHom.mem_ker.mp hmem
    have hcommAB : sl2inv_A q * sl2inv_B q = sl2inv_B q * sl2inv_A q := by
      calc sl2inv_A q * sl2inv_B q
          = (sl2inv_A q * sl2inv_B q * (sl2inv_A q)⁻¹ * (sl2inv_B q)⁻¹) *
              (sl2inv_B q * sl2inv_A q) := by group
        _ = 1 * (sl2inv_B q * sl2inv_A q) := by rw [← hphi_eq, hphi1]
        _ = sl2inv_B q * sl2inv_A q := one_mul _
    exact sl2inv_A_mul_B_ne_B_mul_A q hcommAB
  have hCbot_or : sl2inv_C (h₀ : G) E = ⊥ ∨ sl2inv_I hE (h₀ : G) = ⊥ := by
    by_contra h
    push Not at h
    exact sl2inv_false_of_both hq2 hE hEc hHE h₀.2 h₀_not_cent h₀_sq_cent hcommH
      h₁.2 h₂.2 hd_not_cent h.1 h.2
  rcases hCbot_or with hCbot | hIbot
  · refine ⟨(h₀ : G), h₀.2, ?_⟩
    intro x hx
    have hxsup : x ∈ sl2inv_C (h₀ : G) E ⊔ sl2inv_I hE (h₀ : G) := by
      rw [sl2inv_sup_C_I_eq hq2 hE (hHE h₀.2) h₀_sq_cent]
      exact hx
    have hxI : x ∈ sl2inv_I hE (h₀ : G) := by
      rwa [hCbot, bot_sup_eq] at hxsup
    exact hxI.2
  · exfalso
    have hsup : sl2inv_C (h₀ : G) E ⊔ sl2inv_I hE (h₀ : G) = E :=
      sl2inv_sup_C_I_eq hq2 hE (hHE h₀.2) h₀_sq_cent
    have hEC : E = sl2inv_C (h₀ : G) E := by
      calc E = sl2inv_C (h₀ : G) E ⊔ sl2inv_I hE (h₀ : G) := hsup.symm
        _ = sl2inv_C (h₀ : G) E ⊔ ⊥ := by rw [hIbot]
        _ = sl2inv_C (h₀ : G) E := sup_bot_eq _
    apply h₀_not_cent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ sl2inv_C (h₀ : G) E := hEC ▸ hx
    have hfix : (h₀ : G) * x * (h₀ : G)⁻¹ = x := hxC.2
    calc x * (h₀ : G) = ((h₀ : G) * x * (h₀ : G)⁻¹) * (h₀ : G) := by rw [hfix]
      _ = (h₀ : G) * x := by group

theorem exists_two_element_inverting_of_sl2_quotient {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {E H : Subgroup G} (hE : CFSG.Open.IsElemAbelian q E) (hEc : Nat.card E = q ^ 2)
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (φ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf H) :
    ∃ t ∈ H, (∃ k : ℕ, orderOf t = 2 ^ k) ∧ ∀ x ∈ E, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨h, hhH, hhinv⟩ :=
    exists_inverting_of_sl2_quotient hq2 hE hEc hHE φ hφ hker
  obtain ⟨a, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  have hm_pos : 0 < m := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    exact Nat.not_odd_zero hm_odd
  have hord : orderOf (h ^ m) = 2 ^ a :=
    CFSG.GH74.GLS.IVK.orderOf_pow_odd_part h hm_pos hm_eq
  refine ⟨h ^ m, H.pow_mem hhH m, ⟨a, hord⟩, ?_⟩
  intro x hx
  exact pow_odd_inverts (hhinv x hx) hm_odd

end CFSG.GroupTheory
