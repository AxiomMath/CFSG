module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.GH74.GLS.Prop27.EndGame
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.GLS.Prop27.OddCoreCheck

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

section Generic

variable {K : Type} [Group K] {G : Type} [Group G]

theorem autModel_eq_one_of_centralizes (M : AutModel K G) {σ : G} (hσ : σ ∈ M.A)
    (h : ∀ y ∈ M.P, σ * y * σ⁻¹ = y) : σ = 1 := by
  have hφ : M.Φ.symm ⟨σ, hσ⟩ = 1 := by
    refine MulEquiv.ext fun x => ?_
    apply M.e.injective
    apply Subtype.ext
    have h1 := M.spec (M.Φ.symm ⟨σ, hσ⟩) x
    rw [MulEquiv.apply_symm_apply] at h1
    rw [MulAut.one_apply, h1]
    exact h _ (M.e x).2
  have h2 : (⟨σ, hσ⟩ : M.A) = 1 := by
    have h3 := congrArg M.Φ hφ
    rw [MulEquiv.apply_symm_apply, map_one] at h3
    exact h3
  exact congrArg Subtype.val h2

variable {X : Type} [Group X] (N : Subgroup X) [N.Normal]

noncomputable def embedFromModel (M : AutModel ↥N G) : X →* G :=
  M.ι.comp MulAut.conjNormal

theorem embedFromModel_mem (M : AutModel ↥N G) (x : X) : embedFromModel N M x ∈ M.A :=
  M.ι_mem _

theorem embedFromModel_injective (M : AutModel ↥N G) (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    Function.Injective (embedFromModel N M) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 : M.ι (MulAut.conjNormal x) = 1 := hx
  have h2 : MulAut.conjNormal x = (1 : MulAut ↥N) := M.ι_injective (by rw [h1, map_one])
  have hx' : x ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h3 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : X)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc n * x = x * n * x⁻¹ * x := by rw [h3]
      _ = x * n := by group
  rw [hC] at hx'
  exact hx'

theorem embedFromModel_of_mem (M : AutModel ↥N G) (hPA : M.P ≤ M.A) {n : X} (hn : n ∈ N) :
    embedFromModel N M n = ((M.e ⟨n, hn⟩ : M.P) : G) := by
  have hσ : embedFromModel N M n ∈ M.A := embedFromModel_mem N M n
  have hπ : ((M.e ⟨n, hn⟩ : M.P) : G) ∈ M.A := hPA (M.e ⟨n, hn⟩).2
  have hconj : ∀ y ∈ M.P, (((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ * embedFromModel N M n) * y *
      (((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ * embedFromModel N M n)⁻¹ = y := by
    intro y hy
    obtain ⟨x, hx⟩ := M.e.surjective ⟨y, hy⟩
    have hy' : y = (M.e x : G) := by rw [hx]
    rw [hy']
    have h1 := M.spec (MulAut.conjNormal n) x
    have h2 : (M.e (MulAut.conjNormal n x) : G) =
        ((M.e ⟨n, hn⟩ : M.P) : G) * (M.e x : G) * ((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ := by
      have h3 : MulAut.conjNormal n x = (⟨n, hn⟩ : ↥N) * x * (⟨n, hn⟩ : ↥N)⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv]
      rfl
    have h4 : (M.Φ (MulAut.conjNormal n) : G) = embedFromModel N M n := rfl
    rw [h4] at h1
    rw [h2] at h1
    have h5 : embedFromModel N M n * (M.e x : G) * (embedFromModel N M n)⁻¹ =
        ((M.e ⟨n, hn⟩ : M.P) : G) * (M.e x : G) * ((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ := h1.symm
    calc (((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ * embedFromModel N M n) * (M.e x : G) *
          (((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ * embedFromModel N M n)⁻¹
        = ((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ *
            (embedFromModel N M n * (M.e x : G) * (embedFromModel N M n)⁻¹) *
            ((M.e ⟨n, hn⟩ : M.P) : G) := by group
      _ = (M.e x : G) := by rw [h5]; group
  have hone := autModel_eq_one_of_centralizes M (σ := ((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ *
    embedFromModel N M n) (M.A.mul_mem (M.A.inv_mem hπ) hσ) hconj
  calc embedFromModel N M n = ((M.e ⟨n, hn⟩ : M.P) : G) *
        (((M.e ⟨n, hn⟩ : M.P) : G)⁻¹ * embedFromModel N M n) := by group
    _ = ((M.e ⟨n, hn⟩ : M.P) : G) := by rw [hone, mul_one]

theorem locBal2_of_autModel {G : Type} [Group G] (Pred : ∀ (S : Type) [Group S], Prop)
    (P A : Subgroup G) (hPA : P ≤ A)
    (hmodel : ∀ (S : Type) [Group S], Pred S → ∃ M : AutModel S G, M.P = P ∧ M.A = A)
    (hcheck : ∀ τ ∈ A, τ ^ 2 = 1 → τ ≠ 1 → ∀ x ∈ A, x * τ = τ * x → x ≠ 1 →
      Odd (orderOf x) → ∃ c ∈ P, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹))) :
    LocBal2 Pred := by
  intro X _ _ N hN hPred hC e0 he0
  have : N.Normal := hN
  obtain ⟨M, hMP, hMA⟩ := hmodel ↥N hPred
  have hPA' : M.P ≤ M.A := by rw [hMP, hMA]; exact hPA
  have hψinj : Function.Injective (embedFromModel N M) := embedFromModel_injective N M hC
  have hψA : ∀ x : X, embedFromModel N M x ∈ A := fun x => hMA ▸ embedFromModel_mem N M x
  have he1 : e0 ≠ 1 := by
    rintro rfl
    simp at he0
  have he0sq : e0 ^ 2 = 1 := by
    rw [← he0]
    exact pow_orderOf_eq_one e0
  have hτ1 : embedFromModel N M e0 ≠ 1 := fun h => he1 (hψinj (by rw [h, map_one]))
  have hτ2 : embedFromModel N M e0 ^ 2 = 1 := by rw [← map_pow, he0sq, map_one]
  apply pPrimeCore_two_eq_bot_of_forall
  intro N0 hN0C hN0norm hN0odd
  by_contra hne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have haC : (a : X) * e0 = e0 * (a : X) := by
    have := hN0C a.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have haodd : Odd (orderOf (a : X)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hN0odd (orderOf_dvd_natCard a)
  have hx1 : embedFromModel N M (a : X) ≠ 1 := fun h => by
    have h1 : (a : X) = 1 := hψinj (h.trans (map_one (embedFromModel N M)).symm)
    exact ha1 (Subtype.ext h1)
  have hxodd : Odd (orderOf (embedFromModel N M (a : X))) := by
    rw [orderOf_injective _ hψinj]
    exact haodd
  have hxτ : embedFromModel N M (a : X) * embedFromModel N M e0 =
      embedFromModel N M e0 * embedFromModel N M (a : X) := by
    rw [← map_mul, ← map_mul, haC]
  obtain ⟨c, hcP, hcτ, hceven⟩ := hcheck _ (hψA e0) hτ2 hτ1 _ (hψA _) hxτ hx1 hxodd
  have hcP' : c ∈ M.P := hMP ▸ hcP
  set c0 : ↥N := M.e.symm ⟨c, hcP'⟩ with hc0
  have hψc0 : embedFromModel N M (c0 : X) = c := by
    rw [embedFromModel_of_mem N M hPA' c0.2]
    have : (⟨(c0 : X), c0.2⟩ : ↥N) = c0 := rfl
    rw [this, hc0, MulEquiv.apply_symm_apply]
  have hc0C : (c0 : X) * e0 = e0 * (c0 : X) := by
    apply hψinj
    rw [map_mul, map_mul, hψc0]
    exact hcτ
  have hc0mem : (c0 : X) ∈ Subgroup.centralizer ({e0} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc0C
  have hinv : (c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹ ∈ N0 := hN0norm _ hc0mem _ (N0.inv_mem a.2)
  have hz : (a : X) * (c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹ ∈ N0 := by
    have h1 : (a : X) * (c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹ =
        (a : X) * ((c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹) := by group
    rw [h1]
    exact N0.mul_mem a.2 hinv
  have hzodd : Odd (orderOf ((a : X) * (c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hz⟩ : ↥N0)
    rw [← Subgroup.orderOf_coe] at h1
    exact Odd.of_dvd_nat hN0odd h1
  have hzev : Even (orderOf ((a : X) * (c0 : X) * (a : X)⁻¹ * (c0 : X)⁻¹)) := by
    rw [← orderOf_injective _ hψinj, map_mul, map_mul, map_mul, map_inv, map_inv, hψc0]
    exact hceven
  exact (Nat.not_even_iff_odd.mpr hzodd) hzev

end Generic

section Check

variable {n : ℕ}

theorem odd_orderOf_iff_pow_eq_one {H : Type*} [Group H] (A : Subgroup H) {a m : ℕ} (hm : Odd m)
    (hcard : Nat.card A = 2 ^ a * m) {y : H} (hy : y ∈ A) : Odd (orderOf y) ↔ y ^ m = 1 := by
  have hdvd : orderOf y ∣ 2 ^ a * m := by
    rw [← hcard]
    have h1 := orderOf_dvd_natCard (⟨y, hy⟩ : A)
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  constructor
  · intro hodd
    have hcop : Nat.Coprime (orderOf y) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)
  · intro h
    exact Odd.of_dvd_nat hm (orderOf_dvd_iff_pow_eq_one.mpr h)

theorem oddCoreCheck_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (hPA : QP.originalSubgroup ≤ QA.originalSubgroup) {a m : ℕ}
    (hm : Odd m) (hcard : Nat.card QA.originalSubgroup = 2 ^ a * m)
    (h : oddCoreCheck m (elemsT QA) (elemsT QP) = true) :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ x ∈ QA.originalSubgroup,
      x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
      ∃ c ∈ QP.originalSubgroup, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹)) := by
  intro τ hτ hτ2 hτ1 x hx hxτ hx1 hxodd
  have hpow : x ^ m = 1 := (odd_orderOf_iff_pow_eq_one _ hm hcard hx).mp hxodd
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h τ ((mem_elemsT QA hQA τ).2 hτ))
    (by simp [hτ2, hτ1])
  have h2 := List.all_eq_true.1 h1 x (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QA hQA x).2 hx, by simpa using hxτ⟩)
  have h3 := (bif_imp _ _).1 h2 (by simp [hx1, hpow])
  obtain ⟨c, hc, hc'⟩ := List.any_eq_true.1 h3
  rw [List.mem_filter] at hc
  have hcP : c ∈ QP.originalSubgroup := (mem_elemsT QP hQP c).1 hc.1
  have hcτ : c * τ = τ * c := by simpa using hc.2
  refine ⟨c, hcP, hcτ, ?_⟩
  have hy : x * c * x⁻¹ * c⁻¹ ∈ QA.originalSubgroup :=
    QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem hx
      (hPA hcP)) (QA.originalSubgroup.inv_mem hx)) (QA.originalSubgroup.inv_mem (hPA hcP))
  have hne : (x * c * x⁻¹ * c⁻¹) ^ m ≠ 1 := by simpa using hc'
  exact Nat.not_odd_iff_even.mp fun hodd =>
    hne ((odd_orderOf_iff_pow_eq_one _ hm hcard hy).mp hodd)

theorem locBal2_of_chains (Pred : ∀ (S : Type) [Group S], Prop) (QA QP : RawSchreierDatum n)
    (hQA : ValidSchreier QA) (hQP : ValidSchreier QP)
    (hPA : QP.originalSubgroup ≤ QA.originalSubgroup) {a m : ℕ} (hm : Odd m)
    (hcard : Nat.card QA.originalSubgroup = 2 ^ a * m)
    (hmodel : ∀ (S : Type) [Group S], Pred S → ∃ M : AutModel S (Equiv.Perm (Fin n)),
      M.P = QP.originalSubgroup ∧ M.A = QA.originalSubgroup)
    (h : oddCoreCheck m (elemsT QA) (elemsT QP) = true) : LocBal2 Pred :=
  locBal2_of_autModel Pred QP.originalSubgroup QA.originalSubgroup hPA hmodel
    (oddCoreCheck_sound QA QP hQA hQP hPA hm hcard h)

end Check

end CFSG.GH74.GLS.Prop27
