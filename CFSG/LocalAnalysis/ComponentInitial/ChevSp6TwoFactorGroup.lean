module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

theorem not_sq_dvd_168 {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) : ¬ ℓ ^ 2 ∣ 168 := by
  intro h
  have hle : ℓ ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hℓ13 : ℓ < 13 := by nlinarith
  interval_cases ℓ
  all_goals revert hℓ hodd h; decide

theorem ker_eq_bot_of_perfect_odd_cover {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* S) (hf : Function.Surjective f) (hker : f.ker ≤ center E)
    (hodd : Odd (Nat.card f.ker)) : f.ker = ⊥ := by
  classical
  by_contra hne
  have h1 : Nat.card f.ker ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hℓdvd)
  obtain ⟨Cℓ⟩ := (Sylow.nonempty : Nonempty (Sylow ℓ f.ker))
  obtain ⟨Sℓ⟩ := (Sylow.nonempty : Nonempty (Sylow ℓ S))
  have hSℓ := Sylow.card_eq_multiplicity Sℓ
  rw [card_glThree] at hSℓ
  have hfac : Nat.factorization 168 ℓ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    exact not_sq_dvd_168 hℓ hℓ2 ((hℓ.pow_dvd_iff_le_factorization (by norm_num)).2 hcon)
  have key : ∀ (d : ℕ) (a : Fin d → ℕ), d ≤ 1 → (∀ i, 1 ≤ a i) →
      Nonempty ((Sℓ : Subgroup S) ≃* ((i : Fin d) → Multiplicative (ZMod (ℓ ^ a i)))) →
      Nat.card Cℓ = 1 := by
    intro d a hd ha hS
    obtain ⟨φ, hφ⟩ := perfect_central_cover_abelian_sylow_prime_kernel_bound hf hker Cℓ Sℓ a ha hS
    have hempty : IsEmpty {p : Fin d × Fin d // p.1 < p.2} := ⟨fun p => by
      have h1 := p.2
      have h2 := p.1.1.2
      have h3 := p.1.2.2
      change (p.1.1 : ℕ) < p.1.2 at h1
      omega⟩
    have hsub : Subsingleton ((p : {p : Fin d × Fin d // p.1 < p.2}) →
        Multiplicative (ZMod (ℓ ^ min (a p.1.1) (a p.1.2)))) := inferInstance
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
    obtain ⟨x', rfl⟩ := hφ x
    obtain ⟨y', rfl⟩ := hφ y
    rw [Subsingleton.elim x' y']
  have hC1 : Nat.card Cℓ = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hfac with h0 | h1
    · rw [h0, pow_zero] at hSℓ
      obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.1 hSℓ
      have : Unique (Sℓ : Subgroup S) := @uniqueOfSubsingleton _ hsub hne.some
      exact key 0 Fin.elim0 (by norm_num) (fun i => Fin.elim0 i) ⟨MulEquiv.ofUnique⟩
    · rw [h1, pow_one] at hSℓ
      refine key 1 (fun _ => 1) le_rfl (fun _ => le_rfl) ⟨mulEquivOfPrimeCardEq hSℓ ?_⟩
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one,
        Nat.card_eq_fintype_card, Fintype.card_multiplicative, ← Nat.card_eq_fintype_card,
        Nat.card_zmod, pow_one]
  have hCℓ := Sylow.card_eq_multiplicity Cℓ
  rw [hC1] at hCℓ
  have hpos : 0 < Nat.factorization (Nat.card f.ker) ℓ :=
    hℓ.factorization_pos_of_dvd Nat.card_pos.ne' hℓdvd
  have : 1 < ℓ ^ Nat.factorization (Nat.card f.ker) ℓ := Nat.one_lt_pow hpos.ne' hℓ.one_lt
  omega

section Rank

open Module CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem card_le_sixtyFour_of_le {G : Type*} [Group G] {L : Subgroup G}
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b) {P : Subgroup G} (hPL : P ≤ L)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1) : Nat.card P ≤ 64 := by
  set P' := (P.subgroupOf L).map φ.toMonoidHom with hP'
  have hcard : Nat.card P' = Nat.card P := by
    rw [hP', Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv]
  rw [← hcard]
  refine (BinarySymplecticSix.card_le_of_elementary hb hnd hV ?_ ?_).1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ hx _ hy)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq _ hx), map_one]

theorem card_le_of_le_centralizer {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
    (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
    (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
    (hL : ∀ P : Subgroup G, P ≤ L → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x * x = 1) →
      Nat.card P ≤ 64)
    {P : Subgroup G} (hP : P ≤ centralizer ({z} : Set G))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1) : Nat.card P ≤ 128 := by
  have hLH : L ≤ centralizer ({z} : Set G) := hsup ▸ le_sup_left
  have hHc : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
    rw [← hsup, BinarySymplecticSix.card_sup_eq_mul (zpowers_le.2 hzC) hinf, Nat.card_zpowers, hz]
  have hrelH : L.relIndex (centralizer ({z} : Set G)) = 2 := by
    have h1 := (L.subgroupOf (centralizer ({z} : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv, hHc, mul_comm (Nat.card L)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrelP : L.relIndex P ≤ 2 :=
    hrelH ▸ relIndex_le_of_le_right hP (by rw [hrelH]; norm_num)
  have hLPcard : Nat.card (L.subgroupOf P) = Nat.card (L ⊓ P : Subgroup G) := by
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hLP64 : Nat.card (L ⊓ P : Subgroup G) ≤ 64 :=
    hL _ inf_le_left (fun x hx y hy => hcomm x (mem_inf.1 hx).2 y (mem_inf.1 hy).2)
      (fun x hx => hsq x (mem_inf.1 hx).2)
  have h1 := (L.subgroupOf P).index_mul_card
  rw [hLPcard] at h1
  calc Nat.card P = (L.subgroupOf P).index * Nat.card (L ⊓ P : Subgroup G) := h1.symm
    _ ≤ 2 * 64 := Nat.mul_le_mul hrelP hLP64
    _ = 128 := by norm_num

end Rank

section Ehat

variable {Y : Type*} [Group Y]

@[expose] def zmodTwoHom (a : Y) (ha : a * a = 1) : Multiplicative (ZMod 2) →* Y where
  toFun ε := if Multiplicative.toAdd ε = 0 then 1 else a
  map_one' := rfl
  map_mul' ε ε' := by
    rcases mult_two_cases ε with rfl | rfl <;> rcases mult_two_cases ε' with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 from rfl]
      simp only [toAdd_ofAdd, toAdd_one, ite_true, show (1 : ZMod 2) ≠ 0 from by decide,
        ite_false]
      exact ha.symm

theorem zmodTwoHom_one (a : Y) (ha : a * a = 1) :
    zmodTwoHom a ha (Multiplicative.ofAdd 1) = a := rfl

theorem exists_mulEquiv_Ehat (D : Subgroup Y) [D.Normal] (Ψ : D ≃* K) {a : Y}
    (ha : a * a = 1) (hΨa : ∀ d : D, Ψ (MulAut.conjNormal a d) = (Ψ d).swap)
    (χ : Y →* Multiplicative (ZMod 2)) (hχa : χ a = Multiplicative.ofAdd 1) (hχ : χ.ker = D) :
    ∃ Ω : Y ≃* Ehat, (∀ d : D, Ω d = SemidirectProduct.inl (Ψ d)) ∧ Ω a = sE := by
  set fn : K →* Y := D.subtype.comp Ψ.symm.toMonoidHom with hfn
  set fh := zmodTwoHom a ha with hfh
  have hcompat : ∀ ε : Multiplicative (ZMod 2),
      fn.comp (swapAct ε).toMonoidHom = (MulAut.conj (fh ε)).toMonoidHom.comp fn := by
    intro ε
    rcases mult_two_cases ε with rfl | rfl
    · ext k
      simp [hfh, zmodTwoHom]
    · ext k
      change ((Ψ.symm (k.swap) : D) : Y) = a * (Ψ.symm k : Y) * a⁻¹
      have h1 := hΨa (Ψ.symm k)
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : MulAut.conjNormal a (Ψ.symm k) = Ψ.symm k.swap := by
        rw [← h1, MulEquiv.symm_apply_apply]
      rw [← h2, MulAut.conjNormal_apply]
  set ℓ := SemidirectProduct.lift fn fh hcompat with hℓ
  have hℓapply : ∀ e : Ehat, ℓ e = fn e.left * fh e.right := fun e => rfl
  have hχfn : ∀ k, χ (fn k) = 1 := fun k => by
    rw [← MonoidHom.mem_ker, hχ]
    exact (Ψ.symm k).2
  have hχfh : ∀ ε, χ (fh ε) = ε := fun ε => by
    rcases mult_two_cases ε with rfl | rfl
    · exact map_one χ
    · exact hχa
  have hinj : Function.Injective ℓ := by
    rw [injective_iff_map_eq_one]
    intro e he
    rw [hℓapply] at he
    have hr : e.right = 1 := by
      have h1 := congrArg χ he
      rwa [map_mul, hχfn, hχfh, one_mul, map_one] at h1
    rw [hr, map_one, mul_one] at he
    have hl : e.left = 1 := by
      have h1 : Ψ.symm e.left = 1 := Subtype.ext he
      rwa [MulEquiv.map_eq_one_iff] at h1
    exact SemidirectProduct.ext hl hr
  have hsurj : Function.Surjective ℓ := by
    intro y
    rcases mult_two_cases (χ y) with h | h
    · have hy : y ∈ D := by rw [← hχ]; exact h
      refine ⟨SemidirectProduct.inl (Ψ ⟨y, hy⟩), ?_⟩
      rw [SemidirectProduct.lift_inl]
      simp [hfn]
    · have hy : y * a⁻¹ ∈ D := by
        rw [← hχ, MonoidHom.mem_ker, map_mul, map_inv, h, hχa, mul_inv_cancel]
      refine ⟨SemidirectProduct.inl (Ψ ⟨y * a⁻¹, hy⟩) * sE, ?_⟩
      rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
      simp only [hfn, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
      rw [hfh, zmodTwoHom_one, inv_mul_cancel_right]
  set e := MulEquiv.ofBijective ℓ ⟨hinj, hsurj⟩ with he
  refine ⟨e.symm, fun d => ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    change (d : Y) = ℓ (SemidirectProduct.inl (Ψ d))
    rw [SemidirectProduct.lift_inl]
    simp [hfn]
  · rw [MulEquiv.symm_apply_eq]
    change a = ℓ sE
    rw [SemidirectProduct.lift_inr, hfh, zmodTwoHom_one]

end Ehat

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
