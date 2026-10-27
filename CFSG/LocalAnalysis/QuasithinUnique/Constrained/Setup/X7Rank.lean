module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.QuasithinUnique.Setup.X7

open scoped IsMulCommutative

theorem natCard_eq_two_pow_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  simpa using this

section Abstract

variable {A X Y : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A] [AddCommGroup X]
  [Module (ZMod 2) X] [Finite X] [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem constant_rank_space_bound (t : A →ₗ[ZMod 2] (X →ₗ[ZMod 2] Y)) {r : ℕ} (hm : 1 ≤
    Module.finrank (ZMod 2) A) (hr : 1 ≤ r)
    (hrank : ∀ a, a ≠ 0 → Module.finrank (ZMod 2) (LinearMap.range (t a)) = r) :
    Module.finrank (ZMod 2) A + r ≤ Module.finrank (ZMod 2) X + Module.finrank (ZMod 2) Y := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite X
  set m := Module.finrank (ZMod 2) A with hmdef
  set d := Module.finrank (ZMod 2) X with hd
  set e := Module.finrank (ZMod 2) Y with he
  have hAcard : Nat.card A = 2 ^ m := natCard_eq_two_pow_finrank A
  have hnt : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hAcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have hrd : r ≤ d := by
    rw [← hrank a₀ ha₀]
    exact LinearMap.finrank_range_le _
  let N : ℕ := ∑ a : A, ∑ x : X, if t a x = 0 then 1 else 0
  have hker : ∀ a : A, a ≠ 0 → (∑ x : X, if t a x = 0 then 1 else 0) = 2 ^ (d - r) := by
    intro a ha
    have h1 : (∑ x : X, if t a x = 0 then 1 else 0) = Nat.card (LinearMap.ker (t a)) := by
      rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [LinearMap.mem_ker]
    rw [h1, natCard_eq_two_pow_finrank]
    congr 1
    have := LinearMap.finrank_range_add_finrank_ker (t a)
    rw [hrank a ha] at this
    omega
  have hker0 : (∑ x : X, if t 0 x = 0 then 1 else 0) = 2 ^ d := by
    have h1 : (∑ x : X, if t 0 x = 0 then 1 else 0) = Nat.card X := by
      rw [Finset.sum_boole, Nat.card_eq_fintype_card]
      simp
    rw [h1, natCard_eq_two_pow_finrank]
  have hN1 : N = 2 ^ (d - r) * (2 ^ r + (2 ^ m - 1)) := by
    have h1 : N = (∑ x : X, if t 0 x = 0 then 1 else 0) +
        ∑ a ∈ Finset.univ.erase (0 : A), ∑ x : X, if t a x = 0 then 1 else 0 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    rw [Finset.sum_congr rfl (fun a ha => hker a (Finset.ne_of_mem_erase ha)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      hAcard, smul_eq_mul, hker0] at h1
    rw [h1]
    have h2 : 2 ^ d = 2 ^ (d - r) * 2 ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrd]
    rw [h2]
    ring
  have hdiv : ∀ x : X, 2 ^ (m - e) ∣ ∑ a : A, if t a x = 0 then 1 else 0 := by
    intro x
    let ev : A →ₗ[ZMod 2] Y := (LinearMap.applyₗ x) ∘ₗ t
    have h1 : (∑ a : A, if t a x = 0 then 1 else 0) = Nat.card (LinearMap.ker ev) := by
      rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [LinearMap.mem_ker, ev]
    rw [h1, natCard_eq_two_pow_finrank]
    refine pow_dvd_pow 2 ?_
    have h2 := LinearMap.finrank_range_add_finrank_ker ev
    have h3 : Module.finrank (ZMod 2) (LinearMap.range ev) ≤ e := Submodule.finrank_le _
    omega
  have hN2 : 2 ^ (m - e) ∣ N := by
    show 2 ^ (m - e) ∣ ∑ a : A, ∑ x : X, if t a x = 0 then 1 else 0
    rw [Finset.sum_comm]
    exact Finset.dvd_sum fun x _ => hdiv x
  have hodd : (2 ^ r + (2 ^ m - 1)) % 2 = 1 := by
    have h1 : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have h3 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have hcop : Nat.Coprime (2 ^ (m - e)) (2 ^ r + (2 ^ m - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hodd
  rw [hN1] at hN2
  have hdvd : 2 ^ (m - e) ∣ 2 ^ (d - r) := hcop.dvd_of_dvd_mul_right hN2
  have hle : m - e ≤ d - r := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  omega

end Abstract

section Rep

variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G U) (A : Subgroup G)

@[expose] def commSub : Submodule (ZMod 2) U := ⨆ a ∈ A, LinearMap.range (ρ a - 1)

variable {ρ A}

theorem range_le_commSub {a : G} (ha : a ∈ A) : LinearMap.range (ρ a - 1) ≤ commSub ρ A :=
  le_iSup₂ (f := fun a (_ : a ∈ A) => LinearMap.range (ρ a - 1)) a ha

theorem commSub_le_fixedSub (hquad : ∀ a ∈ A, ∀ b ∈ A, (ρ a - 1) ∘ₗ (ρ b - 1) = 0) :
    commSub ρ A ≤ fixedSub ρ A := by
  refine iSup₂_le fun b hb => ?_
  rintro _ ⟨u, rfl⟩
  refine mem_fixedSub.mpr fun a ha => ?_
  have h := LinearMap.congr_fun (hquad a ha b hb) u
  simpa [sub_eq_zero] using h

noncomputable def tMap (ρ : Representation (ZMod 2) G U) (D : Submodule (ZMod 2) U) (a : A) :
    D →ₗ[ZMod 2] commSub ρ A :=
  LinearMap.codRestrict (commSub ρ A) ((ρ (a : G) - 1) ∘ₗ D.subtype)
    (fun d => range_le_commSub a.2 ⟨d, rfl⟩)

theorem tMap_mul (hquad : ∀ a ∈ A, ∀ b ∈ A, (ρ a - 1) ∘ₗ (ρ b - 1) = 0)
    (D : Submodule (ZMod 2) U) (a b : A) : tMap ρ D (a * b) = tMap ρ D a + tMap ρ D b := by
  refine LinearMap.ext fun d => Subtype.ext ?_
  have h := LinearMap.congr_fun (hquad a a.2 b b.2) (d : U)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at h
  simp only [tMap, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.sub_apply, Module.End.one_apply, LinearMap.add_apply, Submodule.coe_add,
    Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  refine sub_eq_zero.mp ?_
  rw [← h]
  abel

theorem tMap_range (D : Submodule (ZMod 2) U) (hD : IsCompl (fixedSub ρ A) D) (a : A) :
    (LinearMap.range (tMap ρ D a)).map (commSub ρ A).subtype = LinearMap.range (ρ (a : G) - 1) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨d, rfl⟩
  · rintro _ ⟨u, rfl⟩
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp
      (hD.sup_eq_top ▸ Submodule.mem_top : u ∈ fixedSub ρ A ⊔ D)
    have hcfix : ρ (a : G) c = c := mem_fixedSub.mp hc a a.2
    refine ⟨tMap ρ D a ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩, ?_⟩
    rw [← hcd]
    simp [tMap, hcfix]

theorem finrank_tMap (D : Submodule (ZMod 2) U) (hD : IsCompl (fixedSub ρ A) D) (a : A) :
    Module.finrank (ZMod 2) (LinearMap.range (tMap ρ D a)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ (a : G) - 1)) := by
  rw [← tMap_range D hD a]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (commSub ρ A).subtype (commSub ρ A).injective_subtype _))

variable [Finite U]

theorem constant_moving_rank_bound [CFSG.IsElementaryAbelian 2 A]
    (hquad : ∀ a ∈ A, ∀ b ∈ A, (ρ a - 1) ∘ₗ (ρ b - 1) = 0)
    {r m : ℕ} (hr : 1 ≤ r) (hm : Nat.card A = 2 ^ m) (hA : A ≠ ⊥)
    (hrank : ∀ a ∈ A, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = r) :
    m + r ≤ Module.finrank (ZMod 2) (U ⧸ fixedSub ρ A) +
      Module.finrank (ZMod 2) (commSub ρ A) := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (fixedSub ρ A)
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hm]; exact pow_ne_zero _ (by norm_num))
  have : Finite (Additive A) := Finite.of_equiv A Additive.ofMul
  let tadd : Additive A →+ (D →ₗ[ZMod 2] commSub ρ A) :=
    AddMonoidHom.mk' (fun a => tMap ρ D a.toMul) (fun a b => tMap_mul hquad D a.toMul b.toMul)
  let t : Additive A →ₗ[ZMod 2] (D →ₗ[ZMod 2] commSub ρ A) := AddMonoidHom.toZModLinearMap 2 tadd
  have hfr : Module.finrank (ZMod 2) (Additive A) = m := by
    have h1 := natCard_eq_two_pow_finrank (Additive A)
    have h2 : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
    rw [h2, hm] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hA
      subst h0
      have : Nat.card A = 1 := by simpa using hm
      rw [Subgroup.card_eq_one] at this
      exact this
    · exact h0
  have key := constant_rank_space_bound t (r := r) (by rw [hfr]; exact hm1) hr (fun a ha => by
    have ha1 : a.toMul ≠ 1 := fun h => ha (by simpa using h)
    show Module.finrank (ZMod 2) (LinearMap.range (tMap ρ D a.toMul)) = r
    rw [finrank_tMap D hD, hrank _ a.toMul.2 (fun h => ha1 (Subtype.ext h))])
  rw [hfr] at key
  have hq : Module.finrank (ZMod 2) (U ⧸ fixedSub ρ A) = Module.finrank (ZMod 2) D :=
    LinearEquiv.finrank_eq (Submodule.quotientEquivOfIsCompl _ _ hD)
  rw [hq]
  exact key

local instance (priority := 2000) zmod2AddCommGroup : AddCommGroup (ZMod 2) := Ring.toAddCommGroup

omit [Finite U] in
theorem mem_fixedSub_dual {f : Module.Dual (ZMod 2) U} :
    f ∈ fixedSub ρ.dual A ↔ f ∈ (commSub ρ A).dualAnnihilator := by
  rw [mem_fixedSub, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    have hle : commSub ρ A ≤ LinearMap.ker f := by
      refine iSup₂_le fun a ha => ?_
      rintro _ ⟨u, rfl⟩
      have h2 : f (ρ a u) = f u := by
        simpa [Representation.dual_apply, Module.Dual.transpose_apply] using
          LinearMap.congr_fun (h a⁻¹ (A.inv_mem ha)) u
      simp [LinearMap.mem_ker, h2]
    exact hle hw
  · intro h a ha
    refine LinearMap.ext fun u => ?_
    have h1 : f ((ρ a⁻¹ - 1) u) = 0 := h _ (range_le_commSub (A.inv_mem ha) ⟨u, rfl⟩)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, sub_eq_zero] at h1
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h1

omit [Finite U] in
theorem fixedSub_dual_eq : fixedSub ρ.dual A = (commSub ρ A).dualAnnihilator :=
  Submodule.ext fun _ => mem_fixedSub_dual

omit [Finite U] in
theorem natCard_dual_eq (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
  have h : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  have hf : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [natCard_eq_two_pow_finrank (Module.Dual (ZMod 2) V), natCard_eq_two_pow_finrank V,
    Subspace.dual_finrank_eq]

theorem natCard_fixedSub_dual :
    Nat.card (fixedSub ρ.dual A) =
      2 ^ (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (commSub ρ A)) := by
  have h : Finite (Module.Dual (ZMod 2) U) := Module.finite_of_finite (ZMod 2)
  have hf : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have h1 : Module.finrank (ZMod 2) (fixedSub ρ.dual A) =
      Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (commSub ρ A) := by
    rw [fixedSub_dual_eq]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (commSub ρ A)
    omega
  rw [natCard_eq_two_pow_finrank, h1]

omit [Finite U] in
theorem natCard_fixedSub_prod_dual :
    Nat.card {w : U × Module.Dual (ZMod 2) U // ∀ a ∈ A, (ρ.prod ρ.dual) a w = w} =
      Nat.card (fixedSub ρ A) * Nat.card (fixedSub ρ.dual A) := by
  rw [← Nat.card_prod]
  have h : ∀ w : U × Module.Dual (ZMod 2) U, (∀ a ∈ A, (ρ.prod ρ.dual) a w = w) ↔
      (w.1 ∈ fixedSub ρ A ∧ w.2 ∈ fixedSub ρ.dual A) := by
    intro w
    have hprod : ∀ a : G, (ρ.prod ρ.dual) a w = (ρ a w.1, ρ.dual a w.2) := fun a => rfl
    simp only [mem_fixedSub, hprod, Prod.ext_iff]
    constructor
    · intro h
      exact ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩
    · rintro ⟨h1, h2⟩ a ha
      exact ⟨h1 a ha, h2 a ha⟩
  exact Nat.card_congr ((Equiv.subtypeEquivRight h).trans
    (Equiv.subtypeProdEquivProd (p := fun u => u ∈ fixedSub ρ A)
      (q := fun f => f ∈ fixedSub ρ.dual A)))

theorem constant_moving_rank_no_dual_pair_offender [CFSG.IsElementaryAbelian 2 A]
    (hquad : ∀ a ∈ A, ∀ b ∈ A, (ρ a - 1) ∘ₗ (ρ b - 1) = 0)
    {r m : ℕ} (hr : 1 ≤ r) (hm : Nat.card A = 2 ^ m) (hA : A ≠ ⊥)
    (hrank : ∀ a ∈ A, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = r) :
    m + r ≤ Module.finrank (ZMod 2) (U ⧸ fixedSub ρ A) + Module.finrank (ZMod 2) (commSub ρ A) ∧
      Nat.card (U × Module.Dual (ZMod 2) U) =
        Nat.card {w : U × Module.Dual (ZMod 2) U // ∀ a ∈ A, (ρ.prod ρ.dual) a w = w} *
          2 ^ (Module.finrank (ZMod 2) (U ⧸ fixedSub ρ A) +
            Module.finrank (ZMod 2) (commSub ρ A)) ∧
      Nat.card A * Nat.card {w : U × Module.Dual (ZMod 2) U // ∀ a ∈ A, (ρ.prod ρ.dual) a w = w} <
        Nat.card (U × Module.Dual (ZMod 2) U) := by
  have h1 := constant_moving_rank_bound hquad hr hm hA hrank
  set d := Module.finrank (ZMod 2) (U ⧸ fixedSub ρ A) with hd
  set e := Module.finrank (ZMod 2) (commSub ρ A) with he
  set c := Module.finrank (ZMod 2) (fixedSub ρ A) with hc
  set n := Module.finrank (ZMod 2) U with hn
  have hdc : d + c = n := Submodule.finrank_quotient_add_finrank (fixedSub ρ A)
  have hec : e ≤ c := Submodule.finrank_mono (commSub_le_fixedSub hquad)
  have hcn : c ≤ n := by omega
  have hcard : Nat.card {w : U × Module.Dual (ZMod 2) U // ∀ a ∈ A, (ρ.prod ρ.dual) a w = w} =
      2 ^ (c + (n - e)) := by
    rw [natCard_fixedSub_prod_dual, natCard_fixedSub_dual, natCard_eq_two_pow_finrank (fixedSub ρ A),
      pow_add]
  have hW : Nat.card (U × Module.Dual (ZMod 2) U) = 2 ^ (n + n) := by
    rw [Nat.card_prod, natCard_dual_eq, natCard_eq_two_pow_finrank U, pow_add]
  rw [hcard, hW, hm]
  refine ⟨h1, ?_, ?_⟩
  · rw [← pow_add]
    congr 1
    omega
  · rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end Rep


end CFSG.QuasithinUnique.Setup.X7
