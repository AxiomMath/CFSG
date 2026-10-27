module

public import CFSG.LieType.SeitzGeneration.OrthSingular
public import CFSG.LieType.SeitzGeneration.OrthRoot
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions

section Regular

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem nondegenerate_restrict {U : Submodule K V} (hU : PolarNondegOn Q U) :
    (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate := by
  have hrefl : (LinearMap.BilinForm.restrict (polarBilin Q) U).IsRefl := fun x y h => by
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  refine hrefl.nondegenerate_iff_separatingLeft.mpr fun x hx => ?_
  refine Subtype.ext (hU x x.2 fun y hy => ?_)
  have := hx ⟨y, hy⟩
  simpa [polarBilin_apply_apply] using this

theorem nondegenerate_comp_subtype {U : Submodule K V} (hU : PolarNondegOn Q U) :
    (polarBilin (Q.comp U.subtype)).Nondegenerate := by
  rw [polarBilin_comp_subtype]
  exact nondegenerate_restrict hU

end Regular

section GL2

variable {K : Type} [Field K] [Finite K]

theorem dvd_card_sq_sub_one_of_finrank_two {N : Type} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] (h2 : finrank K N = 2) {g : N ≃ₗ[K] N} {p : ℕ} (hp : p.Prime)
    (hgp : g ^ p = 1) (hg1 : g ≠ 1) (hpK : ¬ p ∣ Nat.card K) : p ∣ Nat.card K ^ 2 - 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hfinN : Finite N := Module.finite_of_finite K
  have : Finite (N ≃ₗ[K] N) :=
    Finite.of_injective (fun f : N ≃ₗ[K] N => (f : N → N)) DFunLike.coe_injective
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hdvd : p ∣ Nat.card (N ≃ₗ[K] N) := hord ▸ orderOf_dvd_natCard g
  let e : N ≃ₗ[K] (Fin 2 → K) := LinearEquiv.ofFinrankEq N (Fin 2 → K) (by simp [h2])
  have hc1 : Nat.card (N ≃ₗ[K] N) = Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    Nat.card_congr
      { toFun := fun f => (e.symm.trans f).trans e
        invFun := fun f => (e.trans f).trans e.symm
        left_inv := fun f => by ext v; simp
        right_inv := fun f => by ext v; simp }
  have hc2 : Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) = Nat.card (GL (Fin 2) K) :=
    Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))).toEquiv.symm)
  rw [hc1, hc2, Matrix.card_GL_field, Fin.prod_univ_two] at hdvd
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hdvd
  rw [← Nat.card_eq_fintype_card] at hdvd
  set q := Nat.card K with hq
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · exact h
  · have h' : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_one, _root_.sq]
    rw [h'] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact absurd h1 hpK
    · have : q - 1 ∣ q ^ 2 - 1 := by
        have h1q : 1 ≤ q := Finite.card_pos
        obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
        rw [ht]
        refine ⟨t + 2, ?_⟩
        have : (t + 1) ^ 2 = t * (t + 2) + 1 := by ring
        rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
      exact h1.trans this

end GL2

section Dims

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

open CFSG.RankThree.PartOne.KCOrthogonal in
theorem four_le_finrank_of_fixedPointFree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hpK : ¬ p ∣ Nat.card K) {N : Submodule K V}
    (hN : PolarNondegOn Q N) (hN0 : N ≠ ⊥) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (h1 : ∀ u ∈ N, g u ∈ N) (h2 : ∀ u ∈ N, g.symm u ∈ N) (hfree : ∀ u ∈ N, g u = u → u = 0) :
    4 ≤ finrank K N := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set gN := restrictEquiv N g h1 h2 with hgN
  have hQN := nondegenerate_comp_subtype hN
  have hgNO : gN ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp N.subtype) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun u => by
      change Q (g u) = Q u
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO u
  have hpowN : ∀ (n : ℕ) (u : N), ((gN ^ n) u : V) = (g ^ n) u := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', LinearEquiv.mul_apply, coe_restrictEquiv, ih, pow_succ',
        LinearEquiv.mul_apply]
  have hgNp : gN ^ p = 1 := LinearEquiv.ext fun u => Subtype.ext (by
    rw [hpowN, hgp]
    rfl)
  have hfreeN : ∀ u : N, gN u = u → u = 0 := fun u hu =>
    Subtype.ext (hfree u u.2 (congrArg Subtype.val hu))
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hgN1 : gN ≠ 1 := by
    intro h
    have := hfreeN ⟨u₀, hu₀⟩ (by rw [h]; rfl)
    exact hu₀0 (congrArg Subtype.val this)
  by_contra hlt
  push Not at hlt
  have hpos : 1 ≤ finrank K N := Submodule.one_le_finrank_iff.mpr hN0
  interval_cases hd : finrank K N
  ·
    have := eq_one_of_finrank_le_one hQN (by rw [hd]) (g := ⟨gN, hgNO⟩) hodd
      (Subtype.ext hgNp)
    exact hgN1 this
  ·
    exact hpq (dvd_card_sq_sub_one_of_finrank_two hd hp hgNp hgN1 hpK)
  ·
    have hev := even_finrank_commSpace_of_dicksonHom_eq_one hQN
      (dicksonHom_eq_one_of_pow_eq_one hQN (g := ⟨gN, hgNO⟩) hodd (Subtype.ext hgNp))
    have hsum := finrank_commSpace_add_finrank_fixSpace gN
    rw [hd] at hsum
    have hle : finrank K (commSpace (gN : N ≃ₗ[K] N)) ≤ 3 := by omega
    have hfix : 0 < finrank K (fixSpace gN) := by
      obtain ⟨m, hm⟩ := hev
      change finrank K (commSpace gN) = m + m at hm
      omega
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hfix)
    exact hu0 (hfreeN u (mem_fixSpace.mp hu))

end Dims

section Pairs

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_hypPair_in {W : Submodule K V} (hW : PolarNondegOn Q W) (h3 : 3 ≤ finrank K W) :
    ∃ P : HypPair Q, P.e ∈ W ∧ P.f ∈ W := by
  obtain ⟨e, heW, he0, heQ⟩ := exists_singular_of_three_le_general hW h3
  obtain ⟨f, hfW, hfQ, hef⟩ := exists_hypPair_of_regular (nondegenerate_restrict hW) heW he0 heQ
  exact ⟨⟨e, f, heQ, hfQ, hef⟩, heW, hfW⟩

omit [Finite K] in
theorem finrank_inf_perp_add_two {W : Submodule K V} (P : HypPair Q) (he : P.e ∈ W)
    (hf : P.f ∈ W) : finrank K ↥(W ⊓ P.perp) + 2 = finrank K W := by
  set S : Submodule K V := Submodule.span K {P.e, P.f} with hS
  have hSW : S ≤ W := by
    rw [hS, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact he
    · exact hf
  have hli : LinearIndependent K ![P.e, P.f] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun z => polar Q z P.f) hab
    have h2 := congrArg (fun z => polar Q z P.e) hab
    simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff, P.polar_fe, P.polar_ee,
      polar_zero_left, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  have hSdim : finrank K S = 2 := by
    have hr : ({P.e, P.f} : Set V) = Set.range ![P.e, P.f] := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hS, hr, finrank_span_eq_card hli]
    simp
  have hdisj : S ⊓ (W ⊓ P.perp) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxW⟩ := Submodule.mem_inf.mp hx
    obtain ⟨-, hxp⟩ := Submodule.mem_inf.mp hxW
    obtain ⟨a, b, rfl⟩ : ∃ a b : K, x = a • P.e + b • P.f := by
      rw [hS, Submodule.mem_span_pair] at hxS
      obtain ⟨a, b, h⟩ := hxS
      exact ⟨a, b, h.symm⟩
    rw [HypPair.mem_perp] at hxp
    have h1 := hxp.1
    have h2 := hxp.2
    simp only [polar_add_right, polar_smul_right_eq, P.polar_ef, P.polar_ee, P.polar_fe,
      P.polar_ff, mul_one, mul_zero, zero_add, add_zero] at h1 h2
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  have hsup : S ⊔ (W ⊓ P.perp) = W := by
    refine le_antisymm (sup_le hSW inf_le_left) fun x hx => ?_
    rw [P.eq_add_proj x]
    refine Submodule.add_mem_sup (S.add_mem (S.smul_mem _ (Submodule.subset_span (by simp)))
      (S.smul_mem _ (Submodule.subset_span (by simp)))) ⟨?_, P.proj_mem_perp x⟩
    rw [HypPair.proj]
    exact W.sub_mem (W.sub_mem hx (W.smul_mem _ he)) (W.smul_mem _ hf)
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (W ⊓ P.perp)
  rw [hsup, hdisj, finrank_bot, add_zero, hSdim] at h
  omega

theorem exists_three_hypPairs_in {W : Submodule K V} (hW : PolarNondegOn Q W)
    (h8 : 8 ≤ finrank K W) :
    ∃ P₁ P₂ P₃ : HypPair Q, P₁.e ∈ W ∧ P₁.f ∈ W ∧ P₂.e ∈ W ∧ P₂.f ∈ W ∧ P₃.e ∈ W ∧
      P₃.f ∈ W ∧ P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  obtain ⟨P₁, h1e, h1f⟩ := exists_hypPair_in hW (by omega)
  have hW₁r : PolarNondegOn Q (W ⊓ P₁.perp) := hW.inf_perp P₁ h1e h1f
  have hW₁d := finrank_inf_perp_add_two P₁ h1e h1f
  obtain ⟨P₂, h2e, h2f⟩ := exists_hypPair_in hW₁r (by omega)
  have hW₂r : PolarNondegOn Q ((W ⊓ P₁.perp) ⊓ P₂.perp) := hW₁r.inf_perp P₂ h2e h2f
  have hW₂d := finrank_inf_perp_add_two P₂ h2e h2f
  obtain ⟨P₃, h3e, h3f⟩ := exists_hypPair_in hW₂r (by omega)
  have hp1 : ∀ x ∈ W ⊓ P₁.perp, polar Q P₁.e x = 0 ∧ polar Q P₁.f x = 0 := fun x hx =>
    HypPair.mem_perp.mp (Submodule.mem_inf.mp hx).2
  have hp2 : ∀ x ∈ (W ⊓ P₁.perp) ⊓ P₂.perp, polar Q P₂.e x = 0 ∧ polar Q P₂.f x = 0 :=
    fun x hx => HypPair.mem_perp.mp (Submodule.mem_inf.mp hx).2
  have h3e1 : P₃.e ∈ W ⊓ P₁.perp := (Submodule.mem_inf.mp h3e).1
  have h3f1 : P₃.f ∈ W ⊓ P₁.perp := (Submodule.mem_inf.mp h3f).1
  refine ⟨P₁, P₂, P₃, h1e, h1f, (Submodule.mem_inf.mp h2e).1, (Submodule.mem_inf.mp h2f).1,
    (Submodule.mem_inf.mp h3e1).1, (Submodule.mem_inf.mp h3f1).1, ⟨(hp1 _ h2e).1, (hp1 _ h2f).1,
    (hp1 _ h2e).2, (hp1 _ h2f).2⟩, ⟨(hp1 _ h3e1).1, (hp1 _ h3f1).1, (hp1 _ h3e1).2,
    (hp1 _ h3f1).2⟩, ⟨(hp2 _ h3e).1, (hp2 _ h3f).1, (hp2 _ h3e).2, (hp2 _ h3f).2⟩⟩

end Pairs

end CFSG.LieType.SeitzGeneration
