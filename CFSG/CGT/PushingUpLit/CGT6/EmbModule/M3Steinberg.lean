module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTTwist
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTFinrank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAInj
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Count

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.CharacterTheory.SteinbergBY CFSG.GH74.GLS.Stage4.Rest
open scoped TensorProduct

section P1

variable {p n : ℕ} {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]

theorem m3_simple (hp : p.Prime) (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) :
    IsSimpleModule (MonoidAlgebra L (SLm F)) (steinbergRep F L A).asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hA' : A < Nat.card F := hF ▸ hA
  have hne : (⊥ : Subrepresentation (steinbergRep F L A)) ≠ ⊤ := by
    intro h
    have h1 : xVec F L A ∈ (⊥ : Subrepresentation (steinbergRep F L A)).toSubmodule := by
      rw [h]; trivial
    have h2 : xVec F L A = 0 := (Submodule.mem_bot L).mp h1
    exact monoFun_x_ne_zero (F := F) (L := L) A (congrArg Subtype.val h2)
  exact
    { exists_pair_ne := ⟨⊥, ⊤, hne⟩
      eq_bot_or_eq_top := fun σ => by
        by_cases h : σ = ⊥
        · exact Or.inl h
        · refine Or.inr ?_
          have h1 : σ.toSubmodule ≠ ⊥ := fun h0 => h (Subrepresentation.ext h0)
          obtain ⟨s, hs, hs0⟩ := Submodule.ne_bot_iff _ |>.mp h1
          exact eq_top_of_mem_ne_zero hp hF hA' σ hs hs0 }

theorem m3_finrank (hp : p.Prime) (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) :
    Module.finrank L (steinbergSub F L A) = digitProd p n A := by
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F p := charP_of_card_eq_prime_pow hF'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  have hspan : steinbergSub F L A =
      Submodule.span L (Set.range fun m : monoIdx p n A => monoFun F L m (A - m)) :=
    le_antisymm (steinbergSub_le_span A hA)
      (Submodule.span_le.mpr (by
        rintro _ ⟨m, rfl⟩
        exact monoFun_mem_steinbergSub hF' A hA m.2))
  have hidx : monoIdx p n A = (Finset.range (p ^ n)).filter (fun m => ¬ p ∣ Nat.choose A m) := by
    ext m
    simp [mem_monoIdx]
  rw [hspan, finrank_span_eq_card (linearIndependent_monoFun hF' A), Fintype.card_coe, hidx]
  exact card_filter_not_dvd_choose hp n A hA

theorem m3_inj (hF : Nat.card F = p ^ n) {A A' : ℕ} (hA : A < p ^ n) (hA' : A' < p ^ n)
    (h : Nonempty ((steinbergRep F L A).asModule ≃ₗ[MonoidAlgebra L (SLm F)]
      (steinbergRep F L A').asModule)) : A = A' := by
  obtain ⟨ψ⟩ := h
  have hA1 : A < Nat.card F := hF ▸ hA
  have hA1' : A' < Nat.card F := hF ▸ hA'
  obtain ⟨Ψ, hΨ⟩ := exists_equivariant_of_iso ψ
  have hmod := modEq_of_iso hA1' Ψ hΨ
  by_contra hne
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hneg : (-1 : F) ^ (Nat.card F - 1) = 1 := by
    classical
    have := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one (-1 : F) (neg_ne_zero.mpr one_ne_zero)
    rwa [← Nat.card_eq_fintype_card] at h1
  have hcase : (A = 0 ∧ A' = Nat.card F - 1) ∨ (A = Nat.card F - 1 ∧ A' = 0) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd : Nat.card F - 1 ∣ A' - A := (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have hpos : 0 < A' - A := Nat.sub_pos_of_lt hlt
      have := Nat.le_of_dvd hpos hd
      left
      omega
    · have hd : Nat.card F - 1 ∣ A - A' := (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
      have hpos : 0 < A - A' := Nat.sub_pos_of_lt hgt
      have := Nat.le_of_dvd hpos hd
      right
      omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have htriv := trivial_transfer Ψ hΨ (fun g z => steinbergRep_trivial_zero g z)
    exact steinbergRep_ne_self (A := Nat.card F - 1) (by omega) hneg (htriv _ _)
  · have htriv := trivial_transfer Ψ.symm (equivariant_symm Ψ hΨ)
      (fun g z => steinbergRep_trivial_zero g z)
    exact steinbergRep_ne_self (A := Nat.card F - 1) (by omega) hneg (htriv _ _)

theorem m3_twist (hp : p.Prime) (hF : Nat.card F = p ^ n) (hn : 0 < n) (A : ℕ) :
    ∃ Θ : steinbergSub F F A →+ steinbergSub F F (rot p n A), Function.Bijective Θ ∧
      (∀ (c : F) (x : steinbergSub F F A), Θ (c • x) = c ^ p • Θ x) ∧
      ∀ (g : SLm F) (x : steinbergSub F F A),
        Θ (steinbergRep F F A g x) = steinbergRep F F (rot p n A) g (Θ x) := by
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F p := charP_of_card_eq_prime_pow hF'
  have : RingHomSurjective (frobenius F p) :=
    ⟨Finite.surjective_of_injective (frobenius_inj F p)⟩
  have hmap : Submodule.map (frobFun p) (steinbergSub F F A) = steinbergSub F F (rot p n A) := by
    unfold steinbergSub
    rw [Submodule.map_span, ← Set.range_comp]
    have hfun : (frobFun p ∘ fun g : SLm F => funRep F F g (monoFun F F A 0)) =
        fun g : SLm F => funRep F F g (monoFun F F (rot p n A) 0) := by
      funext g
      show frobFun p (funRep F F g (monoFun F F A 0)) = funRep F F g (monoFun F F (rot p n A) 0)
      rw [frobFun_funRep, frobFun_monoFun hn hF']
    rw [hfun]
  let Θ' : steinbergSub F F A →ₛₗ[frobenius F p] steinbergSub F F (rot p n A) :=
    LinearMap.codRestrict (steinbergSub F F (rot p n A))
      ((frobFun p).domRestrict (steinbergSub F F A))
      (fun x => by rw [← hmap]; exact Submodule.mem_map_of_mem x.2)
  refine ⟨Θ'.toAddMonoidHom, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact frobFun_injective p (congrArg Subtype.val hxy)
  · intro y
    have hy : (y : (Fin 2 → F) → F) ∈ Submodule.map (frobFun p) (steinbergSub F F A) := by
      rw [hmap]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro c x
    exact map_smulₛₗ Θ' c x
  · intro g x
    exact Subtype.ext rfl

end P1

section Complete

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem m3_complete_over (hF : Nat.card F = 2 ^ n) [CharP F 2]
    (k : Type) [Field k] [Algebra F k] [IsAlgClosed k] [CharP k 2]
    (W : Type) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k (SLm F) W) [σ.IsIrreducible] :
    ∃ B : ℕ, B < 2 ^ n ∧ Nonempty (σ.Equiv (steinbergRep F k B)) := by
  have hpf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hirr : ∀ i : Fin (2 ^ n), (steinbergRep F k i.1).IsIrreducible := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
      (m3_simple Nat.prime_two hF i.2)
  have hfd : ∀ i : Fin (2 ^ n), FiniteDimensional k (steinbergSub F k i.1) := fun i =>
    haveI := hirr i
    finiteDimensional_of_isIrreducible (steinbergRep F k i.1)
  have hcard : Fintype.card (PRegularClass 2 (SLm F)) ≤ Fintype.card (Fin (2 ^ n)) := by
    rw [Fintype.card_fin, ← hF']
    exact m3_card_twoRegularClass_le
  have hne : ∀ i j : Fin (2 ^ n), i ≠ j →
      IsEmpty ((steinbergRep F k i.1).Equiv (steinbergRep F k j.1)) := fun i j hij =>
    ⟨fun e => hij (Fin.ext (m3_inj hF i.2 j.2 (steinberg_nonempty_asModule_equiv e)))⟩
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_card_pRegularClass_le_of_univ (k := k) (G := SLm F) 2
    (ι := Fin (2 ^ n)) (V := fun i => ↥(steinbergSub F k i.1)) (fun i => steinbergRep F k i.1)
    hne hcard W σ
    (fun i => ⟨(Module.finBasis k _).equivFun⟩) ⟨(Module.finBasis k W).equivFun⟩
  exact ⟨i.1, i.2, ⟨e⟩⟩

theorem m3_complete (hF : Nat.card F = 2 ^ n)
    (Q : Type) [AddCommGroup Q] [Module F Q] [Module.Finite F Q]
    (π : Representation F (SLm F) Q)
    (hπ : IsSimpleModule (MonoidAlgebra F (SLm F)) π.asModule) :
    ∃ A, A < 2 ^ n ∧ Nonempty (π.asModule ≃ₗ[MonoidAlgebra F (SLm F)]
      (steinbergRep F F A).asModule) := by
  have hpf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow hF'
  have hcharK : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hπirr : π.IsIrreducible := (Representation.irreducible_iff_isSimpleModule_asModule π).mpr hπ
  have hQnt : Nontrivial Q := by
    have := IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) π.asModule
    exact π.asModuleEquiv.symm.toEquiv.nontrivial
  have hk : Nontrivial (AlgebraicClosure F ⊗[F] Q) :=
    (Module.Flat.tensorProduct_mk_injective F Q (AlgebraicClosure F)).nontrivial
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation
    (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) π)
  obtain ⟨B, hB, ⟨e⟩⟩ := m3_complete_over hF (AlgebraicClosure F) U.toSubmodule U.toRepresentation
  have hρirr : (steinbergRep F F B).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (m3_simple Nat.prime_two hF hB)
  have hVnt : Nontrivial (steinbergSub F F B) := by
    have := IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) (steinbergRep F F B).asModule
    exact (steinbergRep F F B).asModuleEquiv.symm.toEquiv.nontrivial
  have : FiniteDimensional F (steinbergSub F F B) :=
    finiteDimensional_of_isIrreducible (steinbergRep F F B)
  let Φ : (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F)
      (steinbergRep F F B)).IntertwiningMap (steinbergRep F (AlgebraicClosure F) B) :=
    ⟨steinbergMulSub F (AlgebraicClosure F) B,
      fun g => LinearMap.ext fun x => steinbergMulSub_rep F _ B g x⟩
  let incl : U.toRepresentation.IntertwiningMap
      (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) π) :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let T := incl.comp (e.symm.toIntertwiningMap.comp Φ)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : steinbergSub F F B)
  have hT : T ≠ 0 := by
    intro h0
    have h1 : T ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) = 0 := by rw [h0]; rfl
    have hΦ : Φ ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) =
        steinbergInclSub F (AlgebraicClosure F) B v₀ := by
      show steinbergMulSub F (AlgebraicClosure F) B ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) = _
      rw [steinbergMulSub_tmul, one_smul]
    have h2 : (e.symm (steinbergInclSub F (AlgebraicClosure F) B v₀) : U.toSubmodule) = 0 := by
      rw [← hΦ]
      exact Subtype.ext h1
    have h3 : steinbergInclSub F (AlgebraicClosure F) B v₀ = 0 := by
      have := congrArg e h2
      rw [Representation.Equiv.apply_symm_apply] at this
      change _ = e.toLinearEquiv 0 at this
      rwa [e.toLinearEquiv.map_zero] at this
    exact hv₀ (steinbergInclSub_injective F (AlgebraicClosure F) B (h3.trans (map_zero _).symm))
  have hnz : ∃ f : (steinbergRep F F B).IntertwiningMap π, f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton ((steinbergRep F F B).IntertwiningMap π) :=
      ⟨fun f g => (hcon f).trans (hcon g).symm⟩
    have hsub' : Subsingleton (AlgebraicClosure F ⊗[F] ((steinbergRep F F B).IntertwiningMap π)) :=
      inferInstance
    obtain ⟨x, hx⟩ := (CFSG.Theory.Representation.intertwiningMapBaseChangeEquiv
      (E := AlgebraicClosure F) (steinbergRep F F B) π).surjective T
    apply hT
    rw [← hx, Subsingleton.elim x 0, map_zero]
  obtain ⟨f, hf⟩ := hnz
  have hbij : Function.Bijective f :=
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  exact ⟨B, hB, ⟨(LinearEquiv.ofBijective (Representation.IntertwiningMap.equivLinearMapAsModule
    (steinbergRep F F B) π f) hbij).symm⟩⟩

end Complete

end CFSG.CGT.PushingUpLit.CGT6
