module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoOdd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem mulAut_eq_one_of_card_le_four {D : Type} [Group D] [Finite D] (hD : Nat.card D ≤ 4)
    (α : MulAut D) (a : ℕ) (hα : α ^ (5 ^ a) = 1) : α = 1 := by
  classical
  have : Fintype D := Fintype.ofFinite D
  have h1 : orderOf α ∣ 5 ^ a := orderOf_dvd_of_pow_eq_one hα
  have hinj : Function.Injective (MulAut.toPerm D) := fun x y h => by
    ext d; exact congrArg (fun f => f d) h
  have h2 : orderOf (MulAut.toPerm D α) ∣ (Nat.card D).factorial := by
    have := orderOf_dvd_natCard (MulAut.toPerm D α)
    rwa [Nat.card_eq_fintype_card (α := Equiv.Perm D), Fintype.card_perm,
      ← Nat.card_eq_fintype_card] at this
  have h3 : orderOf (MulAut.toPerm D α) = orderOf α := orderOf_injective _ hinj α
  rw [h3] at h2
  have h4 : orderOf α ∣ 24 := by
    refine h2.trans ?_
    interval_cases (Nat.card D) <;> decide
  have h5 : orderOf α ∣ Nat.gcd (5 ^ a) 24 := Nat.dvd_gcd h1 h4
  have h6 : Nat.gcd (5 ^ a) 24 = 1 := by
    have : Nat.Coprime (5 ^ a) 24 := Nat.Coprime.pow_left a (by norm_num)
    exact this
  rw [h6] at h5
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

theorem dih_cyc_index {M : Type} [Group M] [Finite M]
    (hM : CFSG.GorensteinWalter.HasDihedralSylowTwo M) (D : Subgroup M) (hD : IsPGroup 2 D) :
    ∃ x ∈ D, Nat.card D ≤ 2 * orderOf x := by
  classical
  obtain ⟨S, hDS⟩ := hD.exists_le_sylow
  obtain ⟨m, hm1, ⟨e⟩⟩ := hM S
  let H : Subgroup (DihedralGroup (2 ^ m)) := (D.subgroupOf (S : Subgroup M)).map e.toMonoidHom
  let ψ : ↥D ≃* ↥H :=
    (Subgroup.subgroupOfEquivOfLe hDS).symm.trans (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
  have hcard : Nat.card D = Nat.card H := Nat.card_congr ψ.toEquiv
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm1 H with hc | ⟨k, hk, ⟨f⟩⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥H)
    refine ⟨((ψ.symm g : ↥D) : M), (ψ.symm g).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg, hcard]
    omega
  · refine ⟨((ψ.symm (f.symm (DihedralGroup.r 1)) : ↥D) : M), (ψ.symm (f.symm (DihedralGroup.r 1))).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one, hcard,
      Nat.card_congr f.toEquiv, DihedralGroup.nat_card]

theorem dih_mulAut_trivial {M : Type} [Group M] [Finite M]
    (hM : CFSG.GorensteinWalter.HasDihedralSylowTwo M) (D : Subgroup M) (hD : IsPGroup 2 D)
    (α : MulAut ↥D) (a : ℕ) (hα : α ^ (5 ^ a) = 1) : α = 1 := by
  classical
  by_cases hcard : Nat.card D ≤ 4
  · exact mulAut_eq_one_of_card_le_four hcard α a hα
  · push Not at hcard
    obtain ⟨S, hDS⟩ := hD.exists_le_sylow
    obtain ⟨m, hm1, ⟨e⟩⟩ := hM S
    have hS2 : IsPGroup 2 ↥(S : Subgroup M) := S.isPGroup'
    have hdih : IsDihedral ↥(S : Subgroup M) :=
      (P27.S45.isDihedral_iff_two_group hS2).2 ⟨m, hm1, ⟨e⟩⟩
    have hK : ¬ IsKleinFour ↥D := fun h => by have := h.card_four; omega
    have hA : IsPGroup 2 (MulAut ↥D) :=
      Signalizer.L52Two.isPGroup_mulAut_of_le hS2 (Or.inr hdih) hDS hK
    obtain ⟨k, hk⟩ := hA α
    have h1 : α ^ Nat.gcd (2 ^ k) (5 ^ a) = 1 := pow_gcd_eq_one.mpr ⟨hk, hα⟩
    have h2 : Nat.gcd (2 ^ k) (5 ^ a) = 1 := Nat.Coprime.pow k a (by norm_num)
    rw [h2, pow_one] at h1
    exact h1

theorem exists_equivariant_aut {X M : Type} [Group X] [Group M] [Finite M] (φ : X →* M)
    (hφ : Function.Surjective φ) (c : MulAut X) (hc : ∀ x, φ x = 1 → φ (c x) = 1) :
    ∃ α : MulAut M, ∀ x, φ (c x) = α (φ x) := by
  classical
  let ψ : X →* M := φ.comp c.toMonoidHom
  have hker : φ.ker ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hc x hx
  let f : M →* M :=
    MonoidHom.liftOfRightInverse φ (Function.surjInv hφ) (Function.rightInverse_surjInv hφ) ⟨ψ, hker⟩
  have hf : ∀ x, f (φ x) = φ (c x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)
      ⟨ψ, hker⟩ x
  have hfs : Function.Surjective f := by
    intro m
    obtain ⟨x, rfl⟩ := hφ m
    obtain ⟨y, rfl⟩ := c.surjective x
    exact ⟨φ y, hf y⟩
  have hfb : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hfs, hfs⟩
  exact ⟨MulEquiv.ofBijective f hfb, fun x => (hf x).symm⟩

theorem exists_equivariant_aut_pow {X M : Type} [Group X] [Group M] [Finite M] (φ : X →* M)
    (hφ : Function.Surjective φ) (c : MulAut X) (hc : ∀ x, φ x = 1 → φ (c x) = 1) (a : ℕ)
    (hca : c ^ (5 ^ a) = 1) :
    ∃ α : MulAut M, (∀ x, φ (c x) = α (φ x)) ∧ α ^ (5 ^ a) = 1 := by
  obtain ⟨α, hα⟩ := exists_equivariant_aut φ hφ c hc
  refine ⟨α, hα, ?_⟩
  have hpow : ∀ (n : ℕ) (x : X), (α ^ n) (φ x) = φ ((c ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ α, MulAut.mul_apply, ← hα x, ih, pow_succ c, MulAut.mul_apply]
  ext m
  obtain ⟨x, rfl⟩ := hφ m
  rw [hpow, hca]
  simp

theorem aut_trivial_on {M : Type} [Group M] [Finite M]
    (hM : CFSG.GorensteinWalter.HasDihedralSylowTwo M) (D : Subgroup M) (hD : IsPGroup 2 D)
    (α : MulAut M) (hαD : ∀ d ∈ D, α d ∈ D) (a : ℕ) (hα : α ^ (5 ^ a) = 1) :
    ∀ d ∈ D, α d = d := by
  classical
  let β₀ : ↥D →* ↥D :=
    { toFun := fun d => ⟨α d, hαD d d.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun x y => Subtype.ext (map_mul α (x : M) (y : M)) }
  have hβinj : Function.Injective β₀ := fun x y h =>
    Subtype.ext (α.injective (congrArg Subtype.val h))
  have : Finite D := inferInstance
  have hβb : Function.Bijective β₀ := ⟨hβinj, Finite.injective_iff_surjective.mp hβinj⟩
  let β : MulAut ↥D := MulEquiv.ofBijective β₀ hβb
  have hβval : ∀ d : ↥D, ((β d : ↥D) : M) = α (d : M) := fun d => rfl
  have hβpow : ∀ (n : ℕ) (d : ↥D), (((β ^ n) d : ↥D) : M) = (α ^ n) (d : M) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [pow_succ β, MulAut.mul_apply, ih (β d), hβval, pow_succ α, MulAut.mul_apply]
  have hβ : β ^ (5 ^ a) = 1 := by
    ext d
    rw [hβpow, hα]
    simp
  have := dih_mulAut_trivial hM D hD β a hβ
  intro d hd
  have h1 := congrArg (fun γ : MulAut ↥D => (γ ⟨d, hd⟩ : M)) this
  simpa [β, β₀] using h1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
