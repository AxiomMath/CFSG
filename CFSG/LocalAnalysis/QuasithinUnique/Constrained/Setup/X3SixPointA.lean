module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv Subgroup

section EightPoints

variable {Γ : Type*} [Group Γ]

@[expose] def movedPoints (φ : Γ →* Perm (Fin 8)) : Set (Fin 8) := {x | ∃ g, φ g x ≠ x}

theorem orbit_ncard_of_moved (φ : Γ →* Perm (Fin 8)) (e : Γ ≃* alternatingGroup (Fin 6))
    {x : Fin 8} (hx : x ∈ movedPoints φ) : {y | ∃ g, φ g x = y}.ncard = 6 := by
  have hle : {y | ∃ g, φ g x = y}.ncard ≤ 8 := by
    have := Set.ncard_le_card {y | ∃ g, φ g x = y}
    simpa using this
  rcases orbit_card_cases' φ e x with h | ⟨h6, hdvd, h8, -, -⟩
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
    obtain ⟨g, hg⟩ := hx
    have h1 : φ g x ∈ ({a} : Set (Fin 8)) := ha ▸ ⟨g, rfl⟩
    have h2 : x ∈ ({a} : Set (Fin 8)) := ha ▸ ⟨1, by simp⟩
    exact hg ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm)
  · have h7 : {y | ∃ g, φ g x = y}.ncard ≠ 7 := by
      intro h7
      rw [h7] at hdvd
      omega
    omega

theorem exists_mem_movedPoints (φ : Γ →* Perm (Fin 8)) (hφ : Function.Injective φ)
    (e : Γ ≃* alternatingGroup (Fin 6)) : ∃ x, x ∈ movedPoints φ := by
  have hfin : Finite Γ := finite_of_equiv_alt6 e
  have hnt : Nontrivial Γ := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_of_equiv_alt6 e]
    norm_num
  obtain ⟨g, hg⟩ := exists_ne (1 : Γ)
  have hφg : φ g ≠ 1 := fun h => hg (hφ (by rw [h, map_one]))
  by_contra hne
  apply hφg
  refine Equiv.ext fun x => ?_
  by_contra hx
  exact hne ⟨x, g, hx⟩

theorem movedPoints_eq_orbit (φ : Γ →* Perm (Fin 8)) (e : Γ ≃* alternatingGroup (Fin 6))
    {x₀ : Fin 8} (hx₀ : x₀ ∈ movedPoints φ) :
    movedPoints φ = {y | ∃ g, φ g x₀ = y} := by
  ext y
  constructor
  · intro hy
    by_contra hyn
    have hdisj : Disjoint {z | ∃ g, φ g x₀ = z} {z | ∃ g, φ g y = z} := by
      rw [Set.disjoint_left]
      rintro z ⟨g, rfl⟩ ⟨h, hh⟩
      apply hyn
      refine ⟨h⁻¹ * g, ?_⟩
      rw [map_mul, Perm.mul_apply, ← hh, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have h6a := orbit_ncard_of_moved φ e hx₀
    have h6b := orbit_ncard_of_moved φ e hy
    have hu := Set.ncard_union_eq hdisj
    have hle := Set.ncard_le_card ({z | ∃ g, φ g x₀ = z} ∪ {z | ∃ g, φ g y = z})
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega
  · rintro ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := hx₀
    refine ⟨g * h * g⁻¹, ?_⟩
    have : φ (g * h * g⁻¹) (φ g x₀) = φ g (φ h x₀) := by
      simp [map_mul, Perm.mul_apply, map_inv, Equiv.Perm.inv_def]
    rw [this]
    exact fun heq => hh ((φ g).injective heq)

theorem ncard_movedPoints (φ : Γ →* Perm (Fin 8)) (hφ : Function.Injective φ)
    (e : Γ ≃* alternatingGroup (Fin 6)) : (movedPoints φ).ncard = 6 := by
  obtain ⟨x₀, hx₀⟩ := exists_mem_movedPoints φ hφ e
  rw [movedPoints_eq_orbit φ e hx₀]
  exact orbit_ncard_of_moved φ e hx₀

end EightPoints


section Normalizer

variable {G : Type*} [Group G] (π : G →* Perm (Fin 8)) (L : Subgroup G)

theorem mem_moved_of_normalizer {n : G} (hn : n ∈ normalizer (L : Set G)) {x : Fin 8}
    (hx : x ∈ movedPoints (π.comp L.subtype)) : π n x ∈ movedPoints (π.comp L.subtype) := by
  obtain ⟨g, hg⟩ := hx
  have hmem : n * (g : G) * n⁻¹ ∈ L := (mem_normalizer_iff.mp hn g).mp g.2
  refine ⟨⟨n * (g : G) * n⁻¹, hmem⟩, ?_⟩
  have : (π.comp L.subtype) ⟨n * (g : G) * n⁻¹, hmem⟩ (π n x) =
      π n ((π.comp L.subtype) g x) := by
    simp [map_mul, Perm.mul_apply, Equiv.Perm.inv_def]
  rw [this]
  exact fun h => hg ((π n).injective h)

@[expose] def moveAct (n : normalizer (L : Set G)) : Perm (movedPoints (π.comp L.subtype)) :=
  (π n.1).subtypePerm (fun x => ⟨fun h => by
    have := mem_moved_of_normalizer π L (inv_mem n.2) h
    simpa [map_inv, Equiv.Perm.inv_def] using this, mem_moved_of_normalizer π L n.2⟩)

theorem moveAct_apply (n : normalizer (L : Set G)) (x : movedPoints (π.comp L.subtype)) :
    (moveAct π L n x : Fin 8) = π n.1 x := rfl

@[expose] def moveHom : normalizer (L : Set G) →* Perm (movedPoints (π.comp L.subtype)) where
  toFun := moveAct π L
  map_one' := Equiv.ext fun x => Subtype.ext (by simp [moveAct_apply])
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by simp [moveAct_apply])

theorem moveHom_apply (n : normalizer (L : Set G)) (x : movedPoints (π.comp L.subtype)) :
    (moveHom π L n x : Fin 8) = π n.1 x := rfl

theorem moveHom_injective (hπ : Function.Injective π) (hsign : ∀ g, Perm.sign (π g) = 1)
    (eL : L ≃* alternatingGroup (Fin 6)) : Function.Injective (moveHom π L) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  by_contra hne
  have hfix : ∀ x : Fin 8, x ∈ movedPoints (π.comp L.subtype) → π n.1 x = x := by
    intro x hx
    have := congrArg (fun f : Perm (movedPoints (π.comp L.subtype)) => (f ⟨x, hx⟩ : Fin 8)) hn
    simpa [moveHom_apply] using this
  have hn1 : π n.1 ≠ 1 := fun h => hne (Subtype.ext (hπ (by rw [h]; simp)))
  have hcard : (movedPoints (π.comp L.subtype)).ncard = 6 :=
    ncard_movedPoints _ (hπ.comp L.subtype_injective) eL
  have hcompl : (movedPoints (π.comp L.subtype))ᶜ.ncard = 2 := by
    have := Set.ncard_add_ncard_compl (movedPoints (π.comp L.subtype))
    have h8 : Nat.card (Fin 8) = 8 := by simp
    omega
  have hsub : ((π n.1).support : Set (Fin 8)) ⊆ (movedPoints (π.comp L.subtype))ᶜ := by
    intro x hx
    simp only [Finset.mem_coe, Perm.mem_support] at hx
    intro hxm
    exact hx (hfix x hxm)
  have hle : (π n.1).support.card ≤ 2 := by
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset] at this
    omega
  have hne0 : (π n.1).support.card ≠ 0 := by rwa [Ne, Perm.card_support_eq_zero]
  have hne1 := Perm.card_support_ne_one (π n.1)
  have h2 : (π n.1).support.card = 2 := by omega
  have hswap := Perm.card_support_eq_two.mp h2
  have := hswap.sign_eq
  rw [hsign] at this
  exact absurd this (by decide)

open scoped Classical in
theorem moveHom_image (hπ : Function.Injective π) (hsign : ∀ g, Perm.sign (π g) = 1)
    (eL : L ≃* alternatingGroup (Fin 6)) :
    (L.subgroupOf (normalizer (L : Set G))).map (moveHom π L) =
      alternatingGroup (movedPoints (π.comp L.subtype)) := by
  classical
  have hLN : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  have eLN : L.subgroupOf (normalizer (L : Set G)) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.subgroupOfEquivOfLe hLN).trans eL
  have hfin : Finite (L.subgroupOf (normalizer (L : Set G))) := finite_of_equiv_alt6 eLN
  have hsimple : IsSimpleGroup (L.subgroupOf (normalizer (L : Set G))) :=
    isSimpleGroup_of_equiv_alt6 eLN
  have hinj := moveHom_injective π L hπ hsign eL
  let sg : L.subgroupOf (normalizer (L : Set G)) →* ℤˣ :=
    Perm.sign.comp ((moveHom π L).comp (L.subgroupOf (normalizer (L : Set G))).subtype)
  have hker : sg.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal sg.ker with h | h
    · exfalso
      have hsginj : Function.Injective sg := (MonoidHom.ker_eq_bot_iff sg).mp h
      have hle := Nat.card_le_card_of_injective sg hsginj
      rw [card_of_equiv_alt6 eLN, Nat.card_eq_fintype_card, Fintype.card_units_int] at hle
      omega
    · exact h
  have hle : (L.subgroupOf (normalizer (L : Set G))).map (moveHom π L) ≤
      alternatingGroup (movedPoints (π.comp L.subtype)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Perm.mem_alternatingGroup]
    have : (⟨l, hl⟩ : L.subgroupOf (normalizer (L : Set G))) ∈ sg.ker := by rw [hker]; trivial
    simpa [sg] using this
  have hcard : Nat.card (movedPoints (π.comp L.subtype)) = 6 := by
    rw [Nat.card_coe_set_eq]
    exact ncard_movedPoints _ (hπ.comp L.subtype_injective) eL
  have hnt : Nontrivial (movedPoints (π.comp L.subtype)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := two_mul_nat_card_alternatingGroup (α := movedPoints (π.comp L.subtype))
  rw [Nat.card_perm, hcard] at h1
  rw [Subgroup.card_map_of_injective hinj]
  have h2 : Nat.card (L.subgroupOf (normalizer (L : Set G))) = 360 := card_of_equiv_alt6 eLN
  rw [h2]
  have h3 : Nat.card (alternatingGroup (movedPoints (π.comp L.subtype))) = 360 := by
    have h720 : (6 : ℕ).factorial = 720 := by decide
    rw [h720] at h1
    omega
  omega

theorem six_point_of_faithful_even_eight (hπ : Function.Injective π)
    (hsign : ∀ g, Perm.sign (π g) = 1) (eL : L ≃* alternatingGroup (Fin 6)) :
    ∃ θ : normalizer (L : Set G) →* Perm (Fin 6), Function.Injective θ ∧
      (L.subgroupOf (normalizer (L : Set G))).map θ = alternatingGroup (Fin 6) := by
  classical
  have hcard : Nat.card (movedPoints (π.comp L.subtype)) = 6 := by
    rw [Nat.card_coe_set_eq]
    exact ncard_movedPoints _ (hπ.comp L.subtype_injective) eL
  let f : movedPoints (π.comp L.subtype) ≃ Fin 6 := Finite.equivFinOfCardEq hcard
  refine ⟨(f.permCongrHom : _ ≃* _).toMonoidHom.comp (moveHom π L),
    f.permCongrHom.injective.comp (moveHom_injective π L hπ hsign eL), ?_⟩
  rw [← Subgroup.map_map, moveHom_image π L hπ hsign eL]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup] at hτ
    rw [Perm.mem_alternatingGroup]
    simpa [Equiv.permCongrHom_coe, Perm.sign_permCongr] using hτ
  · intro hσ
    refine ⟨f.permCongr.symm σ, ?_, ?_⟩
    · rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
      rw [Perm.mem_alternatingGroup] at hσ
      have := Perm.sign_permCongr f (f.permCongr.symm σ)
      rw [Equiv.apply_symm_apply] at this
      rw [← this]
      exact hσ
    · exact f.permCongr.apply_symm_apply σ

end Normalizer


section Binary

@[expose] def linearEquivConj {F V W : Type*} [Semiring F] [AddCommMonoid V] [Module F V]
    [AddCommMonoid W] [Module F W] (e : V ≃ₗ[F] W) : (V ≃ₗ[F] V) ≃* (W ≃ₗ[F] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by ext; simp
  right_inv h := by ext; simp
  map_mul' g h := by ext; simp

@[expose] noncomputable def linearEquivGLFour {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hV : Module.finrank (ZMod 2) V = 4) :
    (V ≃ₗ[ZMod 2] V) ≃* GL (Fin 4) (ZMod 2) :=
  let e1 : (V ≃ₗ[ZMod 2] V) ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    linearEquivConj (Module.finBasisOfFinrankEq (ZMod 2) V hV).equivFun
  let e2 : GL (Fin 4) (ZMod 2) ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2))
  e1.trans e2.symm

theorem four_binary_normalizer_six_point {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hV : Module.finrank (ZMod 2) V = 4)
    (L : Subgroup (V ≃ₗ[ZMod 2] V)) (hL : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    ∃ θ : normalizer (L : Set (V ≃ₗ[ZMod 2] V)) →* Perm (Fin 6), Function.Injective θ ∧
      (L.subgroupOf (normalizer (L : Set (V ≃ₗ[ZMod 2] V)))).map θ = alternatingGroup (Fin 6) ∧
      ∀ K : Subgroup (V ≃ₗ[ZMod 2] V), L ≤ K → K ≤ normalizer (L : Set (V ≃ₗ[ZMod 2] V)) →
        Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Perm (Fin 6)) := by
  obtain ⟨eL⟩ := hL
  let π : (V ≃ₗ[ZMod 2] V) →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp
      ((CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm.toMonoidHom).comp
        (linearEquivGLFour hV).toMonoidHom)
  have hπ : Function.Injective π :=
    Subtype.val_injective.comp
      (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm.injective.comp
        (linearEquivGLFour hV).injective)
  have hsign : ∀ g, Perm.sign (π g) = 1 := fun g =>
    Perm.mem_alternatingGroup.mp (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm
      (linearEquivGLFour hV g)).2
  obtain ⟨θ, hθinj, hθim⟩ := six_point_of_faithful_even_eight π L hπ hsign eL
  refine ⟨θ, hθinj, hθim, ?_⟩
  intro K hLK hKN
  have hge : alternatingGroup (Fin 6) ≤
      (K.subgroupOf (normalizer (L : Set (V ≃ₗ[ZMod 2] V)))).map θ := by
    rw [← hθim]
    exact Subgroup.map_mono (fun x hx => hLK hx)
  set R := (K.subgroupOf (normalizer (L : Set (V ≃ₗ[ZMod 2] V)))).map θ with hR
  have hd1 : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card R := Subgroup.card_dvd_of_le hge
  have hd2 : Nat.card R ∣ Nat.card (Perm (Fin 6)) := Subgroup.card_subgroup_dvd_card R
  have hperm : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  rw [card_alt6] at hd1
  rw [hperm] at hd2
  have hKequiv : K ≃* R :=
    (Subgroup.subgroupOfEquivOfLe hKN).symm.trans (Subgroup.equivMapOfInjective _ θ hθinj)
  obtain ⟨c, hc⟩ := hd1
  have hc2 : c ∣ 2 := by
    have h1 : 360 * c ∣ 360 * 2 := hc ▸ hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with h1 | h2
  · left
    have hcard : Nat.card R = 360 := by omega
    have heq : alternatingGroup (Fin 6) = R :=
      Subgroup.eq_of_le_of_card_ge hge (by rw [hcard, card_alt6])
    exact ⟨hKequiv.trans (MulEquiv.subgroupCongr heq.symm)⟩
  · right
    have hcard : Nat.card R = Nat.card (Perm (Fin 6)) := by omega
    have heq : R = ⊤ := Subgroup.eq_top_of_card_eq R hcard
    exact ⟨hKequiv.trans ((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv)⟩

end Binary

end CFSG.QuasithinUnique.Setup.X3
