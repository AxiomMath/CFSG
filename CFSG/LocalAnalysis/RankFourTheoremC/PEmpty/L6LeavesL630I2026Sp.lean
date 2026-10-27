module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Claim
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Core
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
public import CFSG.LargeExtraspecial.S45QPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

open CFSG.Open CFSG.LocalAnalysis.GorensteinLyons
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped commutatorElement IsMulCommutative

section Helpers

variable {G : Type} [Group G]

theorem comm_mul_central_left {s c y : G} (hc : c ∈ Subgroup.center G) :
    s * c * y * (s * c)⁻¹ * y⁻¹ = s * y * s⁻¹ * y⁻¹ := by
  have h1 : c * y * c⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.mp hc y]
    group
  calc s * c * y * (s * c)⁻¹ * y⁻¹ = s * (c * y * c⁻¹) * s⁻¹ * y⁻¹ := by group
    _ = s * y * s⁻¹ * y⁻¹ := by rw [h1]

theorem comm_mul_central_right {s y c : G} (hc : c ∈ Subgroup.center G) :
    s * (y * c) * s⁻¹ * (y * c)⁻¹ = s * y * s⁻¹ * y⁻¹ := by
  have h1 : c * s⁻¹ * c⁻¹ = s⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hc s⁻¹]
    group
  calc s * (y * c) * s⁻¹ * (y * c)⁻¹ = s * y * (c * s⁻¹ * c⁻¹) * y⁻¹ := by group
    _ = s * y * s⁻¹ * y⁻¹ := by rw [h1]

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_hom_perm_six {X S : Subgroup G} {α β γ δ z : G} (hpres : QDPres S α β γ δ z)
    (hzc : z ∈ Subgroup.center G)
    (hC : ∀ g : G, (∀ s ∈ S, g * s = s * g) → g ∈ Subgroup.center G)
    (hsz : ∀ c ∈ Subgroup.center G, c * c = 1 → c = 1 ∨ c = z)
    (hST : S ≤ pCoreOf 2 X)
    (hTS : ∀ t ∈ pCoreOf 2 X, ∃ s ∈ S, s⁻¹ * t ∈ Subgroup.center G) :
    ∃ ι : ↥X →* Equiv.Perm (Fin 6),
      ∀ g : ↥X, ι g = 1 → (g : G) ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : pCoreOf 2 X ≤ X := pCoreOf_le_self 2 X
  set D : Subgroup ↥X := (pCoreOf 2 X).subgroupOf X with hDdef
  haveI hDn : D.Normal := pCoreOf_subgroupOf_normal 2 X
  have hDmem : ∀ x : ↥D, ((x : ↥X) : G) ∈ pCoreOf 2 X := fun x => x.2
  have hDmk : ∀ (t : G) (ht : t ∈ pCoreOf 2 X), (⟨t, hTX ht⟩ : ↥X) ∈ D := fun t ht => ht
  let sD : ∀ s ∈ S, ↥D := fun s hs => ⟨⟨s, hTX (hST hs)⟩, hDmk s (hST hs)⟩
  have hcen : ∀ x : ↥D, x ∈ Subgroup.center ↥D ↔ ((x : ↥X) : G) ∈ Subgroup.center G := by
    intro x
    constructor
    · intro hx
      apply hC
      intro s hs
      have h1 := Subgroup.mem_center_iff.mp hx (sD s hs)
      exact (congrArg (fun y : ↥D => ((y : ↥X) : G)) h1).symm
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp hx (y : ↥X)))
  have hdec : ∀ x : ↥D, ∃ s ∈ S, ∃ c ∈ Subgroup.center G, ((x : ↥X) : G) = s * c := by
    intro x
    obtain ⟨s, hs, hsc⟩ := hTS _ (hDmem x)
    exact ⟨s, hs, s⁻¹ * ((x : ↥X) : G), hsc, by group⟩
  have hsq : ∀ x : ↥D, x * x ∈ Subgroup.center ↥D := by
    intro x
    rw [hcen]
    obtain ⟨s, hs, c, hc, hx⟩ := hdec x
    show ((x : ↥X) : G) * ((x : ↥X) : G) ∈ Subgroup.center G
    rw [hx]
    have hcs := Subgroup.mem_center_iff.mp hc s
    have h1 : s * c * (s * c) = (s * s) * (c * c) := by
      calc s * c * (s * c) = s * (c * s) * c := by simp only [mul_assoc]
        _ = s * (s * c) * c := by rw [← hcs]
        _ = s * s * (c * c) := by simp only [mul_assoc]
    rw [h1]
    refine Subgroup.mul_mem _ ?_ (Subgroup.mul_mem _ hc hc)
    rcases hpres.sq s hs with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact hzc
  let z' : ↥D := sD z hpres.z_mem
  have hz'c : z' ∈ Subgroup.center ↥D := (hcen z').mpr hzc
  have hzz : ∀ x y : ↥D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z' := by
    intro x y
    obtain ⟨s, hs, c, hc, hx⟩ := hdec x
    obtain ⟨s', hs', c', hc', hy⟩ := hdec y
    have h1 : (((⁅x, y⁆ : ↥D) : ↥X) : G) = s * s' * s⁻¹ * s'⁻¹ := by
      have h2 : (((⁅x, y⁆ : ↥D) : ↥X) : G) = ((x : ↥X) : G) * ((y : ↥X) : G) *
          ((x : ↥X) : G)⁻¹ * ((y : ↥X) : G)⁻¹ := by
        rw [commutatorElement_def]
        rfl
      rw [h2, hx, hy, comm_mul_central_left hc, comm_mul_central_right hc']
    rcases hpres.comm s hs s' hs' with h | h
    · left
      exact Subtype.ext (Subtype.ext (by rw [h1, h]; rfl))
    · right
      exact Subtype.ext (Subtype.ext (by rw [h1, h]))
  have hz'ord : orderOf z' = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact Subtype.ext (Subtype.ext hpres.zz)
    · intro h
      exact hpres.z_ne (congrArg (fun y : ↥D => ((y : ↥X) : G)) h)
  haveI hEA : IsElementaryAbelian 2 (↥D ⧸ Subgroup.center ↥D) := by
    have hcommQ : ∀ a b : ↥D ⧸ Subgroup.center ↥D, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
          have h1 : x * y / (y * x) = ⁅x, y⁆ := by
            simp [commutatorElement_def, div_eq_mul_inv, mul_assoc]
          rw [h1]
          rcases hzz x y with h | h
          · rw [h]
            exact Subgroup.one_mem _
          · rw [h]
            exact hz'c
    exact
      { toIsMulCommutative := ⟨⟨hcommQ⟩⟩
        exponent_dvd_p := by
          apply Monoid.exponent_dvd_of_forall_pow_eq_one
          intro a
          induction a using QuotientGroup.induction_on with
          | H x =>
            rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
            exact hsq x }
  have hcard16 : Nat.card (↥D ⧸ Subgroup.center ↥D) = 16 := by
    let φ : ↥S →* ↥D ⧸ Subgroup.center ↥D :=
      (QuotientGroup.mk' (Subgroup.center ↥D)).comp
        { toFun := fun s => sD (s : G) s.2
          map_one' := rfl
          map_mul' := fun a b => rfl }
    have hφ : Function.Surjective φ := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨s, hs, hsc⟩ := hTS _ (hDmem x)
        refine ⟨⟨s, hs⟩, ?_⟩
        show (QuotientGroup.mk' _ (sD s hs) : ↥D ⧸ Subgroup.center ↥D) = (x : ↥D ⧸ _)
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq, hcen]
        exact hsc
    have hkerφ : ∀ s : ↥S, s ∈ φ.ker ↔ (s : G) = 1 ∨ (s : G) = z := by
      intro s
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : sD (s : G) s.2 ∈ Subgroup.center ↥D := (QuotientGroup.eq_one_iff _).mp h
        have h2 := (hcen _).mp h1
        exact hpres.center s s.2 (fun t ht => (Subgroup.mem_center_iff.mp h2 t).symm)
      · intro h
        show (QuotientGroup.mk' _ (sD (s : G) s.2) : ↥D ⧸ Subgroup.center ↥D) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen]
        show (s : G) ∈ Subgroup.center G
        rcases h with h | h
        · rw [h]
          exact Subgroup.one_mem _
        · rw [h]
          exact hzc
    have hkc : Nat.card φ.ker = 2 := by
      rw [Nat.card_eq_two_iff' (1 : ↥φ.ker)]
      refine ⟨⟨⟨z, hpres.z_mem⟩, (hkerφ _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
      · intro h
        exact hpres.z_ne (congrArg (fun y : ↥φ.ker => ((y : ↥S) : G)) h)
      · intro y hy
        rcases (hkerφ y.1).mp y.2 with h1 | h1
        · exact absurd (Subtype.ext (Subtype.ext h1)) hy
        · exact Subtype.ext (Subtype.ext h1)
    have h := Subgroup.card_ker_mul_card_of_surjective hφ
    rw [hkc, hpres.card] at h
    omega
  set b : LinearMap.BilinForm (ZMod 2) (Additive (↥D ⧸ Subgroup.center ↥D)) :=
    commSignForm hzz hz'ord with hb
  have hba : b.IsAlt := commSignForm_isAlt hzz hz'ord
  have hbn : b.Nondegenerate := commSignForm_nondegenerate hzz hz'ord
  haveI : Module.Finite (ZMod 2) (Additive (↥D ⧸ Subgroup.center ↥D)) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive (↥D ⧸ Subgroup.center ↥D)) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (↥D ⧸ Subgroup.center ↥D))
    have hV16 : Nat.card (Additive (↥D ⧸ Subgroup.center ↥D)) = 16 := by
      rw [Nat.card_congr (Additive.ofMul : (↥D ⧸ Subgroup.center ↥D) ≃
        Additive (↥D ⧸ Subgroup.center ↥D)).symm]
      exact hcard16
    rw [hV16, Nat.card_zmod] at h1
    have h4 : (2 : ℕ) ^ 4 = 2 ^ Module.finrank (ZMod 2) (Additive (↥D ⧸ Subgroup.center ↥D)) := by
      rw [← h1]
      norm_num
    exact (Nat.pow_right_injective le_rfl h4).symm
  obtain ⟨Φ⟩ := CFSG.LargeExtraspecial.S45Q.nonempty_isometryGroup_equiv_perm hba hbn hfin
  set ρ := centerQuotientConjGL D with hρ
  have hV : ∀ v : Additive (↥D ⧸ Subgroup.center ↥D),
      ∃ x : ↥D, v = Additive.ofMul (x : ↥D ⧸ Subgroup.center ↥D) := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, by rw [hx]; rfl⟩
  have hiso : ∀ h : ↥X, ρ h ∈ bilinIsometryGroup b := by
    intro h v w
    obtain ⟨x, rfl⟩ := hV v
    obtain ⟨y, rfl⟩ := hV w
    rw [hρ, centerQuotientConjGL_apply, centerQuotientConjGL_apply, hb, commSignForm_apply,
      commSignForm_apply]
    unfold commSign
    rw [← map_commutatorElement, MulEquiv.map_eq_one_iff]
  let ρ₂ : ↥X →* (Additive (↥D ⧸ Subgroup.center ↥D) ≃ₗ[ZMod 2]
      Additive (↥D ⧸ Subgroup.center ↥D)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (↥D ⧸ Subgroup.center ↥D))).toMonoidHom.comp ρ
  have hρ₂ : ∀ g, ρ₂ g ∈ TauCeti.BilinForm.isometryGroup b := fun g =>
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr (fun x y => hiso g x y)
  refine ⟨Φ.toMonoidHom.comp (ρ₂.codRestrict (TauCeti.BilinForm.isometryGroup b) hρ₂),
    fun g hg => ?_⟩
  have h1 : ρ₂.codRestrict (TauCeti.BilinForm.isometryGroup b) hρ₂ g = 1 := by
    apply Φ.injective
    rw [map_one]
    exact hg
  have h2 : ρ₂ g = 1 := congrArg Subtype.val h1
  have h3 : ρ g = 1 :=
    (MulEquiv.map_eq_one_iff (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (↥D ⧸ Subgroup.center ↥D)))).mp h2
  have h4 : ∀ x : ↥D, ((MulAut.conjNormal g x : ↥D) : ↥D ⧸ Subgroup.center ↥D) =
      (x : ↥D ⧸ Subgroup.center ↥D) := by
    intro x
    have h5 : ((ρ g : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (↥D ⧸ Subgroup.center ↥D))) :
        Module.End (ZMod 2) (Additive (↥D ⧸ Subgroup.center ↥D)))
        (Additive.ofMul (x : ↥D ⧸ Subgroup.center ↥D)) =
        Additive.ofMul (x : ↥D ⧸ Subgroup.center ↥D) := by
      rw [h3]
      rfl
    rw [hρ, centerQuotientConjGL_apply] at h5
    exact Additive.ofMul.injective h5
  have h5 : ∀ t ∈ pCoreOf 2 X, (g : G) * t * (g : G)⁻¹ * t⁻¹ ∈ Subgroup.center G := by
    intro t ht
    have hx := QuotientGroup.eq_iff_div_mem.mp (h4 ⟨⟨t, hTX ht⟩, hDmk t ht⟩)
    have := (hcen _).mp hx
    simpa [MulAut.conjNormal_apply, div_eq_mul_inv] using this
  have hmem : (g : G) ∈ commNormalizer S := fun s hs => h5 s (hST hs)
  obtain ⟨s₀, hs₀, hc⟩ := claimB hpres hzc hC hsz hmem
  have hcX : (g : G) * s₀⁻¹ ∈ X := X.mul_mem g.2 (X.inv_mem (hTX (hST hs₀)))
  have hcore := center_le_core X hc hcX
  have hg' : (g : G) = ((g : G) * s₀⁻¹) * s₀ := by group
  rw [hg']
  exact Subgroup.mul_mem _ hcore (Subgroup.mem_sup_right (hST hs₀))

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026
