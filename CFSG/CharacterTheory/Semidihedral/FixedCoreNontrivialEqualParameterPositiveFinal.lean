module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveLayer

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open _root_.CFSG.Semidihedral.FixedCoreNontrivial.Positive

namespace PositiveInputs

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem mod_four_ne_one (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) : p ^ f % 4 ≠ 1 := by
  intro he
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, -, hbodd, hb1, -, -⟩ := hI.numerics h he
  obtain ⟨Q, ⟨TQ, hTQ⟩, -, -, hFodd, hBO, hBcop⟩ := hI.exists_torus_sylow h he
  obtain ⟨R, -, Y, O, ⟨TR, hTR⟩, -, -, hOY, hRinv, hXcard⟩ := hI.exists_layer_sylow h he
  set B := (N t).map (C t).subtype with hB
  set Fq := Subgroup.normalizer (Q : Set G) with hFq
  set OF := (CFSG.pPrimeCore 2 Fq).map Fq.subtype with hOF
  set X := O ⊔ B with hX
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G TR TQ
  have hRQ : R.map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hTQ, ← hg, coe_smul_sylow, hTR]
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (sup_le_sup_right hOY B).trans hRinv
  have hXgN : X.map (MulAut.conj g).toMonoidHom ≤ Fq := by
    rintro _ ⟨x, hx, rfl⟩
    have hmem := conj_mem_normalizer_map g (hXR hx)
    rw [hRQ] at hmem
    exact hmem
  have hXgodd : Odd (Nat.card (X.map (MulAut.conj g).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
    exact hbodd.pow
  have hXgO : X.map (MulAut.conj g).toMonoidHom ≤ OF := fun x hx =>
    hFodd x (hXgN hx) (odd_orderOf_of_mem hXgodd hx)
  have hdvd : Nat.card B ^ 2 ∣ Nat.card OF := by
    have h1 := Subgroup.card_dvd_of_le hXgO
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard] at h1
  have hOFcard : Nat.card OF = Nat.card B * B.relIndex OF := by
    have h1 := Subgroup.relIndex_mul_card B OF
    rw [inf_eq_left.mpr hBO] at h1
    rw [← h1]
    ring
  rw [hOFcard, pow_two] at hdvd
  have h2 : Nat.card B ∣ B.relIndex OF := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd
  have h3 : Nat.card B = 1 := Nat.Coprime.eq_one_of_dvd hBcop h2
  omega

end PositiveInputs

end CFSG.Semidihedral.FixedCoreNontrivial
