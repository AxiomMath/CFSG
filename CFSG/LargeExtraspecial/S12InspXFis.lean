module

public import CFSG.LargeExtraspecial.S12InspXNd
public import CFSG.Monster.B.TwoA.Base.SymFiveAut
public import CFSG.Quasithin.Background.G118S3
public import CFSG.Fischer.Classification.Recognition.SymOOrth
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
public import CFSG.LargeExtraspecial.S12DWCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12Insp4

open Matrix CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem card_outer_eq_one {Y : Type*} [Group Y]
    (h : ∀ ψ : MulAut Y, ∃ g : Y, ψ = MulAut.conj g) : Nat.card (Outer Y) = 1 := by
  have htop : inner Y = ⊤ := by
    rw [eq_top_iff]
    rintro ψ -
    obtain ⟨g, rfl⟩ := h ψ
    exact ⟨g, rfl⟩
  show (inner Y).index = 1
  rw [htop, Subgroup.index_top]

theorem card_of_perm {X : Type} [Group X] {m : ℕ} (φ : X ≃* Equiv.Perm (Fin m)) :
    Nat.card X = m.factorial := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem false_of_perm_three {X : Type} [Group X] (φ : X ≃* Equiv.Perm (Fin 3))
    (h3 : 3 ^ 4 ∣ Nat.card X * Nat.card (Outer X)) : False := by
  have hO : Nat.card (Outer X) = 1 := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    refine card_outer_eq_one fun ψ => ?_
    obtain ⟨g, hg⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner ψ
    exact ⟨g, MulEquiv.ext fun x => (hg x).trans (MulAut.conj_apply g x).symm⟩
  rw [hO, card_of_perm φ] at h3
  exact absurd h3 (by decide)

theorem false_of_perm_five {X : Type} [Group X] (φ : X ≃* Equiv.Perm (Fin 5))
    (h3 : 3 ^ 4 ∣ Nat.card X * Nat.card (Outer X)) : False := by
  have hO : Nat.card (Outer X) = 1 := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    refine card_outer_eq_one fun ψ => ?_
    obtain ⟨g, hg⟩ := CFSG.Monster.B.TwoA.sym5_conj_surjective ψ
    exact ⟨g, hg.symm⟩
  rw [hO, card_of_perm φ] at h3
  exact absurd h3 (by decide)

theorem card_fischerSp {m : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    Nat.card (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) := by
  have hB : b.IsAlt := halt
  have hBnd : b.Nondegenerate := by
    refine ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => ?_⟩
    have h := hB.self_eq_zero (x + y)
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, halt, halt, hy x, zero_add, add_zero, zero_add] at h
    exact h
  have hmap : (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
      TauCeti.BilinForm.isometryGroup b := by
    ext L
    rw [Subgroup.mem_map_equiv, CFSG.Fischer.Classification.mem_fischerMatrixGroup_bilin_iff,
      TauCeti.BilinForm.mem_isometryGroup_iff]
    refine forall₂_congr fun x y => ?_
    rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply]
  rw [Nat.card_congr
    (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
      (MulEquiv.subgroupCongr hmap)).toEquiv]
  exact CFSG.Fischer.Classification.Recognition.SymO.card_isometryGroup_two b hB hBnd
    (by rw [Module.finrank_fin_fun])

theorem false_of_sp {X : Type} [Group X] {D : Set X} {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7) : False := by
  obtain ⟨φ, -⟩ := hmod
  have h9 : 9 ≤ m ^ 2 := by nlinarith
  refine false_of_two_pow_dvd h2 (a := m ^ 2) (by omega) ?_
  rw [Nat.card_congr φ.toEquiv, card_fischerSp halt hnd]
  exact dvd_mul_right _ _

theorem false_of_orth {X : Type} [Group X] {D : Set X} {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))
    (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7) : False := by
  obtain ⟨φ, -⟩ := hmod
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    refine ⟨fun x hx => hnd x fun y => hx y, fun y hy => hnd y fun x => ?_⟩
    rw [QuadraticMap.polar_comm]
    exact hy x
  have hcl : (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x) = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap rfl
  have hcm : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
        (TauCeti.QuadraticMap.orthogonalGroup Q).map
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2))
      (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hcX : Nat.card X = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [Nat.card_congr φ.toEquiv, hcl, hcm,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hprod := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_mul_ncard_eq hQnd
    (m := m) (by rw [Module.finrank_fin_fun])
  set N := {v : Fin (2 * m) → ZMod 2 | Q v = 0}.ncard with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨0, by simp⟩ |>.ne'
  have hNle : N ≤ 2 ^ (2 * m) := by
    calc N ≤ Nat.card (Fin (2 * m) → ZMod 2) := Set.ncard_le_card _
      _ = 2 ^ (2 * m) := by
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨a, r, hr, hNa⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have ha : a ≤ 2 * m := by
    have h1 : 2 ^ a ≤ 2 ^ (2 * m) :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) ⟨r, hNa⟩) hNle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hdvd : 2 ^ (m ^ 2) ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * 2 ^ a * r := by
    rw [mul_assoc, ← hNa, hprod]
    exact dvd_mul_right _ _
  have hdvd' : 2 ^ (m ^ 2) ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * 2 ^ a :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hr)) hdvd
  have hsq : 2 * m + 8 ≤ m ^ 2 := by nlinarith
  set s := m ^ 2 with hs
  have hdvd'' : 2 ^ (s - a) ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [show s = (s - a) + a by omega, pow_add] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd'
  exact false_of_two_pow_dvd h2 (a := s - a) (by omega) (hcX ▸ hdvd'')

theorem false_of_fi {X : Type} [Group X] (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7)
    (h : Nat.card X = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∨
      Nat.card X = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∨
      Nat.card X = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) : False := by
  rcases h with h | h | h
  · exact false_of_two_pow_dvd h2 (a := 17) (by norm_num) (by rw [h]; norm_num)
  · exact false_of_two_pow_dvd h2 (a := 18) (by norm_num) (by rw [h]; norm_num)
  · exact false_of_two_pow_dvd h2 (a := 22) (by norm_num) (by rw [h]; norm_num)

end CFSG.LargeExtraspecial.S12Insp4
