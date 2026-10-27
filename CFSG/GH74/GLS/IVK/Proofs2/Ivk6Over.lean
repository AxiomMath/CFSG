module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Over

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem overgroup_of_fixed_dihedral (hF : L2Field F) (e : K ≃* L2 F)
    {u : MulAut K} {k : ℕ} (ψ : ↥(fixedSubgroup K u) ≃* DihedralGroup k)
    (hkq : 2 * k = Nat.card F + 1 ∨ 2 * k + 1 = Nat.card F) (hk3 : 3 ≤ k) (hk4 : k ≠ 4)
    (M : Subgroup K) (hCM : fixedSubgroup K u ≤ M) :
    M = fixedSubgroup K u ∨ M = ⊤ ∨ (Nonempty (↥M ≃* alternatingGroup (Fin 4)) ∧ k = 3) ∨
      (Nonempty (↥M ≃* Equiv.Perm (Fin 4)) ∧ k = 3) ∨
      (Nonempty (↥M ≃* alternatingGroup (Fin 5)) ∧ k = 5) := by
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  let φ : K ≃* PSL2 F := toPSL e
  have hkq' : 2 * k = p ^ n + 1 ∨ 2 * k + 1 = p ^ n := by
    rw [← hq]
    exact hkq
  let C : Subgroup K := fixedSubgroup K u
  let D : Subgroup (PSL2 F) := C.map φ.toMonoidHom
  let ψ' : D ≃* DihedralGroup k :=
    (Subgroup.equivMapOfInjective C φ.toMonoidHom φ.injective).symm.trans ψ
  have hM' : D ≤ M.map φ.toMonoidHom := Subgroup.map_mono hCM
  have eM : ↥M ≃* ↥(M.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective
  rcases dihedral_overgroup hq hp2 hk3 hk4 hkq' D (M.map φ.toMonoidHom) ψ' hM' with
    h | h | ⟨⟨e4⟩, hk⟩ | ⟨⟨e4⟩, hk⟩ | ⟨⟨e5⟩, hk⟩
  · exact Or.inl (Subgroup.map_injective φ.injective h)
  · right; left
    rw [← Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective M, h,
      Subgroup.comap_top]
  · exact Or.inr (Or.inr (Or.inl ⟨⟨eM.trans e4⟩, hk⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨eM.trans e4⟩, hk⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨eM.trans e5⟩, hk⟩)))

omit [Finite K] in
theorem exists_dihedral_inner (hF : L2Field F) (hq : 11 ≤ Nat.card F) (e : K ≃* L2 F) [Finite K] {u : K}
    (hu : orderOf u = 2) :
    ∃ k : ℕ, 6 ≤ k ∧ Even k ∧ (2 * k = Nat.card F + 1 ∨ 2 * k + 1 = Nat.card F) ∧
      Nonempty (↥(centralizer ({u} : Set K)) ≃* DihedralGroup k) := by
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
  have hev : Even k := by
    unfold Int.ModEq at hε
    exact ⟨k / 2, by omega⟩
  refine ⟨k, ?_, hev, ?_, ⟨ψ⟩⟩
  · obtain ⟨j, hj⟩ := hev
    omega
  · rcases hε1 with rfl | rfl
    · right
      omega
    · left
      omega

theorem isCoatom_centralizer_of_inner (hF : L2Field F)
    (hq : 11 ≤ Nat.card F) (e : K ≃* L2 F) {u : K} (hu : orderOf u = 2) :
    IsCoatom (centralizer ({u} : Set K)) := by
  obtain ⟨k, hk6, hkev, hkq, ⟨ψ⟩⟩ := exists_dihedral_inner hF hq e hu
  have hfix : fixedSubgroup K (MulAut.conj u) = centralizer ({u} : Set K) :=
    Lemma118.fixedSubgroup_conj u
  let ψ' : ↥(fixedSubgroup K (MulAut.conj u)) ≃* DihedralGroup k :=
    (MulEquiv.subgroupCongr hfix).trans ψ
  have hk4 : k ≠ 4 := by omega
  have hCtop : centralizer ({u} : Set K) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(centralizer ({u} : Set K)) = Nat.card K := by
      rw [htop, Subgroup.card_top]
    have h2 : Nat.card ↥(centralizer ({u} : Set K)) = 2 * k := by
      have : NeZero k := ⟨by omega⟩
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    have h3 := ivk_1_2b F hF K e
    have h144 : 121 ≤ Nat.card F ^ 2 := by nlinarith
    have h4 : Nat.card F * 120 ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : (Nat.card F * 120) / 2 ≤ Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      Nat.div_le_div_right h4
    omega
  refine ⟨hCtop, fun M hCM => ?_⟩
  have hCM' : fixedSubgroup K (MulAut.conj u) ≤ M := by
    rw [hfix]
    exact hCM.le
  rcases overgroup_of_fixed_dihedral hF e ψ' hkq (by omega) hk4 M hCM' with
    h | h | ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩
  · exact absurd (hfix ▸ h) (ne_of_gt hCM)
  · exact h
  · omega
  · omega
  · omega

end Over

end CFSG.GH74.GLS.IVK.Proofs2
