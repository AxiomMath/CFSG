module

public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G] {X : StrothAmbient G}

theorem StrothTypeIndex.m_eq_n_or_succ_or_succ_succ (τ : StrothTypeIndex) :
    τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n ∨ τ.m = τ.n := by
  cases τ <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

theorem item224_of_centralizerInMho_eq (Z : StrothDatum X)
    (hZ : Z.centralizerInMho = Z.D)
    (_hfamily : Z.τ.m + 1 = Z.τ.n)
    (_hΩ : Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2])) :
    (∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D) ∧
    (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 1 → B ≤ Z.centralizerInMho →
      Nonempty (Additive ↥B ≃+
        (ZMod (2 ^ j) × ZMod (2 ^ (j + 1)) × ZMod (2 ^ (j + 1)))) →
      B ≤ Z.D) ∧
    ((Z.centralizerInMho ⊓
        Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) ≠ Z.D →
      ∃ s : G,
        s ∈ Z.centralizerInMho ⊓
            Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G) ∧
        s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
        (Z.centralizerInMho ⊓
            Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) =
          (Z.D ⊔ Subgroup.zpowers s) ∧
        ⁅Subgroup.zpowers s, Z.D⁆ =
          ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆) := by
  haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
  have hDleC : Z.D ≤
      Subgroup.centralizer (((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) :=
    (Subgroup.le_centralizer (H := Z.D)).trans
      (Subgroup.centralizer_le (omegaIn_le (Z.τ.n - 1) Z.D))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hz2
    have hzD : z ∈ Z.D := by
      rw [hZ] at hz
      exact hz
    refine ⟨⟨z, hzD⟩, Subgroup.subset_closure ?_, rfl⟩
    change (⟨z, hzD⟩ : Z.D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa [pow_two] using hz2
  · intro j B _hj hB _hBiso
    have hBD : B ≤ Z.D := by
      rw [hZ] at hB
      exact hB
    exact hBD
  · intro hne
    have hEq : Z.centralizerInMho ⊓
        Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G) = Z.D := by
      rw [hZ]
      exact inf_eq_left.mpr hDleC
    exact (hne hEq).elim

theorem item224_involutions_of_A_le_mho (Z : StrothDatum X)
    (hA : X.A ≤ mhoOne Z.D) :
    ∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D := by
  intro z hz hz2
  have hzS : z ∈ (X.S : Subgroup G) := hz.1.1
  have hzCentA : z ∈ Subgroup.centralizer (X.A : Set G) :=
    Subgroup.centralizer_le (show (X.A : Set G) ⊆ (mhoOne Z.D : Set G) from hA) hz.2
  have hzA : z ∈ X.A := X.hH z hzS hz2 hzCentA
  have hzD : z ∈ Z.D := Z.hAD hzA
  refine ⟨⟨z, hzD⟩, Subgroup.subset_closure ?_, rfl⟩
  change (⟨z, hzD⟩ : Z.D) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa [pow_two] using hz2

theorem item224_of_family_centralizerInMho_eq
    (hZ : ∀ (Z : StrothDatum X), Z.τ.m + 1 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      Z.centralizerInMho = Z.D) :
    (∀ (Z : StrothDatum X),
      Z.τ.m + 1 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      (∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D) ∧
      (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 1 → B ≤ Z.centralizerInMho →
        Nonempty (Additive ↥B ≃+
          (ZMod (2 ^ j) × ZMod (2 ^ (j + 1)) × ZMod (2 ^ (j + 1)))) →
        B ≤ Z.D) ∧
      ((Z.centralizerInMho ⊓
          Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) ≠ Z.D →
        ∃ s : G,
          s ∈ Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G) ∧
          s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
          (Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) =
            (Z.D ⊔ Subgroup.zpowers s) ∧
          ⁅Subgroup.zpowers s, Z.D⁆ =
            ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆)) :=
  fun Z hfamily hΩ =>
    item224_of_centralizerInMho_eq Z (hZ Z hfamily hΩ) hfamily hΩ

theorem item225_of_centralizerInMho_eq (Z : StrothDatum X)
    (hZ : Z.centralizerInMho = Z.D)
    (_hfamily : Z.τ.m + 2 = Z.τ.n)
    (_hΩ : Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2])) :
    (∀ x : G, x ∈ Z.centralizerInMho → x * x ∈ Z.D) ∧
    (∀ x : G, x ∈ Z.centralizerInMho → ∀ y : G, y ∈ Z.centralizerInMho →
      x * y * x⁻¹ * y⁻¹ ∈ Z.D) ∧
    Nat.card Z.centralizerInMho ≤ 8 * Nat.card Z.D ∧
    (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 2 → B ≤ Z.centralizerInMho →
      Nonempty (Additive ↥B ≃+
        (ZMod (2 ^ j) × ZMod (2 ^ (j + 2)) × ZMod (2 ^ (j - 2)))) →
      B ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ∧
    ((Z.centralizerInMho ⊓
        Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ≠ Z.D →
      ∃ s : G,
        s ∈ Z.centralizerInMho ⊓
            Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G) ∧
        s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
        (Z.centralizerInMho ⊓
            Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) =
          (Z.D ⊔ Subgroup.zpowers s) ∧
        ⁅Subgroup.zpowers s, Z.D⁆ =
          ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆) := by
  haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
  have hDleC : Z.D ≤
      Subgroup.centralizer (((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :=
    (Subgroup.le_centralizer (H := Z.D)).trans
      (Subgroup.centralizer_le (omegaIn_le (Z.τ.n - 2) Z.D))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Z.D := by
      rw [hZ] at hx
      exact hx
    exact Subgroup.mul_mem _ hx' hx'
  · intro x hx y hy
    have hx' : x ∈ Z.D := by
      rw [hZ] at hx
      exact hx
    have hy' : y ∈ Z.D := by
      rw [hZ] at hy
      exact hy
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' hy') (Subgroup.inv_mem _ hx'))
      (Subgroup.inv_mem _ hy')
  · rw [hZ, mul_comm]
    exact Nat.le_mul_of_pos_right (Nat.card Z.D) (by norm_num : (0 : ℕ) < 8)
  · intro j B _hj hB _hBiso
    have hBD : B ≤ Z.D := by
      rw [hZ] at hB
      exact hB
    exact hBD.trans hDleC
  · intro hne
    have hEq : Z.centralizerInMho ⊓
        Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G) = Z.D := by
      rw [hZ]
      exact inf_eq_left.mpr hDleC
    exact (hne hEq).elim

theorem item225_of_family_centralizerInMho_eq
    (hZ : ∀ (Z : StrothDatum X), Z.τ.m + 2 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      Z.centralizerInMho = Z.D) :
    (∀ (Z : StrothDatum X),
      Z.τ.m + 2 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      (∀ x : G, x ∈ Z.centralizerInMho → x * x ∈ Z.D) ∧
      (∀ x : G, x ∈ Z.centralizerInMho → ∀ y : G, y ∈ Z.centralizerInMho →
        x * y * x⁻¹ * y⁻¹ ∈ Z.D) ∧
      Nat.card Z.centralizerInMho ≤ 8 * Nat.card Z.D ∧
      (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 2 → B ≤ Z.centralizerInMho →
        Nonempty (Additive ↥B ≃+
          (ZMod (2 ^ j) × ZMod (2 ^ (j + 2)) × ZMod (2 ^ (j - 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ∧
      ((Z.centralizerInMho ⊓
          Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ≠ Z.D →
        ∃ s : G,
          s ∈ Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G) ∧
          s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
          (Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) =
            (Z.D ⊔ Subgroup.zpowers s) ∧
          ⁅Subgroup.zpowers s, Z.D⁆ =
            ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆)) :=
  fun Z hfamily hΩ =>
    item225_of_centralizerInMho_eq Z (hZ Z hfamily hΩ) hfamily hΩ

theorem item226_of_conjugate_le (Z : StrothDatum X) (B : Subgroup G)
    (h : ∀ g : G, Z.D.map (MulAut.conj g).toMonoidHom ≠ Z.D →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.centralizerInOmegaOne →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.D)
    (hB : B ≤ Z.centralizerInOmegaOne)
    (_hBnormal : ∀ h : G, h ∈ Z.centralizerInOmegaOne → ∀ b : G, b ∈ B → h * b * h⁻¹ ∈ B)
    (hBne : B ≠ Z.D)
    (hconj : ∃ g : G, B = Z.D.map (MulAut.conj g).toMonoidHom) :
    Z.τ.m = Z.τ.n := by
  obtain ⟨g, rfl⟩ := hconj
  by_cases hDg : Z.D.map (MulAut.conj g).toMonoidHom = Z.D
  · exact (hBne hDg).elim
  · have hle : Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.D := h g hDg hB
    have hcard : Nat.card (Z.D.map (MulAut.conj g).toMonoidHom) = Nat.card Z.D := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hEq : Z.D.map (MulAut.conj g).toMonoidHom = Z.D := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hcard]
    exact (hDg hEq).elim

theorem item226_of_forall_conjugate_le
    (h : ∀ (Z : StrothDatum X) (g : G),
      Z.D.map (MulAut.conj g).toMonoidHom ≠ Z.D →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.centralizerInOmegaOne →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.D) :
    (∀ (Z : StrothDatum X) (B : Subgroup G),
      B ≤ Z.centralizerInOmegaOne →
      (∀ h : G, h ∈ Z.centralizerInOmegaOne → ∀ b : G, b ∈ B → h * b * h⁻¹ ∈ B) →
      B ≠ Z.D →
      (∃ g : G, B = Z.D.map (MulAut.conj g).toMonoidHom) →
      Z.τ.m = Z.τ.n) :=
  fun Z B hB hBnormal hBne hconj =>
    item226_of_conjugate_le Z B (h Z) hB hBnormal hBne hconj

theorem strothSection2Input_of_centralizer_eq (X : StrothAmbient G)
    (hMho1 : ∀ (Z : StrothDatum X), Z.τ.m + 1 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      Z.centralizerInMho = Z.D)
    (hMho2 : ∀ (Z : StrothDatum X), Z.τ.m + 2 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      Z.centralizerInMho = Z.D)
    (hConj : ∀ (Z : StrothDatum X) (g : G),
      Z.D.map (MulAut.conj g).toMonoidHom ≠ Z.D →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.centralizerInOmegaOne →
      Z.D.map (MulAut.conj g).toMonoidHom ≤ Z.D)
    (induction_step :
      ∀ (B : Subgroup G) (τ : StrothTypeIndex) (Bdata : StrothWeakTypeData B τ),
        X.A ≤ B → B ≤ (X.S : Subgroup G) → Bdata.L = X.L →
        B < (X.S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) →
        ∃ (C : Subgroup G) (τ' : StrothTypeIndex) (Cdata : StrothWeakTypeData C τ'),
          B < C ∧ C ≤ (X.S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) ∧
            Cdata.L = X.L)
    (item227 :
      ∀ (Z : StrothDatum X),
        (∀ x : G, x ∈ omegaIn 1 Z.D → orderOf x = 2 →
          ∀ y : G, y ∈ omegaIn 1 Z.D → orderOf y = 2 →
          ∃ g : G, y = g * x * g⁻¹) →
        Z.τ.m = Z.τ.n)
    (item228 :
      ∀ (Z : StrothDatum X),
        (∃ x : G, x ∈ omegaIn 1 Z.D ∧ orderOf x = 2 ∧
          ∃ y : G, y ∈ omegaIn 1 Z.D ∧ orderOf y = 2 ∧
            ∀ g : G, y ≠ g * x * g⁻¹) →
        (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t200 m)) ∨
        (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t201 m)) ∨
        (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t100 m)) ∨
        (∃ s : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t101 s)) ∨
        (∃ n : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t300 n))) :
    StrothSection2Input X where
  induction_step := induction_step
  item224 := item224_of_family_centralizerInMho_eq hMho1
  item225 := item225_of_family_centralizerInMho_eq hMho2
  item226 := item226_of_forall_conjugate_le hConj
  item227 := item227
  item228 := item228

end CFSG.CGT.Stroth77
