module

public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T8T

section Triangle

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_cent_pair_gen {M : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (haM : a ∈ trivialOnQuot M) (hbM : b ∈ trivialOnQuot M) :
    ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer ({a} : Set G) ∧
      T ≤ Subgroup.centralizer ({b} : Set G) := by
  have hcomm : ∀ u ∈ ({a, b} : Set G), ∀ v ∈ ({a, b} : Set G), u * v = v * u := by
    intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have hsq : ∀ u ∈ ({a, b} : Set G), u * u = 1 := by
    intro u hu
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  set A : Subgroup G := Subgroup.closure ({a, b} : Set G) with hA
  have hA2 : IsPGroup 2 ↥A := fun g =>
    ⟨1, Subtype.ext (by simpa [sq] using T7A.sq_closure hsq hcomm (g : G) g.2)⟩
  have hAM : A ≤ trivialOnQuot M := by
    rw [hA, Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact haM
    · exact hbM
  have hAc : ⁅A, M⁆ ≤ oddCoreOf M :=
    Subgroup.commutator_le.mpr fun x hx m hm => (hAM hx).2 m hm
  obtain ⟨T, hT, hTc⟩ := AscE184Sect.exists_isSylow2In_centralizer hA2 hAc
  have hTa : ∀ g ∈ T, ∀ v ∈ ({a, b} : Set G), g * v = v * g := by
    intro g hg v hv
    have hv' : v ∈ A := Subgroup.subset_closure hv
    exact (Subgroup.mem_centralizer_iff.mp (hTc hg) v hv').symm
  exact ⟨T, hT, fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hTa g hg a (by simp)),
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hTa g hg b (by simp))⟩

theorem exists_triFrame_of_nbrsE
    (hsymm : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → B ∈ omegaNbr Ω A → A ∈ omegaNbr Ω B)
    (hmc : ∀ {A B : Subgroup G} {x y : G}, IsUniqueInvolution A x → B ∈ omegaNbr Ω A →
      IsUniqueInvolution B y → x * y = y * x)
    (hsyl : ∀ {A R : Subgroup G}, A ∈ Ω → R ∈ RSet Ω → R ≤ A → IsSylow2In R A)
    (hmtq : ∀ {c : G} {A : Subgroup G}, IsPGroup 2 (Subgroup.zpowers c) → A ∈ Ω →
      (c ∈ trivialOnQuot A ↔ ∃ R, IsSylow2In R A ∧ R ≤ Subgroup.centralizer ({c} : Set G)))
    {K J₁ J₂ : Subgroup G} {z t₁ t₂ : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (h1 : IsUniqueInvolution J₁ t₁) (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (h12 : J₂ ∈ omegaNbr Ω J₁) :
    ∃ R : Fin 3 → Subgroup G, TriFrame Ω ![K, J₁, J₂] ![z, t₁, t₂] R := by
  classical
  set M : Fin 3 → Subgroup G := ![K, J₁, J₂] with hM
  set x : Fin 3 → G := ![z, t₁, t₂] with hx
  have hMΩ : ∀ i, M i ∈ Ω := by
    intro i
    fin_cases i
    · exact hK
    · exact hJ₁.1
    · exact hJ₂.1
  have hinv : ∀ i, IsUniqueInvolution (M i) (x i) := by
    intro i
    fin_cases i
    · exact hz
    · exact h1
    · exact h2
  have hs1 : K ∈ omegaNbr Ω J₁ := hsymm hK hJ₁.1 hJ₁
  have hs2 : K ∈ omegaNbr Ω J₂ := hsymm hK hJ₂.1 hJ₂
  have hs12 : J₁ ∈ omegaNbr Ω J₂ := hsymm hJ₁.1 hJ₂.1 h12
  have hnbr : ∀ i j, i ≠ j → M j ∈ omegaNbr Ω (M i) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hJ₁
    · exact hJ₂
    · exact hs1
    · exact absurd rfl hij
    · exact h12
    · exact hs2
    · exact hs12
    · exact absurd rfl hij
  have hcomm : ∀ i j, x i * x j = x j * x i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hmc (hinv i) (hnbr i j hij) (hinv j)
  have hTQ : ∀ i j, i ≠ j → x j ∈ trivialOnQuot (M i) := by
    intro i j hij
    have hc2 : IsPGroup 2 (Subgroup.zpowers (x j)) :=
      ExactLayer.isPGroup_zpowers_of_sq_eq_one (hinv j).sq
    obtain ⟨-, -, T, hT, hTM, hTN⟩ := hnbr j i (Ne.symm hij)
    have hTsyl : IsSylow2In T (M i) := hsyl (hMΩ i) hT hTM
    exact (hmtq hc2 (hMΩ i)).mpr
      ⟨T, hTsyl, T3.le_centralizer_of_le_normalizer' (hinv j) hTN⟩
  have hxi : ∀ i, M i ≤ Subgroup.centralizer ({x i} : Set G) := fun i =>
    AscP1Nine3.le_centralizer_of_uniqueInvolution (hinv i)
  have hex0 : ∃ T : Subgroup G, IsSylow2In T (M 0) ∧
      ∀ j, T ≤ Subgroup.centralizer ({x j} : Set G) := by
    obtain ⟨T, hT, hT1, hT2⟩ := exists_sylow_cent_pair_gen (M := M 0) (a := x 1) (b := x 2)
      (hinv 1).sq (hinv 2).sq (hcomm 1 2) (hTQ 0 1 (by decide)) (hTQ 0 2 (by decide))
    refine ⟨T, hT, fun j => ?_⟩
    fin_cases j
    · exact hT.1.trans (hxi 0)
    · exact hT1
    · exact hT2
  have hex1 : ∃ T : Subgroup G, IsSylow2In T (M 1) ∧
      ∀ j, T ≤ Subgroup.centralizer ({x j} : Set G) := by
    obtain ⟨T, hT, hT1, hT2⟩ := exists_sylow_cent_pair_gen (M := M 1) (a := x 0) (b := x 2)
      (hinv 0).sq (hinv 2).sq (hcomm 0 2) (hTQ 1 0 (by decide)) (hTQ 1 2 (by decide))
    refine ⟨T, hT, fun j => ?_⟩
    fin_cases j
    · exact hT1
    · exact hT.1.trans (hxi 1)
    · exact hT2
  have hex2 : ∃ T : Subgroup G, IsSylow2In T (M 2) ∧
      ∀ j, T ≤ Subgroup.centralizer ({x j} : Set G) := by
    obtain ⟨T, hT, hT1, hT2⟩ := exists_sylow_cent_pair_gen (M := M 2) (a := x 0) (b := x 1)
      (hinv 0).sq (hinv 1).sq (hcomm 0 1) (hTQ 2 0 (by decide)) (hTQ 2 1 (by decide))
    refine ⟨T, hT, fun j => ?_⟩
    fin_cases j
    · exact hT1
    · exact hT2
    · exact hT.1.trans (hxi 2)
  have hex : ∀ i, ∃ T : Subgroup G, IsSylow2In T (M i) ∧
      ∀ j, T ≤ Subgroup.centralizer ({x j} : Set G) := by
    intro i
    fin_cases i
    · exact hex0
    · exact hex1
    · exact hex2
  choose R hR using hex
  exact ⟨R, ⟨hMΩ, hinv, hnbr, fun i => (hR i).1, fun i j => (hR i).2 j⟩⟩

end Triangle

section Alpha

variable {G : Type} [Group G]

theorem closure_pair_eq_of_mulE {z t₁ t₂ : G} (hz : z * z = 1) (h : t₂ = z * t₁) :
    Subgroup.closure ({t₂, z} : Set G) = Subgroup.closure ({t₁, z} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl
    · have : v = z * t₂ := by rw [h, ← mul_assoc, hz, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)

theorem closure_pair_mul_leftE {z t : G} (hz : z * z = 1) :
    Subgroup.closure ({z * t, z} : Set G) = Subgroup.closure ({t, z} : Set G) := by
  have hz' : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have ht' : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hz'' : z ∈ Subgroup.closure ({z * t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hzt : z * t ∈ Subgroup.closure ({z * t, z} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mul_mem _ hz' ht'
    · exact hz'
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]
      have h4 : z * (z * t) ∈ Subgroup.closure ({z * t, z} : Set G) :=
        Subgroup.mul_mem _ hz'' hzt
      rwa [← mul_assoc, hz, one_mul] at h4
    · rw [h]
      exact hz''

end Alpha

end T8T

end CFSG.ClassicalInvolution.Asc77
