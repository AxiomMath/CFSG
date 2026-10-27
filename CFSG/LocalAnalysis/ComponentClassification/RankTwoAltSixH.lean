module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsSix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixC

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

@[expose] def e4523 : alternatingGroup (Fin 6) :=
  ⟨swap 4 5 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def e2435 : alternatingGroup (Fin 6) :=
  ⟨swap 2 4 * swap 4 3 * swap 3 5 * swap 0 1, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def e0123 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩

theorem e2435_sq : e2435 * e2435 = e4523 := Subtype.ext (by decide)

theorem e123_mem_rootAlt : e123 ∈ rootAlt 6 := by
  rw [mem_rootAlt_iff (by norm_num)]
  refine ⟨swap 1 2 * swap 2 3, mem_alternatingGroup.mpr (by decide), ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem e0123_mem_rootV : e0123 ∈ rootV 6 := by
  rw [mem_rootV_iff (by norm_num)]
  refine ⟨swap 0 1 * swap 2 3, ?_, ?_⟩
  · exact kOf_mem 1
  · rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}

@[expose] noncomputable def w (ψA : A ≃* alternatingGroup (Fin 6)) : G := (ψA.symm e123 : G)

@[expose] noncomputable def c1 (ψA : A ≃* alternatingGroup (Fin 6)) : G := (ψA.symm e450 : G)

@[expose] noncomputable def cr (ψB : B ≃* alternatingGroup (Fin 6)) : G := (ψB.symm e450 : G)

@[expose] noncomputable def y0 (ψB : B ≃* alternatingGroup (Fin 6)) : G := (ψB.symm e4523 : G)

@[expose] noncomputable def s (ψB : B ≃* alternatingGroup (Fin 6)) : G := (ψB.symm e2435 : G)

@[expose] noncomputable def z (ψB : B ≃* alternatingGroup (Fin 6)) : G := (ψB.symm e0123 : G)

@[expose] noncomputable def H (ψA : A ≃* alternatingGroup (Fin 6)) : Subgroup G :=
  centralizer ({w ψA} : Set G)

variable {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

theorem conj_symm6 {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 6))
    (a b : alternatingGroup (Fin 6)) :
    (ψ.symm a : G) * ψ.symm b * (ψ.symm a : G)⁻¹ = (ψ.symm (a * b * a⁻¹) : G) := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem w_mem : w ψA ∈ A := (ψA.symm e123).2
theorem c1_mem : c1 ψA ∈ A := (ψA.symm e450).2
theorem cr_mem : cr ψB ∈ B := (ψB.symm e450).2
theorem y0_mem : y0 ψB ∈ B := (ψB.symm e4523).2
theorem s_mem : s ψB ∈ B := (ψB.symm e2435).2
theorem w_mem_centralizer_B (hco : AltCoords 6 A B ψA ψB) : w ψA ∈ centralizer (B : Set G) :=
  hco.2.2.1 ⟨ψA.symm e123, ⟨e123, e123_mem_rootAlt, rfl⟩, rfl⟩

theorem z_mem_centralizer_A (hco : AltCoords 6 A B ψA ψB) : z ψB ∈ centralizer (A : Set G) :=
  hco.2.1.le ⟨ψB.symm e0123, ⟨e0123, e0123_mem_rootV, rfl⟩, rfl⟩

theorem B_le_H (hco : AltCoords 6 A B ψA ψB) : B ≤ H ψA := fun b hb =>
  mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (w_mem_centralizer_B hco)) b hb)

theorem c1_mem_H : c1 ψA ∈ H ψA := by
  rw [H, mem_centralizer_singleton_iff]
  show ((ψA.symm e450 : A) : G) * (ψA.symm e123 : A) = (ψA.symm e123 : A) * (ψA.symm e450 : A)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    show e450 * e123 = e123 * e450 from Subtype.ext (by decide)]

theorem s_sq : s ψB * s ψB = y0 ψB := by
  show ((ψB.symm e2435 : B) : G) * (ψB.symm e2435 : B) = (ψB.symm e4523 : B)
  rw [← Subgroup.coe_mul, ← map_mul, e2435_sq]

theorem y0_conj_cr : y0 ψB * cr ψB * (y0 ψB)⁻¹ = (cr ψB)⁻¹ := by
  rw [y0, cr, conj_symm6, show e4523 * e450 * e4523⁻¹ = e450⁻¹ from Subtype.ext (by decide),
    map_inv]
  rfl

theorem y0_conj_c1 (hco : AltCoords 6 A B ψA ψB) : y0 ψB * c1 ψA * (y0 ψB)⁻¹ = (c1 ψA)⁻¹ := by
  obtain ⟨β, hβ, hC2⟩ := hco.2.2.2.2.2.2.1
  have hstab : ∀ i : Fin 6, (i : ℕ) < 4 → ((ψB (ψB.symm e4523) : Perm (Fin 6)) i : ℕ) < 4 := by
    rw [MulEquiv.apply_symm_apply]
    decide
  obtain ⟨ha, hae⟩ := hC2 (ψB.symm e4523) hstab (ψA.symm e450)
  have hr : restrictO ((ψB (ψB.symm e4523) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      swap 4 5 := by
    rw [MulEquiv.apply_symm_apply]
    exact restrictO_eq_swap45_of (by decide) (by decide) (by decide)
  rw [hr, MulEquiv.apply_symm_apply] at hae
  have hβ45 : β * swap 4 5 * β⁻¹ = swap 4 5 := by
    have hge : ∀ j : Fin 6, 4 ≤ (j : ℕ) → β j = 4 ∨ β j = 5 := by
      intro j hj
      have h4 : 4 ≤ (β j : ℕ) := by
        by_contra hlt
        have h1 := hβ (β j) (by omega)
        have h2 : β j = j := β.injective h1
        rw [h2] at hlt
        omega
      have h7 := (β j).isLt
      rcases (by omega : (β j : ℕ) = 4 ∨ (β j : ℕ) = 5) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    have hne : β 4 ≠ β 5 := fun h => absurd (β.injective h) (by decide)
    rw [← swap_apply_apply]
    rcases hge 4 (by norm_num) with h4 | h4 <;> rcases hge 5 (by norm_num) with h5 | h5 <;>
      rw [h4, h5] at hne ⊢ <;> first | exact absurd rfl hne | rfl | exact swap_comm _ _
  rw [hβ45] at hae
  have hae' : (ψA ⟨_, ha⟩ : Perm (Fin 6)) = ((e450⁻¹ : alternatingGroup (Fin 6)) :
      Perm (Fin 6)) := by
    rw [hae]
    decide
  have h1 : ψA ⟨_, ha⟩ = e450⁻¹ := Subtype.ext hae'
  have h2 := congrArg (fun q => ((ψA.symm q : A) : G)) h1
  simp only [MulEquiv.symm_apply_apply] at h2
  rw [y0, c1, h2, map_inv]
  rfl

@[expose] def InOmega6 (ψA : A ≃* alternatingGroup (Fin 6)) (B : Subgroup G) (g : G) : Prop :=
  ∃ k ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G), ∃ i j : ℤ,
    g = k * w ψA ^ i * c1 ψA ^ j

theorem inOmega6_one : InOmega6 ψA B (1 : G) := ⟨1, one_mem _, 0, 0, by simp⟩

theorem w_comm_c1 : Commute (w ψA) (c1 ψA) := (mem_centralizer_singleton_iff.mp c1_mem_H).symm

theorem inOmega6_mul
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    {g g' : G} (hg : InOmega6 ψA B g) (hg' : InOmega6 ψA B g') : InOmega6 ψA B (g * g') := by
  obtain ⟨k₁, hk₁, i, j, rfl⟩ := hg
  obtain ⟨k₂, hk₂, a, b, rfl⟩ := hg'
  have hwN := hN (mem_sup_left (le_normalizer (w_mem (ψA := ψA))))
  have hcN := hN (mem_sup_left (le_normalizer (c1_mem (ψA := ψA))))
  set c := w ψA ^ i * c1 ψA ^ j with hc
  have hcN' : c ∈ normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) :
      Subgroup G) : Set G) := mul_mem (zpow_mem hwN i) (zpow_mem hcN j)
  refine ⟨k₁ * (c * k₂ * c⁻¹), mul_mem hk₁ ((mem_normalizer_iff.mp hcN' k₂).mp hk₂), i + a, j + b,
    ?_⟩
  have hvw : c1 ψA ^ j * w ψA ^ a = w ψA ^ a * c1 ψA ^ j :=
    ((w_comm_c1 (ψA := ψA)).zpow_zpow a j).eq.symm
  rw [zpow_add, zpow_add]
  calc k₁ * w ψA ^ i * c1 ψA ^ j * (k₂ * w ψA ^ a * c1 ψA ^ b)
      = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * (c1 ψA ^ j * w ψA ^ a) * c1 ψA ^ b) := by
        rw [hc]; group
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * (w ψA ^ a * c1 ψA ^ j) * c1 ψA ^ b) := by rw [hvw]
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * w ψA ^ a) * (c1 ψA ^ j * c1 ψA ^ b) := by group

end Six

end CFSG.ComponentClassification.RankTwoAlt
