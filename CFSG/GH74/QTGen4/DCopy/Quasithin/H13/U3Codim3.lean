module

public import CFSG.Quasithin.H13.U3Codim3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Transport6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB Module
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem u3_six_module_transport_adapted_F4
    (h1332 : Stmt13_3_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z) :
    ∃ Φ : Additive V ≃ₗ[ZMod 2] W6,
      (∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      (∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      (∀ n : normalizer (V : Set G), ∃ k ∈ N6,
        linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) ∧
      ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Φ₀, hL, hLs, hN⟩ := u3_six_module_transport_F4 h1332 hH hU3 hF
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1

  set τ : normalizer (V : Set G) →* GL (Fin 6) (ZMod 2) :=
    glLin.symm.toMonoidHom.comp
      ((linConj Φ₀).toMonoidHom.comp (u3ConjLin V (normalizer (V : Set G)) le_rfl)) with hτ
  have hτN : ∀ n, τ n ∈ N6 := fun n => by
    obtain ⟨k, hk, hkn⟩ := hN n
    simp only [hτ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hkn,
      MulEquiv.symm_apply_apply]
    exact hk
  have hτ' : ∀ n, linConj Φ₀ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin (τ n) :=
    fun n => by
      simp only [hτ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.apply_symm_apply]
  set T₀ := (T.subgroupOf (normalizer (V : Set G))).map τ with hT₀
  have hT₀N : T₀ ≤ N6 := by
    rintro _ ⟨t, -, rfl⟩
    exact hτN t
  have hT₀2 : IsPGroup 2 T₀ :=
    ((hH.sylow.1.comap_subtype (K := normalizer (V : Set G))).map τ)
  obtain ⟨k, hk, hkT⟩ := exists_conj_le_S0 hT₀N hT₀2
  have hkJ : ∀ j ∈ J6, k⁻¹ * j * k ∈ J6 := by
    intro j hj
    have hk' : k⁻¹ ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
      rw [normalizer_J6_eq]
      exact inv_mem hk
    have h1 := (mem_normalizer_iff.1 hk' j).1 hj
    rwa [inv_inv] at h1
  have hkJ' : ∀ j ∈ J6, k * j * k⁻¹ ∈ J6 := by
    intro j hj
    have hk' : k ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
      rw [normalizer_J6_eq]
      exact hk
    exact (mem_normalizer_iff.1 hk' j).1 hj

  refine ⟨Φ₀.trans (glLin k⁻¹), ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨j, hj, hjl⟩ := hL l hl
    refine ⟨k⁻¹ * j * k, hkJ j hj, ?_⟩
    rw [linConj_trans, hjl, linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  · intro j hj
    obtain ⟨l, hl, hjl⟩ := hLs _ (hkJ' j hj)
    refine ⟨l, hl, ?_⟩
    rw [linConj_trans, hjl, linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
    congr 1
    group
  · intro n
    refine ⟨k⁻¹ * τ n * k, mul_mem (mul_mem (inv_mem hk) (hτN n)) hk, ?_⟩
    rw [linConj_trans, hτ', linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  · intro t ht
    refine ⟨k⁻¹ * τ ⟨t, hTV ht⟩ * k, hkT _ ⟨⟨t, hTV ht⟩, ht, rfl⟩, ?_⟩
    rw [linConj_trans, hτ', linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]

@[expose] def U3NondegLineCentralizer_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z : G) [IsElementaryAbelian 2 V],
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ b : LinearMap.BilinForm (ZMod 2) (Additive V), b.Nondegenerate → b.IsAlt →
      (∀ (n : normalizer (V : Set G)) (x y : Additive V),
        b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) →
      ∀ (u v : G) (hu : u ∈ V) (hv : v ∈ V),
        b (Additive.ofMul ⟨u, hu⟩) (Additive.ofMul ⟨v, hv⟩) ≠ 0 →
        centralizer ({u, v} : Set G) ≤ normalizer (L : Set G)

end CFSG.Quasithin.H13.U3
