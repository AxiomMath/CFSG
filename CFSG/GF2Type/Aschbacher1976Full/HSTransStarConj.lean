module

public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransStar

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour

variable {G : Type} [Group G] [Finite G]

theorem mem_smul_sylow_iff {p : ℕ} (g : G) (S : Sylow p G) (x : G) :
    x ∈ ((g • S : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv]

theorem ET_conj {z : G} (g : G) {T T' : Subgroup G} (h : ∀ x, x ∈ T' ↔ g⁻¹ * x * g ∈ T) :
    ET T' z = (ET T z).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro v ⟨hc, hZ⟩
    refine ⟨g⁻¹ * v * g, Subgroup.subset_closure ⟨?_, ?_⟩, ?_⟩
    · simpa using (BL.isConj_conj_iff (z := z) (x := v) g⁻¹).mpr hc
    · rw [show ZF (g⁻¹ * v * g) = conjugate (ZF v) g from centerAt_conj v g]
      intro x hx
      have h2 := (h _).mp (hZ (Width.mem_conjugate_iff.mp hx))
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hc, hZ⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨(BL.isConj_conj_iff g).mpr hc, ?_⟩
    rw [show g * x * g⁻¹ = g⁻¹⁻¹ * x * g⁻¹ by rw [inv_inv],
      show ZF (g⁻¹⁻¹ * x * g⁻¹) = conjugate (ZF x) g⁻¹ from centerAt_conj x g⁻¹]
    intro y hy
    have h1 := Width.mem_conjugate_iff.mp hy
    rw [inv_inv] at h1
    exact (h y).mpr (hZ h1)

theorem card_ET_eq (z : G) (T T' : Sylow 2 G) :
    Nat.card (ET (T' : Subgroup G) z) = Nat.card (ET (T : Subgroup G) z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T T'
  rw [ET_conj g (mem_smul_sylow_iff g T)]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

section Ctx

variable {z : G} {w : ℕ} {Z A : Subgroup G} {T : Sylow 2 G}

theorem ET_comm (c : BL.Ctx z w Z A T) (hti : HSTI z) {a b : G}
    (ha : a ∈ ET (T : Subgroup G) z) (hb : b ∈ ET (T : Subgroup G) z) : a * b = b * a :=
  c.WZ_comm a (c.mem_WZ_of_mem_ET hti ha) b (c.mem_WZ_of_mem_ET hti hb)

theorem isElemAbelian_ET (c : BL.Ctx z w Z A T) (hti : HSTI z) :
    CFSG.Open.IsElemAbelian 2 (ET (T : Subgroup G) z) := by
  refine And.intro ⟨⟨fun a b => Subtype.ext ?_⟩⟩ ?_
  · exact ET_comm c hti a.2 b.2
  · intro x hx
    rcases (c.mem_ET_iff hti).mp hx with rfl | hx
    · exact one_pow 2
    · rw [sq]
      exact BL.mul_self_of_isConj c.hz hx.1

theorem ET_le_F (c : BL.Ctx z w Z A T) (hti : HSTI z) : ET (T : Subgroup G) z ≤ Fz z := by
  intro x hx
  rcases (c.mem_ET_iff hti).mp hx with rfl | hx
  · exact (Fz z).one_mem
  · exact c.VS_subset_F hti hx

theorem le_normalizer_ET (c : BL.Ctx z w Z A T) (hti : HSTI z) :
    (T : Subgroup G) ≤ Subgroup.normalizer (ET (T : Subgroup G) z : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [c.mem_ET_iff hti, c.mem_ET_iff hti, c.mem_VS_iff, c.mem_VS_iff]
  have hW : x ∈ BL.WZ Z (T : Subgroup G) ↔ t * x * t⁻¹ ∈ BL.WZ Z (T : Subgroup G) :=
    Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer ht) x
  have h1 : x = 1 ↔ t * x * t⁻¹ = 1 := by
    constructor
    · rintro rfl
      rw [mul_one, mul_inv_cancel]
    · intro h
      calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
  rw [h1, hW, BL.isConj_conj_iff t]

end Ctx

end CFSG.GF2Type.Aschbacher1976Full.HS.TransStar
