module

public import CFSG.GF2Type.Smith1980Orth.S2Basic
public import CFSG.GF2Type.Smith1979.W4AsOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriConf

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

structure TriLocal (S : Setting G) (g : G) (t k : S.O) (M1 : Subgroup S.O) : Prop where
  k_mem : k ∈ S.Mbar
  k_ne : k ≠ 1
  k_cube : k ^ 3 = 1
  k_conj : ∀ x ∈ M1, x * k * x⁻¹ = k ∨ x * k * x⁻¹ = k⁻¹
  t_inv : t * k * t⁻¹ = k⁻¹
  fpf : ∀ v : S.Qt, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0
  mul_Cbar : ∀ {x : S.O}, x ∈ M1 → ∃ s ∈ zpowers k ⊔ zpowers t,
    ∃ c ∈ S.Mbar ⊓ centralizer ((zpowers k ⊔ zpowers t : Subgroup S.O) : Set S.O), x = s * c
  rel : Smith1980Orth.S2Rel S g t k M1

theorem nonempty_s2Data_of_triLocal (hCE : CentralExtInput.{0}) {S : Setting G}
    (hw : S.width = 4) {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {k : S.O} {M1 : Subgroup S.O}
    (T : TriLocal S g t k M1) : Nonempty (Smith1980Orth.S2Data S M1) := by
  have hNo : NoA2 S g := S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hR : Rbar S g t ≠ S.Lbar g := fun h => hVQ (S11.V_le_Qa_of_Rbar_eq H C h)
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  exact ⟨⟨g, t, k, ⟨H, hNo, C, ht, ht1, hR, hVQ, hN, hirr, hnoAll⟩, by omega,
    by rw [h4, hw], T.k_mem, T.k_ne, T.k_cube, T.k_conj, T.t_inv, T.fpf, T.mul_Cbar,
    T.rel⟩, hΩ⟩

end CFSG.GF2Type.Smith1979.TriConf

namespace CFSG.GF2Type.Smith1979.TriConf

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

theorem exists_s2Data_of_triLocal (hCE : CentralExtInput.{0}) {S : Setting G}
    (hw : S.width = 4) {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {k : S.O} {M1 : Subgroup S.O}
    (T : TriLocal S g t k M1) :
    ∃ D : Smith1980Orth.S2Data S M1, D.g = g ∧ D.t = t ∧ D.k = k := by
  have hNo : NoA2 S g := S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hR : Rbar S g t ≠ S.Lbar g := fun h => hVQ (S11.V_le_Qa_of_Rbar_eq H C h)
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  exact ⟨⟨⟨g, t, k, ⟨H, hNo, C, ht, ht1, hR, hVQ, hN, hirr, hnoAll⟩, by omega,
    by rw [h4, hw], T.k_mem, T.k_ne, T.k_cube, T.k_conj, T.t_inv, T.fpf, T.mul_Cbar,
    T.rel⟩, hΩ⟩, rfl, rfl, rfl⟩

end CFSG.GF2Type.Smith1979.TriConf
