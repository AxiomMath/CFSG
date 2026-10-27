module

public import CFSG.GH74.GLS.Stage1.Thm6.Prelude
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type} [Group G] [Finite G]

theorem burnside_weak (S A : Subgroup G) (hS : IsPGroup 2 ↥S) (hSyl : IsSylow2In S ⊤)
    (hAS : A ≤ S) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A) :
    ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ A →
      ∃ n ∈ Subgroup.normalizer (A : Set G), n⁻¹ * a * n = g⁻¹ * a * g := by
  have hidx : ¬ 2 ∣ S.index := by
    have h := hSyl.2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 G, (T : Subgroup G) = S :=
    ⟨hS.toSylow hidx, IsPGroup.toSylow_coe hS hidx⟩
  have hW : CFSG.Quasithin.IsWeaklyClosedIn A (T : Subgroup G) := fun g hg => by
    rw [hT] at hg
    exact hweak g⁻¹ hg
  have hcent : ∀ x ∈ A, x ∈ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun h hh => hab h hh x hx
  intro a ha g hga
  exact CFSG.Quasithin.burnside_fusion_lemma_centralizer T (W := A) (by rw [hT]; exact hAS) hW
    (hcent a ha) (hcent _ hga) rfl

end CFSG.GH74.GLS.C3.Layer2.L5
