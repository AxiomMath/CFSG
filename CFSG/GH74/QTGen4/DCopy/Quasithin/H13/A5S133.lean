module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5S133

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def Input1326Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (g : G)
    (v w : ↥V), g * v * g⁻¹ = w → (IsSing (S.frame.ψ v) ↔ IsSing (S.frame.ψ w))

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_centralizer_conj_F4 (h1326 : Input1326Two_F4) {v g : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hvg : v ∈ conjSub g⁻¹ V) :
    ∃ c ∈ Subgroup.centralizer ({v} : Set G), conjSub g⁻¹ V = conjSub c⁻¹ V := by
  rw [mem_conjSub, inv_inv] at hvg

  have hsing := h1326 G T L V S g ⟨v, hv⟩ ⟨g * v * g⁻¹, hvg⟩ rfl
  have hw1 : S.frame.ψ ⟨g * v * g⁻¹, hvg⟩ ≠ 1 := by
    intro h
    apply hv1
    have : (⟨g * v * g⁻¹, hvg⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    have := congrArg Subtype.val this
    simp only [OneMemClass.coe_one] at this
    have e : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [e, this]; group
  have hv1' : S.frame.ψ ⟨v, hv⟩ ≠ 1 := by
    intro h
    apply hv1
    have : (⟨v, hv⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨σ, hσ, hσx⟩ := exists_alt_pact _ _ hw1 hv1' hsing.symm
  obtain ⟨l, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσ
  refine ⟨l * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := (S.psi_conj l ⟨g * v * g⁻¹, hvg⟩)
    rw [hlσ, hσx] at this
    have hlv : (l : G) * (g * v * g⁻¹) * (l : G)⁻¹ = v := by
      have := congrArg Subtype.val (S.frame.ψ.injective this)
      simpa using this
    calc l * g * v = (l : G) * (g * v * g⁻¹) * (l : G)⁻¹ * (l * g) := by group
      _ = v * (l * g) := by rw [hlv]
  · rw [mul_inv_rev, conjSub_mul, conjSub_self_of_mem (Subgroup.inv_mem _ l.2)]

end Setting

end CFSG.Quasithin.H13.A5
