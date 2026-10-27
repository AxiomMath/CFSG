module

public import CFSG.GH74.QTGen4.Recog.Ku.HStruct

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] def kuPred (P H : Subgroup G) (z x y : G) : Prop :=
  ∀ n ∈ kuN P H, n * z * n⁻¹ = x → n⁻¹ * y * n ∈ kuW P H

open Classical in
@[expose] noncomputable def kuPolar (P H : Subgroup G) (z x y : G) : ZMod 2 :=
  if kuPred P H z x y then 0 else 1

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuPred_conj_iff (h : KuHyp G T M H P z) {n₀ : G} (hn₀ : n₀ ∈ kuN P H) (y : G) :
    kuPred P H z (n₀ * z * n₀⁻¹) y ↔ n₀⁻¹ * y * n₀ ∈ kuW P H := by
  constructor
  · intro hp
    exact hp n₀ hn₀ rfl
  · intro hy n hn hnz
    have h2 : n * z = n₀ * z * n₀⁻¹ * n := by rw [← hnz]; group
    have hmz : (n₀⁻¹ * n) * z = z * (n₀⁻¹ * n) := by
      calc (n₀⁻¹ * n) * z = n₀⁻¹ * (n * z) := by group
        _ = n₀⁻¹ * (n₀ * z * n₀⁻¹ * n) := by rw [h2]
        _ = z * (n₀⁻¹ * n) := by group
    have hmH : n₀⁻¹ * n ∈ H := by
      rw [h.hCz, Subgroup.mem_centralizer_singleton_iff]
      exact hmz
    have hmInv : (n₀⁻¹ * n)⁻¹ ∈ H := H.inv_mem hmH
    have hconj := (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_kuW hmInv) _).mp hy
    have e : n⁻¹ * y * n = (n₀⁻¹ * n)⁻¹ * (n₀⁻¹ * y * n₀) * (n₀⁻¹ * n)⁻¹⁻¹ := by group
    rw [e]
    exact hconj

theorem kuPred_z_iff (h : KuHyp G T M H P z) (y : G) :
    kuPred P H z z y ↔ y ∈ kuW P H := by
  have := h.kuPred_conj_iff (n₀ := 1) (Subgroup.one_mem (kuN P H)) y
  simpa using this

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
