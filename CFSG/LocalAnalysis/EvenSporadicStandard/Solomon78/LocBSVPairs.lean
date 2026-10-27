module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSFuse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLemma39N

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

theorem vPairs_nonempty_of_mem {L K : Subgroup G} {u v : G} (hv : v ∈ vMaximal K u)
    (hl : ∃ l ∈ L, l * u * l⁻¹ = u * v) : (vPairs L K u).Nonempty :=
  ⟨u * v, v, hv, rfl, hl⟩

variable [Finite G]

omit [Finite G] in
theorem generate_of_one {L K : Subgroup G} {u w l₀ : G} (hl₀ : l₀ ∈ L) (hconj : l₀ * u * l₀⁻¹ = w)
    (hnorm : ∀ c ∈ L ⊓ centralizer ({u} : Set G), K.map (conjHom c) = K)
    (hgen : K ⊔ K.map (conjHom l₀) = L) :
    ∀ l ∈ L, l * u * l⁻¹ = w → K ⊔ K.map (conjHom l) = L := by
  intro l hl hlw
  have hd : l₀⁻¹ * l ∈ L ⊓ centralizer ({u} : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hl₀) hl, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : l * u * l⁻¹ = l₀ * u * l₀⁻¹ := by rw [hlw, hconj]
    calc l₀⁻¹ * l * u = l₀⁻¹ * (l * u * l⁻¹) * l := by group
      _ = l₀⁻¹ * (l₀ * u * l₀⁻¹) * l := by rw [h1]
      _ = u * (l₀⁻¹ * l) := by group
  have h1 : K.map (conjHom l) = K.map (conjHom l₀) := by
    have e : conjHom l = (conjHom l₀).comp (conjHom (l₀⁻¹ * l)) := by
      rw [← conjHom_mul, mul_inv_cancel_left]
    rw [e, ← Subgroup.map_map, hnorm _ hd]
  rw [h1, hgen]

omit [Finite G] in
theorem generate_conj_reduce {L K : Subgroup G} {c l₀ : G} (hcL : c ∈ L)
    (hKc : K.map (conjHom c) = K) (hgen : K ⊔ K.map (conjHom l₀) = L) :
    K ⊔ K.map (conjHom (c * l₀)) = L := by
  have e : K.map (conjHom (c * l₀)) = (K.map (conjHom l₀)).map (conjHom c) := by
    rw [conjHom_mul, ← Subgroup.map_map]
  calc K ⊔ K.map (conjHom (c * l₀)) = K.map (conjHom c) ⊔ (K.map (conjHom l₀)).map (conjHom c) := by
        rw [e, hKc]
    _ = (K ⊔ K.map (conjHom l₀)).map (conjHom c) := (Subgroup.map_sup _ _ _).symm
    _ = L := by rw [hgen]; exact map_conj_eq_of_mem' hcL

omit [Finite G] in
theorem mem_vMaximal_of_oneClass {K : Subgroup G} {u v : G} (huK : u ∈ K)
    (hone : OneClassOutside K) (hv : v ∈ vCandidates K u) : v ∈ vMaximal K u := by
  have hKsup : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 huK)
  refine ⟨hv, fun v' hv' => ?_⟩
  have hvK : v ∈ K := hKsup ▸ hv.1
  have hv'K : v' ∈ K := hKsup ▸ hv'.1
  obtain ⟨c, hcK, hc⟩ := hone v' hv'K v hvK
    (mul_self_eq_one_of_orderOf hv'.2.2) (mul_self_eq_one_of_orderOf hv.2.2)
    (ne_one_of_orderOf hv'.2.2) (ne_one_of_orderOf hv.2.2) hv'.2.1 hv.2.1
  rw [← hc, twoAdic_inf_centralizer_conj (map_conj_eq_of_mem hcK) v']

end CFSG.EvenSporadicStandard.Solomon78
