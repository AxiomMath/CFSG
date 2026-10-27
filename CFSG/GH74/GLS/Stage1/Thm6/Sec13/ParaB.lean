module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.SylowB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.PermV
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem conj_mem_cent {V : Subgroup G} {n c : G} (hn : n ∈ normalizer (V : Set G))
    (hc : c ∈ centralizer (V : Set G)) : n * c * n⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : n⁻¹ * v * n ∈ V := (mem_normalizer_iff''.1 hn v).1 hv
  have hc' := mem_centralizer_iff.1 hc (n⁻¹ * v * n) hv'
  calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [hc']
    _ = (n * c * n⁻¹) * v := by group

theorem frattini_N [Finite G] {V H : Subgroup G} (hsyl : Sylow2In H (centralizer (V : Set G)))
    {n : G} (hn : n ∈ normalizer (V : Set G)) :
    ∃ c ∈ centralizer (V : Set G), c⁻¹ * n ∈ normalizer (H : Set G) :=
  sylowIn_frattini (p := 2) (P := H) (N := centralizer (V : Set G)) (M := normalizer (V : Set G))
    hsyl (fun _ hm _ hc => conj_mem_cent hm hc) hn

theorem relIndex_eq_of_mul [Finite G] (V : Subgroup G) {Q Q' : Subgroup G} (hQQ' : Q ≤ Q')
    (hQ' : Q' ≤ normalizer (V : Set G))
    (h : ∀ q' ∈ Q', ∃ c ∈ centralizer (V : Set G), ∃ q ∈ Q, q' = c * q) :
    (centralizer (V : Set G) ⊓ Q).relIndex Q = (centralizer (V : Set G) ⊓ Q').relIndex Q' := by
  apply Nat.dvd_antisymm (relIndex_dvd_of_le V hQQ' hQ')
  rw [relIndex_eq_card_range V hQ', relIndex_eq_card_range V (hQQ'.trans hQ')]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨⟨q', hq'⟩, rfl⟩
  obtain ⟨c, hc, q, hq, hqq⟩ := h q' hq'
  refine ⟨⟨q, hq⟩, ?_⟩
  ext v
  show (q : G) * (v : G) * (q : G)⁻¹ = (q' : G) * (v : G) * (q' : G)⁻¹
  have hqN : (q : G) ∈ normalizer (V : Set G) := hQ' (hQQ' hq)
  have hw : (q : G) * (v : G) * (q : G)⁻¹ ∈ V := (mem_normalizer_iff.1 hqN v).1 v.2.1
  have hcw := mem_centralizer_iff.1 hc _ hw
  rw [hqq]
  calc (q : G) * (v : G) * (q : G)⁻¹ = (c * ((q : G) * (v : G) * (q : G)⁻¹)) * c⁻¹ := by
        rw [← hcw]; group
    _ = c * q * v * (c * q)⁻¹ := by group

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
