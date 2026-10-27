module

public import CFSG.LocalAnalysis.OddStandard.GH71.UFrame
public import CFSG.LocalAnalysis.OddStandard.GH71.Covers
public import CFSG.LocalAnalysis.OddStandard.GH71.Unbalanced3

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem sylow_T₂ (h : Ctx71 G z S U u) :
    Open.fusionIsSylowIn 2 (S ⊓ centralizer ({u} : Set G)) (centralizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCU := h.centralizer_U
  refine ⟨?_, h.S2.to_le inf_le_left, ?_⟩
  · rw [hCU]; exact le_inf (inf_le_left.trans h.S_le) inf_le_right
  intro Q hQ hQ2 hTQ
  by_contra hne
  have hlt : S ⊓ centralizer ({u} : Set G) < Q := lt_of_le_of_ne hTQ (Ne.symm hne)
  have hQM : Q ≤ Cen z := hQ.trans (hCU ▸ inf_le_left)
  have hQu : Q ≤ centralizer ({u} : Set G) := hQ.trans (hCU ▸ inf_le_right)
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hgt : 2 ^ 7 < Nat.card Q := h.card_T₂ ▸ card_lt_of_lt' hlt
  have hcardQ : 2 ^ 8 ≤ Nat.card Q := by
    rw [hk] at hgt ⊢
    exact Nat.pow_le_pow_right (by norm_num) (by
      by_contra hk8; push Not at hk8
      have : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  obtain ⟨P₀, hP₀⟩ := h.ctx.sylow
  obtain ⟨P', hP'⟩ := (hQ2.comap_subtype (K := Cen z)).exists_le_sylow
  have hP'card : Nat.card P' = 2 ^ 8 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P₀]
    rw [← h.card_S, ← hP₀, card_map_of_injective (Cen z).subtype_injective]
  have hQcard : Nat.card (Q.subgroupOf (Cen z)) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv
  have hQP' : Q.subgroupOf (Cen z) = (P' : Subgroup ↥(Cen z)) :=
    eq_of_le_of_card_ge hP' (by rw [hP'card, hQcard]; exact hcardQ)
  refine h.not_mem_center h.u_mem h.u_ne_one h.u_ne_z ?_
  refine mem_center_of_mem_center_sylow (n := 11) (by norm_num) h.cover
    (P'.mapSurjective (QuotientGroup.mk'_surjective _)) ?_ ?_
  · intro s hs
    rw [Sylow.coe_mapSurjective, ← hQP'] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hQu (Subgroup.mem_subgroupOf.mp hs'))
  · rw [← map_mul]
    have : (⟨u, h.U_le.trans h.S_le h.u_mem⟩ * ⟨u, h.U_le.trans h.S_le h.u_mem⟩ : ↥(Cen z)) = 1 :=
      Subtype.ext (h.sq_eq_one_of_mem_U h.u_mem)
    rw [this, map_one]

theorem exists_conj_u (h : Ctx71 G z S U u) :
    ∃ g ∈ normalizer (U : Set G) ⊓
        normalizer ((S ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G),
      g * z * g⁻¹ = u := by
  have htr := transOn_of_three_dvd h.U_four (by rw [h.aut6]; exact ⟨2, rfl⟩)
  obtain ⟨n₀, hn₀, hn₀z⟩ := htr z h.z_mem h.z_ne_one u h.u_mem h.u_ne_one
  have hCN : centralizer (U : Set G) ≤ normalizer (U : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem (fun y hy => by
      have e : x * y * x⁻¹ = y := by rw [(mem_centralizer_iff.mp hx y hy).symm]; group
      rw [e]; exact hy)
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer U
  have hcov := covers_frattini' Nat.prime_two hCN hNC h.sylow_T₂
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    (covers_iff (fun y hy => hNC hy.2)).mp hcov n₀ hn₀
  refine ⟨a, ⟨ha.2, ha.1⟩, ?_⟩
  have hcz : c * z * c⁻¹ = z := by
    rw [mem_centralizer_iff.mp hc z h.z_mem |>.symm]; group
  rw [← hn₀z]
  calc a * z * a⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by rw [hcz]
    _ = a * c * z * (a * c)⁻¹ := by group

end Ctx71

end CFSG.OddStandard.GH71
