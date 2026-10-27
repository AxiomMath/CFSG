module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Def
public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

private theorem aor_l12_U_card {t u : S} (h : L12Main S t u) :
    Nat.card (Subgroup.zpowers u) = 4 := by
  rw [Nat.card_zpowers, h.coord.ord_u]

private theorem aor_l12_U_le_N {t u : S} (h : L12Main S t u) :
    Subgroup.zpowers u ≤ L12N t := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.le_normalizer (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.coord.comm)

private theorem aor_l12_comm_iff [Finite S] {t u : S} (h : L12Main S t u)
    [(Subgroup.zpowers u).Normal] (x : S) :
    QuotientGroup.mk' (Subgroup.zpowers u) x ∈
        Subgroup.centralizer ({(t : S ⧸ Subgroup.zpowers u)} : Set _) ↔
      x ∈ L12N t := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have hx' : (x : S ⧸ Subgroup.zpowers u) * (t : S ⧸ Subgroup.zpowers u) =
        (t : S ⧸ Subgroup.zpowers u) * (x : S ⧸ Subgroup.zpowers u) := by
      simpa only [QuotientGroup.mk'_apply] using hx
    apply h.mem_N
    have h1 : QuotientGroup.mk' (Subgroup.zpowers u) (x * t * x⁻¹ * t⁻¹) = 1 := by
      simp only [map_mul, map_inv, QuotientGroup.mk'_apply]
      rw [hx']
      group
    exact (QuotientGroup.eq_one_iff (x * t * x⁻¹ * t⁻¹)).mp h1
  · intro hx
    rcases h.N_conj x hx with hc | hc
    · have hxt : x * t = t * x := by
        conv_rhs => rw [← hc]
        group
      calc QuotientGroup.mk' (Subgroup.zpowers u) x * QuotientGroup.mk' (Subgroup.zpowers u) t
          = QuotientGroup.mk' (Subgroup.zpowers u) (x * t) :=
            (map_mul (QuotientGroup.mk' (Subgroup.zpowers u)) x t).symm
        _ = QuotientGroup.mk' (Subgroup.zpowers u) (t * x) := by rw [hxt]
        _ = QuotientGroup.mk' (Subgroup.zpowers u) t * QuotientGroup.mk' (Subgroup.zpowers u) x :=
            map_mul (QuotientGroup.mk' (Subgroup.zpowers u)) t x
    · have hxt : x * t = t * u ^ 2 * x := by
        conv_rhs => rw [← hc]
        group
      have hmemU : u ^ 2 ∈ Subgroup.zpowers u :=
        Subgroup.pow_mem (Subgroup.zpowers u) (Subgroup.mem_zpowers u) 2
      have h2 : QuotientGroup.mk' (Subgroup.zpowers u) (u ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff (u ^ 2)).mpr hmemU
      have h3 : QuotientGroup.mk' (Subgroup.zpowers u) (t * u ^ 2 * x) =
          QuotientGroup.mk' (Subgroup.zpowers u) t *
            QuotientGroup.mk' (Subgroup.zpowers u) (u ^ 2) *
            QuotientGroup.mk' (Subgroup.zpowers u) x := by
        rw [map_mul, map_mul]
      calc QuotientGroup.mk' (Subgroup.zpowers u) x * QuotientGroup.mk' (Subgroup.zpowers u) t
          = QuotientGroup.mk' (Subgroup.zpowers u) (x * t) :=
            (map_mul (QuotientGroup.mk' (Subgroup.zpowers u)) x t).symm
        _ = QuotientGroup.mk' (Subgroup.zpowers u) (t * u ^ 2 * x) := by rw [hxt]
        _ = QuotientGroup.mk' (Subgroup.zpowers u) t *
              QuotientGroup.mk' (Subgroup.zpowers u) (u ^ 2) *
              QuotientGroup.mk' (Subgroup.zpowers u) x := h3
        _ = QuotientGroup.mk' (Subgroup.zpowers u) t *
              QuotientGroup.mk' (Subgroup.zpowers u) x := by rw [h2, mul_one]

private theorem aor_l12_centralizer_eq [Finite S] {t u : S} (h : L12Main S t u)
    [(Subgroup.zpowers u).Normal] :
    Subgroup.centralizer ({(t : S ⧸ Subgroup.zpowers u)} : Set _) =
      (L12N t).map (QuotientGroup.mk' (Subgroup.zpowers u)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers u) q
    exact Subgroup.mem_map.mpr ⟨x, (aor_l12_comm_iff h x).mp hq, rfl⟩
  · intro hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    exact (aor_l12_comm_iff h x).mpr hx

theorem aor_l12_quot_card [Finite S] {t u : S} (h : L12Main S t u)
    [(Subgroup.zpowers u).Normal] :
    Nat.card (Subgroup.centralizer
      ({(t : S ⧸ Subgroup.zpowers u)} : Set (S ⧸ Subgroup.zpowers u))) = 4 := by
  rw [aor_l12_centralizer_eq h]
  rw [← Subgroup.relIndex_ker (L12N t) (QuotientGroup.mk' (Subgroup.zpowers u)),
    QuotientGroup.ker_mk']
  rw [Subgroup.relIndex, Subgroup.index_eq_card_div]
  rw [h.N_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (aor_l12_U_le_N h)).toEquiv,
    aor_l12_U_card h]

end CFSG.OddStandard.SmallF3.Omega
