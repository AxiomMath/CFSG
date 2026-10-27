module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSt1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RPn
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mem_normalizer_of_mapsTo {H : Subgroup G} {g : G} (hg : g * g = 1)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hcalc : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [show g⁻¹ = g from inv_eq_of_mul_eq_one_right hg]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg]; simp
  have hx' := h (g * x * g⁻¹) hx
  rwa [hcalc] at hx'

theorem y7n_exists_sylow {V Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQV : Q ≤ V) :
    ∃ P1 : Subgroup G, IsSylowIn 2 V P1 ∧ Q ≤ P1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Subgroup ↥V := Q.subgroupOf V
  have hQ' : IsPGroup 2 Q' := hQ.comap_subtype
  obtain ⟨P', hP'⟩ := hQ'.exists_le_sylow
  refine ⟨(P' : Subgroup ↥V).map V.subtype, ?_, ?_⟩
  · have hgrp : IsPGroup 2 ((P' : Subgroup ↥V).map V.subtype) :=
      IsPGroup.map (H := (P' : Subgroup ↥V)) P'.isPGroup' V.subtype
    have hsub : (((P' : Subgroup ↥V).map V.subtype).subgroupOf V) = P' :=
      Subgroup.comap_map_eq_self_of_injective V.subtype_injective P'
    refine ⟨Subgroup.map_subtype_le (P' : Subgroup ↥V), hgrp, ?_⟩
    rw [Subgroup.relIndex, hsub]
    exact P'.not_dvd_index
  · intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQV hx⟩, hP' (by rwa [Subgroup.mem_subgroupOf]), rfl⟩

theorem y7n_Q_pgroup {c : Ctx7 G L} (hRT : c.s.R ≠ c.s.T) (h5 : c.toCtx5.Facts5)
    (h7 : c.Upto79) : IsPGroup 2 ↥(P7 c.e ⊔ (closure {c.g, c.s.t} : Subgroup G)) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, h72⟩, h73⟩, h74⟩, h75⟩, h76⟩, h77⟩, h78⟩, h79⟩ := h7
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (P7 c.e) := y7n_P_pgroup h76
  have hgpow : c.g ^ 2 = 1 := (c.g_spec hRT).2.2.2.1
  have hg2 : c.g * c.g = 1 := by simpa [pow_two] using hgpow
  have hg1 : c.g ≠ 1 := by
    intro h
    exact (c.g_spec hRT).2.1 (h ▸ c.s.R.one_mem)
  have hgt_comm : c.g * c.s.t = c.s.t * c.g :=
    Subgroup.mem_centralizer_singleton_iff.mp (c.s.sylow_T.1 (c.g_spec hRT).1)
  have hCl : IsPGroup 2 (closure {c.g, c.s.t} : Subgroup G) := by
    have hle : (closure {c.g, c.s.t} : Subgroup G) ≤ zpowers c.g ⊔ zpowers c.s.t := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c.g)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
    refine (IsPGroup.to_sup_of_normal_right' (H := zpowers c.g) (K := zpowers c.s.t)
      ?_ ?_ ?_).to_le hle
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, orderOf_eq_prime hgpow hg1, pow_one])
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, c.s.t_order, pow_one])
    · rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer ((zpowers c.s.t : Subgroup G) : Set G) ?_
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact hgt_comm
  have hgnP : c.g ∈ normalizer (P7 c.e : Set G) :=
    mem_normalizer_of_mapsTo hg2 (y7n_g_norm_P hRT h71 h72 h75)
  have htP : c.s.t ∈ normalizer (P7 c.e : Set G) := c.t_mem_normalizer_P7 h5.2.1 h71
  have hHnorm : (closure {c.g, c.s.t} : Subgroup G) ≤ normalizer (P7 c.e : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hgnP
    · exact htP
  have hsup := IsPGroup.to_sup_of_normal_right' hCl hP hHnorm
  rw [sup_comm (closure {c.g, c.s.t}) (P7 c.e)] at hsup
  exact hsup

theorem y7n_Q_le_N_K {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    (h5 : c.toCtx5.Facts5) (h7 : c.Upto79) :
    P7 c.e ⊔ (closure {c.g, c.s.t} : Subgroup G) ≤ normalizer (K7 c.s : Set G) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, h72⟩, h73⟩, h74⟩, h75⟩, h76⟩, h77⟩, h78⟩, h79⟩ := h7
  refine sup_le ?_ ?_
  · exact le_trans h77.1.1 Subgroup.le_normalizer
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    ·
      apply y7n_N_M3_le_N_K c.s
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm
      · rintro m ⟨n, hn, rfl⟩
        simpa [MulAut.conj_apply, h5.2.2.2.1 hRT n hn] using hn
      · intro m hm
        exact Subgroup.mem_map.mpr
          ⟨m, hm, by simp [MulAut.conj_apply, h5.2.2.2.1 hRT m hm]⟩
    ·
      apply y7n_N_M3_le_N_K c.s
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := y7n_t_norm_M3 c.toCtx5 hH
      rwa [conjSub] at h

theorem y7n_exists_P1 {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    (h5 : c.toCtx5.Facts5) (h7 : c.Upto79) :
    ∃ P1 : Subgroup G, IsSylowIn 2 (normalizer (K7 c.s : Set G)) P1 ∧
      P7 c.e ⊔ (closure {c.g, c.s.t} : Subgroup G) ≤ P1 := by
  exact y7n_exists_sylow
    (V := normalizer (K7 c.s : Set G))
    (Q := P7 c.e ⊔ (closure {c.g, c.s.t} : Subgroup G))
    (y7n_Q_pgroup hRT h5 h7) (y7n_Q_le_N_K hH hRT h5 h7)

end CFSG.OddStandard.HigherRank.YamadaG23
