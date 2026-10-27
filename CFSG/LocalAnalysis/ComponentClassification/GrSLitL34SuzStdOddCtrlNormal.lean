module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Fixed

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

theorem lamLike2_centralizer_inf_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) :
    EvenSporadicStandard.Induction.LamLike2 8
      ↥(centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) := by
  refine ⟨isSolvable_centralizer_inf_of_l34SuzOdd hS hD, fun P hP2 => ?_⟩
  have hPle : P.map (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)).subtype ≤
      centralizer ({t} : Set G) ⊓ centralizer (K : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP2' := hP2.map (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)).subtype
  refine ⟨fun x hx => ?_, ?_⟩
  · exact Subtype.ext
      (mul_self_eq_one_of_isPGroup_of_l34SuzOdd hS hD hPle hP2' (x : G) ⟨x, hx, rfl⟩)
  · rw [← Subgroup.card_map_of_injective
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)).subtype_injective]
    exact card_le_eight_of_isPGroup_of_l34SuzOdd hS hD hPle hP2'

theorem involutionFixesNotLam2_of_l34SuzOddData
    (hD : L34SuzOddData A V K y) :
    EvenSporadicStandard.Induction.InvolutionFixesNotLam2 ↥K 8 := by
  have hperf : Group.IsPerfect ↥K := by
    refine ⟨?_⟩
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hD.perfect]
  obtain ⟨ψ⟩ := EvenSporadicStandard.L34Q8.nonempty_equiv_S_of_lieModel hD.l34
  obtain ⟨π, hπ, hker⟩ := EvenSporadicStandard.L34Q8.exists_cover_map (MulEquiv.refl _) ψ
  exact EvenSporadicStandard.L34Q8.involutionFixesNotLam2_eight hperf π hπ hker

theorem le_normalizer_of_isComponent_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {X : Subgroup G} (htX : t ∈ X) (hKX : K ≤ X) (hK : IsComponent (K.subgroupOf X)) :
    X ≤ normalizer (K : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have hN : normalizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    apply le_antisymm
    · intro g hg
      rw [mem_centralizer_singleton_iff]
      have hmem : g * t * g⁻¹ ∈ zpowers t := (mem_normalizer_iff.1 hg t).1 (mem_zpowers t)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
      rw [← zpow_mod_orderOf, hS.orderOf_t] at hk
      push_cast at hk
      have h01 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases h01 with h | h
      · rw [h, zpow_zero] at hk
        have h1 : t = 1 := by
          calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
            _ = 1 := by rw [← hk]; group
        have h2 := hS.orderOf_t
        rw [h1, orderOf_one] at h2
        omega
      · rw [h, zpow_one] at hk
        calc g * t = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [← hk]
    · intro g hg
      rw [mem_centralizer_singleton_iff] at hg
      have hc : Commute g t := hg
      rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
        rw [show g * t ^ k * g⁻¹ = t ^ k by rw [(hc.zpow_right k).eq, mul_inv_cancel_right]]
        exact zpow_mem (mem_zpowers t) k
      · intro hh
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hh
        have e : h = t ^ k := by
          calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
            _ = g⁻¹ * (t ^ k * g) := by rw [← hk, mul_assoc]
            _ = t ^ k := by rw [← (hc.zpow_right k).eq]; group
        rw [e]
        exact zpow_mem (mem_zpowers t) k
  have hKA := le_A_of_l34SuzOddData hD
  have htK : t ∈ centralizer (K : Set G) := fun k hk => (hS.t_mem k (hKA hk))
  have hn := EvenSporadicStandard.Induction.normal_of_component_emb (L := zpowers t)
    ⟨hKX, hK⟩ htX htK ht2 hN.ge
    (by rw [hN]; exact isSolvable_centralizer_inf_of_l34SuzOdd hS hD)
    (by
      rw [hN]
      exact EvenSporadicStandard.Induction.NoFixedEmbeds.of_lamLike2
        (involutionFixesNotLam2_of_l34SuzOddData hD) (lamLike2_centralizer_inf_of_l34SuzOdd hS hD))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hn

theorem centralizer_le_normalizer_K_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hK : IsComponent (K.subgroupOf (centralizer ({u} : Set G)))) :
    centralizer ({u} : Set G) ≤ normalizer (K : Set G) :=
  le_normalizer_of_isComponent_of_l34SuzOdd hS hD
    (mem_centralizer_singleton_iff.2 (hS.t_mem u (hD.le_A hu)).symm)
    (le_centralizer_of_l34SuzOddData hD hu) hK

end CFSG.ComponentClassification.GrSLit.L34Sec5S
