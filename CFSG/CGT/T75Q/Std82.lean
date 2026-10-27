module

public import CFSG.CGT.T75Q.CentU
public import CFSG.CGT.T75Q.OrdersSL
public import CFSG.CGT.T75P.NatTrans

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G] {T T₁ : Subgroup G}

structure Std82 (T T₁ : Subgroup G) : Prop where
  h1 : Sec4NoA
  h62 : Sec62
  h63 : Sec63
  h66 : Sec66
  hc : Sec6Ctx T T₁ 4 1
  hnat : NaturalSL T (hSub T (normIn T₁ T)) 4 1

theorem eq_one_of_forall_comm_of_simple [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {c : G} (hc : ∀ g : G, g * c = c * g) : c = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · have : c ∈ Subgroup.center G := Subgroup.mem_center_iff.2 hc
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

namespace Std82

theorem hTH (_s : Std82 T T₁) : T ≤ hSub T (normIn T₁ T) := (hSub_data T T₁).1

theorem hHN (_s : Std82 T T₁) : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
  (hSub_data T T₁).2.1

theorem hTU (_s : Std82 T T₁) : T ≤ ugen T := T_le_ugen

variable (s : Std82 T T₁)

include s

theorem finite : Finite G := s.hc.finite

theorem simple : IsSimpleGroup G := s.hc.hy.simple

theorem wc : IsWC T := s.hc.hy.pair.wc

theorem card_T : Nat.card T = 16 := by
  have := s.hc.hT
  norm_num at this
  exact this

theorem exists_ne_one : ∃ t ∈ T, t ≠ 1 := exists_ne_one_of_ctx s.hc

theorem h66' :
    ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T :=
  h66_of_ctx s.h66 s.hc

theorem hHC : hSub T (normIn T₁ T) ⊓ Subgroup.centralizer (T : Set G) = T :=
  inf_centralizer_eq_of_natural s.hTH s.hHN s.hnat

theorem htrans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y :=
  natural_trans s.hHN s.hnat

theorem hH2 : ¬ IsPGroup 2 (hSub T (normIn T₁ T)) := by
  have := s.finite
  exact not_isPGroup_of_natural_four s.hTH s.card_T s.hnat

theorem hHgen : hSub T (normIn T₁ T) ≤
    Subgroup.closure {x | x ∈ hSub T (normIn T₁ T) ∧ x * x = 1} := by
  refine s.hc.hSub_le_closure.trans (Subgroup.closure_mono ?_)
  intro x hx
  exact ⟨s.hc.normD_le_hSub s.h1 s.h63 (sec64Eight_of s.h62 s.h63) hx,
    mul_self_eq_one_of_mem_classD s.wc.1 hx.1⟩

theorem hprod : ∀ g ∈ Subgroup.normalizer (T : Set G), ∃ h ∈ hSub T (normIn T₁ T),
    ∃ c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G), g = h * c :=
  fun _ hg => normalizer_eq_mul s.h62 s.h63 s.hc s.hnat chain4 hg

theorem hinf : hSub T (normIn T₁ T) ⊓ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) = ⊥ :=
  inf_hSub_centralizer_eq_bot s.hc s.hnat

theorem hCeq : Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) =
    Subgroup.centralizer (ugen T : Set G) :=
  centralizer_hSub_eq_centralizer_ugen s.h1 s.h62 s.h63 s.h66 s.hc s.hnat chain4 (by norm_num)

theorem hHU : hSub T (normIn T₁ T) ≤ ugen T := hSub_le_ugen s.hc (by norm_num)

theorem hN : ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T) := by
  have := s.finite
  exact hN_ugen s.wc s.hc.hS (two_dvd_card_of_ctx s.hc (by norm_num))

theorem hCU : ∀ c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G), c ∈ ugen T →
    ∀ u ∈ ugen T, c * u = u * c := by
  intro c hc _ u hu
  rw [s.hCeq] at hc
  exact (Subgroup.mem_centralizer_iff.1 hc u hu).symm

theorem ne_top_of_centralizer {V : Subgroup G} {c : G}
    (hcV : c ∈ Subgroup.centralizer (V : Set G)) (hc1 : c ≠ 1) : V ≠ ⊤ := by
  intro hV
  have := s.simple
  apply hc1
  refine eq_one_of_forall_comm_of_simple s.hc.hy.nonab fun g => ?_
  rw [hV] at hcV
  exact Subgroup.mem_centralizer_iff.1 hcV g (Subgroup.mem_top g)

end Std82

end CFSG.CGT.T75Q
