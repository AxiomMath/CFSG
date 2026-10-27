module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_F_le_L (s : Setting3 G L) : s.fr.F ≤ L :=
  (s3_F_le_A s).trans (s3_A_le_L s)

theorem y54_t_comm_F (s : Setting3 G L) : ∀ f ∈ s.fr.F, f * s.t = s.t * f :=
  fun f hf => s3_comm_t_of_mem_L s (y54_F_le_L s hf)

theorem y54_F_isE3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsE 3 ↥s.fr.F :=
  s3_isE3_F hH.hS hH.hZ hH.hOut s

theorem y54_F_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.F, f ^ 2 = 1 := by
  have hE := y54_F_isE3 hH
  intro f hf
  simpa using congrArg Subtype.val (hE.1.2 ⟨f, hf⟩ (Subgroup.mem_top _))

theorem y54_F_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.F, ∀ f' ∈ s.fr.F, f * f' = f' * f := by
  have hE := y54_F_isE3 hH
  intro f hf f' hf'
  have hcomm := hE.1.1.is_comm.comm
    (⟨⟨f, hf⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥s.fr.F))
    (⟨⟨f', hf'⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥s.fr.F))
  exact congrArg Subtype.val (congrArg Subtype.val hcomm)

theorem y54_mem_P (s : Setting3 G L) {p : G} (hp : p ∈ f4P s) :
    p ∈ s.fr.F ∨ ∃ f ∈ s.fr.F, p = f * s.t := by
  have htt : s.t * s.t = 1 := by rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  rw [show f4P s = Subgroup.closure ((s.fr.F : Set G) ∪ (Subgroup.zpowers s.t : Set G)) from
    Subgroup.sup_eq_closure _ _] at hp
  refine Subgroup.closure_induction (p := fun p _ => p ∈ s.fr.F ∨ ∃ f ∈ s.fr.F, p = f * s.t)
    ?_ ?_ ?_ ?_ hp
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rcases Int.emod_two_eq_zero_or_one n with h2 | h2
      · left
        have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
        rw [show s.t ^ n = 1 by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp]
        exact s.fr.F.one_mem
      · right
        have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
        exact ⟨1, s.fr.F.one_mem, by
          rw [show s.t ^ n = s.t by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp,
            one_mul]⟩
  · exact Or.inl s.fr.F.one_mem
  · intro x y _ _ hx hy
    rcases hx with hx | ⟨b, hb, rfl⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · exact Or.inl (s.fr.F.mul_mem hx hy)
      · exact Or.inr ⟨x * c, s.fr.F.mul_mem hx hc, by group⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · refine Or.inr ⟨b * y, s.fr.F.mul_mem hb hy, ?_⟩
        calc b * s.t * y = b * (s.t * y) := by group
          _ = b * (y * s.t) := by rw [← s3_comm_t_of_mem_L s (y54_F_le_L s hy)]
          _ = b * y * s.t := by group
      · refine Or.inl ?_
        rw [show b * s.t * (c * s.t) = b * c by
          calc b * s.t * (c * s.t) = b * (s.t * c) * s.t := by group
            _ = b * (c * s.t) * s.t := by rw [← s3_comm_t_of_mem_L s (y54_F_le_L s hc)]
            _ = b * c * (s.t * s.t) := by group
            _ = b * c := by rw [htt, mul_one]]
        exact s.fr.F.mul_mem hb hc
  · intro x _ hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · exact Or.inl (s.fr.F.inv_mem hx)
    · refine Or.inr ⟨b⁻¹, s.fr.F.inv_mem hb, ?_⟩
      have htb : s.t * b⁻¹ = b⁻¹ * s.t :=
        (s3_comm_t_of_mem_L s (y54_F_le_L s (s.fr.F.inv_mem hb))).symm
      calc (b * s.t)⁻¹ = s.t⁻¹ * b⁻¹ := mul_inv_rev b s.t
        _ = s.t * b⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
        _ = b⁻¹ * s.t := htb

theorem y54_mem_P_not_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {p : G}
    (hp : p ∈ f4P s) (hpL : p ∉ L) : ∃ f ∈ s.fr.F, p = f * s.t := by
  rcases y54_mem_P s hp with h | h
  · exact absurd (y54_F_le_L s h) hpL
  · exact h

theorem y54_ft_conj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.F, ∃ g : G, g * s.t * g⁻¹ = f * s.t := by
  intro f hf
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  by_cases hf1 : f = 1
  · exact ⟨1, by rw [hf1]; group⟩
  · have hfL : f ∈ L := y54_F_le_L s hf
    have hfsq : f ^ 2 = 1 := y54_F_sq hH f hf
    have hford : orderOf f = 2 := orderOf_eq_prime hfsq hf1
    have hzord : orderOf s.fr.z = 2 := s3_z_order s hA
    obtain ⟨l, hlL, hl⟩ :=
      s3_invol_conj hH.hS hH.hZ s (u := s.fr.z) (v := f) (s3_z_mem_L s) hzord hfL hford
    have hzmem : s.fr.z ∈ cen s.fr.S := by
      rw [s3_cen_S s hA]
      exact Subgroup.mem_zpowers s.fr.z
    have hzt_mem : s.fr.z * s.t ∈ s.tCoset (cen s.fr.S) := ⟨s.fr.z, hzmem, rfl⟩
    have hzt_conj : s.fr.z * s.t ∈ conjClass e.T₁ s.t := by
      rw [hH.hDef.2.2]
      exact hzt_mem
    obtain ⟨x, -, hx⟩ := hzt_conj
    refine ⟨l * x, ?_⟩
    have hlt : Commute l s.t := s3_comm_t_of_mem_L s hlL
    have htl : s.t * l⁻¹ = l⁻¹ * s.t := hlt.symm.inv_right.eq
    calc (l * x) * s.t * (l * x)⁻¹
        = l * (x * s.t * x⁻¹) * l⁻¹ := by group
      _ = l * (s.fr.z * s.t) * l⁻¹ := by rw [← hx]
      _ = l * s.fr.z * (s.t * l⁻¹) := by group
      _ = l * s.fr.z * (l⁻¹ * s.t) := by rw [htl]
      _ = l * s.fr.z * l⁻¹ * s.t := by group
      _ = f * s.t := by rw [← hl]

theorem y54_tX_sub {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ f4X s, ∃ v ∈ s.fr.F, x * s.t * x⁻¹ = v * s.t := by
  intro x hx
  have hxP : x ∈ Subgroup.normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G) := hx
  have hxtxP : x * s.t * x⁻¹ ∈ s.fr.F ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP s.t).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  exact y54_mem_P_not_L hH hxtxP (hH.h31.2.2.1 x)

private theorem y54_conj_mem_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hx : x ∈ f4X s) : ∀ f ∈ s.fr.F, x * f * x⁻¹ ∈ s.fr.F := by
  intro f hf
  have hxP : x ∈ Subgroup.normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G) := hx
  have hftP : f * s.t ∈ s.fr.F ⊔ zpowers s.t :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hf)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hftxP : x * (f * s.t) * x⁻¹ ∈ s.fr.F ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP (f * s.t)).mp hftP
  have hftx_notL : x * (f * s.t) * x⁻¹ ∉ L := by
    obtain ⟨g, hg⟩ := y54_ft_conj hH f hf
    intro hmem
    refine hH.h31.2.2.1 (x * g) ?_
    rw [show (x * g) * s.t * (x * g)⁻¹ = x * (f * s.t) * x⁻¹ by rw [← hg]; group]
    exact hmem
  obtain ⟨b₁, hb₁F, hb₁⟩ := y54_mem_P_not_L hH hftxP hftx_notL
  have htxP : x * s.t * x⁻¹ ∈ s.fr.F ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP s.t).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  obtain ⟨b₂, hb₂F, hb₂⟩ := y54_mem_P_not_L hH htxP (hH.h31.2.2.1 x)
  have hcalc : x * f * x⁻¹ = b₁ * b₂⁻¹ := by
    calc x * f * x⁻¹ = (x * (f * s.t) * x⁻¹) * (x * s.t * x⁻¹)⁻¹ := by group
      _ = (b₁ * s.t) * (b₂ * s.t)⁻¹ := by rw [hb₁, hb₂]
      _ = b₁ * b₂⁻¹ := by group
  rw [hcalc]
  exact s.fr.F.mul_mem hb₁F (s.fr.F.inv_mem hb₂F)

theorem y54_X_le_normF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f4X s ≤ normalizer (s.fr.F : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    exact y54_conj_mem_F hH hx f hf
  · intro hf
    have hmem := y54_conj_mem_F hH ((f4X s).inv_mem hx) (x * f * x⁻¹) hf
    rwa [show x⁻¹ * (x * f * x⁻¹) * (x⁻¹)⁻¹ = f by group] at hmem

end CFSG.OddStandard.HigherRank.YamadaG23
