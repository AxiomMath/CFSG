module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_V_le_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ s.fr.F := by
  have hcen : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  rw [hcen, SFrame.F]
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl <;> simp

theorem y54_F_le_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.F ≤ s.fr.B := by
  calc s.fr.F ≤ s.fr.E ⊔ s.fr.F := le_sup_right
    _ = s.fr.A ⊓ s.fr.B := hH.hLF.fact14.2.2.2.1.1
    _ ≤ s.fr.B := inf_le_right

theorem y54_B_le_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.B ≤ s.C₂ :=
  (le_sup_left : s.fr.B ≤ s.fr.B ⊔ zpowers s.t).trans (f3_P_le_C₂ hH)

theorem y54_t_mem_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.t ∈ s.C₂ :=
  f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))

theorem y54_C2_cent_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.C₂, ∀ v ∈ cen s.fr.B, x * v * x⁻¹ = v := by
  intro x hx v hv
  have hc := Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp (f3_C₂_le_Y hH hx)).2 v hv
  rw [← hc]
  group

theorem y54_C2_norm_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.C₂, ∀ b ∈ s.fr.B, x * b * x⁻¹ ∈ s.fr.B :=
  fun x hx b hb =>
    (Subgroup.mem_normalizer_iff.mp (f3_X_le_normB hH (f3_C₂_le_X hH hx)) b).mp hb

theorem y54_C2_comm_V (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.C₂, ∀ y ∈ c.s.C₂, ⁅x, y⁆ ∈ cen c.s.fr.B := by
  obtain ⟨hVn, hcomm⟩ := (y52_fact (c := c) hH).2.2.2
  haveI := hVn
  intro x hx y hy
  have hq : QuotientGroup.mk' ((cen c.s.fr.B).subgroupOf c.s.C₂)
      (⟨⁅x, y⁆, by
        rw [commutatorElement_def]
        exact c.s.C₂.mul_mem (c.s.C₂.mul_mem (c.s.C₂.mul_mem hx hy) (c.s.C₂.inv_mem hx))
          (c.s.C₂.inv_mem hy)⟩ : ↥c.s.C₂) = 1 := by
    rw [show (⟨⁅x, y⁆, _⟩ : ↥c.s.C₂) = ⁅(⟨x, hx⟩ : ↥c.s.C₂), ⟨y, hy⟩⁆ from rfl,
      map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    exact congrArg Subtype.val (hcomm.1.is_comm.comm
      ⟨QuotientGroup.mk' _ (⟨x, hx⟩ : ↥c.s.C₂), trivial⟩
      ⟨QuotientGroup.mk' _ (⟨y, hy⟩ : ↥c.s.C₂), trivial⟩)
  have hmem : (⟨⁅x, y⁆, by
        rw [commutatorElement_def]
        exact c.s.C₂.mul_mem (c.s.C₂.mul_mem (c.s.C₂.mul_mem hx hy) (c.s.C₂.inv_mem hx))
          (c.s.C₂.inv_mem hy)⟩ : ↥c.s.C₂) ∈ (cen c.s.fr.B).subgroupOf c.s.C₂ :=
    (QuotientGroup.eq_one_iff (N := (cen c.s.fr.B).subgroupOf c.s.C₂) _).mp (by
      simpa [QuotientGroup.mk'_apply] using hq)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem y54_C2_eq_M2t (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.C₂ = M2 c.s ⊔ zpowers c.s.t :=
  (y52_fact (c := c) hH).1

theorem y54_B_le_M2 (s : Setting3 G L) : s.fr.B ≤ M2 s :=
  le_sup_right

private theorem y54_V_le_M2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ M2 s :=
  (inf_le_left : cen s.fr.B ≤ s.fr.B).trans (y54_B_le_M2 s)

theorem y54_M2_le_C2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : M2 c.s ≤ c.s.C₂ := by
  have hcomm : ⁅c.s.C₂, normIn L c.s.fr.B⁆ ≤ c.s.C₂ := by
    apply Subgroup.commutator_le.mpr
    intro x hx n hn
    have hnX : n ∈ c.s.X :=
      f3_N_le_X c.s ⟨s3_L_le_H c.s hH.hS hn.1, hn.2⟩
    have hnx : n * x * n⁻¹ ∈ c.s.C₂ := f3_C₂_normal hH n hnX x hx
    rw [show ⁅x, n⁆ = x * (n * x * n⁻¹)⁻¹ by rw [commutatorElement_def]; group]
    exact c.s.C₂.mul_mem hx (c.s.C₂.inv_mem hnx)
  exact sup_le hcomm (y54_B_le_C2 hH)

theorem y54_t_notin_M2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.t ∉ M2 c.s := by
  intro ht
  have hle : zpowers c.s.t ≤ M2 c.s := by rwa [Subgroup.zpowers_le]
  have hsup : M2 c.s ⊔ zpowers c.s.t = M2 c.s := sup_eq_left.mpr hle
  have hC₂M2 : c.s.C₂ = M2 c.s := (y52_fact (c := c) hH).1.trans hsup
  exact (y52_fact (c := c) hH).2.1 hC₂M2.symm

theorem y54_M2_norm_C2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.C₂, ∀ m ∈ M2 c.s, x * m * x⁻¹ ∈ M2 c.s := by
  intro x hx m hm
  have hmC : m ∈ c.s.C₂ := y54_M2_le_C2 c hH hm
  have hcomm : ⁅x, m⁆ ∈ M2 c.s := y54_V_le_M2 hH (y54_C2_comm_V c hH x hx m hmC)
  rw [show x * m * x⁻¹ = ⁅x, m⁆ * m by rw [commutatorElement_def]; group]
  exact (M2 c.s).mul_mem hcomm hm

theorem y54_C2_cases (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.C₂, x ∈ M2 c.s ∨ ∃ m ∈ M2 c.s, x = m * c.s.t := by
  have hnorm : ∀ y ∈ zpowers c.s.t, ∀ m ∈ M2 c.s, y * m * y⁻¹ ∈ M2 c.s := by
    intro y hy m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact y54_M2_norm_C2 c hH (c.s.t ^ k)
      (c.s.C₂.zpow_mem (y54_t_mem_C2 hH) k) m hm
  intro x hx
  rw [y54_C2_eq_M2t c hH] at hx
  obtain ⟨m, hm, n, hn, hx'⟩ := mem_sup_of_normalizes (T := zpowers c.s.t) (C := M2 c.s)
    hnorm x (by rw [sup_comm]; exact hx)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hm' : c.s.t ^ k * n * (c.s.t ^ k)⁻¹ ∈ M2 c.s :=
    hnorm (c.s.t ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) n hn
  have hx'' : x = (c.s.t ^ k * n * (c.s.t ^ k)⁻¹) * c.s.t ^ k := by
    rw [hx']; group
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    have hk' : k % ((2 : ℕ) : ℤ) = 0 := hk
    have h1 : c.s.t ^ k = 1 := by
      rw [← zpow_mod_orderOf, c.s.t_order, hk']; simp
    rw [hx'', h1, mul_one]
    simpa only [h1] using hm'
  · right
    refine ⟨c.s.t ^ k * n * (c.s.t ^ k)⁻¹, hm', ?_⟩
    have hk' : k % ((2 : ℕ) : ℤ) = 1 := hk
    have h1 : c.s.t ^ k = c.s.t := by
      rw [← zpow_mod_orderOf, c.s.t_order, hk']; simp
    rw [hx'', h1]

theorem y54_M2_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ normIn s.H s.fr.B, ∀ m ∈ M2 s, n * m * n⁻¹ ∈ M2 s := by
  intro n hn m hm
  have hnH : n ∈ s.H := (Subgroup.mem_inf.mp hn).1
  have hnB : n ∈ Subgroup.normalizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hn).2
  have hnN : n ∈ Subgroup.normalizer (L : Set G) := s3_H_le_N s hH.hS hnH
  have hnX : n ∈ s.X := f3_N_le_X s hn
  have hC₂n : n ∈ Subgroup.normalizer (s.C₂ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => f3_C₂_normal hH n hnX x hx, fun hx => by
      have h := f3_C₂_normal hH n⁻¹ (s.X.inv_mem hnX) (n * x * n⁻¹) hx
      rwa [show n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x by group] at h⟩
  have hNLn : n ∈ Subgroup.normalizer (normIn L s.fr.B : Set G) := by
    have hnL' : n⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem hnN
    have hnB' : n⁻¹ ∈ Subgroup.normalizer (s.fr.B : Set G) :=
      (Subgroup.normalizer (s.fr.B : Set G)).inv_mem hnB
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp hnN x).mp hx.1, ?_⟩
      exact (Subgroup.normalizer (s.fr.B : Set G)).mul_mem
        ((Subgroup.normalizer (s.fr.B : Set G)).mul_mem hnB hx.2) hnB'
    · intro hx
      refine ⟨?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp hnL' (n * x * n⁻¹)).mp hx.1
        rwa [show n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x by group] at h
      · have h := (Subgroup.normalizer (s.fr.B : Set G)).mul_mem
          ((Subgroup.normalizer (s.fr.B : Set G)).mul_mem hnB' hx.2) hnB
        rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h
  have hH1n : n ∈ Subgroup.normalizer (⁅s.C₂, normIn L s.fr.B⁆ : Subgroup G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hC₂n,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hNLn]
  have hM2n : n ∈ Subgroup.normalizer (M2 s : Set G) := by
    have h := inf_normalizer_le_normalizer_sup (⁅s.C₂, normIn L s.fr.B⁆ : Subgroup G) s.fr.B
    exact h ⟨hH1n, hnB⟩
  exact (Subgroup.mem_normalizer_iff.mp hM2n m).mp hm

private theorem y54_F_le_L' (s : Setting3 G L) : s.fr.F ≤ L :=
  (s3_F_le_A s).trans (s3_A_le_L s)

private theorem y54_mem_P' (s : Setting3 G L) {p : G} (hp : p ∈ f4P s) :
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
          _ = b * (y * s.t) := by rw [← s3_comm_t_of_mem_L s (y54_F_le_L' s hy)]
          _ = b * y * s.t := by group
      · refine Or.inl ?_
        rw [show b * s.t * (c * s.t) = b * c by
          calc b * s.t * (c * s.t) = b * (s.t * c) * s.t := by group
            _ = b * (c * s.t) * s.t := by rw [← s3_comm_t_of_mem_L s (y54_F_le_L' s hc)]
            _ = b * c * (s.t * s.t) := by group
            _ = b * c := by rw [htt, mul_one]]
        exact s.fr.F.mul_mem hb hc
  · intro x _ hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · exact Or.inl (s.fr.F.inv_mem hx)
    · refine Or.inr ⟨b⁻¹, s.fr.F.inv_mem hb, ?_⟩
      have htb : s.t * b⁻¹ = b⁻¹ * s.t :=
        (s3_comm_t_of_mem_L s (y54_F_le_L' s (s.fr.F.inv_mem hb))).symm
      calc (b * s.t)⁻¹ = s.t⁻¹ * b⁻¹ := mul_inv_rev b s.t
        _ = s.t * b⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
        _ = b⁻¹ * s.t := htb

theorem y54_C2_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.C₂ ≤ f4X c.s := by
  have hVF : cen c.s.fr.B ≤ c.s.fr.F := y54_V_le_F hH
  have hnorm : ∀ y ∈ c.s.C₂, ∀ q ∈ f4P c.s, y * q * y⁻¹ ∈ f4P c.s := by
    intro y hy q hq
    rcases y54_mem_P' c.s hq with hqF | ⟨f, hf, rfl⟩
    · have hqC : q ∈ c.s.C₂ := y54_B_le_C2 hH (y54_F_le_B hH hqF)
      have hcomm := y54_C2_comm_V c hH y hy q hqC
      rw [show y * q * y⁻¹ = ⁅y, q⁆ * q by rw [commutatorElement_def]; group]
      exact Subgroup.mem_sup_left (c.s.fr.F.mul_mem (hVF hcomm) hqF)
    · have hfC : f ∈ c.s.C₂ := y54_B_le_C2 hH (y54_F_le_B hH hf)
      have hcomm := y54_C2_comm_V c hH y hy f hfC
      have hyt : y * c.s.t * y⁻¹ = f3phi c.s y * c.s.t := by unfold f3phi; group
      have hphi : f3phi c.s y ∈ c.s.fr.F :=
        hVF (f3_phi_mem hH y (f3_C₂_le_Y hH hy))
      rw [show y * (f * c.s.t) * y⁻¹ = (y * f * y⁻¹) * (y * c.s.t * y⁻¹) by group,
        show y * f * y⁻¹ = ⁅y, f⁆ * f by rw [commutatorElement_def]; group, hyt]
      exact (c.s.fr.F ⊔ zpowers c.s.t).mul_mem
        ((c.s.fr.F ⊔ zpowers c.s.t).mul_mem (Subgroup.mem_sup_left (hVF hcomm))
          (Subgroup.mem_sup_left hf))
        ((c.s.fr.F ⊔ zpowers c.s.t).mul_mem (Subgroup.mem_sup_left hphi)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro p
  exact ⟨hnorm x hx p, fun hp => by
    have h := hnorm x⁻¹ (c.s.C₂.inv_mem hx) (x * p * x⁻¹) hp
    rwa [show x⁻¹ * (x * p * x⁻¹) * (x⁻¹)⁻¹ = p by group] at h⟩

end CFSG.OddStandard.HigherRank.YamadaG23
