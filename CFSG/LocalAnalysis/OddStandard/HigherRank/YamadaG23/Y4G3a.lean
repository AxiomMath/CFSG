module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Ctx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem y4_F_sup_g_isE (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1)
    (hgσ : ActsAs L g s.fr'.σ) : IsE 4 ↥(s.fr.F ⊔ zpowers g) := by
  have h15 : (frameWith s g).Fact15 := (c.hLF.sigma g hg2 hgσ).2.1
  have h4 : IsE 4 ↥((frameWith s g).F ⊔ closure {(frameWith s g).σ}) := h15.2.2.2.1.2.1
  have h4' : IsE 4 ↥(s.fr.F ⊔ closure {g}) := h4
  rw [Subgroup.zpowers_eq_closure]
  exact h4'

private theorem y4_g_ne_one (c : Ctx4 s e) {g : G} (hgσ : ActsAs L g s.fr'.σ) : g ≠ 1 := by
  intro h
  have hone : ActsAs L g (1 : MulAut (L ⧸ center L)) := by rw [h]; exact actsAs_one L
  have hσ1 : s.fr'.σ = 1 := actsAs_unique L hgσ hone
  exact frame_sigma_not_mem_inner s.fr' s.facts.1 c.hOut (hσ1 ▸ Subgroup.one_mem _)

private theorem y4_mem_F_sup_zpowers (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1)
    (hgσ : ActsAs L g s.fr'.σ) {y : G} :
    y ∈ s.fr.F ⊔ zpowers g ↔ y ∈ s.fr.F ∨ ∃ f ∈ s.fr.F, y = f * g := by
  have hgnorm : g ∈ normalizer (s.fr.F : Set G) := (c.hLF.fact110 g hg2 hgσ).2.1
  have hnorm : ∀ x ∈ zpowers g, ∀ d ∈ s.fr.F, x * d * x⁻¹ ∈ s.fr.F := by
    intro x hx d hd
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hgnorm hx) d).mp hd
  have hg1 : g ≠ 1 := y4_g_ne_one c hgσ
  have hgord : orderOf g = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hg2 hg1
  have hgp : ∀ n : ℤ, g ^ n = 1 ∨ g ^ n = g := by
    intro n
    have h := zpow_mod_orderOf g n
    rw [hgord] at h
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      have h0' : n % ((2 : ℕ) : ℤ) = 0 := by simpa using h0
      rwa [← h, h0', zpow_zero]
    · right
      have h1' : n % ((2 : ℕ) : ℤ) = 1 := by simpa using h1
      rwa [← h, h1', zpow_one]
  constructor
  · intro hy
    rw [sup_comm] at hy
    obtain ⟨x, hx, d, hd, hxeq⟩ := mem_sup_of_normalizes hnorm y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases hgp n with h1 | h1
    · left
      rw [hxeq, ← hn, h1, one_mul]
      exact hd
    · right
      refine ⟨g * d * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgnorm d).mp hd, ?_⟩
      rw [hxeq, ← hn, h1]
      group
  · rintro (hy | ⟨f, hf, rfl⟩)
    · exact Subgroup.mem_sup_left hy
    · exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left hf) (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

private theorem y4_t_not_mem_F_sup_g (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1)
    (hgσ : ActsAs L g s.fr'.σ) : s.t ∉ s.fr.F ⊔ zpowers g := by
  intro ht
  rcases (y4_mem_F_sup_zpowers c hg2 hgσ).mp ht with htF | ⟨f, hf, hft⟩
  · exact s3_t_not_mem_L s c.h31 (y54_F_le_L s htF)
  · have hg_eq : g = f⁻¹ * s.t := by rw [hft]; group
    have hfL : f⁻¹ ∈ L := y54_F_le_L s (s.fr.F.inv_mem hf)
    have h1 : ActsAs L (f⁻¹ * s.t)
        (MulAut.conj (QuotientGroup.mk (⟨f⁻¹, hfL⟩ : ↥L)) * 1) :=
      actsAs_mul L (actsAs_of_mem L hfL) (actsAs_of_mem_centralizer L s.t_mem)
    have h2 : ActsAs L (f⁻¹ * s.t) s.fr'.σ := by rw [← hg_eq]; exact hgσ
    have hσeq : s.fr'.σ = MulAut.conj (QuotientGroup.mk (⟨f⁻¹, hfL⟩ : ↥L)) := by
      have := actsAs_unique L h2 h1
      simpa using this
    refine frame_sigma_not_mem_inner s.fr' s.facts.1 c.hOut ?_
    rw [hσeq, innerAut, MonoidHom.mem_range]
    exact ⟨_, rfl⟩

private theorem y4_F_sup_g_norm_t (s : Setting3 G L) {g : G} (hgT : g ∈ s.T) :
    ∀ x ∈ s.fr.F ⊔ zpowers g, ∀ y ∈ zpowers s.t, x * y * x⁻¹ ∈ zpowers s.t := by
  intro x hx y hy
  have hxT : x ∈ s.T :=
    (sup_le ((s3_F_le_A s).trans (s3_A_le_T s)) (Subgroup.zpowers_le.mpr hgT)) hx
  have hxt : Commute x s.t := s3_comm_t_of_mem_T s hxT
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hn]
  have heq : x * s.t ^ n * x⁻¹ = s.t ^ n := by
    calc x * s.t ^ n * x⁻¹ = (s.t ^ n * x) * x⁻¹ := by rw [hxt.zpow_right n]
      _ = s.t ^ n := by group
  rw [heq]
  exact Subgroup.zpow_mem_zpowers s.t n

private theorem y4_mem_zpowers_t (s : Setting3 G L) {y : G} (hy : y ∈ zpowers s.t) :
    y = 1 ∨ y = s.t := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hn]
  have h := zpow_mod_orderOf s.t n
  rw [s.t_order] at h
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    have h0' : n % ((2 : ℕ) : ℤ) = 0 := by simpa using h0
    rwa [← h, h0', zpow_zero]
  · right
    have h1' : n % ((2 : ℕ) : ℤ) = 1 := by simpa using h1
    rwa [← h, h1', zpow_one]

private theorem y4_mem_Y0_imp (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1) (hgT : g ∈ s.T)
    (hgσ : ActsAs L g s.fr'.σ) {x : G} (hx : x ∈ y4Y0 s g) :
    x ∈ s.fr.F ∨ (∃ f ∈ s.fr.F, x = f * g) ∨ (∃ f ∈ s.fr.F, x = f * s.t) ∨
      (∃ f ∈ s.fr.F, x = f * g * s.t) := by
  change x ∈ (s.fr.F ⊔ zpowers g) ⊔ zpowers s.t at hx
  obtain ⟨p, hp, q, hq, hxeq⟩ := mem_sup_of_normalizes (y4_F_sup_g_norm_t s hgT) x hx
  rcases (y4_mem_F_sup_zpowers c hg2 hgσ).mp hp with hpF | ⟨f, hf, hpf⟩
  · rcases y4_mem_zpowers_t s hq with rfl | rfl
    · left
      rw [hxeq, mul_one]
      exact hpF
    · right; right; left
      exact ⟨p, hpF, hxeq⟩
  · rcases y4_mem_zpowers_t s hq with rfl | rfl
    · right; left
      exact ⟨f, hf, by rw [hxeq, hpf, mul_one]⟩
    · right; right; right
      exact ⟨f, hf, by rw [hxeq, hpf]⟩

theorem y4_Y0_le_T (c : Ctx4 s e) {g : G} (hgT : g ∈ s.T) : y4Y0 s g ≤ s.T := by
  change s.fr.F ⊔ zpowers g ⊔ zpowers s.t ≤ s.T
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (s3_F_le_A s).trans (s3_A_le_T s)
  · exact Subgroup.zpowers_le.mpr hgT
  · exact Subgroup.zpowers_le.mpr (s3_t_mem_T s)

theorem y4_Y0_isElemAbelian (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1) (hgT : g ∈ s.T)
    (hgR : g ∉ s.R) (hgσ : ActsAs L g s.fr'.σ) : IsElemAbelian 2 (y4Y0 s g) := by
  set P : Subgroup G := s.fr.F ⊔ zpowers g with hP
  have hE : IsE 4 ↥P := by rw [hP]; exact y4_F_sup_g_isE c hg2 hgσ
  have hP_le_T : P ≤ s.T := by
    rw [hP]
    exact sup_le ((s3_F_le_A s).trans (s3_A_le_T s)) (Subgroup.zpowers_le.mpr hgT)
  have hP_ab : IsMulCommutative ↥P := by
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    have h := hE.1.1.is_comm.comm
      (⟨a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥P))
      (⟨b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥P))
    exact congrArg Subtype.val (congrArg Subtype.val h)
  have hP_sq : ∀ x ∈ P, x ^ 2 = 1 := by
    intro x hx
    have h := hE.1.2 (⟨x, hx⟩ : ↥P) (Subgroup.mem_top _)
    simpa using congrArg Subtype.val h
  have hH : IsElemAbelian 2 P := ⟨hP_ab, hP_sq⟩
  have hK : IsElemAbelian 2 (zpowers s.t) := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hm, ← hn]
      calc s.t ^ m * s.t ^ n = s.t ^ (m + n) := by rw [← zpow_add]
        _ = s.t ^ (n + m) := by rw [add_comm m n]
        _ = s.t ^ n * s.t ^ m := by rw [zpow_add]
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hn, pow_two, ← zpow_add]
      rw [← orderOf_dvd_iff_zpow_eq_one, s.t_order]
      exact ⟨n, by ring⟩
  have hcommP : ∀ x ∈ P, ∀ y ∈ zpowers s.t, x * y = y * x := by
    intro x hx y hy
    have hxt : Commute x s.t := s3_comm_t_of_mem_T s (hP_le_T hx)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact (hxt.zpow_right n).eq
  change IsElemAbelian 2 (P ⊔ zpowers s.t)
  exact IsElemAbelian.sup_of_commute hH hK hcommP

theorem y4_Y0_card (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1) (hgT : g ∈ s.T)
    (hgR : g ∉ s.R) (hgσ : ActsAs L g s.fr'.σ) : Nat.card ↥(y4Y0 s g) = 32 := by
  set P : Subgroup G := s.fr.F ⊔ zpowers g with hP
  have hE : IsE 4 ↥P := by rw [hP]; exact y4_F_sup_g_isE c hg2 hgσ
  have hcardP : Nat.card ↥P = 16 := by rw [hE.2]; norm_num
  have htP : s.t ∉ P := by rw [hP]; exact y4_t_not_mem_F_sup_g c hg2 hgσ
  have hnorm : ∀ x ∈ P, ∀ y ∈ zpowers s.t, x * y * x⁻¹ ∈ zpowers s.t := by
    rw [hP]
    exact y4_F_sup_g_norm_t s hgT
  have hdisj : P ⊓ zpowers s.t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxP, hxt⟩ := Subgroup.mem_inf.mp hx
    rcases y4_mem_zpowers_t s hxt with rfl | rfl
    · rfl
    · exact absurd hxP htP
  have hrel : P.relIndex (P ⊔ zpowers s.t) = 2 := by
    rw [relIndex_sup_of_normalizes hnorm, hdisj, Subgroup.relIndex_bot_left, Nat.card_zpowers,
      s.t_order]
  have hprod : P.relIndex (P ⊔ zpowers s.t) * Nat.card ↥P = Nat.card ↥(P ⊔ zpowers s.t) := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := P ⊔ zpowers s.t)
    rwa [inf_eq_left.mpr le_sup_left] at h
  change Nat.card ↥(P ⊔ zpowers s.t) = 32
  rw [← hprod, hrel, hcardP]

theorem y4_Y0_inf_B (c : Ctx4 s e) {g : G} (hg2 : g ^ 2 = 1) (hgT : g ∈ s.T)
    (hgR : g ∉ s.R) (hgσ : ActsAs L g s.fr'.σ) : y4Y0 s g ⊓ s.fr.B = s.fr.F := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxY, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ L := f3_B_le_L s hxB
    rcases y4_mem_Y0_imp c hg2 hgT hgσ hxY with hF | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ |
      ⟨f, hf, rfl⟩
    · exact hF
    · exact absurd hxL (s3_mul_g_not_mem_L c.hS c.hOut s hgσ (y54_F_le_L s hf))
    · exact absurd hxL (by
        intro hmem
        exact s3_t_not_mem_L s c.h31 (by
          have h' : f⁻¹ * (f * s.t) ∈ L :=
            L.mul_mem (L.inv_mem (y54_F_le_L s hf)) hmem
          simpa using h'))
    · exact absurd hxL (by
        intro hmem
        have hgt : ActsAs L (g * s.t) s.fr'.σ := by
          have h := actsAs_mul L hgσ (actsAs_of_mem_centralizer L s.t_mem)
          simpa using h
        have hnot : f * (g * s.t) ∉ L :=
          s3_mul_g_not_mem_L c.hS c.hOut s hgt (y54_F_le_L s hf)
        exact hnot (by
          simpa only [show f * g * s.t = f * (g * s.t) by group] using hmem))
  · refine le_inf ?_ ?_
    · intro x hx
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
    · exact y54_F_le_B c.toF33

end CFSG.OddStandard.HigherRank.YamadaG23
