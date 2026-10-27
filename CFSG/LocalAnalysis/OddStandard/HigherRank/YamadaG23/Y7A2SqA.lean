module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Norm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_exists_D (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {K : Subgroup G} (hKM : K ≤ M6 c.e) (hKX : ∀ x ∈ y7aX c, ∀ m ∈ K, x * m * x⁻¹ ∈ K)
    (hAV : AV1 c.e ≤ K) (hM3 : M3 c.s ≤ K) :
    ∃ D : Subgroup G, V1 c.e ≤ D ∧ D ≤ AV1 c.e ∧
      (∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ D, k * x * k⁻¹ ∈ D) ∧ c.s.fr.F ≤ D ∧
      (c.s.fr.A ≤ D → M6 c.e ≤ K) := by
  have hcfg := c.y7acfg hH
  haveI hZ : (c.s.fr.Z.subgroupOf c.s.fr.A).Normal := y7a_Z_normal_A c hH
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨f, hf1, hex, _, hker⟩ := y7a_mod_hom c hH hF hP
  let J : Subgroup (↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) :=
    (K.subgroupOf (M6 c.e)).map f
  let D0 : Subgroup ↥(c.s.fr.A) :=
    J.comap (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.s.fr.A))
  let D : Subgroup G := D0.map (c.s.fr.A).subtype ⊔ V1 c.e
  have hcomm : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm hcfg.cfg a ha v (y7a_V_le_C0 hcfg hv)
  have hcommD : ∀ a ∈ D0.map (c.s.fr.A).subtype, ∀ v ∈ V1 c.e, a * v = v * a := by
    intro a ha v hv
    obtain ⟨a', -, rfl⟩ := Subgroup.mem_map.mp ha
    exact hcomm a' a'.2 v hv
  have hDmem : ∀ x : G, x ∈ D ↔ ∃ a : ↥(c.s.fr.A),
      ((a : ↥(c.s.fr.A)) : ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) ∈ J ∧
      ∃ v ∈ V1 c.e, x = (a : G) * v := by
    intro x
    show x ∈ D0.map (c.s.fr.A).subtype ⊔ V1 c.e ↔ _
    constructor
    · intro hx
      obtain ⟨y, hy, v, hv, hxy⟩ :=
        CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcommD hx
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hy
      exact ⟨a, Subgroup.mem_comap.mp ha, v, hv,
        hxy.trans (congrArg (fun z => z * v) haeq.symm)⟩
    · rintro ⟨a, ha, v, hv, rfl⟩
      exact Subgroup.mul_mem_sup
        (Subgroup.mem_map.mpr ⟨a, Subgroup.mem_comap.mpr ha, rfl⟩) hv
  refine ⟨D, le_sup_right, ?_, ?_, ?_, ?_⟩
  · exact sup_le ((Subgroup.map_subtype_le D0).trans le_sup_left) le_sup_right
  ·
    intro k hk x hx
    have hkY : k ∈ y7aY c := s5_NLA_le_Y c.toCtx5 hH hk
    have hkX : k ∈ y7aX c := y7a_Y_le_X c hH hkY
    have hkM6 : ∀ m ∈ M6 c.e, k * m * k⁻¹ ∈ M6 c.e := y7a_M6_normal c hH hF k hkX
    have hkV : ∀ v ∈ V1 c.e, k * v * k⁻¹ ∈ V1 c.e := fun v hv =>
      (Subgroup.mem_set_normalizer_iff.mp (Subgroup.mem_inf.mp hkX).2 v).mp hv
    have hkA : ∀ a ∈ c.s.fr.A, k * a * k⁻¹ ∈ c.s.fr.A := fun a ha =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hk).2 a).mp ha
    have hkt : k * c.s.t * k⁻¹ = c.s.t := by
      have hkH : k ∈ c.s.H := s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp hk).1
      have hcommt : k * c.s.t = c.s.t * k :=
        Subgroup.mem_centralizer_singleton_iff.mp hkH
      rw [hcommt, mul_assoc, mul_inv_cancel, mul_one]
    have hf_equiv : ∀ (m : ↥(M6 c.e)) (a : ↥(c.s.fr.A)),
        f m = ((a : ↥(c.s.fr.A)) : ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) →
        f ⟨k * (m : G) * k⁻¹, hkM6 (m : G) m.2⟩ =
          ((⟨k * (a : G) * k⁻¹, hkA (a : G) a.2⟩ : ↥(c.s.fr.A)) :
            ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) := by
      intro m a hfm
      have haV : (a : G)⁻¹ * ⁅(m : G), c.s.t⁆ ∈ V1 c.e := by
        obtain ⟨a₀, ha0⟩ := hex m
        have h0 : f m = ((a₀ : ↥(c.s.fr.A)) :
            ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) := hf1 m a₀ ha0
        have hclass : ((a : ↥(c.s.fr.A)) :
              ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) =
            ((a₀ : ↥(c.s.fr.A)) : ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) :=
          hfm.symm.trans h0
        have hz : (a : G)⁻¹ * (a₀ : G) ∈ c.s.fr.Z := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hclass
          simpa using hclass
        have hZleV : c.s.fr.Z ≤ V1 c.e := by
          rw [SFrame.Z]
          exact Subgroup.zpowers_le.mpr (y7a_z_mem_V hcfg)
        have heq : (a : G)⁻¹ * ⁅(m : G), c.s.t⁆ =
            ((a : G)⁻¹ * (a₀ : G)) * ((a₀ : G)⁻¹ * ⁅(m : G), c.s.t⁆) := by group
        rw [heq]
        exact (V1 c.e).mul_mem (hZleV hz) ha0
      have hconj : ⁅k * (m : G) * k⁻¹, c.s.t⁆ = k * ⁅(m : G), c.s.t⁆ * k⁻¹ := by
        have h1 : k * ⁅(m : G), c.s.t⁆ * k⁻¹ =
            ⁅k * (m : G) * k⁻¹, k * c.s.t * k⁻¹⁆ :=
          conjugate_commutatorElement (g₁ := (m : G)) (g₂ := c.s.t) (g₃ := k)
        simpa only [hkt] using h1.symm
      refine hf1 ⟨k * (m : G) * k⁻¹, hkM6 (m : G) m.2⟩
        ⟨k * (a : G) * k⁻¹, hkA (a : G) a.2⟩ ?_
      have heq : (k * (a : G) * k⁻¹)⁻¹ * ⁅k * (m : G) * k⁻¹, c.s.t⁆ =
          k * ((a : G)⁻¹ * ⁅(m : G), c.s.t⁆) * k⁻¹ := by
        rw [hconj]; group
      rw [heq]
      exact hkV _ haV
    obtain ⟨a, haJ, v, hv, rfl⟩ := (hDmem x).mp hx
    rw [hDmem]
    refine ⟨⟨k * (a : G) * k⁻¹, hkA (a : G) a.2⟩, ?_, k * v * k⁻¹, hkV v hv, ?_⟩
    · obtain ⟨m, hmK, hfm⟩ := Subgroup.mem_map.mp haJ
      have hkeq := hf_equiv m a hfm
      refine Subgroup.mem_map.mpr ⟨⟨k * (m : G) * k⁻¹, hkM6 (m : G) m.2⟩, ?_, hkeq⟩
      rw [Subgroup.mem_subgroupOf]
      exact hKX k hkX (m : G) (Subgroup.mem_subgroupOf.mp hmK)
    · group
  ·
    intro u hu
    rw [hDmem]
    have huA : u ∈ c.s.fr.A := s3_F_le_A c.s hu
    refine ⟨⟨u, huA⟩, ?_, 1, (V1 c.e).one_mem, ?_⟩
    · have hmem : u * c.s.t ∈ c.s.tCoset c.s.fr.F := ⟨u, hu, rfl⟩
      rw [← hF.2.2.1.1.2.2.1] at hmem
      obtain ⟨m, hmM3, hm⟩ := hmem
      have hmM6 : m ∈ M6 c.e := hKM (hM3 hmM3)
      have hcommut : ⁅m, c.s.t⁆ = u := by
        have ht : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y7a_t_sq hcfg)
        calc ⁅m, c.s.t⁆ = (m * c.s.t * m⁻¹) * c.s.t⁻¹ := by rw [commutatorElement_def]
          _ = (u * c.s.t) * c.s.t⁻¹ := by rw [hm]
          _ = u := by rw [ht, mul_assoc, y7a_t_sq hcfg, mul_one]
      refine Subgroup.mem_map.mpr ⟨⟨m, hmM6⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact hM3 hmM3
      · refine hf1 ⟨m, hmM6⟩ ⟨u, huA⟩ ?_
        rw [hcommut, inv_mul_cancel]
        exact (V1 c.e).one_mem
    · simp
  ·
    intro hAD m hm
    obtain ⟨a, ha⟩ := hex ⟨m, hm⟩
    have hfa : f ⟨m, hm⟩ = ((a : ↥(c.s.fr.A)) :
        ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) := hf1 ⟨m, hm⟩ a ha
    have haD : (a : G) ∈ D := hAD a.2
    obtain ⟨a', ha'J, v, hv, haeq⟩ := (hDmem (a : G)).mp haD
    have ha'Z : (a' : ↥(c.s.fr.A))⁻¹ * a ∈ c.s.fr.Z.subgroupOf c.s.fr.A := by
      rw [Subgroup.mem_subgroupOf]
      have hvV : (((a' : ↥(c.s.fr.A))⁻¹ * a : ↥(c.s.fr.A)) : G) ∈ V1 c.e := by
        have heq : (((a' : ↥(c.s.fr.A))⁻¹ * a : ↥(c.s.fr.A)) : G) =
            (a' : G)⁻¹ * (a : G) := by simp
        rw [heq, haeq, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hv
      have hmemA : (((a' : ↥(c.s.fr.A))⁻¹ * a : ↥(c.s.fr.A)) : G) ∈ c.s.fr.A :=
        ((a' : ↥(c.s.fr.A))⁻¹ * a).2
      have hmem : (((a' : ↥(c.s.fr.A))⁻¹ * a : ↥(c.s.fr.A)) : G) ∈
          c.s.fr.A ⊓ V1 c.e := ⟨hmemA, hvV⟩
      rw [y7a_A_inf_V hcfg] at hmem
      rwa [SFrame.Z]
    have hclass : ((a' : ↥(c.s.fr.A)) :
          ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) =
        ((a : ↥(c.s.fr.A)) : ↥(c.s.fr.A) ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) :=
      QuotientGroup.eq.mpr ha'Z
    have hfaJ : f ⟨m, hm⟩ ∈ J := by
      rw [hfa, ← hclass]
      exact ha'J
    obtain ⟨k, hkK, hfk⟩ := Subgroup.mem_map.mp hfaJ
    have hkK' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
    have hker_mem : (k⁻¹ * ⟨m, hm⟩ : ↥(M6 c.e)) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hfk, inv_mul_cancel]
    rw [hker] at hker_mem
    have hAv : (k : G)⁻¹ * m ∈ AV1 c.e := by
      have h1 : ((k⁻¹ * ⟨m, hm⟩ : ↥(M6 c.e)) : G) ∈ AV1 c.e :=
        Subgroup.mem_subgroupOf.mp hker_mem
      simpa using h1
    have heq : (k : G) * ((k : G)⁻¹ * m) = m := by group
    rw [← heq]
    exact K.mul_mem hkK' (hAV hAv)

end CFSG.OddStandard.HigherRank.YamadaG23
