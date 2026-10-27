module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2CT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1C4C

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_C4_cent_E (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ C4 c.s, ∀ e ∈ c.s.fr.E, x * e = e * x := by
  have hY : C4 c.s ≤ e4Y c.s := (y56_C4_cand c.toCtx5 hH).2.1
  intro x hx e he
  have hxE : x ∈ centralizer (↑(c.s.fr.E) : Set G) := (Subgroup.mem_inf.mp (hY hx)).2
  exact (Subgroup.mem_centralizer_iff.mp hxE e he).symm

theorem y7a_C6_cases (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ x ∈ C6 c.e, x ∈ M6 c.e ∨ ∃ m ∈ M6 c.e, x = m * c.s.t := by
  have h := c.y7acfg hH
  have ht2 : c.s.t * c.s.t = 1 := y7a_t_sq h
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  have htX : c.s.t ∈ y7aX c :=
    y7a_C6_le_X c hH hF
      (y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h)))
  have htN : zpowers c.s.t ≤ normalizer (M6 c.e : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact y7a_M6_normal c hH hF c.s.t htX x hx
    · intro hx
      have hmem := y7a_M6_normal c hH hF c.s.t htX _ hx
      have heq : c.s.t * (c.s.t * x * c.s.t⁻¹) * c.s.t⁻¹ = x := by
        rw [htinv]
        calc c.s.t * (c.s.t * x * c.s.t) * c.s.t
            = (c.s.t * c.s.t) * x * (c.s.t * c.s.t) := by group
          _ = x := by rw [ht2]; group
      rwa [heq] at hmem
  intro x hx
  have hx' : x ∈ ((M6 c.e ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
    (y7a_C6_eq_M6 c hH hF).2 ▸ hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (M6 c.e) (zpowers c.s.t) htN] at hx'
  obtain ⟨m, hm, τ, hτ, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have ht2z : c.s.t ^ (2 : ℤ) = 1 := by simpa [pow_two] using ht2
  rw [zpow_eq_zpow_emod i ht2z]
  rcases Int.emod_two_eq_zero_or_one i with hi | hi
  · left
    rw [hi]
    simpa using hm
  · right
    rw [hi]
    exact ⟨m, hm, by simp⟩

theorem y7a_comm_t_E (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {m : G} (hm : m ∈ M6 c.e) (hmE : ∀ x ∈ c.s.fr.E, m * x = x * m) :
    ⁅m, c.s.t⁆ ∈ c.s.fr.E := by
  refine y7a_comm_t_mem c hH hF (X := c.s.fr.E) (Y := c.s.fr.E)
    (s3_E_le_A c.s) ?_ ?_ ?_ hm hmE
  · intro a ha hcomm
    have hmem : a ∈ centIn L c.s.fr.E :=
      Subgroup.mem_inf.mpr ⟨s3_A_le_L c.s ha,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcomm x hx).symm)⟩
    rwa [y56_centIn_L_E hH] at hmem
  · intro y hy
    rw [← pow_two]
    exact y56_E_sq hH y hy
  · exact y56_z_mem_E hH

theorem y7a_cent_M6_E (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : centIn (M6 c.e) c.s.fr.E = M4 c.e := by
  have ht2 : c.s.t * c.s.t = 1 := y7a_t_sq (c.y7acfg hH)
  have hQle : e4Q c.s ≤ C4 c.s := (y56_C4_cand c.toCtx5 hH).1
  have hC4C6 : C4 c.s ≤ C6 c.e := y7a_C4_le_C6 c hH hF
  have hC4cent : C4 c.s ≤ centralizer (↑(c.s.fr.E) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (y7a_C4_cent_E c hH y hy e he).symm
  have htcent : c.s.t ∈ centralizer (↑(c.s.fr.E) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun e he => y56_t_comm_E c.s e he)
  have hmemA : ∀ {n : G}, n ∈ M6 c.e → n ∈ centralizer (↑(c.s.fr.E) : Set G) →
      n * c.s.t = c.s.t * n → n ∈ c.s.fr.A := by
    intro n hnM6 _ hnt
    have hnH : n ∈ c.s.H := Subgroup.mem_centralizer_singleton_iff.mpr hnt
    have hn : n ∈ c.s.H ⊓ M6 c.e := Subgroup.mem_inf.mpr ⟨hnH, hnM6⟩
    rwa [h71.2.1.2.1] at hn
  have hmemE : ∀ {n : G}, n ∈ c.s.fr.A → n ∈ centralizer (↑(c.s.fr.E) : Set G) →
      n ∈ c.s.fr.E := by
    intro n hnA hncent
    have hn : n ∈ centIn L c.s.fr.E :=
      Subgroup.mem_inf.mpr ⟨s3_A_le_L c.s hnA, hncent⟩
    rwa [y56_centIn_L_E hH] at hn
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxM6, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxE : ∀ e ∈ c.s.fr.E, x * e = e * x :=
      fun e he => (Subgroup.mem_centralizer_iff.mp hxc e he).symm
    have hxV : x ∈ centralizer (↑(V1 c.e) : Set G) := (Subgroup.mem_inf.mp hxM6).2
    have hxt : x * c.s.t * x⁻¹ ∈ c.s.tCoset c.s.fr.E :=
      ⟨⁅x, c.s.t⁆, y7a_comm_t_E c hH hF hxM6 hxE, by
        rw [commutatorElement_def]; group⟩
    rw [← hF.2.2.2.2.1.1.2.2.1] at hxt
    obtain ⟨m', hm'C4, hm'eq⟩ := hxt
    have hnC6 : m'⁻¹ * x ∈ C6 c.e :=
      (C6 c.e).mul_mem ((C6 c.e).inv_mem (hC4C6 hm'C4)) (y7a_M6_le_C6 c hxM6)
    have hncent : m'⁻¹ * x ∈ centralizer (↑(c.s.fr.E) : Set G) :=
      (centralizer (↑(c.s.fr.E) : Set G)).mul_mem
        ((centralizer (↑(c.s.fr.E) : Set G)).inv_mem (hC4cent hm'C4)) hxc
    have hnt : (m'⁻¹ * x) * c.s.t = c.s.t * (m'⁻¹ * x) := by
      calc (m'⁻¹ * x) * c.s.t = m'⁻¹ * (x * c.s.t * x⁻¹) * x := by group
        _ = m'⁻¹ * (m' * c.s.t * m'⁻¹) * x := by rw [hm'eq]
        _ = c.s.t * (m'⁻¹ * x) := by group
    have hnC4 : m'⁻¹ * x ∈ C4 c.s := by
      rcases y7a_C6_cases c hH hF (m'⁻¹ * x) hnC6 with hnM6 | ⟨m'', hm'', hn_eq⟩
      · exact hQle (Subgroup.mem_sup_left (hmemE (hmemA hnM6 hncent hnt) hncent))
      · have hmt : m'' * c.s.t = c.s.t * m'' := by
          have h1 : m'' = c.s.t * m'' * c.s.t := by
            have h := hnt
            rw [hn_eq, mul_assoc] at h
            rw [mul_assoc, ← h, ht2, mul_one]
          calc m'' * c.s.t = (c.s.t * m'' * c.s.t) * c.s.t :=
                congrArg (fun z => z * c.s.t) h1
            _ = c.s.t * m'' := by
                  rw [show (c.s.t * m'' * c.s.t) * c.s.t = c.s.t * m'' * (c.s.t * c.s.t)
                    by group, ht2, mul_one]
        have hm''cent : m'' ∈ centralizer (↑(c.s.fr.E) : Set G) := by
          have heq : m'' = (m'⁻¹ * x) * c.s.t := by
            rw [hn_eq, mul_assoc, ht2, mul_one]
          rw [heq]
          exact (centralizer (↑(c.s.fr.E) : Set G)).mul_mem hncent htcent
        have hm''E : m'' ∈ c.s.fr.E := hmemE (hmemA hm'' hm''cent hmt) hm''cent
        rw [hn_eq]
        exact hQle (Subgroup.mul_mem_sup hm''E (Subgroup.mem_zpowers c.s.t))
    have hxC4 : x ∈ C4 c.s := by
      rw [show x = m' * (m'⁻¹ * x) by group]
      exact (C4 c.s).mul_mem hm'C4 hnC4
    exact Subgroup.mem_inf.mpr ⟨hxC4, hxV⟩
  · intro x hx
    have hxC4 : x ∈ C4 c.s := (Subgroup.mem_inf.mp hx).1
    refine Subgroup.mem_inf.mpr ⟨h71.2.2.2.2 hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (y7a_C4_cent_E c hH x hxC4 e he).symm

end CFSG.OddStandard.HigherRank.YamadaG23
