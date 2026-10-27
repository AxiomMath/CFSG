module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_NHA_le_normM6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : normIn c.s.H c.s.fr.A ≤ normalizer (M6 c.e : Set G) := by
  have hNHA_X : normIn c.s.H c.s.fr.A ≤ y7aX c := by
    intro n hn
    rw [← y7a_NC1_eq c hH hF, h71.2.1.1]
    exact Subgroup.mem_sup_left hn
  intro n hn
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · exact y7a_M6_normal c hH hF n (hNHA_X hn) y
  · intro hy
    have hmem := y7a_M6_normal c hH hF n⁻¹ ((y7aX c).inv_mem (hNHA_X hn)) _ hy
    have heq : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rw [heq] at hmem
    exact hmem

theorem y7a_NC1_cs (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) {x : G} (hx : x ∈ normalizer (C1 c.e : Set G))
    (hxK : x ∈ centralizerSection c.s.fr.A c.s.fr.Z) : x ∈ C1 c.e := by
  have h := c.y7acfg hH
  have hVA : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  obtain ⟨hxNA, -, hxc⟩ := hxK
  have hNM6 := y7a_NHA_le_normM6 c hH hF h71
  have hx' : x ∈ ((normIn c.s.H c.s.fr.A ⊔ M6 c.e : Subgroup G) : Set G) := by
    have := (h71.2.1.1 ▸ hx : x ∈ normIn c.s.H c.s.fr.A ⊔ M6 c.e)
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (normIn c.s.H c.s.fr.A) (M6 c.e) hNM6] at hx'
  obtain ⟨n, hn, m, hm, rfl⟩ := hx'
  have hnNA : n ∈ normalizer (c.s.fr.A : Set G) := (Subgroup.mem_inf.mp hn).2
  have hmNA : m ∈ normalizer (c.s.fr.A : Set G) := by
    have hmeq : m = n⁻¹ * (n * m) := by group
    rw [hmeq]
    exact (normalizer (c.s.fr.A : Set G)).mul_mem
      ((normalizer (c.s.fr.A : Set G)).inv_mem hnNA) hxNA
  have hmAV : m ∈ AV1 c.e := by
    rw [← y7a_normM6_A c hH hF]
    exact Subgroup.mem_inf.mpr ⟨hm, hmNA⟩
  obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h m hmAV
  have haH : a ∈ c.s.H := s3_L_le_H c.s hH.hS (s3_A_le_L c.s ha)
  have hn' : n * a ∈ normIn c.s.H c.s.fr.A :=
    (normIn c.s.H c.s.fr.A).mul_mem hn (Subgroup.mem_inf.mpr ⟨haH, Subgroup.le_normalizer ha⟩)
  have hc' : ∀ a' ∈ c.s.fr.A, ⁅a', n * a⁆ ∈ zpowers c.s.fr.z := by
    intro a' ha'
    have h1 : ⁅a', n * (a * v)⁆ ∈ c.s.fr.Z := hxc a' ha'
    have hvc : v * a'⁻¹ * v⁻¹ = a'⁻¹ := by
      have hcomm := hVA a'⁻¹ (c.s.fr.A.inv_mem ha') v hv
      calc v * a'⁻¹ * v⁻¹ = (a'⁻¹ * v) * v⁻¹ := by rw [hcomm]
        _ = a'⁻¹ := by group
    have heq : ⁅a', n * (a * v)⁆ = ⁅a', n * a⁆ := by
      simp only [commutatorElement_def]
      calc a' * (n * (a * v)) * a'⁻¹ * (n * (a * v))⁻¹
          = a' * (n * a) * (v * a'⁻¹ * v⁻¹) * (n * a)⁻¹ := by group
        _ = a' * (n * a) * a'⁻¹ * (n * a)⁻¹ := by rw [hvc]
    rw [← heq]
    exact h1
  have hn'C1 : n * a ∈ C1 c.e :=
    y6_K_core c.toCtx5 hH (s5_NHA_le_Y c.toCtx5 hH hn') hc'
  have heq : n * (a * v) = (n * a) * v := by group
  show n * (a * v) ∈ C1 c.e
  rw [heq]
  exact (C1 c.e).mul_mem hn'C1 (y7a_AV_le_C1 h (Subgroup.mem_sup_right hv))

end CFSG.OddStandard.HigherRank.YamadaG23
