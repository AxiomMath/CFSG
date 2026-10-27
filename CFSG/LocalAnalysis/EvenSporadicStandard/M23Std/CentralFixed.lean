module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.L1Fixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FixFourDef

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

omit [Finite G] in
theorem L1_inf_centralizer_mul {g l : G} (hl : l ∈ L1) :
    L1 ⊓ centralizer ({g * l} : Set G) = L1 ⊓ centralizer ({g} : Set G) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, mul_right_cancel (b := l) ?_⟩
    calc x * g * l = x * (g * l) := by group
      _ = g * l * x := h
      _ = g * (l * x) := by group
      _ = g * (x * l) := by rw [S.L1_comm l hl x hx]
      _ = g * x * l := by group
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    calc x * (g * l) = x * g * l := by group
      _ = g * x * l := by rw [h]
      _ = g * (x * l) := by group
      _ = g * (l * x) := by rw [S.L1_comm x hx l hl]
      _ = g * l * x := by group

omit [Finite G] in
theorem L1_inf_centralizer_z : L1 ⊓ centralizer ({z} : Set G) = F := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxz⟩ := mem_inf.1 hx
    exact S.L1_cz x hxL (mem_centralizer_singleton_iff.1 hxz).symm
  · intro f hf
    refine mem_inf.2 ⟨S.F_le hf, mem_centralizer_singleton_iff.2 ?_⟩
    exact (S.one.z_comm f (S.nd.F_le hf)).symm

omit [Finite G] in
theorem sq_mem_F_of_involution {g l : G} (hgX : g ∈ normalizer (L1 : Set G)) (hgL : g * g ∈ L)
    (hl : l ∈ L1) (h2 : g * l * (g * l) = 1) : g * g ∈ F := by
  have hm : g⁻¹ * l * g ∈ L1 := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgX) l).1 hl
    simpa using this
  have h3 : g * g = (g⁻¹ * l * g * l)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc g * g * (g⁻¹ * l * g * l) = g * l * (g * l) := by group
      _ = 1 := h2
  have h4 : g * g ∈ L1 := by
    rw [h3]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hm hl)
  exact S.L1_cz _ h4 (S.one.z_comm _ hgL)

theorem card_centralizer_L1_involution (hFix : FixFour L F)
    (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y) {P : Subgroup G}
    (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) {u : G}
    (hu : u ∈ P) (hu2 : u * u = 1) (hu1 : u ∉ L1) :
    Nat.card ↥(L1 ⊓ centralizer ({u} : Set G)) = 16 := by
  obtain ⟨d, hd, l, hl, hul⟩ := S.exists_eq_mul_of_mem_sylowX hcen hP hT hu
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hdX : d ∈ normalizer (L1 : Set G) := S.D_le_X hd
  have hdz : d * z = z * d := (S.one.z_comm d (mem_inf.1 hd).2).symm
  have hdL : d * d ∈ L := L.mul_mem (mem_inf.1 hd).2 (mem_inf.1 hd).2
  rcases hul with rfl | rfl
  · have hd2 : d * d ∈ F := S.sq_mem_F_of_involution hdX hdL hl hu2
    have hdF : d ∉ F := fun h => hu1 (L1.mul_mem (S.F_le h) hl)
    rw [S.L1_inf_centralizer_mul hl]
    exact S.card_centralizer_L1_eq hdX hdz hd2 (hFix d hd hdF hd2)
  · have hzdX : z * d ∈ normalizer (L1 : Set G) := (normalizer (L1 : Set G)).mul_mem S.zX.2 hdX
    have hzdz : z * d * z = z * (z * d) := by
      calc z * d * z = z * (d * z) := by group
        _ = z * (z * d) := by rw [hdz]
    have hzdsq : z * d * (z * d) = d * d := by
      calc z * d * (z * d) = z * (d * z) * d := by group
        _ = z * (z * d) * d := by rw [hdz]
        _ = (z * z) * d * d := by group
        _ = d * d := by rw [hz2, one_mul]
    have hzdL : z * d * (z * d) ∈ L := hzdsq ▸ hdL
    have hg2 : z * d * (z * d) ∈ F := S.sq_mem_F_of_involution hzdX hzdL hl hu2
    rw [S.L1_inf_centralizer_mul hl]
    by_cases hdF : d ∈ F
    ·
      rw [S.L1_inf_centralizer_mul (g := z) (S.F_le hdF), S.L1_inf_centralizer_z, S.nd.F_card]
    · have hFeq : F ⊓ centralizer ({z * d} : Set G) = F ⊓ centralizer ({d} : Set G) := by
        ext f
        simp only [mem_inf, mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨hf, h⟩
          have hfz : z * f = f * z := S.one.z_comm f (S.nd.F_le hf)
          refine ⟨hf, ?_⟩
          have : z * (f * d) = z * (d * f) := by
            calc z * (f * d) = (z * f) * d := by group
              _ = (f * z) * d := by rw [hfz]
              _ = f * (z * d) := by group
              _ = (z * d) * f := h
              _ = z * (d * f) := by group
          exact mul_left_cancel this
        · rintro ⟨hf, h⟩
          have hfz : z * f = f * z := S.one.z_comm f (S.nd.F_le hf)
          refine ⟨hf, ?_⟩
          calc f * (z * d) = (f * z) * d := by group
            _ = (z * f) * d := by rw [hfz]
            _ = z * (f * d) := by group
            _ = z * (d * f) := by rw [h]
            _ = (z * d) * f := by group
      have hF4 : Nat.card ↥(F ⊓ centralizer ({z * d} : Set G)) ≤ 4 := by
        rw [hFeq]
        exact hFix d hd hdF (by
          have := S.sq_mem_F_of_involution hzdX hzdL hl hu2
          rwa [hzdsq] at this)
      exact S.card_centralizer_L1_eq hzdX hzdz hg2 hF4

end Setup

end CFSG.EvenSporadicStandard.M23Std
