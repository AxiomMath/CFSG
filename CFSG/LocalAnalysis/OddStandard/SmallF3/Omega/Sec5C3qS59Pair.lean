module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem sec5c3q_inducesTypeSome_mem_normalizer {L : Subgroup G} {s : G} {n : ℕ} {ε : ℤˣ}
    {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s n ε r α) : s ∈ normalizer (L : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, -, -, hind, -⟩ := h
  exact hind.1

theorem sec5c3q_s59_outer [Finite G] (hy : Sec5B59Hyp) (hZ : Asc82ZExists) (tab56 : Asc82Tab56)
    (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ) {g₀ : G}
    (hg₀ : g₀⁻¹ * t * g₀ = t * z) :
    ∃ b ∈ A, IsI4PlusIn L b ∧ b ∉ CFSG.conjugate L g₀ ∧
      ∃ β : ℤˣ, InducesTypeSome (CFSG.conjugate L g₀) (t * b) 6 (-1) 1 β := by
  have h := hR.toSec5Ctx
  have h' := sec5_step56_ctx hy.h52b hy.h53 hy.h37 hZ hy.tab h hg₀
  obtain ⟨w, hwA, hw, hw'⟩ := sec5c3q_exists_pair hR hm
  have ht2 : orderOf t = 2 := h.involution
  have hz2 : orderOf z = 2 := h.pocket.1
  have htS : t ∈ S := sec4_t_mem_S h.sylow ht2
  have htz : t * z = z * t := h.central t htS
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hwz : w * z = z * w := sec5c3q_A_comm hm hwA hm.mem_A.2.2
  have hw'z : (t * z * w) * z = z * (t * z * w) := by
    have e1 : (t * z * w) * z = t * w := by
      calc (t * z * w) * z = t * z * (w * z) := by group
        _ = t * z * (z * w) := by rw [hwz]
        _ = t * (z * z) * w := by group
        _ = t * w := by rw [hz1, mul_one]
    have e2 : z * (t * z * w) = t * w := by
      calc z * (t * z * w) = (z * t) * z * w := by group
        _ = (t * z) * z * w := by rw [← htz]
        _ = t * (z * z) * w := by group
        _ = t * w := by rw [hz1, mul_one]
    rw [e1, e2]
  have hpp : t * z * (t * z * w) = w := by
    calc t * z * (t * z * w) = t * (z * t) * z * w := by group
      _ = t * (t * z) * z * w := by rw [← htz]
      _ = (t * t) * (z * z) * w := by group
      _ = w := by rw [ht1, hz1, one_mul, one_mul]
  have htzA : t * z * w ∈ A := A.mul_mem (A.mul_mem hm.mem_A.1 hm.mem_A.2.2) hwA
  by_cases hwL' : w ∈ CFSG.conjugate L g₀
  · have hw'L' : t * z * w ∉ CFSG.conjugate L g₀ := by
      intro hw'L'
      have hp1 := sec5_step56_pocket_of_mem hy.h52b hy.h54 hy.tab h h' hw hwz hwL'
      have hp2 := sec5_step56_pocket_of_mem hy.h52b hy.h54 hy.tab h h' hw' hw'z hw'L'
      exact (hy.tab.tz_not_pocket G _ h'.toSec5Setting.isOm6Z2 (t * z)
        (sec5_t_mem_centerIn hy.h52b h'.toSec5Setting) h'.involution w hp1) hp2
    obtain ⟨β, hβ⟩ := sec5_step56_key hy.h52b hy.h54 hy.h37 hy.tab tab56 h h' hg₀ hw'
      (by rw [hpp]; exact hw) hw'z hw'L'
    exact ⟨t * z * w, htzA, hw', hw'L', β, hβ⟩
  · obtain ⟨β, hβ⟩ := sec5_step56_key hy.h52b hy.h54 hy.h37 hy.tab tab56 h h' hg₀ hw hw' hwz hwL'
    exact ⟨w, hwA, hw, hwL', β, hβ⟩

theorem sec5c3q_s59_outer_a [Finite G] (hy : Sec5B59Hyp) (hZ : Asc82ZExists)
    (tab56 : Asc82Tab56) (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ)
    {g₀ : G} (hg₀ : g₀⁻¹ * t * g₀ = t * z) :
    ∃ a ∈ A, a ∉ CFSG.conjugate L g₀ ∧ orderOf a = 2 ∧ (∃ g : G, g⁻¹ * (t * z) * g = a) ∧
      ∃ β : ℤˣ, InducesTypeSome (CFSG.conjugate L g₀) a 6 (-1) 1 β := by
  obtain ⟨b, hbA, hb, -, β, hβ⟩ := sec5c3q_s59_outer hy hZ tab56 hR hm hg₀
  have h := hR.toSec5Ctx
  have h' := sec5_step56_ctx hy.h52b hy.h53 hy.h37 hZ hy.tab h hg₀
  have hL1 : IsOm6Z2 (CFSG.conjugate L g₀) := h'.toSec5Setting.isOm6Z2
  obtain ⟨a₁, ha₁L, hba₁⟩ := sec5_pocket_class hy.h52b hy.tab h hb
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn hy.h52b h.toSec5Setting
  have hta₁ : t * a₁ = a₁ * t := (sec5_mem_centerIn_iff.mp htZ).2 a₁ ha₁L
  have hconj : (a₁⁻¹)⁻¹ * (t * z) * a₁⁻¹ = t * b := by
    rw [hba₁, inv_inv]
    calc a₁ * (t * z) * a₁⁻¹ = (a₁ * t) * z * a₁⁻¹ := by group
      _ = (t * a₁) * z * a₁⁻¹ := by rw [hta₁]
      _ = t * (a₁ * z * a₁⁻¹) := by group
  have ha2 : orderOf (t * b) = 2 := by
    rw [← hconj, orderOf_conjugate_eq]
    exact h'.involution
  have haN : t * b ∈ normalizer (CFSG.conjugate L g₀ : Set G) :=
    sec5c3q_inducesTypeSome_mem_normalizer hβ
  have haL' : t * b ∉ CFSG.conjugate L g₀ := by
    intro haL
    have hk2 : Kind5 (CFSG.conjugate L g₀) (t * b) 2 := ⟨β, hβ⟩
    have hnc := hy.tab.kind_ne_central G _ hL1 (t * b) ha2 haN (Or.inr (Or.inl hk2))
    have hk0 : Kind5 (CFSG.conjugate L g₀) (t * b) 0 := ⟨Subgroup.mem_sup_left haL, hnc⟩
    exact hy.tab.excl G _ hL1 (t * b) ha2 haN 0 2 (by norm_num) (by norm_num) (by norm_num)
      hk0 hk2
  exact ⟨t * b, A.mul_mem hm.mem_A.1 hbA, haL', ha2, ⟨a₁⁻¹, hconj⟩, β, hβ⟩

end CFSG.OddStandard.SmallF3.Omega
