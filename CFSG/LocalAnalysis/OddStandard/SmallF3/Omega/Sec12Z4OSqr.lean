module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G]

theorem z4o_exists_c [Finite G] {t : G} {L S : Subgroup G} (F : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {X0 : Subgroup G}
    (hX0B : X0 ⊓ secB S L = ⊥) (hX0sup : X0 ⊔ secB S L = (secM t S L ⊓ L) ⊔ S)
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    {y : G} (hy : y ∈ (secM t S L ⊓ L) ⊔ S) {σ : Equiv.Perm (Fin 5)} (hσ2 : σ * σ = 1)
    (hyσ : SecActs φ y σ) :
    ∃ c ∈ (secM t S L ⊓ L) ⊔ S, SecActs φ c σ ∧
      (c * c = 1 ∨ ∃ b ∈ secB S L, c * c = b * t) := by
  have hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L := fun v hv =>
    (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hBY : secB S L ≤ secM t S L ⊓ L :=
    le_inf ((le_sup_left : secB S L ≤ secA t S L).trans Subgroup.le_normalizer) F.bdata.1
  have hBYc : secB S L ≤ (secM t S L ⊓ L) ⊔ S := hBY.trans le_sup_left
  have hX0Yc : X0 ≤ (secM t S L ⊓ L) ⊔ S := by rw [← hX0sup]; exact le_sup_left
  have hX0N : X0 ≤ normalizer (secB S L : Set G) := hX0Yc.trans (sec122_Yc_le_normalizer_B F)
  have hyYc : y ∈ X0 ⊔ secB S L := by rw [hX0sup]; exact hy
  have hy' : y ∈ (X0 : Set G) * (secB S L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X0 (secB S L) hX0N]
    exact hyYc
  obtain ⟨x, hxX, b, hbB, hxb⟩ := Set.mem_mul.mp hy'
  have hx_eq : x = y * b⁻¹ := by rw [← hxb]; group
  have hxYc : x ∈ (secM t S L ⊓ L) ⊔ S := hX0Yc hxX
  have hact : SecActs φ x σ := by
    intro v hv
    have hcomm : b⁻¹ * φ v * b = φ v := by
      have h := sec12E_B_comm F hbB (hφB v hv)
      rw [show b⁻¹ * φ v * b = b⁻¹ * (φ v * b) by group, ← h]
      group
    rw [hx_eq]
    calc (y * b⁻¹) * φ v * (y * b⁻¹)⁻¹ = y * (b⁻¹ * φ v * b) * y⁻¹ := by group
      _ = y * φ v * y⁻¹ := by rw [hcomm]
      _ = φ (permVec σ v) := hyσ v hv
  refine ⟨x, hxYc, hact, ?_⟩
  have hxx_comm : ∀ c ∈ secB S L, x * x * c = c * (x * x) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := (hperm.2.2.1 c).mp hc
    have h2 := (hact.mul hact) v hv
    rw [hσ2, permVec_one] at h2
    calc x * x * φ v = (x * x * φ v * (x * x)⁻¹) * (x * x) := by group
      _ = φ v * (x * x) := by rw [h2]
  have hxN : x ∈ normalizer (L : Set G) := sec122_Yc_le_normalizer_L F hS.1 hxYc
  have hxxK := F.centB (x * x) (mul_mem hxN hxN) hxx_comm
  have hcomm : ∀ b ∈ secB S L, ∀ k ∈ centralizer (L : Set G), b * k = k * b :=
    fun b hb k hk => Subgroup.mem_centralizer_iff.mp hk b (F.bdata.1 hb)
  obtain ⟨b', hb', k, hk, hxxk⟩ := exists_mul_of_mem_sup_of_commute hcomm hxxK
  have hkYc : k ∈ (secM t S L ⊓ L) ⊔ S := by
    have e : k = b'⁻¹ * (x * x) := by rw [hxxk]; group
    rw [e]
    exact mul_mem (inv_mem (hBYc hb')) (mul_mem hxYc hxYc)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (sec122_Yc_inf_centralizer F hS hkYc hk)
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left
    have hti : t ^ i = 1 := by rw [← zpow_mod_orderOf, F.ht2]; simp [h]
    rw [hti, mul_one] at hxxk
    have hmem : x * x ∈ X0 ⊓ secB S L := ⟨mul_mem hxX hxX, hxxk ▸ hb'⟩
    rw [hX0B] at hmem
    exact (Subgroup.mem_bot.mp hmem)
  · right
    have hti : t ^ i = t := by rw [← zpow_mod_orderOf, F.ht2]; simp [h]
    exact ⟨b', hb', by rw [hxxk, hti]⟩

end CFSG.OddStandard.SmallF3.Omega
