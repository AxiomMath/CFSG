module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10Z_comm [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := by
  obtain ⟨K1', K2', _, _, _, huniq, hcomm, _, _, _⟩ :=
    hP5 G L hpsp z hctx.toSec10Z.pocket
  have hkey : ∀ a ∈ K1', ∀ b ∈ K2', a * b = b * a := by
    intro a ha b hb
    have hca : a ∈ centralizer (K2' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
    exact (Subgroup.mem_centralizer_iff.mp hca b hb).symm
  intro a ha b hb
  rcases huniq K1 hctx.pocket1 with h1 | h1 <;>
    rcases huniq K2 hctx.pocket2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hctx.ne
  · subst h1; subst h2; exact hkey a ha b hb
  · subst h1; subst h2; exact (hkey b hb a ha).symm
  · exact absurd (h1.trans h2.symm) hctx.ne

theorem sec10Z_normalizes [Finite G] (h36 : Asc82Lemma36) (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {c : G}
    (hct : c ∈ centralizer ({t} : Set G)) (hcz : c ∈ centralizer ({z} : Set G)) :
    ∀ x ∈ K1 ⊔ K2, c * x * c⁻¹ ∈ K1 ⊔ K2 := by
  have hN : c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB c hct
  have hczc : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hciz : c⁻¹ * z = z * c⁻¹ := hczc.inv_left.eq
  rw [sec10K0_pockets_sup hP5 hpsp hctx]
  intro x hx
  unfold oTwoRes at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      have hyL : y ∈ L := hy.1.1
      have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy.1.2
      refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩
      · exact (Subgroup.mem_set_normalizer_iff.mp hN y).mp hyL
      · change c * y * c⁻¹ ∈ centralizer ({z} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (c * y * c⁻¹) * z = c * y * (c⁻¹ * z) := by simp only [mul_assoc]
          _ = c * (y * z) * c⁻¹ := by rw [hciz]; simp only [mul_assoc]
          _ = c * (z * y) * c⁻¹ := by rw [hyz]
          _ = (c * z) * y * c⁻¹ := by simp only [mul_assoc]
          _ = (z * c) * y * c⁻¹ := by rw [hczc.eq]
          _ = z * (c * y * c⁻¹) := by simp only [mul_assoc]
      · have hconj : orderOf (c * y * c⁻¹) = orderOf y := by
          rw [← MulAut.conj_apply c y]
          exact (MulAut.conj c).orderOf_eq y
        rw [hconj]
        exact hy.2
  | one => simpa using Subgroup.one_mem (Subgroup.closure _)
  | mul y w _ _ ihy ihw => simpa only [conj_mul] using Subgroup.mul_mem _ ihy ihw
  | inv y _ ihy => simpa only [conj_inv] using Subgroup.inv_mem _ ihy

end CFSG.OddStandard.SmallF3.Omega
