module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem le_sup_glaPPrimeCoreOf_of_chevTransfer_eq_top {Q : Type} [Group Q] [Finite Q] (p : ℕ)
    {K I₀ : Subgroup Q} (hperf : commutator (PQuot p K) = ⊤) (h : chevTransfer p K I₀ = ⊤) :
    K ≤ I₀ ⊔ GLAPPrimeCoreOf p K := by
  have hmk : ∀ x : PQuot p K, ∃ a ∈ (I₀.subgroupOf K).map (pQuotHom p K),
      a⁻¹ * x ∈ Subgroup.center (PQuot p K) := by
    intro x
    have hx : QuotientGroup.mk' (Subgroup.center (PQuot p K)) x ∈ chevTransfer p K I₀ := by
      rw [h]; exact Subgroup.mem_top _
    rw [chevTransfer_eq] at hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
    exact ⟨a, ha, QuotientGroup.eq.1 hax⟩
  have hcc : ∀ {z : PQuot p K}, z ∈ Subgroup.center (PQuot p K) → ∀ g : PQuot p K, Commute z g :=
    fun hz g => (Subgroup.mem_center_iff.1 hz g).symm
  have hAtop : (I₀.subgroupOf K).map (pQuotHom p K) = ⊤ := by
    rw [eq_top_iff, ← hperf]
    refine Subgroup.commutator_le.2 fun x _ g _ => ?_
    obtain ⟨a, ha, hac⟩ := hmk x
    obtain ⟨b, hb, hbd⟩ := hmk g
    have e := CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul' (a := a) (b := b)
      (hcc hac b) (hcc hac _) (hcc hbd a)
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at e
    rw [e, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  intro k hk
  have hk' : pQuotHom p K ⟨k, hk⟩ ∈ (I₀.subgroupOf K).map (pQuotHom p K) := by
    rw [hAtop]; exact Subgroup.mem_top _
  obtain ⟨i, hi, hik⟩ := Subgroup.mem_map.1 hk'
  have hker : i⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥K := by
    rw [← ker_pQuotHom, MonoidHom.mem_ker, map_mul, map_inv, hik, inv_mul_cancel]
  have hmem : ((i⁻¹ * ⟨k, hk⟩ : ↥K) : Q) ∈ GLAPPrimeCoreOf p K := ⟨_, hker, rfl⟩
  have hkeq : k = (i : Q) * ((i⁻¹ * ⟨k, hk⟩ : ↥K) : Q) := by simp
  rw [hkeq]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hi) hmem

theorem chevTransfer_ne_top {Q : Type} [Group Q] [Finite Q] (p : ℕ) {K I₀ : Subgroup Q}
    (hperf : commutator (PQuot p K) = ⊤) (hnot : ¬ K ≤ I₀ ⊔ GLAPPrimeCoreOf p K) :
    chevTransfer p K I₀ ≠ ⊤ :=
  fun h => hnot (le_sup_glaPPrimeCoreOf_of_chevTransfer_eq_top p hperf h)

theorem false_of_glaPComponent_fixSubgroup_one {p : ℕ} (hp : p.Prime) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup (1 : MulAut S)) J) (hne : J ≠ ⊤) : False := by
  have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
    ext x
    simp [mem_fixSubgroup]
  rw [hfix] at hJ
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top hJ.2.1 with h | h
  · have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
    subst h
    have hnt := hq.2.toNontrivial
    have hss : Subsingleton (PQuot p (⊥ : Subgroup S) ⧸
        Subgroup.center (PQuot p (⊥ : Subgroup S))) := inferInstance
    exact (not_subsingleton_iff_nontrivial.2 hnt) hss
  · exact hne h

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
