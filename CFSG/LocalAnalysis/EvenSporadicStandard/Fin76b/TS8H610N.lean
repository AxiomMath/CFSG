module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure OuterMFacts {G : Type} [Group G] [Finite G] (E S : Subgroup G) (z t : G) : Prop where
  gen_four : ∃ a b c d : G, Subgroup.closure ({a, b, c, d} : Set G) = E
  cent_z : ∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z = z * m →
    m ∈ normalizer (E : Set G)
  centZ : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z
  cardM : Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) = 245760
  NH_le : normalizer (E : Set G) ⊓ centralizer ({z} : Set G) ≤
    normalizer ((S ⊔ E : Subgroup G) : Set G)

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem Fnorm_inner (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) {f : G}
    (hf : f ∈ Fsub h hα) (hfN : f ∈ normalizer (E : Set G)) :
    ∃ e' ∈ E, ∀ x ∈ E, f * x * f⁻¹ = e' * x * e'⁻¹ :=
  central_aut_inner h.t_sq h.t_ne h.t_mem_E h.oe.econfig.comm h.oe.econfig.center h.wf.card_E
    hM.gen_four hfN (fun x hx => h.Fnorm_acts_on_E hα hf
      (fun e he => (mem_normalizer_iff.1 hfN e).1 he) hx)

theorem CFz_eq (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) :
    Fsub h hα ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z := by
  have hzF : z ∈ Fsub h hα := h.U_le_Fsub hα (mem_sup_left h.zS)
  apply le_antisymm
  · rintro m ⟨hmF, hmc⟩
    have hmz : m * z = z * m := mem_centralizer_singleton_iff.1 hmc
    have hmN : m ∈ normalizer (E : Set G) := hM.cent_z m hmF.1 hmz
    obtain ⟨e', he', hme⟩ := h.Fnorm_inner hM hα hmF hmN
    have hcE : e'⁻¹ * m ∈ centralizer (E : Set G) := by
      refine mem_centralizer_iff.2 fun x hx => ?_
      have h1 := hme x hx
      calc x * (e'⁻¹ * m) = e'⁻¹ * (e' * x * e'⁻¹) * m := by group
        _ = e'⁻¹ * (m * x * m⁻¹) * m := by rw [h1]
        _ = e'⁻¹ * m * x := by group
    have hcz : e'⁻¹ * m * z = z * (e'⁻¹ * m) := by
      have he'z : e'⁻¹ * z = z * e'⁻¹ := h.oe.cfg.z_comm_of_mem_A (h.oe.E_le_L (inv_mem he'))
      calc e'⁻¹ * m * z = e'⁻¹ * (m * z) := by group
        _ = e'⁻¹ * (z * m) := by rw [hmz]
        _ = (e'⁻¹ * z) * m := by group
        _ = (z * e'⁻¹) * m := by rw [he'z]
        _ = z * (e'⁻¹ * m) := by group
    have hzmem : z ∈ E ⊔ zpowers z := mem_sup_right (mem_zpowers z)
    have htmem : t ∈ E ⊔ zpowers z := mem_sup_left h.t_mem_E
    have hm : m = e' * (e'⁻¹ * m) := by group
    rw [hm]
    refine mul_mem (mem_sup_left he') ?_
    rcases hM.centZ _ hcE hcz with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hzmem
    · rw [h1]; exact htmem
    · rw [h1]; exact mul_mem htmem hzmem
  · refine sup_le ?_ ?_
    · intro e he
      exact ⟨h.U_le_Fsub hα (mem_sup_right he),
        mem_centralizer_singleton_iff.2 (h.S_comm_E z h.zS e he).symm⟩
    · rw [zpowers_le]
      exact ⟨hzF, mem_centralizer_singleton_iff.2 rfl⟩

theorem card_CFz (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(Fsub h hα ⊓ centralizer ({z} : Set G)) = 64 := by
  rw [h.CFz_eq hM hα]
  have hAB : zpowers z ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => (h.S_comm_E z h.zS e he).symm
  have hd : Disjoint E (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxz
    rcases mem_zpowers_sq_eq_one h.z_sq hxz with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hxE
      rcases h.S_inf_E h.zS hxE with h2 | h2
      · exact h.z_ne h2
      · exact h.z_ne_t h2
  have e := mulEquivProdSup hAB hd
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, h.oe.cfg.z_order,
    h.wf.card_E]

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
