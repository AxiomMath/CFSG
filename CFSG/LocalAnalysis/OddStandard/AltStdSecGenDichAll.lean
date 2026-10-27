module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenDich

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section ClaimC2

theorem exists_rel_of_cyc3 {G : Type} [Group G] {n : ℕ} {z : G} {U : Finset (Fin n)}
    (hU : 5 ≤ U.card) {F F' : ↥(altSub U) →* G} (hFinj : Function.Injective F)
    (hcomm' : ∀ x y, F' x * (z * F' y * z⁻¹) = (z * F' y * z⁻¹) * F' x)
    (hloc : ∀ (a b c : Fin n), a ∈ U → b ∈ U → c ∈ U → a ≠ b → b ≠ c → a ≠ c →
      ∀ (hmem : cyc3 a b c ∈ altSub U), ∃ cc : Bool,
        F ⟨cyc3 a b c, hmem⟩ = cjHom z cc (F' ⟨cyc3 a b c, hmem⟩)) :
    ∃ c : Bool, ∀ γ, F γ = cjHom z c (F' γ) := by
  classical
  have hsimple : IsSimpleGroup ↥(altSub U) := isSimpleGroup_of_alt hU (altSubEquiv U)
  let E : Bool → Subgroup ↥(altSub U) := fun c => MonoidHom.eqLocus F ((cjHom z c).comp F')
  have hE : ∀ c γ, γ ∈ E c ↔ F γ = cjHom z c (F' γ) := fun c γ => Iff.rfl
  have hcomm : ∀ x ∈ E false, ∀ y ∈ E true, x * y = y * x := by
    intro x hx y hy
    apply hFinj
    have hx' : F x = F' x := (hE false x).1 hx
    have hy' : F y = z * F' y * z⁻¹ := (hE true y).1 hy
    rw [map_mul, map_mul, hx', hy']
    exact hcomm' _ _
  have hsup : E false ⊔ E true = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    have hgen := altSub_le_of_cyc3 (T := U) (H := (E false ⊔ E true).map (altSub U).subtype)
      (fun a b c ha hb hc hab hbc hac => by
        have hmem : cyc3 a b c ∈ altSub U := cyc3_mem_altSub ha hb hc hab hbc hac
        refine ⟨⟨cyc3 a b c, hmem⟩, ?_, rfl⟩
        obtain ⟨cc, hcc⟩ := hloc a b c ha hb hc hab hbc hac hmem
        cases cc
        · exact Subgroup.mem_sup_left ((hE false _).2 hcc)
        · exact Subgroup.mem_sup_right ((hE true _).2 hcc))
    obtain ⟨w, hw, hwγ⟩ := hgen γ.2
    have : w = γ := Subtype.ext hwγ
    rw [← this]
    exact hw
  rcases eq_top_or_eq_top_of_commute_sup hcomm hsup with h0 | h1
  · exact ⟨false, fun γ => (hE false γ).1 (by rw [h0]; exact Subgroup.mem_top γ)⟩
  · exact ⟨true, fun γ => (hE true γ).1 (by rw [h1]; exact Subgroup.mem_top γ)⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem rootLift_rel_all (h : ExactShape z L n) (hn : 11 ≤ n)
    (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') :
    ∃ c : Bool, ∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
      (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = cjHom z c (ψ' ⟨x, hx'⟩) := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = (S ∪ S')ᶜ := ⟨_, rfl⟩
  have hUc : 5 ≤ U.card := by
    rw [hU, card_compl_fin]
    have := Finset.card_union_le S S'
    omega
  have hUS : U ⊆ Sᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.1
  have hUS' : U ⊆ S'ᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.2
  have hDB : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hUS)
  have hDB' : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub S'ᶜ) :=
    corr_mono e (altSub_mono hUS')
  let φ : ↥(altSub U) →* ↥(corr (X := G) e (altSub U)) :=
    corrIn (X := G) e (altSub_le_alternatingGroup U)
  let F : ↥(altSub U) →* G := ψ.comp ((Subgroup.inclusion hDB).comp φ)
  let F' : ↥(altSub U) →* G := ψ'.comp ((Subgroup.inclusion hDB').comp φ)
  have hFinj : Function.Injective F :=
    hψ.inj.comp ((Subgroup.inclusion_injective hDB).comp (corrIn_injective (X := G) e _))
  obtain ⟨c, hc⟩ := exists_rel_of_cyc3 (by omega) (F := F) (F' := F') hFinj
    (fun x y => hψ'.comm _ _) (fun a b c ha hb hc hab hbc hac hmem => by
      have hxT : ((φ ⟨cyc3 a b c, hmem⟩ : ↥(corr (X := G) e (altSub U))) : G) ∈
          corr (X := G) e (altSub ({a, b, c} : Finset (Fin n))) := by
        show ((e.symm ⟨cyc3 a b c, altSub_le_alternatingGroup U hmem⟩ : L) : G) ∈ _
        apply mem_corr_of_mem
        simp only [MulEquiv.apply_symm_apply]
        exact cyc3_mem_altSub (by simp) (by simp) (by simp) hab hbc hac
      exact rootLift_rel_local h hn hIII hS hS' hψ hψ' (T := {a, b, c})
        (Finset.card_le_three) (x := ((φ ⟨cyc3 a b c, hmem⟩ : ↥(corr (X := G) e (altSub U))) : G))
        (hDB (φ ⟨cyc3 a b c, hmem⟩).2) (hDB' (φ ⟨cyc3 a b c, hmem⟩).2) hxT)
  refine ⟨c, fun x hx hx' => ?_⟩
  have hxD : x ∈ corr (X := G) e (altSub U) := by
    have := corr_inf_le e S S' ⟨hx, hx'⟩
    rwa [← hU] at this
  obtain ⟨hxA, hxe⟩ := mem_corr.1 hxD
  have hφ : ((φ ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ : ↥(corr (X := G) e (altSub U))) : G) =
      x := by
    show ((e.symm ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), _⟩ : L) : G) = x
    simp
  have h1 := hc ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩
  have h2 : F ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ = ψ ⟨x, hx⟩ :=
    congrArg ψ (Subtype.ext hφ)
  have h3 : F' ⟨(e ⟨x, hxA⟩ : Equiv.Perm (Fin n)), hxe⟩ = ψ' ⟨x, hx'⟩ :=
    congrArg ψ' (Subtype.ext hφ)
  rw [h2, h3] at h1
  exact h1

end ClaimC2

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem rootDichotomy_of_caseIII (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S) :
    RootDichotomy e z := by
  intro S S' hS hS' ψ ψ' hψ hψ'
  obtain ⟨c, hc⟩ := rootLift_rel_all h hn hIII hS hS' hψ hψ'
  cases c
  · exact Or.inl hc
  · exact Or.inr hc

theorem exists_wreathPair_of_caseIII (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S) :
    ∃ H : Subgroup G, WreathPair L z n H :=
  stageM_of_dichotomy h e hn hIII (rootDichotomy_of_caseIII h e hn hIII)

end Final

end CFSG.OddStandard.AltStdSec
