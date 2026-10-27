module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped commutatorElement

section Comm

variable {G : Type*} [Group G]

theorem l514c_commutator_iSup_le {X N O : Subgroup G} (hO : X ≤ normalizer (O : Set G))
    {𝒞 : Set (Subgroup G)} (hCX : ∀ C ∈ 𝒞, C ≤ X) (h : ∀ C ∈ 𝒞, ⁅N, C⁆ ≤ O) :
    ⁅N, ⨆ C ∈ 𝒞, C⁆ ≤ O := by
  let S : Subgroup G :=
    { carrier := {g | g ∈ X ∧ ∀ n ∈ N, ⁅n, g⁆ ∈ O}
      one_mem' := ⟨X.one_mem, fun n _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
        refine ⟨X.mul_mem hgX hhX, fun n hn => ?_⟩
        have e : ⁅n, g * h⁆ = ⁅n, g⁆ * (g * ⁅n, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem (hg n hn) ((mem_normalizer_iff.1 (hO hgX) _).1 (hh n hn))
      inv_mem' := by
        rintro g ⟨hgX, hg⟩
        refine ⟨X.inv_mem hgX, fun n hn => ?_⟩
        have e : ⁅n, g⁻¹⁆ = g⁻¹ * ⁅n, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (mem_normalizer_iff.1 (hO (X.inv_mem hgX)) _).1 (O.inv_mem (hg n hn)) }
  have hle : (⨆ C ∈ 𝒞, C) ≤ S := iSup₂_le fun C hC g hg =>
    ⟨hCX C hC hg, fun n hn => h C hC (commutator_mem_commutator hn hg)⟩
  rw [commutator_le]
  intro n hn m hm
  exact (hle hm).2 n hn

end Comm

theorem lemma514Cover_inputFixComp_holds : LocalBalance.Lemma514CoverNs.InputFixComp := by
  intro G _ _ hKP X 𝒞 E a N hC hEX hE hstab htrans haE hN hNM hEN C hCm C' hC'm
  have hp : Nat.Prime 3 := Nat.prime_three
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  have hAX : zpowers a ≤ X := zpowers_le.2 (hEX haE)
  have hAe : IsElemAbelian 3 (zpowers a) := i183v_isElemAbelian_zpowers ha3
  have hAp : IsPGroup 3 ↥(zpowers a) := isPGroup_of_isElemAbelian' hAe
  have hcz : centralizer ((zpowers a : Subgroup G) : Set G) = Cs a := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hNA : GLAPComponent 3 (X ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) N := by
    rw [hcz]; exact hN
  have hNL : N ≤ GLAPLayer 3 X :=
    hNM.trans (iSup₂_le fun C hCm' => le_sSup (hC C hCm'))
  have hNX : N ≤ X := hN.1.trans inf_le_left
  have hfam : ∀ C ∈ 𝒞, C ∈ i183Family 3 X N := by
    intro C₀ hC₀
    refine ⟨hC C₀ hC₀, fun hle => ?_⟩
    have hall : ∀ C'' ∈ 𝒞, ⁅N, C''⁆ ≤ GLAPPrimeCoreOf 3 X := by
      intro C'' hC''
      obtain ⟨e, he, rfl⟩ := htrans C₀ hC₀ C'' hC''
      have hNe : GLBConj e N = N :=
        gLBConj_eq_of_mem_normalizer (hEN he)
      have h1 : GLBConj e ⁅N, C₀⁆ = ⁅N, GLBConj e C₀⁆ := by
        conv_rhs => rw [← hNe]
        exact Subgroup.map_commutator _ _ _
      rw [← h1]
      have h2 := gLBConj_mono e hle
      rwa [gLBConj_eq_of_mem_normalizer
        (le_normalizer_glaPPrimeCoreOf 3 X (hEX he))] at h2
    have hNN : ⁅N, ⨆ C ∈ 𝒞, C⁆ ≤ GLAPPrimeCoreOf 3 X :=
      l514c_commutator_iSup_le (le_normalizer_glaPPrimeCoreOf 3 X)
        (fun C hC' => (hC C hC').1) hall
    have hNO : N ≤ GLAPPrimeCoreOf 3 X := by
      have := (commutator_mono (le_refl N) hNM).trans hNN
      rwa [glaPComponent_perfect hN] at this
    exact i183v_not_le_core hN inf_le_left hNO
  obtain ⟨e, he, hCe⟩ := i183_transitive hp hAX hAp hNA hNL (hfam C hCm) (hfam C' hC'm)
  obtain ⟨r, -, rfl⟩ := i183v_mem_zpowers ha3 he
  exact ⟨r, hCe⟩

end CFSG.HardMathSupport.Solomon.Coordinator
