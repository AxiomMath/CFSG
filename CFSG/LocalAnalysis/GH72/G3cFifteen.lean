module

public import CFSG.LocalAnalysis.GH72.G3cFourteen
public import CFSG.LocalAnalysis.GH72.GWForm
import CFSG.LocalAnalysis.GH72.Sec4Iso
public import CFSG.LocalAnalysis.GH72.G3cFusion

public section

namespace CFSG.GH72

open Subgroup
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

namespace G3cF

section Side

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_O_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (O H : Set G) := by
  rw [G4b.mem_normalizer_iff_map_conj_eq'] at hg ⊢
  rw [G4b.map_O, hg]

theorem bar_C_structure {M P Q : Subgroup G} (hPM : P ≤ M) (hQH : Q ≤ O2 M)
    (hPH : P ⊓ O2 M = ⊥) (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hsyl : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) M) (hPD : IsDih P)
    (hiso : ∀ f ∈ P, f * f = 1 → f ≠ 1 → IsIsolatedIn (O2 M ⊔ zpowers f) f) :
    bar M P ⊓ bar M (O2 M) = ⊥ ∧ bar M P ⊔ bar M (O2 M) = ⊤ ∧
      bar M (O2 M) ≤ centralizer (bar M P : Set (Bar M)) ∧ ABGLocalTools.IsSylowOf 2 Q (O2 M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHM : O2 M ≤ M := twoResidualOf_le_self M
  refine ⟨bar_inf_bar_twoResidualOf_eq_bot hPH, ?_, ?_, ?_⟩
  ·
    have hMeq : P ⊔ O2 M = M := by
      refine le_antisymm (sup_le hPM hHM) ?_
      calc M = (P ⊔ Q) ⊔ O2 M := (sup_twoResidualOf_eq hsyl).symm
        _ ≤ P ⊔ O2 M := sup_le (sup_le le_sup_left (hQH.trans le_sup_right)) le_sup_right
    rw [← G4b.bar_sup hPM hHM, hMeq, bar_self']
  ·
    have hOO : O (O2 M) ≤ O M := G4b.le_O_of_odd ((G4b.O_le_self _).trans hHM)
      (fun g hg => mem_normalizer_O_of_mem_normalizer (le_normalizer_twoResidualOf M hg))
      (card_O_odd _)
    set L : Subgroup G :=
      ((centralizer (bar M (O2 M) : Set (Bar M))).comap (QuotientGroup.mk' (CFSG.oddCore M))).map
        M.subtype with hL
    have hPL : P ≤ L := le_of_forall_mul_self_eq_one hPD fun f hf hff => by
      by_cases hf1 : f = 1
      · rw [hf1]
        exact one_mem _
      have hfM : f ∈ M := hPM hf
      have hfH : f ∉ O2 M := fun h => hf1 (by
        have h' : f ∈ P ⊓ O2 M := mem_inf.2 ⟨hf, h⟩
        rw [hPH] at h'
        exact (mem_bot).1 h')
      have hfN : f ∈ normalizer (O2 M : Set G) := le_normalizer_twoResidualOf M hfM
      have hcom := fun k (hk : k ∈ O2 M) =>
        hOO (conj_mul_inv_mem_O (hiso f hf hff hf1) hfN hfH hk)
      refine ⟨⟨f, hfM⟩, ?_, rfl⟩
      show QuotientGroup.mk' (CFSG.oddCore M) ⟨f, hfM⟩ ∈ centralizer (bar M (O2 M) : Set (Bar M))
      rw [mem_centralizer_iff]
      rintro _ ⟨⟨k, hkM⟩, hk, rfl⟩
      have hk' : k ∈ O2 M := hk
      obtain ⟨o, ho, hoe⟩ := hcom k hk'
      have h1 : QuotientGroup.mk' (CFSG.oddCore M)
          (⟨k, hkM⟩ * ⟨f, hfM⟩ * ⟨k, hkM⟩⁻¹ * ⟨f, hfM⟩⁻¹) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have : (⟨k, hkM⟩ * ⟨f, hfM⟩ * ⟨k, hkM⟩⁻¹ * ⟨f, hfM⟩⁻¹ : M) = o := Subtype.ext hoe.symm
        rw [this]
        exact ho
      simp only [map_mul, map_inv] at h1
      have h2 := mul_inv_eq_one.1 h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hPbar : bar M P ≤ centralizer (bar M (O2 M) : Set (Bar M)) := by
      rintro _ ⟨⟨p, hpM⟩, hp, rfl⟩
      obtain ⟨p', hp', hpp'⟩ := hPL hp
      have : p' = ⟨p, hpM⟩ := Subtype.ext hpp'
      rw [← this]
      exact hp'
    exact le_centralizer_iff.1 hPbar
  ·
    have h1 := hsyl.inf_of_le_normalizer hHM (le_normalizer_twoResidualOf M)
    have heq : (P ⊔ Q) ⊓ O2 M = Q := by
      refine le_antisymm (fun g hg => ?_) (le_inf le_sup_right hQH)
      obtain ⟨hgPQ, hgH⟩ := mem_inf.1 hg
      obtain ⟨x, hx, y, hy, rfl⟩ := (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer
        (CFSG.CGT.Foote81L6.le_normalizer_of_comm hcomm)).1 hgPQ
      have hxH : x ∈ O2 M := by
        have h := (O2 M).mul_mem hgH ((O2 M).inv_mem (hQH hy))
        rwa [mul_inv_cancel_right] at h
      have hx1 : x = 1 := by
        have h : x ∈ P ⊓ O2 M := mem_inf.2 ⟨hx, hxH⟩
        rw [hPH] at h
        exact (mem_bot).1 h
      rw [hx1, one_mul]
      exact hy
    rwa [heq] at h1

variable (𝔖 : Sec3Setting G)

theorem bar_C_structure_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {z : G}
    (hz : z ∈ 𝔖.S₁ ∧ orderOf z = 2 ∧ 𝔖.S₁ ≤ C z) :
    bar (C z) 𝔖.S₁ ⊓ bar (C z) (O2 (C z)) = ⊥ ∧ bar (C z) 𝔖.S₁ ⊔ bar (C z) (O2 (C z)) = ⊤ ∧
      bar (C z) (O2 (C z)) ≤ centralizer (bar (C z) 𝔖.S₁ : Set (Bar (C z))) ∧
      ABGLocalTools.IsSylowOf 2 𝔖.S₂ (O2 (C z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzS₁, hz2, hzc⟩ := hz
  have hS₂z : 𝔖.S₂ ≤ C z := fun y hy => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hzS₁ hy).symm
  have hSz : (𝔖.S : Subgroup G) ≤ C z := le_C_of_central 𝔖 hzc hS₂z
  have hsylC : ABGLocalTools.IsSylowOf 2 (𝔖.S : Subgroup G) (C z) := isSylowOf_S 𝔖 hSz
  have hS₂H : 𝔖.S₂ ≤ O2 (C z) := le_twoResidualOf_right 𝔖 hpf hS₂z fun A hAS hA => by
    have hzA : z ∈ A := 𝔖.decomp.center_le hAS hA (𝔖.decomp.le_left hzS₁) hSz
    exact centralizer_le (Set.singleton_subset_iff.2 (mem_inf.2 ⟨hzA, hzS₁⟩))
  have hsylH : ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ O2 (C z)) ⊔ 𝔖.S₂) (O2 (C z)) := by
    rw [← sup_inf_eq_inf_sup 𝔖.decomp hS₂H]
    exact hsylC.inf_of_le_normalizer (twoResidualOf_le_self _) (le_normalizer_twoResidualOf _)
  have hS₁H : 𝔖.S₁ ⊓ O2 (C z) = ⊥ := inf_left_eq_bot 𝔖 hpf (twoResidualOf_twoResidualOf _) hS₂H
    hsylH hzS₁ hz2 hzc (twoResidualOf_le_self _)
  have hS₂syl : ABGLocalTools.IsSylowOf 2 𝔖.S₂ (O2 (C z)) := by
    rwa [hS₁H, bot_sup_eq] at hsylH
  exact bar_C_structure hzc hS₂H hS₁H (fun x hx y hy => 𝔖.decomp.comm hx hy)
    (by rw [𝔖.decomp.sup_eq]; exact hsylC) 𝔖.decomp.dih₁ fun f hf hff hf1 =>
      isIsolatedIn_sup_zpowers_left 𝔖 hpf hS₂syl hf (orderOf_eq_prime (by rw [sq]; exact hff) hf1)
        (le_normalizer_twoResidualOf _ (hzc hf)) fun h => hf1 (by
          have h' : f ∈ 𝔖.S₁ ⊓ O2 (C z) := mem_inf.2 ⟨hf, h⟩
          rw [hS₁H] at h'
          exact (mem_bot).1 h')

theorem bar_C_structure_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {z : G}
    (hz : z ∈ 𝔖.S₂ ∧ orderOf z = 2 ∧ 𝔖.S₂ ≤ C z) :
    bar (C z) 𝔖.S₂ ⊓ bar (C z) (O2 (C z)) = ⊥ ∧ bar (C z) 𝔖.S₂ ⊔ bar (C z) (O2 (C z)) = ⊤ ∧
      bar (C z) (O2 (C z)) ≤ centralizer (bar (C z) 𝔖.S₂ : Set (Bar (C z))) ∧
      ABGLocalTools.IsSylowOf 2 𝔖.S₁ (O2 (C z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzS₂, hz2, hzc⟩ := hz
  have hS₁z : 𝔖.S₁ ≤ C z := fun y hy => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hy hzS₂)
  have hSz : (𝔖.S : Subgroup G) ≤ C z := le_C_of_central 𝔖 hS₁z hzc
  have hsylC : ABGLocalTools.IsSylowOf 2 (𝔖.S : Subgroup G) (C z) := isSylowOf_S 𝔖 hSz
  have hS₁H : 𝔖.S₁ ≤ O2 (C z) := le_twoResidualOf_left 𝔖 hpf hS₁z fun A hAS hA => by
    have hzA : z ∈ A := 𝔖.decomp.center_le hAS hA (𝔖.decomp.le_right hzS₂) hSz
    exact centralizer_le (Set.singleton_subset_iff.2 (mem_inf.2 ⟨hzA, hzS₂⟩))
  have hsplit : (𝔖.S : Subgroup G) ⊓ O2 (C z) = 𝔖.S₁ ⊔ (𝔖.S₂ ⊓ O2 (C z)) := by
    refine le_antisymm (fun g hg => ?_)
      (sup_le (le_inf 𝔖.decomp.le_left hS₁H) (inf_le_inf_right _ 𝔖.decomp.le_right))
    obtain ⟨hgS, hgH⟩ := mem_inf.1 hg
    obtain ⟨x, hx, y, hy, rfl⟩ := 𝔖.decomp.mem_iff.1 hgS
    have hyH : y ∈ O2 (C z) := by
      have h := (O2 (C z)).mul_mem ((O2 (C z)).inv_mem (hS₁H hx)) hgH
      rwa [inv_mul_cancel_left] at h
    exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_inf.2 ⟨hy, hyH⟩))
  have hsylH : ABGLocalTools.IsSylowOf 2 (𝔖.S₁ ⊔ (𝔖.S₂ ⊓ O2 (C z))) (O2 (C z)) := by
    rw [← hsplit]
    exact hsylC.inf_of_le_normalizer (twoResidualOf_le_self _) (le_normalizer_twoResidualOf _)
  have hS₂H : 𝔖.S₂ ⊓ O2 (C z) = ⊥ := inf_right_eq_bot 𝔖 hpf (twoResidualOf_twoResidualOf _) hS₁H
    hsylH hzS₂ hz2 hzc (twoResidualOf_le_self _)
  have hS₁syl : ABGLocalTools.IsSylowOf 2 𝔖.S₁ (O2 (C z)) := by
    rwa [hS₂H, sup_bot_eq] at hsylH
  exact bar_C_structure hzc hS₁H hS₂H (fun x hx y hy => (𝔖.decomp.comm hy hx).symm)
    (by rw [sup_comm, 𝔖.decomp.sup_eq]; exact hsylC) 𝔖.decomp.isDih₂ fun f hf hff hf1 =>
      isIsolatedIn_sup_zpowers_right 𝔖 hpf hS₁syl hf (orderOf_eq_prime (by rw [sq]; exact hff) hf1)
        (le_normalizer_twoResidualOf _ (hzc hf)) fun h => hf1 (by
          have h' : f ∈ 𝔖.S₂ ⊓ O2 (C z) := mem_inf.2 ⟨hf, h⟩
          rw [hS₂H] at h'
          exact (mem_bot).1 h')

end Side

section GW

variable {G : Type} [Group G] [Finite G]

theorem gw_inputs {M Q : Subgroup G} (hQ : ABGLocalTools.IsSylowOf 2 Q (O2 M)) (hQD : IsDih Q) :
    CFSG.oddCore ↥(O2 (⊤ : Subgroup (Bar M))) = ⊥ ∧
      (∀ N : Subgroup ↥(O2 (⊤ : Subgroup (Bar M))), N.Normal → N.index ≠ 2) ∧
      HasDihedralSylowTwo ↥(O2 (⊤ : Subgroup (Bar M))) ∧
      ABGLocalTools.IsSylowOf 2 (bar M Q) (O2 (⊤ : Subgroup (Bar M))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup (Bar M) := O2 (⊤ : Subgroup (Bar M)) with hHdef
  have hQM : Q ≤ M := hQ.le.trans (twoResidualOf_le_self M)
  have hQsyl : ABGLocalTools.IsSylowOf 2 (bar M Q) H := by
    have h := G4b.isSylowOf_bar_of_isSylowOf (twoResidualOf_le_self M) hQ
    rwa [bar_twoResidualOf] at h
  refine ⟨?_, index_ne_two_of_twoResidualOf (⊤ : Subgroup (Bar M)), ?_, hQsyl⟩
  ·
    have hOH : O H = ⊥ := G4b.eq_bot_of_odd_of_le_normal (oddCore_quotient_oddCore_eq_bot M)
      twoResidualOf_top_normal (G4b.O_le_self H) (le_normalizer_O H) (card_O_odd H)
    exact (map_eq_bot_iff_of_injective _ H.subtype_injective).1 hOH
  ·
    intro T
    obtain ⟨a, ha, ⟨eQ⟩⟩ := hQD
    have hT : ABGLocalTools.IsSylowOf 2 ((T : Subgroup H).map H.subtype) H := ⟨T, rfl⟩
    obtain ⟨k, -, hk⟩ := G4b.exists_map_conj_eq_of_isSylowOf hT hQsyl
    obtain ⟨eb⟩ := G4b.nonempty_mulEquiv_bar hQM hQ.isPGroup
    have e₁ : (T : Subgroup H) ≃* (T : Subgroup H).map H.subtype :=
      (T : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
    have e₂ : ((T : Subgroup H).map H.subtype : Subgroup (Bar M)) ≃*
        ((T : Subgroup H).map H.subtype).map (MulAut.conj k).toMonoidHom :=
      ((T : Subgroup H).map H.subtype).equivMapOfInjective _ (MulAut.conj k).injective
    exact ⟨a, ha, ⟨((e₁.trans e₂).trans (MulEquiv.subgroupCongr hk)).trans (eb.symm.trans eQ)⟩⟩

theorem le_commutator_of_odd_index {X : Type} [Group X] [Finite X] {H W : Subgroup X}
    (hWH : W ≤ H) (hW : IsPGroup 2 W) (hodd : Odd (commutator ↥H).index) : W ≤ ⁅H, H⁆ := by
  have h := G4b.le_of_isPGroup_of_odd_index (Z := ↥H) (L := commutator ↥H) hodd
    (W := W.subgroupOf H) hW.comap_subtype
  intro w hw
  rw [← map_subtype_commutator H]
  exact ⟨⟨w, hWH hw⟩, h (mem_subgroupOf.2 hw), rfl⟩

theorem card_commutator_subgroup {X : Type} [Group X] (H : Subgroup X) :
    Nat.card ↥(⁅H, H⁆ : Subgroup X) = Nat.card ↥(commutator ↥H) := by
  rw [← map_subtype_commutator H, card_map_of_injective H.subtype_injective]


variable (𝔖 : Sec3Setting G)

theorem exists_bar_C_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {z₁ : G}
    (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) :
    ∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
      H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
      bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₁, h₂, h₃, hsyl⟩ := bar_C_structure_left 𝔖 hpf hz₁
  rw [bar_twoResidualOf] at h₁ h₂ h₃
  obtain ⟨hO, h2, hD, hQsyl⟩ := gw_inputs hsyl 𝔖.decomp.isDih₂
  set H₁ : Subgroup (Bar (C z₁)) := O2 (⊤ : Subgroup (Bar (C z₁))) with hH₁
  have h8 : 8 ∣ Nat.card ↥H₁ := by
    obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₂
    have hcard : Nat.card ↥(bar (C z₁) 𝔖.S₂) = 2 * 2 ^ a := by
      rw [G4b.card_bar_of_isPGroup (hsyl.le.trans (twoResidualOf_le_self _)) hsyl.isPGroup,
        Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h8' : 8 ∣ 2 * 2 ^ a := ⟨2 ^ (a - 2), by
      rw [show (8 : ℕ) = 2 * 2 ^ 2 by norm_num, mul_assoc, ← pow_add, Nat.add_sub_cancel' ha]⟩
    exact (hcard ▸ h8').trans (card_dvd_of_le hQsyl.le)
  refine ⟨H₁, h₁, h₂, h₃, ?_, isL2OrA7_commutator_of_subgroup H₁
    (gw_commutator_isL2OrA7_seven hO h2 hD h8)⟩
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨hodd, -, -⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h8
    exact absurd h8 (by decide)
  · exact le_commutator_of_odd_index hQsyl.le hQsyl.isPGroup hodd

theorem exists_bar_C_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {z₂ : G}
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) :
    ∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
      K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
      bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
      (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₁, h₂, h₃, hsyl⟩ := bar_C_structure_right 𝔖 hpf hz₂
  rw [bar_twoResidualOf] at h₁ h₂ h₃
  obtain ⟨hO, h2, hD, hQsyl⟩ := gw_inputs hsyl 𝔖.decomp.dih₁
  set K₁ : Subgroup (Bar (C z₂)) := O2 (⊤ : Subgroup (Bar (C z₂))) with hK₁
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨hodd, hL, -⟩
  ·
    obtain ⟨h4, h3⟩ := isKleinFour_commutator_of_mulEquiv_alternatingGroup_four e
    have hle : bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ :=
      le_commutator_of_odd_index hQsyl.le hQsyl.isPGroup (by rw [h3]; decide)
    have hcomm2 : IsPGroup 2 ↥(⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) :=
      IsPGroup.of_card (n := 2) (by rw [card_commutator_subgroup, h4.card_four]; norm_num)
    have hKK : (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) ≤ K₁ :=
      commutator_le.2 fun a ha b hb => mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact ⟨K₁, h₁, h₂, h₃, hle, Or.inr (hQsyl.eq_of_le hle hKK hcomm2)⟩
  · exact ⟨K₁, h₁, h₂, h₃, le_commutator_of_odd_index hQsyl.le hQsyl.isPGroup hodd,
      Or.inl (isL2OrA7_commutator_of_subgroup K₁ hL)⟩

end GW

end G3cF

namespace Sec3Setting

variable {G : Type} [Group G] [Finite G]

theorem prop_3_15 (𝔖 : Sec3Setting G) (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) (z₁ z₂ : G)
    (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁)
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) :
    (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
      H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
      bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
    (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
      K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
      bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
      (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)) :=
  ⟨G3cF.exists_bar_C_left 𝔖 hpf hz₁, G3cF.exists_bar_C_right 𝔖 hpf hz₂⟩

end Sec3Setting

end CFSG.GH72
