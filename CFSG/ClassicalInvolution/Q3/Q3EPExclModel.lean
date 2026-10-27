module

public import CFSG.ClassicalInvolution.Q3.Q3EPGeom
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot3.chainBound1 (h : CentralQuot3 π 𝓕 𝓕' Z') {d : ℕ}
    (hb : ChainBound1 Z' 𝓕' d) : ChainBound1 (Subgroup.center KY) 𝓕 d := by
  intro r hr c hc S hS hSc
  refine hb r hr (fun a => (c a).map π) ⟨?_, ?_, ?_⟩ (S.map π) (h.map_mem S hS) ?_
  · intro a ha
    exact h.map_mem _ (hc.mem a ha)
  · intro a ha
    exact h.modelAdj (hc.mem a (by omega)) (hc.mem (a + 1) ha) (hc.adj a ha)
  · intro a b hab hb'
    exact (h.commutes_iff (hc.mem a (by omega))).mpr (hc.comm a b hab hb')
  · intro a ha
    exact (h.commutes_iff hS).mpr (hSc a ha)

theorem CentralQuot3.d4Centralizer (h : CentralQuot3 π 𝓕 𝓕' Z') (hG : D4Centralizer Z' 𝓕') :
    D4Centralizer (Subgroup.center KY) 𝓕 := by
  intro c hc l₁ h₁ l₂ h₂ l₃ h₃ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23 S hS S' hS' hne cS c1 c2 c3 cS'
    c1' c2' c3'
  refine h.modelIndist hS hS' hne ?_
  refine hG (c.map π) (h.map_mem c hc) (l₁.map π) (h.map_mem l₁ h₁) (l₂.map π)
    (h.map_mem l₂ h₂) (l₃.map π) (h.map_mem l₃ h₃) (h.modelAdj hc h₁ a₁) (h.modelAdj hc h₂ a₂)
    (h.modelAdj hc h₃ a₃) (fun e => n12 (h.map_inj h₁ h₂ e)) (fun e => n13 (h.map_inj h₁ h₃ e))
    (fun e => n23 (h.map_inj h₂ h₃ e)) ((h.commutes_iff h₁).mpr k12) ((h.commutes_iff h₁).mpr k13)
    ((h.commutes_iff h₂).mpr k23) (S.map π) (h.map_mem S hS) (S'.map π) (h.map_mem S' hS')
    (fun e => hne (h.map_inj hS hS' e)) ((h.commutes_iff hS).mpr cS) ((h.commutes_iff hS).mpr c1)
    ((h.commutes_iff hS).mpr c2) ((h.commutes_iff hS).mpr c3) ((h.commutes_iff hS').mpr cS')
    ((h.commutes_iff hS').mpr c1') ((h.commutes_iff hS').mpr c2') ((h.commutes_iff hS').mpr c3')

end Transfer

section Plus

theorem chainBound1_3_plus6 :
    ChainBound1 (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D) 12 := by
  have hm3 : 3 ≤ 6 := by norm_num
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hb := chainBound1_model (Q := quadPlus 6 (GaloisField 3 1)) odd_gf3
    (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1)) hdim
  rw [finrank_plus] at hb
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  rw [e]
  exact centralQuot3_plus6.chainBound1 hb

theorem d4Centralizer3_plus6 :
    D4Centralizer (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D) := by
  have hm3 : 3 ≤ 6 := by norm_num
  have hd := finrank_plus 3 1 6
  have hG : D4Centralizer (scalars (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1))
      (fundSet (quadPlus 6 (GaloisField 3 1))) :=
    orth_d4_centralizer odd_gf3 (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1))
      (by omega) (by omega)
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  rw [e]
  exact centralQuot3_plus6.d4Centralizer hG

end Plus

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {N : Subgroup G} {x : G}

theorem ETCtx3.chain1_config (cx : ETCtx3 tY nY Ω N x) {d : ℕ}
    (hF : ChainBound1 (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) d)
    {r : ℕ} (hr : 4 ≤ r) {c : ℕ → Subgroup G} {w : ℕ → G}
    (hc : ∀ a < r, cx.IsLayerMember (c a))
    (hw : ∀ a < r, IsClassicalMember3 (c a) (w a))
    (hadj : ∀ a, a + 1 < r → c a ≠ c (a + 1) ∧ ¬ Commutes (c a) (c (a + 1)) ∧
      Commute (w a) (w (a + 1)) ∧ conjSub (w (a + 1)) (c a) = c a)
    (hcomm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b))
    {S : Subgroup G} (hS : cx.IsLayerMember S) (hSc : ∀ a < r, Commutes S (c a)) :
    2 * (r + 1) + 4 ≤ d := by
  classical
  have hex : ∀ a : ℕ, ∃ R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K, a < r →
      R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
        locImg Ω x (c a) = R.map cx.d.ψ := by
    intro a
    by_cases h : a < r
    · obtain ⟨R, hR, hlR⟩ := (hc a h).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h' => absurd h' h⟩
  choose R hR using hex
  obtain ⟨RS, hRS, hSR⟩ := hS.exists_fund
  refine hF r hr R ⟨fun a ha => (hR a ha).1, fun a ha => ?_, fun a b hab hb => ?_⟩ RS hRS
    (fun a ha => ?_)
  · exact cx.modelAdj_of_adj (hc a (by omega)).1 (hc (a + 1) ha).1 (hR a (by omega)).1
      (hR (a + 1) ha).1 (hR a (by omega)).2 (hR (a + 1) ha).2 (hw a (by omega)) (hw (a + 1) ha)
      (hadj a ha).1 (hadj a ha).2.1 (hadj a ha).2.2.1 (hadj a ha).2.2.2
  · exact (cx.commutes_iff_fund (hc a (by omega)).1 (hc b hb).1 (hR a (by omega)).1
      (hR a (by omega)).2 (hR b hb).2).mp (hcomm a b hab hb)
  · exact (cx.commutes_iff_fund hS.1 (hc a ha).1 hRS hSR (hR a ha).2).mp (hSc a ha)

theorem ETCtx3.chain5_member_false (cx : ETCtx3 tY nY Ω N x) {d : ℕ}
    (hF : ChainBound1 (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) d) (hd : d < 16)
    {m₀ m₁ m₂ m₃ m₄ S : Subgroup G} {v₀ v₁ v₂ v₃ v₄ : G}
    (h₀ : cx.IsLayerMember m₀) (h₁ : cx.IsLayerMember m₁) (h₂ : cx.IsLayerMember m₂)
    (h₃ : cx.IsLayerMember m₃) (h₄ : cx.IsLayerMember m₄) (hS : cx.IsLayerMember S)
    (hw₀ : IsClassicalMember3 m₀ v₀) (hw₁ : IsClassicalMember3 m₁ v₁)
    (hw₂ : IsClassicalMember3 m₂ v₂) (hw₃ : IsClassicalMember3 m₃ v₃)
    (hw₄ : IsClassicalMember3 m₄ v₄)
    (a₀₁ : m₀ ≠ m₁ ∧ ¬ Commutes m₀ m₁ ∧ Commute v₀ v₁ ∧ conjSub v₁ m₀ = m₀)
    (a₁₂ : m₁ ≠ m₂ ∧ ¬ Commutes m₁ m₂ ∧ Commute v₁ v₂ ∧ conjSub v₂ m₁ = m₁)
    (a₂₃ : m₂ ≠ m₃ ∧ ¬ Commutes m₂ m₃ ∧ Commute v₂ v₃ ∧ conjSub v₃ m₂ = m₂)
    (a₃₄ : m₃ ≠ m₄ ∧ ¬ Commutes m₃ m₄ ∧ Commute v₃ v₄ ∧ conjSub v₄ m₃ = m₃)
    (c₀₂ : Commutes m₀ m₂) (c₀₃ : Commutes m₀ m₃) (c₀₄ : Commutes m₀ m₄)
    (c₁₃ : Commutes m₁ m₃) (c₁₄ : Commutes m₁ m₄) (c₂₄ : Commutes m₂ m₄)
    (s₀ : Commutes S m₀) (s₁ : Commutes S m₁) (s₂ : Commutes S m₂) (s₃ : Commutes S m₃)
    (s₄ : Commutes S m₄) : False := by
  have key := cx.chain1_config hF (r := 5) (by norm_num)
    (c := fun a => match a with | 0 => m₀ | 1 => m₁ | 2 => m₂ | 3 => m₃ | _ => m₄)
    (w := fun a => match a with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃ | _ => v₄)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by
      have : a < 4 := by omega
      interval_cases a <;> assumption)
    (fun a b hab hb => by
      have : a < 4 := by omega
      interval_cases a <;> interval_cases b <;> omega)
    hS (fun a ha => by interval_cases a <;> assumption)
  omega

theorem ETCtx3.commutes_iff_of_d4 (cx : ETCtx3 .POmegaPlus 6 Ω N x)
    {S S' J₂ J₃ J₄ J₅ B : Subgroup G} {wS wS' w₂ w₃ w₄ w₅ wB : G}
    (hS : cx.IsLayerMember S) (hS' : cx.IsLayerMember S') (h₂ : cx.IsLayerMember J₂)
    (h₃ : cx.IsLayerMember J₃) (h₄ : cx.IsLayerMember J₄) (h₅ : cx.IsLayerMember J₅)
    (hB : cx.IsLayerMember B) (hwS : IsClassicalMember3 S wS)
    (hwS' : IsClassicalMember3 S' wS') (hw₂ : IsClassicalMember3 J₂ w₂)
    (hw₃ : IsClassicalMember3 J₃ w₃) (hw₄ : IsClassicalMember3 J₄ w₄)
    (hw₅ : IsClassicalMember3 J₅ w₅) (hwB : IsClassicalMember3 B wB)
    (p23 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W J₂ J₃)
    (p34 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W J₃ J₄)
    (p35 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W J₃ J₅)
    (c24 : Commutes J₂ J₄) (c25 : Commutes J₂ J₅) (c45 : Commutes J₄ J₅) (hSS' : S ≠ S')
    (s₂ : Commutes S J₂) (s₃ : Commutes S J₃) (s₄ : Commutes S J₄) (s₅ : Commutes S J₅)
    (s₂' : Commutes S' J₂) (s₃' : Commutes S' J₃) (s₄' : Commutes S' J₄)
    (s₅' : Commutes S' J₅) (hBS : B ≠ S) (hBS' : B ≠ S') (cBS : Commute wB wS)
    (cBS' : Commute wB wS') : Commutes B S ↔ Commutes B S' := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨RS, hRS, hSR⟩ := hS.exists_fund
  obtain ⟨RS', hRS', hSR'⟩ := hS'.exists_fund
  obtain ⟨R₂, hR₂, h₂R⟩ := h₂.exists_fund
  obtain ⟨R₃, hR₃, h₃R⟩ := h₃.exists_fund
  obtain ⟨R₄, hR₄, h₄R⟩ := h₄.exists_fund
  obtain ⟨R₅, hR₅, h₅R⟩ := h₅.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hB.exists_fund
  obtain ⟨W₂₃, hW₂₃⟩ := p23
  obtain ⟨W₃₄, hW₃₄⟩ := p34
  obtain ⟨W₃₅, hW₃₅⟩ := p35
  have a32 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R₃
      R₂ :=
    cx.modelAdj_of_adj h₃.1 h₂.1 hR₃ hR₂ h₃R h₂R hw₃ hw₂ (ne_of_linearBlockStandardPair hW₂₃).symm
      (fun h => not_commutes_of_linearBlockStandardPair hW₂₃ (Gaps.commutes_symm h))
      (Gaps.standardPair_involutions_commute h2 hW₂₃ hw₂.mem hw₃.mem hw₂.orderOf_eq_two
        hw₃.orderOf_eq_two).symm
      (Gaps.conjSub_eq_of_standardPair h2 hW₂₃.symm hw₂.mem hw₂.orderOf_eq_two)
  have a34 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R₃
      R₄ :=
    cx.modelAdj_of_adj h₃.1 h₄.1 hR₃ hR₄ h₃R h₄R hw₃ hw₄ (ne_of_linearBlockStandardPair hW₃₄)
      (not_commutes_of_linearBlockStandardPair hW₃₄)
      (Gaps.standardPair_involutions_commute h2 hW₃₄ hw₃.mem hw₄.mem hw₃.orderOf_eq_two
        hw₄.orderOf_eq_two)
      (Gaps.conjSub_eq_of_standardPair h2 hW₃₄ hw₄.mem hw₄.orderOf_eq_two)
  have a35 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R₃
      R₅ :=
    cx.modelAdj_of_adj h₃.1 h₅.1 hR₃ hR₅ h₃R h₅R hw₃ hw₅ (ne_of_linearBlockStandardPair hW₃₅)
      (not_commutes_of_linearBlockStandardPair hW₃₅)
      (Gaps.standardPair_involutions_commute h2 hW₃₅ hw₃.mem hw₅.mem hw₃.orderOf_eq_two
        hw₅.orderOf_eq_two)
      (Gaps.conjSub_eq_of_standardPair h2 hW₃₅ hw₅.mem hw₅.orderOf_eq_two)
  have ne_of_comm : ∀ {L L' : Subgroup G}, L ∈ centralizingMembers Ω {x} → Commutes L L' →
      L ≠ L' := by
    intro L L' hL hc e
    obtain ⟨w, hw⟩ := cx.hΩ.classical L hL.1
    exact not_commutes_self3 hw (e ▸ hc)
  have hne_of_R : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 6 3 1
      Nat.prime_three).K}, L ∈ centralizingMembers Ω {x} → L' ∈ centralizingMembers Ω {x} →
      L ≠ L' → locImg Ω x L = R.map cx.d.ψ → locImg Ω x L' = R'.map cx.d.ψ → R ≠ R' :=
    fun hL hL' hne hlR hlR' h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hlR, hlR', h]))
  have cR : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 6 3 1
      Nat.prime_three).K}, L ∈ centralizingMembers Ω {x} → L' ∈ centralizingMembers Ω {x} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D →
      locImg Ω x L = R.map cx.d.ψ → locImg Ω x L' = R'.map cx.d.ψ → Commutes L L' →
      Commutes R R' := fun hL hL' hR hlR hlR' hc =>
    (cx.commutes_iff_fund hL hL' hR hlR hlR').mp hc
  have hind := d4Centralizer3_plus6 R₃ hR₃ R₂ hR₂ R₄ hR₄ R₅ hR₅ a32 a34 a35
    (hne_of_R h₂.1 h₄.1 (ne_of_comm h₂.1 c24) h₂R h₄R)
    (hne_of_R h₂.1 h₅.1 (ne_of_comm h₂.1 c25) h₂R h₅R)
    (hne_of_R h₄.1 h₅.1 (ne_of_comm h₄.1 c45) h₄R h₅R)
    (cR h₂.1 h₄.1 hR₂ h₂R h₄R c24) (cR h₂.1 h₅.1 hR₂ h₂R h₅R c25)
    (cR h₄.1 h₅.1 hR₄ h₄R h₅R c45) RS hRS RS' hRS' (hne_of_R hS.1 hS'.1 hSS' hSR hSR')
    (cR hS.1 h₃.1 hRS hSR h₃R s₃) (cR hS.1 h₂.1 hRS hSR h₂R s₂) (cR hS.1 h₄.1 hRS hSR h₄R s₄)
    (cR hS.1 h₅.1 hRS hSR h₅R s₅) (cR hS'.1 h₃.1 hRS' hSR' h₃R s₃')
    (cR hS'.1 h₂.1 hRS' hSR' h₂R s₂') (cR hS'.1 h₄.1 hRS' hSR' h₄R s₄')
    (cR hS'.1 h₅.1 hRS' hSR' h₅R s₅')
  have hiK : Gaps.ModelInvComm (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) RB
      RS := by
    obtain ⟨r, r', hr, hr', hcen, -, -⟩ := cx.modelInvComm_of_commute hB.1 hS.1 hRB hRS hBR hSR
      hwB hwS cBS
    exact ⟨r, r', hr, hr', hcen⟩
  have hiN : Gaps.ModelInvComm (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) RB
      RS' := by
    obtain ⟨r, r', hr, hr', hcen, -, -⟩ := cx.modelInvComm_of_commute hB.1 hS'.1 hRB hRS' hBR
      hSR' hwB hwS' cBS'
    exact ⟨r, r', hr, hr', hcen⟩
  have key := hind.2 RB hRB (hne_of_R hB.1 hS.1 hBS hBR hSR) (hne_of_R hB.1 hS'.1 hBS' hBR hSR')
    hiK hiN
  rw [cx.commutes_iff_fund hB.1 hS.1 hRB hBR hSR, cx.commutes_iff_fund hB.1 hS'.1 hRB hBR hSR']
  exact key

end Witness

end CFSG.ClassicalInvolution.Q3.Q3W
