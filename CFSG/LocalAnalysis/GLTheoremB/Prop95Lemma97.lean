module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97QGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace L97

variable {G : Type} [Group G] [Finite G]

theorem commutator_sup_le {Γ X N O M : Subgroup G} (hΓM : Γ ≤ M) (hXM : X ≤ M) (hNM : N ≤ M)
    (hO : M ≤ Subgroup.normalizer (O : Set G)) (hX : ⁅Γ, X⁆ ≤ O) (hN : ⁅Γ, N⁆ ≤ O) :
    ⁅Γ, X ⊔ N⁆ ≤ O := by
  let C : Subgroup G :=
    { carrier := {b | b ∈ M ∧ ∀ a ∈ Γ, ⁅a, b⁆ ∈ O}
      one_mem' := ⟨M.one_mem, fun a _ => by simp⟩
      mul_mem' := by
        rintro b c ⟨hb, hbO⟩ ⟨hc, hcO⟩
        refine ⟨M.mul_mem hb hc, fun a ha => ?_⟩
        have h1 : b * ⁅a, c⁆ * b⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (hO hb) _).1 (hcO a ha)
        have h2 := O.mul_mem (hbO a ha) h1
        have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact h2
      inv_mem' := by
        rintro b ⟨hb, hbO⟩
        refine ⟨M.inv_mem hb, fun a ha => ?_⟩
        have h1 : b⁻¹ * ⁅a, b⁆⁻¹ * b⁻¹⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (hO (M.inv_mem hb)) _).1 (O.inv_mem (hbO a ha))
        have e : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact h1 }
  have hXC : X ≤ C := fun b hb => ⟨hXM hb, fun a ha => hX (Subgroup.commutator_mem_commutator ha hb)⟩
  have hNC : N ≤ C := fun b hb => ⟨hNM hb, fun a ha => hN (Subgroup.commutator_mem_commutator ha hb)⟩
  have hXNC : X ⊔ N ≤ C := sup_le hXC hNC
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact (hXNC hb).2 a ha

theorem le_normalizer_sup' {X N M : Subgroup G} (hX : M ≤ Subgroup.normalizer (X : Set G))
    (hN : M ≤ Subgroup.normalizer (N : Set G)) : M ≤ Subgroup.normalizer ((X ⊔ N : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hX hm),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hN hm)]

end L97

open L97

variable {G : Type} [Group G] [Finite G]

theorem lemma97_of (hab : Lemma97Ab) (hnab : Lemma97NonAb) : Lemma97 := by
  intro G _ _ m p hS M D hD
  classical
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have hΓM : gammaD D ≤ M := gammaD_le_of_hyp hD
  have hPM : GLAPPrimeCoreOf p M ≤ M := GLAPPrimeCoreOf_le p M
  have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
  have hMP : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    le_normalizer_glaPPrimeCoreOf p M
  let F : Set (Subgroup G) := {N | N ≤ GLAPPrimeCoreOf p M ∧ M ≤ Subgroup.normalizer (N : Set G) ∧
    ⁅gammaD D, N⁆ ≤ pCoreOf 2 M}
  have hOF : pCoreOf 2 M ∈ F := by
    refine ⟨pCoreOf_two_le_glaPPrimeCoreOf hp hp2 M, hMO, ?_⟩
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 := (Subgroup.mem_normalizer_iff.1 (hMO (hΓM ha)) b).1 hb
    have := (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hb)
    simpa [commutatorElement_def, mul_assoc] using this
  obtain ⟨X, hXF, hXmax⟩ := Set.exists_max_image F (fun N => Nat.card N) (Set.toFinite F) ⟨_, hOF⟩
  have hXP : X ≤ GLAPPrimeCoreOf p M := hXF.1
  have hXM : X ≤ M := hXP.trans hPM
  have hXle : ∀ N ∈ F, N ≤ X := by
    intro N hN
    have hNM : N ≤ M := hN.1.trans hPM
    have hsup : X ⊔ N ∈ F :=
      ⟨sup_le hXF.1 hN.1, le_normalizer_sup' hXF.2.1 hN.2.1,
        commutator_sup_le hΓM hXM hNM hMO hXF.2.2 hN.2.2⟩
    have h1 : Nat.card ↥(X ⊔ N) ≤ Nat.card ↥X := hXmax _ hsup
    have h2 : X ⊔ N = X := (Subgroup.eq_of_le_of_card_ge le_sup_left h1).symm
    exact le_sup_right.trans h2.le
  by_cases hXeq : X = GLAPPrimeCoreOf p M
  · rw [← hXeq]; exact hXF.2.2
  · exfalso
    have hXlt : X < GLAPPrimeCoreOf p M := lt_of_le_of_ne hXP hXeq
    let S : Set (Subgroup G) := {V | X < V ∧ V ≤ GLAPPrimeCoreOf p M ∧
      M ≤ Subgroup.normalizer (V : Set G)}
    have hPS : GLAPPrimeCoreOf p M ∈ S := ⟨hXlt, le_rfl, hMP⟩
    obtain ⟨W, hWS, hWmin⟩ := Set.exists_min_image S (fun N => Nat.card N) (Set.toFinite S) ⟨_, hPS⟩
    have hWM : W ≤ M := hWS.2.1.trans hPM
    have hch : Lemma97Chief p M D X W :=
      { two_le := hXle _ hOF
        lt := hWS.1
        le_core := hWS.2.1
        normalX := (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hXF.2.1
        normalW := (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).2 hWS.2.2
        commX := hXF.2.2
        chief := by
          intro V hVM hVn hXV hVW
          by_cases hVX : V = X
          · exact Or.inl hVX
          · refine Or.inr ?_
            have hVS : V ∈ S := ⟨lt_of_le_of_ne hXV (Ne.symm hVX), hVW.trans hWS.2.1,
              (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).1 hVn⟩
            exact Subgroup.eq_of_le_of_card_ge hVW (hWmin V hVS)
        comm_ne := by
          intro hc
          have hWF : W ∈ F := ⟨hWS.2.1, hWS.2.2, hc⟩
          exact absurd (hXle W hWF) (not_le_of_gt hWS.1) }
    by_cases hWW : ⁅W, W⁆ ≤ X
    · exact hab G m p hS M D hD X W hch hWW
    · exact hnab G m p hS M D hD X W hch hWW

theorem prop95i_of (h : Lemma97) : Prop95i := by
  intro G _ _ m p hS M D hD
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have hΓM : gammaD D ≤ M := gammaD_le_of_hyp hD
  have hPM : GLAPPrimeCoreOf p M ≤ M := GLAPPrimeCoreOf_le p M
  have hcomm : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M := h G m p hS M D hD
  refine le_antisymm ?_ (le_inf hD.clause_c (pCoreOf_two_le_glaPPrimeCoreOf hp hp2 M))
  intro x hx
  have hxM : x ∈ M := hΓM hx.1
  have hPn : ((GLAPPrimeCoreOf p M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 (le_normalizer_glaPPrimeCoreOf p M)
  have hT : IsPGroup 2 (tl M (gammaD D)) := isPGroup_tl (isPGroup_gammaD D)
  have hTN : ∀ t ∈ tl M (gammaD D), ∀ n ∈ tl M (GLAPPrimeCoreOf p M), t * n = n * t := by
    intro t ht n hn
    obtain ⟨a, ha, rfl⟩ := mem_tl.1 ht
    obtain ⟨b, hb, rfl⟩ := mem_tl.1 hn
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, piM_eq_one_iff]
    simpa [commutatorElement_def] using hcomm (Subgroup.commutator_mem_commutator ha hb)
  have hbot := QGroup.inf_eq_bot_of_forall_commute (hO_Mt M) hT (tl_normal hPn) hTN
  have hmem : piM M ⟨x, hxM⟩ ∈ tl M (gammaD D) ⊓ tl M (GLAPPrimeCoreOf p M) :=
    ⟨piM_mem_tl hx.1, piM_mem_tl hx.2⟩
  rw [hbot, Subgroup.mem_bot, piM_eq_one_iff] at hmem
  exact hmem

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
