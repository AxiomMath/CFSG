module

public import CFSG.ClassicalInvolution.Q3.Q3TWY24

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_bridges_group3 {u : ℕ} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaOdd (u + 5)).1
      (twinYModel 3 .POmegaOdd (u + 5)).2) Ω x) {M : Subgroup G} (nd : DNodes3 (u + 5) Ω M)
    (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {x}) :
    ∃ N₁ ∈ centralizingMembers Ω {x}, ∃ N₂ ∈ centralizingMembers Ω {x},
      (∀ a : Fin (u + 5), a.val < u + 3 → Commutes N₁ (nd.J a) ∧ Commutes N₂ (nd.J a)) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 4, by omega⟩) N₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N₂) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 4, by omega⟩) N₂) ∧
      ¬ Commutes N₁ N₂ ∧ N₁ ≠ N₂ := by
  classical
  have hmod : twinYModel 3 .POmegaOdd (u + 5) = (.POmegaOdd, u + 6) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaOdd (u + 6) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  have hY := yData3_odd (by omega : 3 ≤ u + 6) hadm
  have : Finite (modelUniv .POmegaOdd (u + 6) 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc (hx ⟨0, by omega⟩) hshape
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have cq := centralQuot3_odd (m := u + 6) (by omega)
  have hQ : (polarBilin (quadOdd (u + 6) 𝔽₃)).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd (u + 6) _ h2
  have hdim : 2 * (u + 3) + 7 ≤ Module.finrank 𝔽₃ (Fin (u + 6) ⊕ Fin (u + 6) ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
    omega
  have hmem : ∀ a : Fin (u + 5), ∃ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd (u + 6) 3 1 Nat.prime_three).D, locImg Ω x (nd.J a) = R.map e.φ :=
    fun a => e.mem _ (hx a)
  choose R hRf hLR using hmem
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ → Fin (u + 5), ∀ a, a < u + 5 → (jn a).val = a :=
    ⟨fun a => ⟨min a (u + 4), by omega⟩, fun a h => by simp only; omega⟩
  have hadjn : ∀ a, a < u + 3 → DNodes3.DAdj (jn a) (jn (a + 1)) := fun a h => by
    simp [DNodes3.DAdj, edgeD, hjn a (by omega), hjn (a + 1) (by omega)]
    omega
  have hnadj : ∀ a b, a + 1 < b → b ≤ u + 3 → ¬ DNodes3.DAdj (jn a) (jn b) := fun a b hab hb => by
    simp [DNodes3.DAdj, edgeD, hjn a (by omega), hjn b (by omega)]
    omega
  have hne : ∀ a b, a < u + 5 → b < u + 5 → a ≠ b → jn a ≠ jn b := fun a b ha hb hab h => by
    have := congrArg Fin.val h
    rw [hjn a ha, hjn b hb] at this
    exact hab this
  have h4 : jn (u + 3) = ⟨u + 3, by omega⟩ := Fin.ext (hjn (u + 3) (by omega))
  have h5 : jn (u + 4) = ⟨u + 4, by omega⟩ := Fin.ext (hjn (u + 4) (by omega))
  have hcommR : ∀ a b : ℕ, a < u + 5 → b < u + 5 → Commutes (nd.J (jn a)) (nd.J (jn b)) →
      Commutes (R (jn a)) (R (jn b)) := fun a b ha hb hc =>
    (e.commutes_iff hY hΩ hex hP1 hO3 (hx _) (hx _) (hRf _) (hLR _) (hLR _)).mp hc
  have hadjR : ∀ a b : ℕ, a < u + 5 → b < u + 5 → DNodes3.DAdj (jn a) (jn b) →
      ModelAdj (Subgroup.center (modelUniv .POmegaOdd (u + 6) 3 1 Nat.prime_three).K)
        (R (jn a)) (R (jn b)) := fun a b ha hb hab =>
    e.modelAdj hY hΩ hex hP1 hO3 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) (nd.cl _)
      (nd.cl _) (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _)
      (nd.conjSub_w h2 hab)
  have hlinR : ∀ a b : ℕ, a < u + 5 → b < u + 5 → DNodes3.DAdj (jn a) (jn b) →
      ∃ W, LinearBlockStandardPair 𝔽₃ W (R (jn a)) (R (jn b)) := fun a b ha hb hab => by
    obtain ⟨W, hW⟩ := nd.pair_of_adj hab
    exact e.pair_to_model hY hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) hW
  have hadj35 : DNodes3.DAdj (jn (u + 2)) (jn (u + 4)) := by
    simp [DNodes3.DAdj, edgeD, hjn (u + 2) (by omega), hjn (u + 4) (by omega)]
  have hn45 : ¬ DNodes3.DAdj (jn (u + 3)) (jn (u + 4)) := by
    simp [DNodes3.DAdj, edgeD, hjn (u + 3) (by omega), hjn (u + 4) (by omega)]
  have hnadjtw : ∀ a, a ≤ u + 1 → ¬ DNodes3.DAdj (jn a) (jn (u + 4)) := fun a ha => by
    simp [DNodes3.DAdj, edgeD, hjn a (by omega), hjn (u + 4) (by omega)]
    omega
  have hne54 : R (jn (u + 4)) ≠ R (jn (u + 3)) := fun h =>
    nd.ne_J (hne (u + 4) (u + 3) (by omega) (by omega) (by omega))
      (locImg_injOn3 hΩ hex hP1 hO3 (hx _) (hx _) (by rw [hLR, hLR, h]))
  obtain ⟨T₁, hT₁, T₂, hT₂, hc, s₁, t₁, s₂, t₂, hnc, hT12⟩ := exists_bridges_spin3 hQ
    (u := u) hdim cq
    (fun A hA B hB hl => exists_lin_of_map3 (not_three_dvd_card_center hY.cop)
      (spinAction (quadOdd (u + 6) 𝔽₃)) cq.ker_le (cq.pow3 A hA) (cq.pow3 B hB) hl)
    (R := fun a => R (jn a)) (Rtw := R (jn (u + 4))) (fun a ha => hRf _) (hRf _)
    (fun a ha => hadjR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a ha => hlinR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a b hab hb => hcommR a b (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a b (by omega) (by omega) (by omega)) (hnadj a b hab hb)))
    (hadjR (u + 2) (u + 4) (by omega) (by omega) hadj35)
    (fun a ha => hcommR a (u + 4) (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a (u + 4) (by omega) (by omega) (by omega)) (hnadjtw a ha)))
    (hcommR (u + 3) (u + 4) (by omega) (by omega)
      (nd.commutes_of_not_adj (hne (u + 3) (u + 4) (by omega) (by omega) (by omega)) hn45))
    hne54
  obtain ⟨N₁, hN₁, hNT₁⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hNT₂⟩ := e.comp T₂ hT₂
  have hjnfin : ∀ a : Fin (u + 5), jn a.val = a := fun a => Fin.ext (hjn a.val a.isLt)
  have back : ∀ {N : Subgroup G} {T : Subgroup (modelUniv .POmegaOdd (u + 6) 3 1
      Nat.prime_three).K}, N ∈ centralizingMembers Ω {x} → T ∈ fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd (u + 6) 3 1 Nat.prime_three).D → locImg Ω x N = T.map e.φ →
      ∀ a : Fin (u + 5), Commutes T (R (jn a.val)) → Commutes N (nd.J a) := by
    intro N T hN hT hNT a hTa
    rw [hjnfin a] at hTa
    exact (e.commutes_iff hY hΩ hex hP1 hO3 hN (hx a) hT hNT (hLR a)).mpr hTa
  have pairs : ∀ {N : Subgroup G} {T : Subgroup (modelUniv .POmegaOdd (u + 6) 3 1
      Nat.prime_three).K}, N ∈ centralizingMembers Ω {x} → locImg Ω x N = T.map e.φ →
      ∀ k : ℕ, k < u + 5 → (∃ W, LinearBlockStandardPair 𝔽₃ W (R (jn k)) T) →
      ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J (jn k)) N := by
    intro N T hN hNT k hk ⟨W, hW⟩
    exact e.pair_of_model hΩ hex hP1 hO3 (hx _) hN (hLR _) hNT hW
  refine ⟨N₁, hN₁, N₂, hN₂, fun a ha => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact back hN₁ hT₁ hNT₁ a (hc a.val ha).1
  · exact back hN₂ hT₂ hNT₂ a (hc a.val ha).2
  · rw [← h4]
    exact pairs hN₁ hNT₁ (u + 3) (by omega) s₁
  · rw [← h5]
    exact pairs hN₁ hNT₁ (u + 4) (by omega) t₁
  · rw [← h4]
    exact pairs hN₂ hNT₂ (u + 3) (by omega) s₂
  · rw [← h5]
    exact pairs hN₂ hNT₂ (u + 4) (by omega) t₂
  · intro h
    exact hnc ((e.commutes_iff hY hΩ hex hP1 hO3 hN₁ hN₂ hT₁ hNT₁ hNT₂).mp h)
  · intro h
    refine hT12 (eq_of_map_eq_of_pow3 e.φ e.ker_le (e.ker_cop hY) (hY.pow3 T₁ hT₁)
      (hY.pow3 T₂ hT₂) ?_)
    rw [← hNT₁, ← hNT₂, h]

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
